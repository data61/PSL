subsection \<open>Big-step semantics with conflation of constants and variables\<close>

theory Big_Step_Value_ML
imports Big_Step_Value
begin

definition mk_rec_env :: "(name, sclauses) fmap \<Rightarrow> (name, value) fmap \<Rightarrow> (name, value) fmap" where
"mk_rec_env css \<Gamma>' = fmmap_keys (\<lambda>name cs. Vrecabs css name \<Gamma>') css"

context special_constants begin

inductive veval' :: "(name, value) fmap \<Rightarrow> sterm \<Rightarrow> value \<Rightarrow> bool"  ("_/ \<turnstile>\<^sub>v/ _ \<down>/ _" [50,0,50] 50) where
const: "name |\<notin>| C \<Longrightarrow> fmlookup \<Gamma> name = Some val \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v Sconst name \<down> val" |
var: "fmlookup \<Gamma> name = Some val \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v Svar name \<down> val" |
abs: "\<Gamma> \<turnstile>\<^sub>v Sabs cs \<down> Vabs cs \<Gamma>" |
comb: "
  \<Gamma> \<turnstile>\<^sub>v t \<down> Vabs cs \<Gamma>' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v u \<down> u' \<Longrightarrow>
  vfind_match cs u' = Some (env, _, rhs) \<Longrightarrow>
  \<Gamma>' ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> val \<Longrightarrow>
  \<Gamma> \<turnstile>\<^sub>v t $\<^sub>s u \<down> val" |
rec_comb: "
  \<Gamma> \<turnstile>\<^sub>v t \<down> Vrecabs css name \<Gamma>' \<Longrightarrow>
  fmlookup css name = Some cs \<Longrightarrow>
  \<Gamma> \<turnstile>\<^sub>v u \<down> u' \<Longrightarrow>
  vfind_match cs u' = Some (env, _, rhs) \<Longrightarrow>
  \<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> val \<Longrightarrow>
  \<Gamma> \<turnstile>\<^sub>v t $\<^sub>s u \<down> val" |
constr: "name |\<in>| C \<Longrightarrow> list_all2 (veval' \<Gamma>) ts us \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>v name $$ ts \<down> Vconstr name us"

lemma veval'_sabs_svarE:
  assumes "\<Gamma> \<turnstile>\<^sub>v Sabs cs $\<^sub>s Svar n \<down> v"
  obtains u' env pat rhs
    where "fmlookup \<Gamma> n = Some u'"
          "vfind_match cs u' = Some (env, pat, rhs)"
          "\<Gamma> ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v"
using assms proof cases
  case (constr name ts)
  hence "strip_comb (Sabs cs $\<^sub>s Svar n) = strip_comb (name $$ ts)"
    by simp
  hence False
    apply (fold app_sterm_def)
    apply (simp add: strip_list_comb_const)
    apply (simp add: const_sterm_def)
    done
  thus ?thesis by simp
next
  case rec_comb
  hence False by cases
  thus ?thesis by simp
next
  case (comb cs' \<Gamma>' u' env pat rhs)
  moreover have "fmlookup \<Gamma> n = Some u'"
    using \<open>\<Gamma> \<turnstile>\<^sub>v Svar n \<down> u'\<close>
    proof cases
      case (constr name ts)
      hence False
        by (fold free_sterm_def) simp
      thus ?thesis by simp
    qed auto
  moreover have "cs = cs'" "\<Gamma> = \<Gamma>'"
    using \<open>\<Gamma> \<turnstile>\<^sub>v Sabs cs \<down> Vabs cs' \<Gamma>'\<close>
    by (cases; auto)+

  ultimately show ?thesis
    using that by auto
qed

lemma veval'_wellformed:
  assumes "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "wellformed t" "wellformed_venv \<Gamma>"
  shows "vwellformed v"
using assms proof induction
  case comb
  show ?case
    apply (rule comb)
    using comb by (auto simp: list_all_iff dest: vfind_match_elem intro: vwellformed.vmatch_env)
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact
  show ?case
    proof (rule rec_comb)
      show "wellformed_venv (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        proof (intro fmpred_add)
          show "wellformed_venv \<Gamma>'"
            using rec_comb by auto
        next
          show "wellformed_venv env"
            using rec_comb by (auto dest: vfind_match_elem intro: vwellformed.vmatch_env)
        next
          show "wellformed_venv (mk_rec_env css \<Gamma>')"
            unfolding mk_rec_env_def
            using rec_comb by (auto intro: fmdomI)
        qed
    next
      have "vwellformed (Vrecabs css name \<Gamma>')"
        unfolding mk_rec_env_def
        using rec_comb by (auto intro: fmdom'I)
      thus "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> rec_comb by (auto simp: list_all_iff)
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vwellformed us"
    using \<open>list_all2 _ _ _\<close> \<open>wellformed (_ $$ _)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      thus ?case
        using constr by (auto simp: app_sterm_def wellformed.list_comb)
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed auto

lemma (in constants) veval'_shadows:
  assumes "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "not_shadows_vconsts_env \<Gamma>" "\<not> shadows_consts t"
  shows "not_shadows_vconsts v"
using assms proof induction
  case comb
  show ?case
    apply (rule comb)
    using comb by (auto simp: list_all_iff dest: vfind_match_elem intro: not_shadows_vconsts.vmatch_env)
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact
  show ?case
    proof (rule rec_comb)
      show "not_shadows_vconsts_env (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        proof (intro fmpred_add)
          show "not_shadows_vconsts_env env"
            using rec_comb by (auto dest: vfind_match_elem intro: not_shadows_vconsts.vmatch_env)
        next
          show "not_shadows_vconsts_env (mk_rec_env css \<Gamma>')"
            unfolding mk_rec_env_def
            using rec_comb by (auto intro: fmdomI)
        next
          show "not_shadows_vconsts_env \<Gamma>'"
            using rec_comb by auto
        qed
    next
      have "not_shadows_vconsts (Vrecabs css name \<Gamma>')"
        using rec_comb by auto
      thus "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> rec_comb by (auto simp: list_all_iff)
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all (not_shadows_vconsts) us"
    using \<open>list_all2 _ _ _\<close> \<open>\<not> shadows_consts (name $$ ts)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      thus ?case
        using constr by (auto simp: shadows.list_comb app_sterm_def)
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed (auto simp: list_all_iff list_ex_iff)

lemma veval'_closed:
  assumes "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "closed_except t (fmdom \<Gamma>)" "closed_venv \<Gamma>"
  assumes "wellformed t" "wellformed_venv \<Gamma>"
  shows "vclosed v"
using assms proof induction
  case (comb \<Gamma> t cs \<Gamma>' u u' env pat rhs val)
  hence "vclosed (Vabs cs \<Gamma>')"
    by (auto simp: closed_except_def)

  have "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (rule vfind_match_elem; fact)+
  hence "fmdom env = patvars (mk_pat pat)"
    by (simp add: vmatch_dom)

  have "vwellformed (Vabs cs \<Gamma>')"
    apply (rule veval'_wellformed)
    using comb by auto
  hence "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close>
    by (auto simp: list_all_iff)
  hence "fmdom env = frees pat"
    unfolding \<open>fmdom env = _\<close>
    by (simp add: mk_pat_frees)

  show ?case
    proof (rule comb)
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close>
        by (auto simp: list_all_iff)
    next
      show "closed_venv (\<Gamma>' ++\<^sub>f env)"
        apply rule
        using \<open>vclosed (Vabs cs \<Gamma>')\<close> apply auto[]
        apply (rule vclosed.vmatch_env)
         apply (rule vfind_match_elem)
        using comb by (auto simp: closed_except_def)
    next
      show "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f env))"
        using \<open>vclosed (Vabs cs \<Gamma>')\<close> \<open>fmdom env = frees pat\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    next
      show "wellformed_venv (\<Gamma>' ++\<^sub>f env)"
        apply rule
        using \<open>vwellformed (Vabs cs \<Gamma>')\<close> apply auto[]
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
        using comb by auto
    qed
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  have "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (rule vfind_match_elem; fact)+
  hence "fmdom env = patvars (mk_pat pat)"
    by (simp add: vmatch_dom)

  have "vwellformed (Vrecabs css name \<Gamma>')"
    apply (rule veval'_wellformed)
    using rec_comb by auto
  hence "wellformed_clauses cs"
    using rec_comb by auto
  hence "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close>
    by (auto simp: list_all_iff)
  hence "fmdom env = frees pat"
    unfolding \<open>fmdom env = _\<close>
    by (simp add: mk_pat_frees)
  show ?case
    proof (rule rec_comb)
      show "closed_venv (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        proof (intro fmpred_add)
          show "closed_venv \<Gamma>'"
            using rec_comb by (auto simp: closed_except_def)
        next
          show "closed_venv env"
            using rec_comb by (auto simp: closed_except_def dest: vfind_match_elem intro: vclosed.vmatch_env)
        next
          show "closed_venv (mk_rec_env css \<Gamma>')"
            unfolding mk_rec_env_def
            using rec_comb by (auto simp: closed_except_def intro: fmdomI)
        qed
    next
      have "vclosed (Vrecabs css name \<Gamma>')"
        using mk_rec_env_def
        using rec_comb by (auto simp: closed_except_def intro: fmdom'I)
      hence "closed_except rhs (fmdom \<Gamma>' |\<union>| frees pat)"
        apply simp
        apply (elim conjE)
        apply (drule fmpredD[where m = css])
         apply (rule rec_comb)
        using \<open>(pat, rhs) \<in> set cs\<close>
        unfolding list_all_iff by auto

      thus "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env))"
        unfolding closed_except_def
        using \<open>fmdom env = frees pat\<close>
        by auto
    next
      show "wellformed rhs"
        using \<open>wellformed_clauses cs\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    next
      show "wellformed_venv (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        proof (intro fmpred_add)
          show "wellformed_venv \<Gamma>'"
            using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> by auto
        next
          show "wellformed_venv env"
            using rec_comb by (auto dest: vfind_match_elem intro: veval'_wellformed vwellformed.vmatch_env)
        next
          show "wellformed_venv (mk_rec_env css \<Gamma>')"
            unfolding mk_rec_env_def
            using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> by (auto intro: fmdomI)
        qed
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vclosed us"
    using \<open>list_all2 _ _ _\<close> \<open>closed_except (_ $$ _) _\<close> \<open>wellformed (_ $$ _)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      with constr show ?case
        unfolding closed.list_comb wellformed.list_comb
        by (auto simp: Sterm.closed_except_simps)
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed (auto simp: Sterm.closed_except_simps)

primrec vwelldefined' :: "value \<Rightarrow> bool" where
"vwelldefined' (Vconstr name vs) \<longleftrightarrow> list_all vwelldefined' vs" |
"vwelldefined' (Vabs cs \<Gamma>) \<longleftrightarrow>
  pred_fmap id (fmmap vwelldefined' \<Gamma>) \<and>
  list_all (\<lambda>(pat, t). consts t |\<subseteq>| (fmdom \<Gamma> |\<union>| C)) cs \<and>
  fdisjnt C (fmdom \<Gamma>)" |
"vwelldefined' (Vrecabs css name \<Gamma>) \<longleftrightarrow>
  pred_fmap id (fmmap vwelldefined' \<Gamma>) \<and>
  pred_fmap (\<lambda>cs.
    list_all (\<lambda>(pat, t). consts t |\<subseteq>| fmdom \<Gamma> |\<union>| (C |\<union>| fmdom css)) cs \<and>
    fdisjnt C (fmdom \<Gamma>)) css \<and>
  name |\<in>| fmdom css \<and>
  fdisjnt C (fmdom css)"

lemma vmatch_welldefined':
  assumes "vmatch pat v = Some env" "vwelldefined' v"
  shows "fmpred (\<lambda>_. vwelldefined') env"
using assms proof (induction pat v arbitrary: env rule: vmatch_induct)
  case (constr name ps name' vs)
  hence
    "map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch ps vs)) = Some env"
    "name = name'" "length ps = length vs"
    by (auto split: if_splits)
  then obtain envs where "env = foldl (++\<^sub>f) fmempty envs" "map2 vmatch ps vs = map Some envs"
    by (blast dest: those_someD)

  moreover have "fmpred (\<lambda>_. vwelldefined') env" if "env \<in> set envs" for env
    proof -
      from that have "Some env \<in> set (map2 vmatch ps vs)"
        unfolding \<open>map2 _ _ _ = _\<close> by simp
      then obtain p v where "p \<in> set ps" "v \<in> set vs" "vmatch p v = Some env"
        by (auto elim: map2_elemE)
      hence "vwelldefined' v"
        using constr by (simp add: list_all_iff)
      show ?thesis
        by (rule constr; safe?) fact+
    qed

    ultimately show ?case
      by auto
qed auto

(* FIXME ad hoc rules after introduction of "constants" locale *)
lemma sconsts_list_comb:
   "consts (list_comb f xs) |\<subseteq>| S \<longleftrightarrow> consts f |\<subseteq>| S \<and> list_all (\<lambda>x. consts x |\<subseteq>| S) xs"
by (induction xs arbitrary: f) auto

lemma sconsts_sabs:
  "consts (Sabs cs) |\<subseteq>| S \<longleftrightarrow> list_all (\<lambda>(_, t). consts t |\<subseteq>| S) cs"
  apply (auto simp: list_all_iff ffUnion_alt_def dest!: ffUnion_least_rev)
   apply (subst (asm) list_all_iff_fset[symmetric])
   apply (auto simp: list_all_iff fset_of_list_elem)
  done

lemma (in constants) veval'_welldefined':
  assumes "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "fdisjnt C (fmdom \<Gamma>)"
  assumes "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C" "fmpred (\<lambda>_. vwelldefined') \<Gamma>"
  assumes "wellformed t" "wellformed_venv \<Gamma>"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>"
  shows "vwelldefined' v"
using assms proof induction
  case (abs \<Gamma> cs)
  thus ?case
    unfolding sconsts_sabs
    by (auto simp: list_all_iff list_ex_iff)
next
  case (comb \<Gamma> t cs \<Gamma>' u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs"
    by (auto dest: vfind_match_elem)
  moreover have "vwelldefined' (Vabs cs \<Gamma>')"
    using comb by auto
  ultimately have "consts rhs |\<subseteq>| fmdom \<Gamma>' |\<union>| C"
    by (auto simp: list_all_iff)

  have "vwellformed (Vabs cs \<Gamma>')"
    apply (rule veval'_wellformed)
    using comb by auto
  hence "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close>
    by (auto simp: list_all_iff)
  hence "frees pat = patvars (mk_pat pat)"
    by (simp add: mk_pat_frees)
  hence "fmdom env = frees pat"
    apply simp
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply (rule comb)
    done

  have "not_shadows_vconsts (Vabs cs \<Gamma>')"
    apply (rule veval'_shadows)
    using comb by auto

  have "vwelldefined' (Vabs cs \<Gamma>')"
    using comb by auto

  show ?case
    proof (rule comb)
      show "consts rhs |\<subseteq>| fmdom (\<Gamma>' ++\<^sub>f env) |\<union>| C"
        using \<open>consts rhs |\<subseteq>| fmdom \<Gamma>' |\<union>| C\<close>
        by auto
    next
      have "vwelldefined' u'"
        using comb by auto
      hence "fmpred (\<lambda>_. vwelldefined') env"
        using comb
        by (auto intro: vmatch_welldefined' dest: vfind_match_elem)
      thus "fmpred (\<lambda>_. vwelldefined') (\<Gamma>' ++\<^sub>f env)"
        using \<open>vwelldefined' (Vabs cs \<Gamma>')\<close> by auto
    next
      have "fdisjnt C (fmdom \<Gamma>')"
        using \<open>vwelldefined' (Vabs cs \<Gamma>')\<close>
        by simp
      moreover have "fdisjnt C (fmdom env)"
        unfolding \<open>fmdom env = frees pat\<close>
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vabs cs \<Gamma>')\<close>
        by (auto simp: list_all_iff all_consts_def fdisjnt_alt_def)
      ultimately show "fdisjnt C (fmdom (\<Gamma>' ++\<^sub>f env))"
        unfolding fdisjnt_alt_def by auto
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close>
        by (auto simp: list_all_iff)
    next
      have "wellformed_venv \<Gamma>'"
        using \<open>vwellformed (Vabs cs \<Gamma>')\<close> by simp
      moreover have "wellformed_venv env"
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
        using comb by auto
      ultimately show "wellformed_venv (\<Gamma>' ++\<^sub>f env)"
        by blast
    next
      have "not_shadows_vconsts_env \<Gamma>'"
        using \<open>not_shadows_vconsts (Vabs cs \<Gamma>')\<close> by simp
      moreover have "not_shadows_vconsts_env env"
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
        using comb by auto
      ultimately show "not_shadows_vconsts_env (\<Gamma>' ++\<^sub>f env)"
        by blast
    next
      show "\<not> shadows_consts rhs"
        using \<open>not_shadows_vconsts (Vabs cs \<Gamma>')\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    qed
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs"
    by (auto dest: vfind_match_elem)
  moreover have "vwelldefined' (Vrecabs css name \<Gamma>')"
    using rec_comb by auto
  ultimately have "consts rhs |\<subseteq>| fmdom \<Gamma>' |\<union>| (C |\<union>| fmdom css)"
    using \<open>fmlookup css name = Some cs\<close>
    by (auto simp: list_all_iff dest!: fmpredD[where m = css])

  have "vwellformed (Vrecabs css name \<Gamma>')"
    apply (rule veval'_wellformed)
    using rec_comb by auto
  hence "wellformed_clauses cs"
    using rec_comb by auto
  hence "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close>
    by (auto simp: list_all_iff)
  hence "frees pat = patvars (mk_pat pat)"
    by (simp add: mk_pat_frees)
  hence "fmdom env = frees pat"
    apply simp
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply (rule rec_comb)
    done

  have "not_shadows_vconsts (Vrecabs css name \<Gamma>')"
    apply (rule veval'_shadows)
    using rec_comb by auto

  have "vwelldefined' (Vrecabs css name \<Gamma>')"
    using rec_comb by auto

  show ?case
    proof (rule rec_comb)
      show "consts rhs |\<subseteq>| fmdom (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env) |\<union>| C"
        using \<open>consts rhs |\<subseteq>| _\<close> unfolding mk_rec_env_def
        by auto
    next
      have "fmpred (\<lambda>_. vwelldefined') \<Gamma>'"
        using \<open>vwelldefined' (Vrecabs css name \<Gamma>')\<close> by auto
      moreover have "fmpred (\<lambda>_. vwelldefined') (mk_rec_env css \<Gamma>')"
        unfolding mk_rec_env_def
        using rec_comb by (auto intro: fmdomI)
      moreover have "fmpred (\<lambda>_. vwelldefined') env"
        using rec_comb by (auto dest: vfind_match_elem intro: vmatch_welldefined')
      ultimately show "fmpred (\<lambda>_. vwelldefined') (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        by blast
    next
      have "fdisjnt C (fmdom \<Gamma>')"
        using rec_comb by auto
      moreover have "fdisjnt C (fmdom env)"
        unfolding \<open>fmdom env = frees pat\<close>
        using \<open>fmlookup css name = Some cs\<close> \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>')\<close>
        apply auto
        apply (drule fmpredD[where m = css])
        by (auto simp: list_all_iff all_consts_def fdisjnt_alt_def)
      moreover have "fdisjnt C (fmdom (mk_rec_env css \<Gamma>'))"
        unfolding mk_rec_env_def
        using \<open>vwelldefined' (Vrecabs css name \<Gamma>')\<close>
        by simp
      ultimately show "fdisjnt C (fmdom (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env))"
        unfolding fdisjnt_alt_def by auto
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>wellformed_clauses cs\<close>
        by (auto simp: list_all_iff)
    next
      have "wellformed_venv \<Gamma>'"
        using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> by simp
      moreover have "wellformed_venv (mk_rec_env css \<Gamma>')"
        unfolding mk_rec_env_def
        using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close>
        by (auto intro: fmdomI)
      moreover have "wellformed_venv env"
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
        using rec_comb by auto
      ultimately show "wellformed_venv (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        by blast
    next
      have "not_shadows_vconsts_env \<Gamma>'"
        using \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>')\<close> by simp
      moreover have "not_shadows_vconsts_env (mk_rec_env css \<Gamma>')"
        unfolding mk_rec_env_def
        using \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>')\<close>
        by (auto intro: fmdomI)
      moreover have "not_shadows_vconsts_env env"
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
        using rec_comb by auto
      ultimately show "not_shadows_vconsts_env (\<Gamma>' ++\<^sub>f mk_rec_env css \<Gamma>' ++\<^sub>f env)"
        by blast
    next
      show "\<not> shadows_consts rhs"
        using rec_comb \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>')\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vwelldefined' us"
    using \<open>list_all2 _ _ _\<close> \<open>consts (name $$ ts) |\<subseteq>| _\<close>
    using \<open>wellformed (name $$ ts)\<close> \<open>\<not> shadows_consts (name $$ ts)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      with constr show ?case
        unfolding wellformed.list_comb shadows.list_comb
        by (auto simp: consts_list_comb)
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed auto

end


subsubsection (in special_constants) \<open>Correctness wrt @{const veval}\<close>

context vrules begin

text \<open>
  The following relation can be characterized as follows:
  \<^item> Values have to have the same structure. (We prove an interpretation of @{const value_struct_rel}.)
  \<^item> For closures, the captured environments must agree on constants and variables occurring in the
    body.
  The first @{typ value} argument is from @{const veval} (i.e. from
  @{theory CakeML_Codegen.Big_Step_Value}), the second from @{const veval'}.
\<close>

(* FIXME move into locale *)

coinductive vrelated :: "value \<Rightarrow> value \<Rightarrow> bool" ("\<turnstile>\<^sub>v/ _ \<approx> _" [0, 50] 50) where
constr: "list_all2 vrelated ts us \<Longrightarrow> \<turnstile>\<^sub>v Vconstr name ts \<approx> Vconstr name us" |
abs:
  "fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<Longrightarrow>
   fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) \<Gamma>\<^sub>2 \<Longrightarrow>
     \<turnstile>\<^sub>v Vabs cs \<Gamma>\<^sub>1 \<approx> Vabs cs \<Gamma>\<^sub>2" |
rec_abs:
  "pred_fmap (\<lambda>cs.
    fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<and>
    fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) (\<Gamma>\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>2)) css \<Longrightarrow>
     name |\<in>| fmdom css \<Longrightarrow>
     \<turnstile>\<^sub>v Vrecabs css name \<Gamma>\<^sub>1 \<approx> Vrecabs css name \<Gamma>\<^sub>2"

text \<open>
  Perhaps unexpectedly, @{term vrelated} is not reflexive. The reason is that it does not just check
  syntactic equality including captured environments, but also adherence to the external rules.
\<close>

sublocale vrelated: value_struct_rel vrelated
proof
  fix t\<^sub>1 t\<^sub>2
  assume "\<turnstile>\<^sub>v t\<^sub>1 \<approx> t\<^sub>2"
  thus "veq_structure t\<^sub>1 t\<^sub>2"
    apply (induction t\<^sub>1 arbitrary: t\<^sub>2)
      apply (erule vrelated.cases; auto)
      apply (erule list.rel_mono_strong)
      apply simp
     apply (erule vrelated.cases; auto)
    apply (erule vrelated.cases; auto)
    done
next
  fix name name' and ts us :: "value list"
  show "\<turnstile>\<^sub>v Vconstr name ts \<approx> Vconstr name' us \<longleftrightarrow> (name = name' \<and> list_all2 vrelated ts us)"
    proof safe
      assume "\<turnstile>\<^sub>v Vconstr name ts \<approx> Vconstr name' us"
      thus "name = name'" "list_all2 vrelated ts us"
        by (cases; auto)+
    qed (auto intro: vrelated.intros)
qed

text \<open>
  The technically involved relation @{term vrelated} implies a weaker, but more intuitive property:
  If @{prop "\<turnstile>\<^sub>v t \<approx> u"} then \<open>t\<close> and \<open>u\<close> are equal after termification (i.e. conversion with
  @{term value_to_sterm}). In fact, if both terms are ground terms, it collapses to equality. This
  follows directly from the interpretation of @{const value_struct_rel}.
\<close>

lemma veval'_correct:
  assumes "\<Gamma>\<^sub>2 \<turnstile>\<^sub>v t \<down> v\<^sub>2" "wellformed t" "wellformed_venv \<Gamma>\<^sub>2"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>\<^sub>2"
  assumes "welldefined t"
  assumes "fmpred (\<lambda>_. vwelldefined) \<Gamma>\<^sub>1"
  assumes "fmrel_on_fset (frees t) vrelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2"
  assumes "fmrel_on_fset (consts t) vrelated (fmap_of_list rs) \<Gamma>\<^sub>2"
  obtains v\<^sub>1 where "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> v\<^sub>1" "\<turnstile>\<^sub>v v\<^sub>1 \<approx> v\<^sub>2"
apply atomize_elim
using assms proof (induction arbitrary: \<Gamma>\<^sub>1)
  case (const name \<Gamma>\<^sub>2 val\<^sub>2)
  hence "fmrel_on_fset {|name|} vrelated (fmap_of_list rs) \<Gamma>\<^sub>2"
    by simp
  have "rel_option vrelated (fmlookup (fmap_of_list rs) name) (fmlookup \<Gamma>\<^sub>2 name)"
    apply (rule fmrel_on_fsetD[where S = "{|name|}"])
     apply simp
    apply fact
    done
  then obtain val\<^sub>1 where "fmlookup (fmap_of_list rs) name = Some val\<^sub>1" "\<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    using const by cases auto
  hence "(name, val\<^sub>1) \<in> set rs"
    by (auto dest: fmap_of_list_SomeD)

  show ?case
    apply (intro conjI exI)
     apply (rule veval.const)
     apply fact+
    done
next
  case (var \<Gamma>\<^sub>2 name val\<^sub>2)
  hence "fmrel_on_fset {|name|} vrelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2"
    by simp
  have "rel_option vrelated (fmlookup \<Gamma>\<^sub>1 name) (fmlookup \<Gamma>\<^sub>2 name)"
    apply (rule fmrel_on_fsetD[where S = "{|name|}"])
     apply simp
    apply fact
    done
  then obtain val\<^sub>1 where "fmlookup \<Gamma>\<^sub>1 name = Some val\<^sub>1" "\<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    using var by cases auto
  show ?case
    apply (intro conjI exI)
     apply (rule veval.var)
     apply fact+
    done
next
  case abs
  thus ?case
    by (auto intro!: veval.abs vrelated.abs)
next
  case (comb \<Gamma>\<^sub>2 t cs \<Gamma>'\<^sub>2 u u'\<^sub>2 env\<^sub>2 pat rhs val\<^sub>2)
  hence "\<exists>v. rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> v \<and> \<turnstile>\<^sub>v v \<approx> Vabs cs \<Gamma>'\<^sub>2"
    by (auto intro: fmrel_on_fsubset)
  then obtain v where "\<turnstile>\<^sub>v v \<approx> Vabs cs \<Gamma>'\<^sub>2" "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> v"
    by blast
  moreover then obtain \<Gamma>'\<^sub>1
    where "v = Vabs cs \<Gamma>'\<^sub>1"
      and "fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>'\<^sub>1 \<Gamma>'\<^sub>2"
      and "fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) \<Gamma>'\<^sub>2"
    by cases auto
  ultimately have "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> Vabs cs \<Gamma>'\<^sub>1"
    by simp

  have "\<exists>u\<^sub>1'. rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v u \<down> u\<^sub>1' \<and> \<turnstile>\<^sub>v u\<^sub>1' \<approx> u'\<^sub>2"
    using comb by (auto intro: fmrel_on_fsubset)
  then obtain u'\<^sub>1 where "\<turnstile>\<^sub>v u'\<^sub>1 \<approx> u'\<^sub>2" "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v u \<down> u'\<^sub>1"
    by blast

  have "rel_option (rel_prod (fmrel vrelated) (=)) (vfind_match cs u'\<^sub>1) (vfind_match cs u'\<^sub>2)"
    by (rule vrelated.vfind_match_rel') fact
  then obtain env\<^sub>1 where "vfind_match cs u'\<^sub>1 = Some (env\<^sub>1, pat, rhs)" "fmrel vrelated env\<^sub>1 env\<^sub>2"
    using \<open>vfind_match cs u'\<^sub>2 = _\<close>
    by cases auto

  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact

  have "vwellformed (Vabs cs \<Gamma>'\<^sub>2)"
    apply (rule veval'_wellformed)
      apply fact
    using \<open>wellformed (t $\<^sub>s u)\<close> apply simp
    apply fact+
    done
  hence "wellformed_venv \<Gamma>'\<^sub>2"
    by simp

  have "vwelldefined v"
    apply (rule veval_welldefined)
      apply fact+
    using comb by simp
  hence "vwelldefined (Vabs cs \<Gamma>'\<^sub>1)"
    unfolding \<open>v = _\<close> .

  have "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>'\<^sub>2)\<close>
    by (auto simp: list_all_iff)

  have "fmdom env\<^sub>1 = patvars (mk_pat pat)"
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply fact
    done
  with \<open>linear pat\<close> have "fmdom env\<^sub>1 = frees pat"
    by (simp add: mk_pat_frees)

  have "fmdom env\<^sub>2 = patvars (mk_pat pat)"
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply fact
    done
  with \<open>linear pat\<close> have "fmdom env\<^sub>2 = frees pat"
    by (simp add: mk_pat_frees)

  note fset_of_list_map[simp del]
  have "\<exists>val\<^sub>1. rs, \<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1 \<turnstile>\<^sub>v rhs \<down> val\<^sub>1 \<and> \<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    proof (rule comb)
      show "fmrel_on_fset (frees rhs) vrelated (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        proof
          fix name
          assume "name |\<in>| frees rhs"
          show "rel_option vrelated (fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name) (fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name)"
            proof (cases "name |\<in>| frees pat")
              case True
              hence "name |\<in>| fmdom env\<^sub>1" "name |\<in>| fmdom env\<^sub>2"
                using \<open>fmdom env\<^sub>1 = frees pat\<close> \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp+
              hence "fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name = fmlookup env\<^sub>1 name" "fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name = fmlookup env\<^sub>2 name"
                by auto
              thus ?thesis
                using \<open>fmrel vrelated env\<^sub>1 env\<^sub>2\<close>
                by auto
            next
              case False
              hence "name |\<notin>| fmdom env\<^sub>1" "name |\<notin>| fmdom env\<^sub>2"
                using \<open>fmdom env\<^sub>1 = frees pat\<close> \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp+
              hence "fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name = fmlookup \<Gamma>'\<^sub>1 name" "fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name = fmlookup \<Gamma>'\<^sub>2 name"
                by auto

              moreover have "name |\<in>| frees (Sabs cs)"
                using False \<open>name |\<in>| frees rhs\<close> \<open>(pat, rhs) \<in> set cs\<close>
                apply (auto simp: ffUnion_alt_def)
                apply (rule fBexI[where x = "frees rhs |-| frees pat"])
                 apply (auto simp: fset_of_list_elem)
                done

              ultimately show ?thesis
                using \<open>fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>'\<^sub>1 \<Gamma>'\<^sub>2\<close>
                by (auto dest: fmrel_on_fsetD)
            qed
        qed
    next
      have "not_shadows_vconsts (Vabs cs \<Gamma>'\<^sub>2)"
        apply (rule veval'_shadows)
          apply fact+
        using comb by auto
      thus "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)

      show "not_shadows_vconsts_env (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        apply rule
        using \<open>not_shadows_vconsts (Vabs cs \<Gamma>'\<^sub>2)\<close> apply simp
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
          apply fact
         apply fact
        using comb by auto

      show "fmrel_on_fset (consts rhs) vrelated (fmap_of_list rs) (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        proof
          fix name
          assume "name |\<in>| consts rhs"
          hence "name |\<in>| consts (Sabs cs)"
            using \<open>(pat, rhs) \<in> set cs\<close>
            by (auto intro!: fBexI simp: fset_of_list_elem ffUnion_alt_def)
          hence "rel_option vrelated (fmlookup (fmap_of_list rs) name) (fmlookup \<Gamma>'\<^sub>2 name)"
            using \<open>fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) \<Gamma>'\<^sub>2\<close>
            by (auto dest: fmrel_on_fsetD)
          moreover have "name |\<notin>| fmdom env\<^sub>2"
            proof
              assume "name |\<in>| fmdom env\<^sub>2"
              hence "fmlookup env\<^sub>2 name \<noteq> None"
                by (meson fmdom_notI)
              then obtain v where "fmlookup env\<^sub>2 name = Some v"
                by blast
              hence "name |\<in>| fmdom env\<^sub>2"
                by (auto intro: fmdomI)
              hence "name |\<in>| frees pat"
                using \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp

              have "welldefined rhs"
                using \<open>vwelldefined (Vabs cs \<Gamma>'\<^sub>1)\<close> \<open>(pat, rhs) \<in> set cs\<close>
                by (auto simp: list_all_iff)
              hence "name |\<in>| fst |`| fset_of_list rs |\<union>| C"
                using \<open>name |\<in>| consts rhs\<close>
                by (auto simp: all_consts_def)
              moreover have "\<not> shadows_consts pat"
                using \<open>not_shadows_vconsts (Vabs cs \<Gamma>'\<^sub>2)\<close> \<open>(pat, rhs) \<in> set cs\<close>
                by (auto simp: list_all_iff shadows_consts_def all_consts_def)
              ultimately show False
                using \<open>name |\<in>| frees pat\<close>
                unfolding shadows_consts_def fdisjnt_alt_def all_consts_def
                by auto
            qed
          ultimately show "rel_option vrelated (fmlookup (fmap_of_list rs) name) (fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name)"
            by simp
        qed
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>'\<^sub>2)\<close>
        by (auto simp: list_all_iff)
    next
      have "wellformed_venv \<Gamma>'\<^sub>2"
        by fact
      moreover have "wellformed_venv env\<^sub>2"
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
          apply fact
        using \<open>wellformed (t $\<^sub>s u)\<close> apply simp
        apply fact+
        done
      ultimately show "wellformed_venv (\<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        by blast
    next
      show "welldefined rhs"
        using \<open>vwelldefined (Vabs cs \<Gamma>'\<^sub>1)\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    next
      have "fmpred (\<lambda>_. vwelldefined) \<Gamma>'\<^sub>1"
        using \<open>vwelldefined (Vabs cs \<Gamma>'\<^sub>1)\<close> by simp

      moreover have "fmpred (\<lambda>_. vwelldefined) env\<^sub>1"
        apply (rule vwelldefined.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval_welldefined)
          apply fact
         apply fact
        using comb apply simp
        done

      ultimately show "fmpred (\<lambda>_. vwelldefined) (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1)"
        by blast
    qed

  then obtain val\<^sub>1 where "rs, \<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1 \<turnstile>\<^sub>v rhs \<down> val\<^sub>1" "\<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    by blast

  show ?case
    apply (intro conjI exI)
     apply (rule veval.comb)
        apply fact+
    done
next
  \<comment> \<open>Almost verbatim copy from \<open>comb\<close> case.\<close>
  case (rec_comb \<Gamma>\<^sub>2 t css name \<Gamma>'\<^sub>2 cs u u'\<^sub>2 env\<^sub>2 pat rhs val\<^sub>2)
  hence "\<exists>v. rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> v \<and> \<turnstile>\<^sub>v v \<approx> Vrecabs css name \<Gamma>'\<^sub>2"
    by (auto intro: fmrel_on_fsubset)
  then obtain v where "\<turnstile>\<^sub>v v \<approx> Vrecabs css name \<Gamma>'\<^sub>2" "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> v"
    by blast
  moreover then obtain \<Gamma>'\<^sub>1
    where "v = Vrecabs css name \<Gamma>'\<^sub>1"
      and "fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>'\<^sub>1 \<Gamma>'\<^sub>2"
      and "fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2)"
    using \<open>fmlookup css name = Some cs\<close>
    by cases auto
  ultimately have "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> Vrecabs css name \<Gamma>'\<^sub>1"
    by simp

  have "\<exists>u\<^sub>1'. rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v u \<down> u\<^sub>1' \<and> \<turnstile>\<^sub>v u\<^sub>1' \<approx> u'\<^sub>2"
    using rec_comb by (auto intro: fmrel_on_fsubset)
  then obtain u'\<^sub>1 where "\<turnstile>\<^sub>v u'\<^sub>1 \<approx> u'\<^sub>2" "rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v u \<down> u'\<^sub>1"
    by blast

  have "rel_option (rel_prod (fmrel vrelated) (=)) (vfind_match cs u'\<^sub>1) (vfind_match cs u'\<^sub>2)"
    by (rule vrelated.vfind_match_rel') fact
  then obtain env\<^sub>1 where "vfind_match cs u'\<^sub>1 = Some (env\<^sub>1, pat, rhs)" "fmrel vrelated env\<^sub>1 env\<^sub>2"
    using \<open>vfind_match cs u'\<^sub>2 = _\<close>
    by cases auto

  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact

  have "vwellformed (Vrecabs css name \<Gamma>'\<^sub>2)"
    apply (rule veval'_wellformed)
      apply fact
    using \<open>wellformed (t $\<^sub>s u)\<close> apply simp
    apply fact+
    done
  hence "wellformed_venv \<Gamma>'\<^sub>2" "vwellformed (Vabs cs \<Gamma>'\<^sub>2)"
    using rec_comb by auto

  have "vwelldefined v"
    apply (rule veval_welldefined)
      apply fact+
    using rec_comb by simp
  hence "vwelldefined (Vrecabs css name \<Gamma>'\<^sub>1)"
    unfolding \<open>v = _\<close> .
  hence "vwelldefined (Vabs cs \<Gamma>'\<^sub>1)"
    using rec_comb by auto

  have "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>'\<^sub>2)\<close>
    by (auto simp: list_all_iff)

  have "fmdom env\<^sub>1 = patvars (mk_pat pat)"
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply fact
    done
  with \<open>linear pat\<close> have "fmdom env\<^sub>1 = frees pat"
    by (simp add: mk_pat_frees)

  have "fmdom env\<^sub>2 = patvars (mk_pat pat)"
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply fact
    done
  with \<open>linear pat\<close> have "fmdom env\<^sub>2 = frees pat"
    by (simp add: mk_pat_frees)

  note fset_of_list_map[simp del]
  have "\<exists>val\<^sub>1. rs, \<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1 \<turnstile>\<^sub>v rhs \<down> val\<^sub>1 \<and> \<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    proof (rule rec_comb)
      have "not_shadows_vconsts (Vrecabs css name \<Gamma>'\<^sub>2)"
        apply (rule veval'_shadows)
          apply fact+
        using rec_comb by auto
      thus "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> rec_comb
        by (auto simp: list_all_iff)
      hence "fdisjnt all_consts (frees rhs)"
        by (rule shadows_consts_frees)

      have "not_shadows_vconsts_env \<Gamma>'\<^sub>2"
        using \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>'\<^sub>2)\<close>
        by simp

      moreover have "not_shadows_vconsts_env (mk_rec_env css \<Gamma>'\<^sub>2)"
        unfolding mk_rec_env_def
        using \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>'\<^sub>2)\<close>
        by (auto intro: fmdomI)

      moreover have "not_shadows_vconsts_env env\<^sub>2"
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
          apply fact
         apply fact
        using rec_comb by auto

      ultimately show "not_shadows_vconsts_env (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        by auto

      have "not_shadows_vconsts (Vabs cs \<Gamma>'\<^sub>2)"
        using \<open>not_shadows_vconsts (Vrecabs _ _ _)\<close> rec_comb
        by auto

      show "fmrel_on_fset (frees rhs) vrelated (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        proof
          fix name
          assume "name |\<in>| frees rhs"
          moreover have "fmdom css |\<subseteq>| all_consts"
            using \<open>vwelldefined (Vrecabs _ _ _)\<close> unfolding all_consts_def
            by auto
          ultimately have "name |\<notin>| fmdom css"
            using \<open>fdisjnt _ (frees rhs)\<close>
            unfolding fdisjnt_alt_def
            by (metis (full_types) fempty_iff finterI fset_rev_mp)

          show "rel_option vrelated (fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name) (fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name)"
            proof (cases "name |\<in>| frees pat")
              case True
              hence "name |\<in>| fmdom env\<^sub>1" "name |\<in>| fmdom env\<^sub>2"
                using \<open>fmdom env\<^sub>1 = frees pat\<close> \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp+
              hence
                "fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name = fmlookup env\<^sub>1 name"
                "fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name = fmlookup env\<^sub>2 name"
                by auto
              thus ?thesis
                using \<open>fmrel vrelated env\<^sub>1 env\<^sub>2\<close>
                by auto
            next
              case False
              hence "name |\<notin>| fmdom env\<^sub>1" "name |\<notin>| fmdom env\<^sub>2"
                using \<open>fmdom env\<^sub>1 = frees pat\<close> \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp+
              hence
                "fmlookup (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1) name = fmlookup \<Gamma>'\<^sub>1 name"
                "fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name = fmlookup \<Gamma>'\<^sub>2 name"
                unfolding mk_rec_env_def using \<open>name |\<notin>| fmdom css\<close>
                by auto

              moreover have "name |\<in>| frees (Sabs cs)"
                using False \<open>name |\<in>| frees rhs\<close> \<open>(pat, rhs) \<in> set cs\<close>
                apply (auto simp: ffUnion_alt_def)
                apply (rule fBexI[where x = "frees rhs |-| frees pat"])
                 apply (auto simp: fset_of_list_elem)
                done

              ultimately show ?thesis
                using \<open>fmrel_on_fset (frees (Sabs cs)) vrelated \<Gamma>'\<^sub>1 \<Gamma>'\<^sub>2\<close>
                by (auto dest: fmrel_on_fsetD)
            qed
        qed

      show "fmrel_on_fset (consts rhs) vrelated (fmap_of_list rs) (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        proof
          fix name
          assume "name |\<in>| consts rhs"
          hence "name |\<in>| consts (Sabs cs)"
            using \<open>(pat, rhs) \<in> set cs\<close>
            by (auto intro!: fBexI simp: fset_of_list_elem ffUnion_alt_def)
          hence "rel_option vrelated (fmlookup (fmap_of_list rs) name) (fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2) name)"
            using \<open>fmrel_on_fset (consts (Sabs cs)) vrelated (fmap_of_list rs) (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2)\<close>
            by (auto dest: fmrel_on_fsetD)
          moreover have "name |\<notin>| fmdom env\<^sub>2"
            proof
              assume "name |\<in>| fmdom env\<^sub>2"
              hence "fmlookup env\<^sub>2 name \<noteq> None"
                by (meson fmdom_notI)
              then obtain v where "fmlookup env\<^sub>2 name = Some v"
                by blast
              hence "name |\<in>| fmdom env\<^sub>2"
                by (auto intro: fmdomI)
              hence "name |\<in>| frees pat"
                using \<open>fmdom env\<^sub>2 = frees pat\<close>
                by simp

              have "vwelldefined (Vabs cs \<Gamma>'\<^sub>1)"
                using \<open>vwelldefined (Vrecabs css _ \<Gamma>'\<^sub>1)\<close>
                using rec_comb
                by auto

              hence "welldefined rhs"
                using \<open>(pat, rhs) \<in> set cs\<close> rec_comb
                by (auto simp: list_all_iff)
              hence "name |\<in>| fst |`| fset_of_list rs |\<union>| C"
                using \<open>name |\<in>| consts rhs\<close> all_consts_def
                by blast
              moreover have "\<not> shadows_consts pat"
                using \<open>not_shadows_vconsts (Vabs cs \<Gamma>'\<^sub>2)\<close> \<open>(pat, rhs) \<in> set cs\<close>
                by (auto simp: list_all_iff shadows_consts_def all_consts_def)
              ultimately show False
                using \<open>name |\<in>| frees pat\<close>
                unfolding shadows_consts_def fdisjnt_alt_def all_consts_def
                by auto
            qed
          ultimately show "rel_option vrelated (fmlookup (fmap_of_list rs) name) (fmlookup (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2) name)"
            by simp
        qed
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>'\<^sub>2)\<close>
        by (auto simp: list_all_iff)
    next
      have "wellformed_venv \<Gamma>'\<^sub>2"
        by fact
      moreover have "wellformed_venv env\<^sub>2"
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
          apply fact
        using \<open>wellformed (t $\<^sub>s u)\<close> apply simp
        apply fact+
        done
      moreover have "wellformed_venv (mk_rec_env css \<Gamma>'\<^sub>2)"
        unfolding mk_rec_env_def
        using \<open>vwellformed (Vrecabs _ _ _)\<close>
        by (auto intro: fmdomI)
      ultimately show "wellformed_venv (\<Gamma>'\<^sub>2 ++\<^sub>f mk_rec_env css \<Gamma>'\<^sub>2 ++\<^sub>f env\<^sub>2)"
        by blast
    next
      show "welldefined rhs"
        using \<open>vwelldefined (Vabs cs \<Gamma>'\<^sub>1)\<close> \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)
    next
      have "fmpred (\<lambda>_. vwelldefined) \<Gamma>'\<^sub>1"
        using \<open>vwelldefined (Vabs cs \<Gamma>'\<^sub>1)\<close> by simp

      moreover have "fmpred (\<lambda>_. vwelldefined) env\<^sub>1"
        apply (rule vwelldefined.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval_welldefined)
          apply fact
         apply fact
        using rec_comb apply simp
        done

      ultimately show "fmpred (\<lambda>_. vwelldefined) (\<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1)"
        by blast
    qed

  then obtain val\<^sub>1 where "rs, \<Gamma>'\<^sub>1 ++\<^sub>f env\<^sub>1 \<turnstile>\<^sub>v rhs \<down> val\<^sub>1" "\<turnstile>\<^sub>v val\<^sub>1 \<approx> val\<^sub>2"
    by blast

  show ?case
    apply (intro conjI exI)
     apply (rule veval.rec_comb)
         apply fact+
    done
next
  case (constr name \<Gamma>\<^sub>2 ts us\<^sub>2)

  have "list_all2 (\<lambda>t u\<^sub>2. (\<exists>u\<^sub>1. rs, \<Gamma>\<^sub>1 \<turnstile>\<^sub>v t \<down> u\<^sub>1 \<and> \<turnstile>\<^sub>v u\<^sub>1 \<approx> u\<^sub>2)) ts us\<^sub>2"
    using \<open>list_all2 _ ts us\<^sub>2\<close>
    proof (rule list.rel_mono_strong, elim conjE impE allE exE)
      fix t u\<^sub>2
      assume "t \<in> set ts" "u\<^sub>2 \<in> set us\<^sub>2"
      assume "\<Gamma>\<^sub>2 \<turnstile>\<^sub>v t \<down> u\<^sub>2"

      show "wellformed t" "welldefined t" "\<not> shadows_consts t"
        using constr \<open>t \<in> set ts\<close>
        unfolding welldefined.list_comb wellformed.list_comb shadows.list_comb
        by (auto simp: list_all_iff list_ex_iff)

      show
        "wellformed_venv \<Gamma>\<^sub>2"
        "not_shadows_vconsts_env \<Gamma>\<^sub>2"
        "fmpred (\<lambda>_. vwelldefined) \<Gamma>\<^sub>1"
        by fact+

      have "consts t |\<in>| fset_of_list (map consts ts)"
        using \<open>t \<in> set ts\<close> by (simp add: fset_of_list_elem)
      hence "consts t |\<subseteq>| consts (name $$ ts)"
        unfolding consts_list_comb
        by (metis ffUnion_subset_elem le_supI2)
      thus "fmrel_on_fset (consts t) vrelated (fmap_of_list rs) \<Gamma>\<^sub>2"
        using constr by (blast intro: fmrel_on_fsubset)

      have "frees t |\<in>| fset_of_list (map frees ts)"
        using \<open>t \<in> set ts\<close> by (simp add: fset_of_list_elem)
      hence "frees t |\<subseteq>| frees (name $$ ts)"
        unfolding frees_list_comb const_sterm_def freess_def
        by (auto intro!: ffUnion_subset_elem)
      thus "fmrel_on_fset (frees t) vrelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2"
        using constr by (blast intro: fmrel_on_fsubset)
    qed auto

  then obtain us\<^sub>1 where "list_all2 (veval rs \<Gamma>\<^sub>1) ts us\<^sub>1" "list_all2 vrelated us\<^sub>1 us\<^sub>2"
    by induction auto

  thus ?case
    using constr
    by (auto intro: veval.constr vrelated.constr)
qed

lemma veval'_correct':
  assumes "\<Gamma>\<^sub>2 \<turnstile>\<^sub>v t \<down> v\<^sub>2" "wellformed t" "wellformed_venv \<Gamma>\<^sub>2"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>\<^sub>2"
  assumes "welldefined t"
  assumes "closed t"
  assumes "fmrel_on_fset (consts t) vrelated (fmap_of_list rs) \<Gamma>\<^sub>2"
  obtains v\<^sub>1 where "rs, fmempty \<turnstile>\<^sub>v t \<down> v\<^sub>1" "\<turnstile>\<^sub>v v\<^sub>1 \<approx> v\<^sub>2"
proof (rule veval'_correct[where \<Gamma>\<^sub>1 = fmempty])
  show "fmpred (\<lambda>_. vwelldefined) fmempty" by simp
next
  show "fmrel_on_fset (frees t) vrelated fmempty \<Gamma>\<^sub>2"
    using \<open>closed t\<close> unfolding closed_except_def by auto
qed (rule assms)+

end

subsubsection \<open>Preservation of extensional equality\<close>

lemma (in constants) veval'_agree_eq:
  assumes "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "fmrel_on_fset (ids t) erelated \<Gamma>' \<Gamma>"
  assumes "closed_venv \<Gamma>" "closed_except t (fmdom \<Gamma>)"
  assumes "wellformed t" "wellformed_venv \<Gamma>" "fdisjnt C (fmdom \<Gamma>)"
  assumes "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C" "fmpred (\<lambda>_. vwelldefined') \<Gamma>"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>"
  obtains v' where "\<Gamma>' \<turnstile>\<^sub>v t \<down> v'" "v' \<approx>\<^sub>e v"
using assms proof (induction arbitrary: \<Gamma>' thesis)
  case (const name \<Gamma> val)
  hence "name |\<in>| ids (Sconst name)"
    unfolding ids_def by simp
  with const have "rel_option erelated (fmlookup \<Gamma>' name) (fmlookup \<Gamma> name)"
    by (auto dest: fmrel_on_fsetD)
  then obtain val' where "fmlookup \<Gamma>' name = Some val'" "val' \<approx>\<^sub>e val"
    using \<open>fmlookup \<Gamma> name = Some val\<close>
    by cases auto
  thus ?case
    using const by (auto intro: veval'.const)
next
  case (var \<Gamma> name val)
  hence "name |\<in>| ids (Svar name)"
    unfolding ids_def by simp
  with var have "rel_option erelated (fmlookup \<Gamma>' name) (fmlookup \<Gamma> name)"
    by (auto dest: fmrel_on_fsetD)
  then obtain val' where "fmlookup \<Gamma>' name = Some val'" "val' \<approx>\<^sub>e val"
    using \<open>fmlookup \<Gamma> name = Some val\<close>
    by cases auto
  thus ?case
    using var by (auto intro: veval'.var)
next
  case (abs \<Gamma> cs)
  hence "Vabs cs \<Gamma>' \<approx>\<^sub>e Vabs cs \<Gamma>"
    by (auto intro: erelated.abs)
  thus ?case
    using abs by (auto intro: veval'.abs)
next
  case (comb \<Gamma> t cs \<Gamma>\<^sub>\<Lambda> u v\<^sub>2 env pat rhs val)

  have "fmrel_on_fset (ids t) erelated \<Gamma>' \<Gamma>"
    apply (rule fmrel_on_fsubset)
     apply fact
    unfolding ids_def by auto
  then obtain v\<^sub>1' where "\<Gamma>' \<turnstile>\<^sub>v t \<down> v\<^sub>1'" "v\<^sub>1' \<approx>\<^sub>e Vabs cs \<Gamma>\<^sub>\<Lambda>"
    using comb by (auto simp: closed_except_def)
  then obtain \<Gamma>\<^sub>\<Lambda>' where "v\<^sub>1' = Vabs cs \<Gamma>\<^sub>\<Lambda>'" "fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>"
    by (auto elim: erelated.cases)

  have "fmrel_on_fset (ids u) erelated \<Gamma>' \<Gamma>"
    apply (rule fmrel_on_fsubset)
     apply fact
    unfolding ids_def by auto
  then obtain v\<^sub>2' where "\<Gamma>' \<turnstile>\<^sub>v u \<down> v\<^sub>2'" "v\<^sub>2' \<approx>\<^sub>e v\<^sub>2"
    apply -
    apply (erule comb.IH(2))
    using comb by (auto simp: closed_except_def)

  have "rel_option (rel_prod (fmrel erelated) (=)) (vfind_match cs v\<^sub>2') (vfind_match cs v\<^sub>2)"
    using \<open>v\<^sub>2' \<approx>\<^sub>e v\<^sub>2\<close> by (rule erelated.vfind_match_rel')
  then obtain env' where "fmrel erelated env' env" "vfind_match cs v\<^sub>2' = Some (env', pat, rhs)"
    using comb by cases auto

  have "vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_closed)
    using comb by (auto simp: closed_except_def)
  have "vclosed v\<^sub>2"
    apply (rule veval'_closed)
    using comb by (auto simp: closed_except_def)

  have "closed_except (Sabs cs) (fmdom \<Gamma>\<^sub>\<Lambda>)"
    using \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> by (auto simp: Sterm.closed_except_simps)
  hence "frees (Sabs cs) |\<subseteq>| fmdom \<Gamma>\<^sub>\<Lambda>"
    unfolding closed_except_def .

  have "vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_wellformed)
      apply fact
    using comb by auto

  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact
  hence "linear pat"
    using \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
    by (auto simp: list_all_iff)
  hence "frees pat = patvars (mk_pat pat)"
    by (simp add: mk_pat_frees)
  hence "fmdom env = frees pat"
    apply simp
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply (rule comb)
    done

  have "vwelldefined' (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_welldefined')
           apply fact
    using comb by auto
  hence "consts rhs |\<subseteq>| fmdom \<Gamma>\<^sub>\<Lambda> |\<union>| C" "fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)"
    using \<open>(pat, rhs) \<in> set cs\<close>
    by (auto simp: list_all_iff)

  have "not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_shadows)
    using comb by auto

  obtain val' where "\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env' \<turnstile>\<^sub>v rhs \<down> val'" "val' \<approx>\<^sub>e val"
    proof (erule comb.IH)
      show "closed_venv (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        apply rule
        using \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> apply simp
        apply (rule vclosed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply fact
        done
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff)
    next
      show "wellformed_venv (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        apply rule
        using \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> apply simp
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply (rule comb)
        apply (rule veval'_wellformed)
          apply fact
        using comb by auto
    next
      show "closed_except rhs (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> \<open>fmdom env = frees pat\<close>
        by (auto simp: list_all_iff)

      have "fmdom env = fmdom env'"
        using \<open>fmrel erelated env' env\<close>
        by (metis fmrel_fmdom_eq)

      show "fmrel_on_fset (ids rhs) erelated (\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env') (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        proof
          fix id
          assume "id |\<in>| ids rhs"

          thus "rel_option erelated (fmlookup (\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env') id) (fmlookup (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) id)"
            unfolding ids_def
            proof (cases rule: funion_strictE)
              case A
              hence "id |\<in>| fmdom env |\<union>| fmdom \<Gamma>\<^sub>\<Lambda>"
                using \<open>closed_except rhs (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))\<close>
                unfolding closed_except_def
                by auto

              thus ?thesis
                proof (cases rule: funion_strictE)
                  case A
                  hence "id |\<in>| fmdom env'"
                    using \<open>fmdom env = frees pat\<close> \<open>fmdom env = fmdom env'\<close> by simp
                  with A show ?thesis
                    using \<open>fmrel erelated env' env\<close> by auto
                next
                  case B
                  hence "id |\<notin>| frees pat"
                    using \<open>fmdom env = frees pat\<close> by simp
                  hence "id |\<in>| frees (Sabs cs)"
                    apply auto
                    unfolding ffUnion_alt_def
                    apply simp
                    apply (rule fBexI[where x = "(pat, rhs)"])
                    using \<open>id |\<in>| frees rhs\<close> apply simp
                    unfolding fset_of_list_elem
                    apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                    done
                  hence "id |\<in>| ids (Sabs cs)"
                    unfolding ids_def by simp

                  have "id |\<notin>| fmdom env'"
                    using B unfolding \<open>fmdom env = fmdom env'\<close> by simp
                  thus ?thesis
                    using \<open>id |\<notin>| fmdom env\<close>
                    apply simp
                    apply (rule fmrel_on_fsetD)
                     apply (rule \<open>id |\<in>| ids (Sabs cs)\<close>)
                    apply (rule \<open>fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>\<close>)
                    done
                qed
            next
              case B
              have "id |\<in>| consts (Sabs cs)"
                apply auto
                unfolding ffUnion_alt_def
                apply simp
                apply (rule fBexI[where x = "(pat, rhs)"])
                 apply simp
                 apply fact
                unfolding fset_of_list_elem
                apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                done
              hence "id |\<in>| ids (Sabs cs)"
                unfolding ids_def by auto

              show ?thesis
                using \<open>fmdom env = fmdom env'\<close>
                apply auto
                 apply (rule fmrelD)
                 apply (rule \<open>fmrel erelated env' env\<close>)
                apply (rule fmrel_on_fsetD)
                 apply (rule \<open>id |\<in>| ids (Sabs cs)\<close>)
                apply (rule \<open>fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>\<close>)
                done
            qed
        qed
    next
      show "fmpred (\<lambda>_. vwelldefined') (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        proof
          have "vwelldefined' (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
            apply (rule veval'_welldefined')
                   apply fact
            using comb by auto
          thus "fmpred (\<lambda>_. vwelldefined') \<Gamma>\<^sub>\<Lambda>"
            by simp
        next
          have "vwelldefined' v\<^sub>2"
            apply (rule veval'_welldefined')
                   apply fact
            using comb by auto

          show "fmpred (\<lambda>_. vwelldefined') env"
            apply (rule vmatch_welldefined')
             apply (rule vfind_match_elem)
             apply fact+
            done
        qed
    next
      have "fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)"
        using \<open>vwelldefined' (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> by simp
      moreover have "fdisjnt C (fmdom env)"
        unfolding \<open>fmdom env = _\<close>
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff all_consts_def fdisjnt_alt_def)
      ultimately show "fdisjnt C (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
        unfolding fdisjnt_alt_def by auto
    next
      show "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff)
    next
      have "not_shadows_vconsts_env \<Gamma>\<^sub>\<Lambda>"
        using \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> by auto
      moreover have "not_shadows_vconsts_env env"
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
        using comb by auto
      ultimately show "not_shadows_vconsts_env (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        by blast
    next
      show "consts rhs |\<subseteq>| fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) |\<union>| C"
        using \<open>consts rhs |\<subseteq>| _\<close>
        by auto
    qed

  moreover have "\<Gamma>' \<turnstile>\<^sub>v t $\<^sub>s u \<down> val'"
    proof (rule veval'.comb)
      show "\<Gamma>' \<turnstile>\<^sub>v t \<down> Vabs cs \<Gamma>\<^sub>\<Lambda>'"
        using \<open>\<Gamma>' \<turnstile>\<^sub>v t \<down> v\<^sub>1'\<close>
        unfolding \<open>v\<^sub>1' = _\<close> .
    qed fact+

  ultimately show ?case
    using comb by metis
next
  case (rec_comb \<Gamma> t css name \<Gamma>\<^sub>\<Lambda> cs u v\<^sub>2 env pat rhs val)

  have "fmrel_on_fset (ids t) erelated \<Gamma>' \<Gamma>"
    apply (rule fmrel_on_fsubset)
    apply fact
    unfolding ids_def by auto
  then obtain v\<^sub>1' where "\<Gamma>' \<turnstile>\<^sub>v t \<down> v\<^sub>1'" "v\<^sub>1' \<approx>\<^sub>e Vrecabs css name \<Gamma>\<^sub>\<Lambda>"
    using rec_comb by (auto simp: closed_except_def)
  then obtain \<Gamma>\<^sub>\<Lambda>'
    where "v\<^sub>1' = Vrecabs css name \<Gamma>\<^sub>\<Lambda>'"
      and "pred_fmap (\<lambda>cs. fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>) css"
    by (auto elim: erelated.cases)

  have "fmrel_on_fset (ids u) erelated \<Gamma>' \<Gamma>"
    apply (rule fmrel_on_fsubset)
     apply fact
    unfolding ids_def by auto
  then obtain v\<^sub>2' where "\<Gamma>' \<turnstile>\<^sub>v u \<down> v\<^sub>2'" "v\<^sub>2' \<approx>\<^sub>e v\<^sub>2"
    apply -
    apply (erule rec_comb.IH(2))
    using rec_comb by (auto simp: closed_except_def)

  have "rel_option (rel_prod (fmrel erelated) (=)) (vfind_match cs v\<^sub>2') (vfind_match cs v\<^sub>2)"
    using \<open>v\<^sub>2' \<approx>\<^sub>e v\<^sub>2\<close> by (rule erelated.vfind_match_rel')
  then obtain env' where "fmrel erelated env' env" "vfind_match cs v\<^sub>2' = Some (env', pat, rhs)"
    using rec_comb by cases auto

  have "vclosed (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_closed)
    using rec_comb by (auto simp: closed_except_def)
  hence "vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    using rec_comb by (auto simp: closed_except_def)
  have "vclosed v\<^sub>2"
    apply (rule veval'_closed)
    using rec_comb by (auto simp: closed_except_def)

  have "closed_except (Sabs cs) (fmdom \<Gamma>\<^sub>\<Lambda>)"
    using \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> by (auto simp: Sterm.closed_except_simps)
  hence "frees (Sabs cs) |\<subseteq>| fmdom \<Gamma>\<^sub>\<Lambda>"
    unfolding closed_except_def .

  have "vwellformed (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_wellformed)
      apply fact
    using rec_comb by auto
  hence "vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    using rec_comb by (auto simp: closed_except_def)

  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact
  hence "linear pat"
    using \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
    by (auto simp: list_all_iff)
  hence "frees pat = patvars (mk_pat pat)"
    by (simp add: mk_pat_frees)
  hence "fmdom env = frees pat"
    apply simp
    apply (rule vmatch_dom)
    apply (rule vfind_match_elem)
    apply (rule rec_comb)
    done

  have "vwelldefined' (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_welldefined')
           apply fact
    using rec_comb by auto
  hence "consts rhs |\<subseteq>| fmdom \<Gamma>\<^sub>\<Lambda> |\<union>| (C |\<union>| fmdom css)" "fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)"
    using \<open>(pat, rhs) \<in> set cs\<close> \<open>fmlookup css name = Some cs\<close>
    by (auto simp: list_all_iff dest!: fmpredD[where m = css])

  have "not_shadows_vconsts (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)"
    apply (rule veval'_shadows)
    using rec_comb by auto
  hence "not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)"
    using rec_comb by auto

  obtain val' where "\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env' \<turnstile>\<^sub>v rhs \<down> val'" "val' \<approx>\<^sub>e val"
    proof (erule rec_comb.IH)
      show "closed_venv (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        apply rule
         apply rule
        using \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> apply simp
        unfolding mk_rec_env_def
        using \<open>vclosed (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)\<close> apply (auto intro: fmdomI)[]
        apply (rule vclosed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply fact
        done
    next
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff)
    next
      show "wellformed_venv (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        apply rule
         apply rule
        using \<open>vwellformed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> apply simp
        unfolding mk_rec_env_def
        using \<open>vwellformed (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)\<close> apply (auto intro: fmdomI)[]
        apply (rule vwellformed.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_wellformed)
          apply fact
        using rec_comb by auto
    next
      have "closed_except rhs (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>vclosed (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> \<open>fmdom env = frees pat\<close>
        by (auto simp: list_all_iff closed_except_def)
      thus "closed_except rhs (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
        unfolding closed_except_def
        by auto

      have "fmdom env = fmdom env'"
        using \<open>fmrel erelated env' env\<close>
        by (metis fmrel_fmdom_eq)

      have "fmrel_on_fset (ids rhs) erelated (mk_rec_env css \<Gamma>\<^sub>\<Lambda>') (mk_rec_env css \<Gamma>\<^sub>\<Lambda>)"
        unfolding mk_rec_env_def
        apply rule
        apply simp
        unfolding option.rel_map
        apply (rule option.rel_refl)
        apply (rule erelated.intros)
        apply (rule \<open>pred_fmap (\<lambda>cs. fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>) css\<close>)
        done

      have "fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>"
        using \<open>pred_fmap (\<lambda>cs. fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>) css\<close> rec_comb
        by auto

      have "fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) = fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>')"
        unfolding mk_rec_env_def by auto

      show "fmrel_on_fset (ids rhs) erelated (\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env') (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        proof
          fix id
          assume "id |\<in>| ids rhs"

          thus "rel_option erelated (fmlookup (\<Gamma>\<^sub>\<Lambda>' ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>' ++\<^sub>f env') id) (fmlookup (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) id)"
            unfolding ids_def
            proof (cases rule: funion_strictE)
              case A
              hence "id |\<in>| fmdom env |\<union>| fmdom \<Gamma>\<^sub>\<Lambda>"
                using \<open>closed_except rhs (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))\<close>
                unfolding closed_except_def
                by auto

              thus ?thesis
                proof (cases rule: funion_strictE)
                  case A
                  hence "id |\<in>| fmdom env'"
                    using \<open>fmdom env = frees pat\<close> \<open>fmdom env = fmdom env'\<close> by simp
                  with A show ?thesis
                    using \<open>fmrel erelated env' env\<close> by auto
                next
                  case B
                  hence "id |\<notin>| frees pat"
                    using \<open>fmdom env = frees pat\<close> by simp
                  hence "id |\<in>| frees (Sabs cs)"
                    apply auto
                    unfolding ffUnion_alt_def
                    apply simp
                    apply (rule fBexI[where x = "(pat, rhs)"])
                    using \<open>id |\<in>| frees rhs\<close> apply simp
                    unfolding fset_of_list_elem
                    apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                    done
                  hence "id |\<in>| ids (Sabs cs)"
                    unfolding ids_def by simp

                  have "id |\<notin>| fmdom env'"
                    using B unfolding \<open>fmdom env = fmdom env'\<close> by simp
                  thus ?thesis
                    using \<open>id |\<notin>| fmdom env\<close> \<open>fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) = fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>')\<close>
                    apply auto
                     apply (rule fmrel_on_fsetD)
                      apply (rule \<open>id |\<in>| ids rhs\<close>)
                     apply (rule \<open>fmrel_on_fset (ids rhs) erelated (mk_rec_env css \<Gamma>\<^sub>\<Lambda>') (mk_rec_env css \<Gamma>\<^sub>\<Lambda>)\<close>)
                    apply (rule fmrel_on_fsetD)
                     apply (rule \<open>id |\<in>| ids (Sabs cs)\<close>)
                    apply (rule \<open>fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>\<close>)
                    done
                qed
            next
              case B
              have "id |\<in>| consts (Sabs cs)"
                apply auto
                unfolding ffUnion_alt_def
                apply simp
                apply (rule fBexI[where x = "(pat, rhs)"])
                 apply simp
                 apply fact
                unfolding fset_of_list_elem
                apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                done
              hence "id |\<in>| ids (Sabs cs)"
                unfolding ids_def by auto

              show ?thesis
                using \<open>fmdom env = fmdom env'\<close> \<open>fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) = fmdom (mk_rec_env css \<Gamma>\<^sub>\<Lambda>')\<close>
                apply auto
                   apply (rule fmrelD)
                   apply (rule \<open>fmrel erelated env' env\<close>)
                  apply (rule fmrel_on_fsetD)
                   apply (rule \<open>id |\<in>| ids rhs\<close>)
                  apply (rule \<open>fmrel_on_fset (ids rhs) erelated (mk_rec_env css \<Gamma>\<^sub>\<Lambda>') (mk_rec_env css \<Gamma>\<^sub>\<Lambda>)\<close>)
                 apply (rule fmrelD)
                 apply (rule \<open>fmrel erelated env' env\<close>)
                apply (rule fmrel_on_fsetD)
                 apply (rule \<open>id |\<in>| ids (Sabs cs)\<close>)
                apply (rule \<open>fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>\<Lambda>' \<Gamma>\<^sub>\<Lambda>\<close>)
                done
            qed
        qed
    next
      show "fmpred (\<lambda>_. vwelldefined') (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        proof (intro fmpred_add)
          have "vwelldefined' (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)"
            apply (rule veval'_welldefined')
                   apply fact
            using rec_comb by auto
          thus "fmpred (\<lambda>_. vwelldefined') \<Gamma>\<^sub>\<Lambda>" "fmpred (\<lambda>_. vwelldefined') (mk_rec_env css \<Gamma>\<^sub>\<Lambda>)"
            unfolding mk_rec_env_def
            by (auto intro: fmdomI)
        next
          have "vwelldefined' v\<^sub>2"
            apply (rule veval'_welldefined')
                   apply fact
            using rec_comb by auto

          show "fmpred (\<lambda>_. vwelldefined') env"
            apply (rule vmatch_welldefined')
             apply (rule vfind_match_elem)
             apply fact+
            done
        qed
    next
      have "fdisjnt C (fmdom env)"
        unfolding \<open>fmdom env = _\<close>
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff all_consts_def fdisjnt_alt_def)
      moreover have "fdisjnt C (fmdom css)"
        using \<open>vwelldefined' (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)\<close> by simp
      ultimately show "fdisjnt C (fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
        using \<open>fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)\<close>
        unfolding fdisjnt_alt_def mk_rec_env_def by auto
    next
      show "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto simp: list_all_iff)
    next
      have "not_shadows_vconsts_env \<Gamma>\<^sub>\<Lambda>"
        using \<open>not_shadows_vconsts (Vabs cs \<Gamma>\<^sub>\<Lambda>)\<close> by auto
      moreover have "not_shadows_vconsts_env env"
        apply (rule not_shadows_vconsts.vmatch_env)
         apply (rule vfind_match_elem)
         apply fact
        apply (rule veval'_shadows)
        using rec_comb by auto
      moreover have "not_shadows_vconsts_env (mk_rec_env css \<Gamma>\<^sub>\<Lambda>)"
        unfolding mk_rec_env_def
        using \<open>not_shadows_vconsts (Vrecabs css name \<Gamma>\<^sub>\<Lambda>)\<close>
        by (auto intro: fmdomI)
      ultimately show "not_shadows_vconsts_env (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
        by blast
    next
      show "consts rhs |\<subseteq>| fmdom (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) |\<union>| C"
        using \<open>consts rhs |\<subseteq>| _\<close> unfolding mk_rec_env_def
        by auto
    qed

  moreover have "\<Gamma>' \<turnstile>\<^sub>v t $\<^sub>s u \<down> val'"
    proof (rule veval'.rec_comb)
      show "\<Gamma>' \<turnstile>\<^sub>v t \<down> Vrecabs css name \<Gamma>\<^sub>\<Lambda>'"
        using \<open>\<Gamma>' \<turnstile>\<^sub>v t \<down> v\<^sub>1'\<close>
        unfolding \<open>v\<^sub>1' = _\<close> .
    qed fact+

  ultimately show ?case
    using rec_comb by metis
next
  case (constr name \<Gamma> ts us)

  have "list_all (\<lambda>t. fmrel_on_fset (ids t) erelated \<Gamma>' \<Gamma> \<and> closed_except t (fmdom \<Gamma>) \<and> wellformed t \<and> consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C \<and> \<not> shadows_consts t) ts"
    apply (rule list_allI)
    apply rule
     apply (rule fmrel_on_fsubset)
      apply (rule constr)
    subgoal
      unfolding ids_list_comb
      by (induct ts; auto)
    subgoal
      apply (intro conjI)
      subgoal
        using \<open>closed_except (name $$ ts) (fmdom \<Gamma>)\<close>
        unfolding closed.list_comb by (auto simp: list_all_iff)
      subgoal
        using \<open>wellformed (name $$ ts)\<close>
        unfolding wellformed.list_comb by (auto simp: list_all_iff)
      subgoal
        using \<open>consts (name $$ ts) |\<subseteq>| fmdom \<Gamma> |\<union>| C\<close>
        unfolding consts_list_comb
        by (metis Ball_set constr.prems(8) special_constants.sconsts_list_comb)
      subgoal
        using \<open>\<not> shadows_consts (name $$ ts)\<close>
        unfolding shadows.list_comb by (auto simp: list_ex_iff)
      done
    done

  obtain us' where "list_all3 (\<lambda>t u u'. \<Gamma>' \<turnstile>\<^sub>v t \<down> u' \<and> u' \<approx>\<^sub>e u) ts us us'"
    using \<open>list_all2 _ _ _\<close> \<open>list_all _ ts\<close>
    proof (induction arbitrary: thesis rule: list.rel_induct)
      case (Cons t ts u us)
      then obtain us' where "list_all3 (\<lambda>t u u'. \<Gamma>' \<turnstile>\<^sub>v t \<down> u' \<and> u' \<approx>\<^sub>e u) ts us us'"
        by auto
      have
        "fmrel_on_fset (ids t) erelated \<Gamma>' \<Gamma>" "closed_except t (fmdom \<Gamma>)"
        "wellformed t" "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C" "\<not> shadows_consts t"
        using Cons by auto

      then obtain u' where "\<Gamma>' \<turnstile>\<^sub>v t \<down> u'" "u' \<approx>\<^sub>e u"
        using \<open>closed_venv \<Gamma>\<close> \<open>wellformed_venv \<Gamma>\<close> \<open>fdisjnt C (fmdom \<Gamma>)\<close> \<open>fmpred (\<lambda>_. vwelldefined') \<Gamma>\<close>
        using \<open>not_shadows_vconsts_env \<Gamma>\<close> Cons.hyps
        by blast

      show ?case
        apply (rule Cons.prems)
        apply (rule list_all3_cons)
         apply fact
        apply (rule conjI)
         apply fact+
        done
    qed auto

  show ?case
    apply (rule constr.prems)
     apply (rule veval'.constr[where us = us'])
      apply fact
    using \<open>list_all3 _ ts us us'\<close>
     apply (induct; auto)
    apply (rule erelated.intros)
    using \<open>list_all3 _ ts us us'\<close>
    apply (induct; auto)
    done
qed

end