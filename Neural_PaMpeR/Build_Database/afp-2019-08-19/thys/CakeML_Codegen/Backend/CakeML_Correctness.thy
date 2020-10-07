subsection \<open>Correctness of compilation\<close>

theory CakeML_Correctness
imports
  CakeML_Backend
  "../Rewriting/Big_Step_Value_ML"
begin

context cakeml' begin

lemma mk_rec_env_related:
  assumes "fmrel (\<lambda>cs (n, e). related_fun cs n e) css (fmap_of_list (map (map_prod Name (map_prod Name id)) funs))"
  assumes "fmrel_on_fset (fbind (fmran css) (ids \<circ> Sabs)) related_v \<Gamma>\<^sub>\<Lambda> (fmap_of_ns (sem_env.v env\<^sub>\<Lambda>))"
  shows "fmrel related_v (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) (cake_mk_rec_env funs env\<^sub>\<Lambda>)"
proof (rule fmrelI)
  fix name
  have "rel_option (\<lambda>cs (n, e). related_fun cs n e) (fmlookup css name) (map_of (map (map_prod Name (map_prod Name id)) funs) name)"
    using assms by (auto simp: fmap_of_list.rep_eq)

  then have "rel_option (\<lambda>cs (n, e). related_fun cs (Name n) e) (fmlookup css name) (map_of funs (as_string name))"
    unfolding name.map_of_rekey'
    by cases auto

  have *: "related_v (Vrecabs css name \<Gamma>\<^sub>\<Lambda>) (Recclosure env\<^sub>\<Lambda> funs (as_string name))"
    using assms by (auto intro: related_v.rec_closure)

  show "rel_option related_v (fmlookup (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) name) (fmlookup (cake_mk_rec_env funs env\<^sub>\<Lambda>) name)"
    unfolding mk_rec_env_def cake_mk_rec_env_def fmap_of_list.rep_eq
    apply (simp add: map_of_map_keyed name.map_of_rekey option.rel_map)
    apply (rule option.rel_mono_strong)
     apply fact
    apply (rule *)
    done
qed

lemma mk_exp_correctness:
  "ids t |\<subseteq>| S \<Longrightarrow> all_consts |\<subseteq>| S \<Longrightarrow> \<not> shadows_consts t \<Longrightarrow> related_exp t (mk_exp S t)"
  "ids (Sabs cs) |\<subseteq>| S \<Longrightarrow> all_consts |\<subseteq>| S \<Longrightarrow> \<not> shadows_consts (Sabs cs) \<Longrightarrow> list_all2 (rel_prod related_pat related_exp) cs (mk_clauses S cs)"
  "ids t |\<subseteq>| S \<Longrightarrow> all_consts |\<subseteq>| S \<Longrightarrow> \<not> shadows_consts t \<Longrightarrow> related_exp t (mk_con S t)"
proof (induction rule: mk_exp_mk_clauses_mk_con.induct)
  case (2 S name)
  show ?case
    proof (cases "name |\<in>| C")
      case True
      hence "related_exp (name $$ []) (mk_exp S (Sconst name))"
        by (auto intro: related_exp.intros simp del: list_comb.simps)
      thus ?thesis
        by (simp add: const_sterm_def)
    qed (auto intro: related_exp.intros)
next
  case (4 S cs)

  have "fresh_fNext (S |\<union>| all_consts) |\<notin>| S |\<union>| all_consts"
    by (rule fNext_not_member)
  hence "fresh_fNext S |\<notin>| S |\<union>| all_consts"
    using \<open>all_consts |\<subseteq>| S\<close> by (simp add: sup_absorb1)
  hence "fresh_fNext S |\<notin>| ids (Sabs cs) |\<union>| all_consts"
    using 4 by auto

  show ?case
    apply (simp add: Let_def)
    apply (rule related_exp.fun)
      apply (rule "4.IH"[unfolded mk_clauses.simps])
         apply (rule refl)
        apply fact+
    using \<open>fresh_fNext S |\<notin>| ids (Sabs cs) |\<union>| all_consts\<close> by auto
next
  case (5 S t)
  show ?case
    apply (simp add: mk_con.simps split!: prod.splits sterm.splits if_splits)
    subgoal premises prems for args c
      proof -
        from prems have "t = c $$ args"
          apply (fold const_sterm_def)
          by (metis fst_conv list_strip_comb snd_conv)
        show ?thesis
          unfolding \<open>t = _\<close>
          apply (rule related_exp.constr)
           apply fact
          apply (simp add: list.rel_map)
          apply (rule list.rel_refl_strong)
          apply (rule 5(1))
                apply (rule prems(1)[symmetric])
               apply (rule refl)
          subgoal by (rule prems)
          subgoal by assumption
          subgoal
            using \<open>ids t |\<subseteq>| S\<close> unfolding \<open>t = _\<close>
            apply (auto simp: ids_list_comb)
            by (meson ffUnion_subset_elem fimage_eqI fset_of_list_elem fset_rev_mp)
          subgoal by (rule 5)
          subgoal
            using \<open>\<not> shadows_consts t\<close> unfolding \<open>t = _\<close>
            unfolding shadows.list_comb
            by (auto simp: list_ex_iff)
          done
      qed
    using 5 by (auto split: prod.splits sterm.splits)
next
  case (6 S cs)

  have "list_all2 (\<lambda>x y. rel_prod related_pat related_exp x (case y of (pat, t) \<Rightarrow> (mk_ml_pat (mk_pat pat), mk_con (frees pat |\<union>| S) t))) cs cs"
    proof (rule list.rel_refl_strong, safe intro!: rel_prod.intros)
      fix pat rhs
      assume "(pat, rhs) \<in> set cs"

      hence "consts rhs |\<subseteq>| S"
        using \<open>ids (Sabs cs) |\<subseteq>| S\<close>
        unfolding ids_def
        apply auto
        apply (drule ffUnion_least_rev)+
        apply (auto simp: fset_of_list_elem elim!: fBallE)
        done

      have "frees rhs |\<subseteq>| frees pat |\<union>| S"
        using \<open>ids (Sabs cs) |\<subseteq>| S\<close> \<open>(pat, rhs) \<in> set cs\<close>
        unfolding ids_def
        apply auto
        apply (drule ffUnion_least_rev)+
        apply (auto simp: fset_of_list_elem elim!: fBallE)
        done

      have "\<not> shadows_consts rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> 6
        by (auto simp: list_ex_iff)

      show "related_exp rhs (mk_con (frees pat |\<union>| S) rhs)"
        apply (rule 6)
            apply fact
        subgoal by simp
        subgoal
          unfolding ids_def
          using \<open>consts rhs |\<subseteq>| S\<close> \<open>frees rhs |\<subseteq>| frees pat |\<union>| S\<close>
          by auto
        subgoal using 6(3) by fast
        subgoal by fact
        done
    qed

  thus ?case
    by (simp add: list.rel_map)
qed (auto intro: related_exp.intros simp: ids_def fdisjnt_alt_def)

context begin

private lemma semantic_correctness0:
  fixes exp
  assumes "cupcake_evaluate_single env exp r" "is_cupcake_all_env env"
  assumes "fmrel_on_fset (ids t) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
  assumes "related_exp t exp"
  assumes "wellformed t" "wellformed_venv \<Gamma>"
  assumes "closed_venv \<Gamma>" "closed_except t (fmdom \<Gamma>)"
  assumes "fmpred (\<lambda>_. vwelldefined') \<Gamma>" "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C"
  assumes "fdisjnt C (fmdom \<Gamma>)"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>"
  shows "if_rval (\<lambda>ml_v. \<exists>v. \<Gamma> \<turnstile>\<^sub>v t \<down> v \<and> related_v v ml_v) r"
using assms proof (induction arbitrary: \<Gamma> t)
  case (con1 env cn es ress ml_vs ml_v')
  obtain name ts where "cn = Some (Short (as_string name))" "name |\<in>| C" "t = name $$ ts" "list_all2 related_exp ts es"
    using \<open>related_exp t (Con cn es)\<close>
    by cases auto
  with con1 obtain tid where "ml_v' = Conv (Some (id_to_n (Short (as_string name)), tid)) (rev ml_vs)"
    by (auto split: option.splits)

  have "ress = map Rval ml_vs"
    using con1 by auto

  define ml_vs' where "ml_vs' = rev ml_vs"

  note IH = \<open>list_all2_shortcircuit _ _ _\<close>[
              unfolded \<open>ress = _\<close> list_all2_shortcircuit_rval list_all2_rev1,
              folded ml_vs'_def]
  moreover have
    "list_all wellformed ts" "list_all (\<lambda>t. \<not> shadows_consts t) ts"
    "list_all (\<lambda>t. consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C) ts" "list_all (\<lambda>t. closed_except t (fmdom \<Gamma>)) ts"
    subgoal
      using \<open>wellformed t\<close> unfolding \<open>t = _\<close> wellformed.list_comb by simp
    subgoal
      using \<open>\<not> shadows_consts t\<close> unfolding \<open>t = _\<close> shadows.list_comb
      by (simp add: list_all_iff list_ex_iff)
    subgoal
      using \<open>consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C\<close>
      unfolding list_all_iff
      by (metis Ball_set \<open>t = name $$ ts\<close> con1.prems(9) special_constants.sconsts_list_comb)
    subgoal
      using \<open>closed_except t (fmdom \<Gamma>)\<close> unfolding \<open>t = _\<close> closed.list_comb by simp
    done
  moreover have
    "list_all (\<lambda>t'. fmrel_on_fset (ids t') related_v \<Gamma> (fmap_of_ns (sem_env.v env))) ts"
    proof (standard, rule fmrel_on_fsubset)
      fix t'
      assume "t' \<in> set ts"
      thus "ids t' |\<subseteq>| ids t"
        unfolding \<open>t = _\<close>
        apply (simp add: ids_list_comb)
        apply (subst (2) ids_def)
        apply simp
        apply (rule fsubset_finsertI2)
        apply (auto simp: fset_of_list_elem intro!: ffUnion_subset_elem)
        done
      show "fmrel_on_fset (ids t) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
        by fact
    qed

  ultimately obtain us where "list_all2 (veval' \<Gamma>) ts us" "list_all2 related_v us ml_vs'"
    using \<open>list_all2 related_exp ts es\<close>
    proof (induction es ml_vs' arbitrary: ts thesis rule: list.rel_induct)
      case (Cons e es ml_v ml_vs ts0)
      then obtain t ts where "ts0 = t # ts" "related_exp t e" by (cases ts0) auto
      with Cons have "list_all2 related_exp ts es" by simp
      with Cons obtain us where "list_all2 (veval' \<Gamma>) ts us" "list_all2 related_v us ml_vs"
        unfolding \<open>ts0 = _\<close>
        by auto

      from Cons.hyps[simplified, THEN conjunct2, rule_format, of t \<Gamma>]
      obtain u where "\<Gamma> \<turnstile>\<^sub>v t \<down> u " "related_v u ml_v"
        proof
          show
            "is_cupcake_all_env env" "related_exp t e" "wellformed_venv \<Gamma>" "closed_venv \<Gamma>"
            "fmpred (\<lambda>_. vwelldefined') \<Gamma>" "fdisjnt C (fmdom \<Gamma>)"
            "not_shadows_vconsts_env \<Gamma>"
            by fact+
        next
          show
            "wellformed t" "\<not> shadows_consts t" "closed_except t (fmdom \<Gamma>)"
            "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C" "fmrel_on_fset (ids t) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
            using Cons unfolding \<open>ts0 = _\<close>
            by auto
        qed blast

      show ?case
        apply (rule Cons(3)[of "u # us"])
        unfolding \<open>ts0 = _\<close>
         apply auto
           apply fact+
        done
    qed auto

    show ?case
      apply simp
      apply (intro exI conjI)
      unfolding \<open>t = _\<close>
       apply (rule veval'.constr)
        apply fact+
      unfolding \<open>ml_v' = _\<close>
      apply (subst ml_vs'_def[symmetric])
      apply simp
      apply (rule related_v.conv)
      apply fact
      done
next
  case (var1 env id ml_v)

  from \<open>related_exp t (Var id)\<close> obtain name where "id = Short (as_string name)"
    by cases auto
  with var1 have "cupcake_nsLookup (sem_env.v env) (as_string name) = Some ml_v"
    by auto

  from \<open>related_exp t (Var id)\<close> consider
      (var) "t = Svar name"
    | (const) "t = Sconst name" "name |\<notin>| C"
    unfolding \<open>id = _\<close>
    apply (cases t)
    using name.expand by blast+
  thus ?case
    proof cases
      case var
      hence "name |\<in>| ids t"
        unfolding ids_def by simp

      have "rel_option related_v (fmlookup \<Gamma> name) (cupcake_nsLookup (sem_env.v env) (as_string name))"
        using \<open>fmrel_on_fset (ids t) _ _ _\<close>
        apply -
        apply (drule fmrel_on_fsetD[OF \<open>name |\<in>| ids t\<close>])
        apply simp
        done
      then obtain v where "related_v v ml_v" "fmlookup \<Gamma> name = Some v"
        using \<open>cupcake_nsLookup (sem_env.v env) _ = _\<close>
        by cases auto

      show ?thesis
        unfolding \<open>t = _\<close>
        apply simp
        apply (rule exI)
        apply (rule conjI)
         apply (rule veval'.var)
         apply fact+
        done
    next
      case const
      hence "name |\<in>| ids t"
        unfolding ids_def by simp

      have "rel_option related_v (fmlookup \<Gamma> name) (cupcake_nsLookup (sem_env.v env) (as_string name))"
        using \<open>fmrel_on_fset (ids t) _ _ _\<close>
        apply -
        apply (drule fmrel_on_fsetD[OF \<open>name |\<in>| ids t\<close>])
        apply simp
        done
      then obtain v where "related_v v ml_v" "fmlookup \<Gamma> name = Some v"
        using \<open>cupcake_nsLookup (sem_env.v env) _ = _\<close>
        by cases auto

      show ?thesis
        unfolding \<open>t = _\<close>
        apply simp
        apply (rule exI)
        apply (rule conjI)
         apply (rule veval'.const)
          apply fact+
        done
    qed
next
  case (fn env n u)
  obtain n' where "n = as_string n'"
    by (metis name.sel)
  obtain cs ml_cs
    where "t = Sabs cs" "u = Mat (Var (Short (as_string n'))) ml_cs" "n' |\<notin>| ids (Sabs cs)" "n' |\<notin>| all_consts"
      and "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
    using \<open>related_exp t (Fun n u)\<close> unfolding \<open>n = _\<close>
    by cases (auto dest: name.expand)

  obtain ns where "fmap_of_ns (sem_env.v env) = fmap_of_list ns"
    apply (cases env)
    apply simp
    subgoal for v by (cases v) simp
    done

  show ?case
    apply simp
    apply (rule exI)
    apply (rule conjI)
    unfolding \<open>t = _\<close>
     apply (rule veval'.abs)
    unfolding \<open>n = _\<close>
    apply (rule related_v.closure)
    unfolding \<open>u = _\<close>
     apply (subst related_fun_alt_def; rule conjI)
      apply fact
     apply (rule conjI; fact)
    using \<open>fmrel_on_fset (ids t) _ _ _\<close>
    unfolding \<open>t = _\<close> \<open>fmap_of_ns (sem_env.v env) = _\<close>
    by simp
next
  case (app1 env exps ress ml_vs env' exp' bv)
  from \<open>related_exp t _\<close> obtain exp\<^sub>1 exp\<^sub>2 t\<^sub>1 t\<^sub>2
    where "rev exps = [exp\<^sub>2, exp\<^sub>1]" "exps = [exp\<^sub>1, exp\<^sub>2]" "t = t\<^sub>1 $\<^sub>s t\<^sub>2"
      and "related_exp t\<^sub>1 exp\<^sub>1" "related_exp t\<^sub>2 exp\<^sub>2"
    by cases auto
  moreover from app1 have "ress = map Rval ml_vs"
    by auto
  ultimately obtain ml_v\<^sub>1 ml_v\<^sub>2 where "ml_vs = [ml_v\<^sub>2, ml_v\<^sub>1]"
    using app1(1)
    by (smt list_all2_shortcircuit_rval list_all2_Cons1 list_all2_Nil)

  have "is_cupcake_exp exp\<^sub>1" "is_cupcake_exp exp\<^sub>2"
    using app1 unfolding \<open>exps = _\<close> by (auto dest: related_exp_is_cupcake)
  moreover have "fmrel_on_fset (ids t\<^sub>1) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
    using app1 unfolding ids_def \<open>t = _\<close>
    by (auto intro: fmrel_on_fsubset)
  moreover have "fmrel_on_fset (ids t\<^sub>2) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
    using app1 unfolding ids_def \<open>t = _\<close>
    by (auto intro: fmrel_on_fsubset)
  ultimately have
    "cupcake_evaluate_single env exp\<^sub>1 (Rval ml_v\<^sub>1)" "cupcake_evaluate_single env exp\<^sub>2 (Rval ml_v\<^sub>2)" and
    "\<exists>t\<^sub>1'. \<Gamma> \<turnstile>\<^sub>v t\<^sub>1 \<down> t\<^sub>1' \<and> related_v t\<^sub>1' ml_v\<^sub>1" "\<exists>t\<^sub>2'. \<Gamma> \<turnstile>\<^sub>v t\<^sub>2 \<down> t\<^sub>2' \<and> related_v t\<^sub>2' ml_v\<^sub>2"
    using app1 \<open>related_exp t\<^sub>1 exp\<^sub>1\<close> \<open>related_exp t\<^sub>2 exp\<^sub>2\<close>
    unfolding \<open>ress = _\<close> \<open>exps = _\<close> \<open>ml_vs = _\<close> \<open>t = _\<close>
    by (auto simp: closed_except_def)

  then obtain v\<^sub>1 v\<^sub>2
    where "\<Gamma> \<turnstile>\<^sub>v t\<^sub>1 \<down> v\<^sub>1" "related_v v\<^sub>1 ml_v\<^sub>1"
      and "\<Gamma> \<turnstile>\<^sub>v t\<^sub>2 \<down> v\<^sub>2" "related_v v\<^sub>2 ml_v\<^sub>2"
    by blast

  have "is_cupcake_value ml_v\<^sub>1"
    by (rule cupcake_single_preserve) fact+
  moreover have "is_cupcake_value ml_v\<^sub>2"
    by (rule cupcake_single_preserve) fact+
  ultimately have "list_all is_cupcake_value (rev ml_vs)"
    unfolding \<open>ml_vs = _\<close> by simp

  hence "is_cupcake_exp exp'" "is_cupcake_all_env env'"
    using \<open>do_opapp _ = _\<close> by (metis cupcake_opapp_preserve)+

  have "vclosed v\<^sub>1"
    proof (rule veval'_closed)
      show "closed_except t\<^sub>1 (fmdom \<Gamma>)"
        using \<open>closed_except _ (fmdom \<Gamma>)\<close>
        unfolding \<open>t = _\<close>
        by (simp add: closed_except_def)
    next
      show "wellformed t\<^sub>1"
        using \<open>wellformed t\<close> unfolding \<open>t = _\<close>
        by simp
    qed fact+
  have "vclosed v\<^sub>2"
    apply (rule veval'_closed)
        apply fact
    using app1 unfolding \<open>t = _\<close> by (auto simp: closed_except_def)

  have "vwellformed v\<^sub>1"
    apply (rule veval'_wellformed)
      apply fact
    using app1 unfolding \<open>t = _\<close> by auto
  have "vwellformed v\<^sub>2"
    apply (rule veval'_wellformed)
      apply fact
    using app1 unfolding \<open>t = _\<close> by auto

  have "vwelldefined' v\<^sub>1"
    apply (rule veval'_welldefined')
           apply fact
    using app1 unfolding \<open>t = _\<close> by auto
  have "vwelldefined' v\<^sub>2"
    apply (rule veval'_welldefined')
           apply fact
    using app1 unfolding \<open>t = _\<close> by auto

  have "not_shadows_vconsts v\<^sub>1"
    apply (rule veval'_shadows)
      apply fact
    using app1 unfolding \<open>t = _\<close> by auto
  have "not_shadows_vconsts v\<^sub>2"
    apply (rule veval'_shadows)
      apply fact
    using app1 unfolding \<open>t = _\<close> by auto

  show ?case
    proof (rule if_rvalI)
      fix ml_v
      assume "bv = Rval ml_v"
      show "\<exists>v. \<Gamma> \<turnstile>\<^sub>v t \<down> v \<and> related_v v ml_v"
        using \<open>do_opapp _ = _\<close>
        proof (cases rule: do_opapp_cases)
          case (closure env\<^sub>\<Lambda> n)
          then have closure':
            "ml_v\<^sub>1 = Closure env\<^sub>\<Lambda> (as_string (Name n)) exp'"
            "env' = update_v (\<lambda>_. nsBind (as_string (Name n)) ml_v\<^sub>2 (sem_env.v env\<^sub>\<Lambda>)) env\<^sub>\<Lambda>"
            unfolding \<open>ml_vs = _\<close> by auto
          obtain \<Gamma>\<^sub>\<Lambda> cs
            where "v\<^sub>1 = Vabs cs \<Gamma>\<^sub>\<Lambda>" "related_fun cs (Name n) exp'"
              and "fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma>\<^sub>\<Lambda> (fmap_of_ns (sem_env.v env\<^sub>\<Lambda>))"
            using \<open>related_v v\<^sub>1 ml_v\<^sub>1\<close> unfolding \<open>ml_v\<^sub>1 = _\<close>
            by cases auto

          then obtain ml_cs
            where "exp' = Mat (Var (Short (as_string (Name n)))) ml_cs" "Name n |\<notin>| ids (Sabs cs)" "Name n |\<notin>| all_consts"
              and "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
            by (auto elim: related_funE)

          hence "cupcake_evaluate_single env' (Mat (Var (Short (as_string (Name n)))) ml_cs) (Rval ml_v)"
            using \<open>cupcake_evaluate_single env' exp' bv\<close>
            unfolding \<open>bv = _\<close>
            by simp

          then obtain m_env v' ml_rhs ml_pat
            where "cupcake_evaluate_single env' (Var (Short (as_string (Name n)))) (Rval v')"
              and "cupcake_match_result (sem_env.c env') v' ml_cs Bindv = Rval (ml_rhs, ml_pat, m_env)"
              and "cupcake_evaluate_single (env' \<lparr> sem_env.v := nsAppend (alist_to_ns m_env) (sem_env.v env') \<rparr>) ml_rhs (Rval ml_v)"
            by cases auto

          have
            "closed_venv (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)" "wellformed_venv (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)"
            "not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)" "fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)"
            using \<open>vclosed v\<^sub>1\<close> \<open>vclosed v\<^sub>2\<close>
            using \<open>vwellformed v\<^sub>1\<close> \<open>vwellformed v\<^sub>2\<close>
            using \<open>not_shadows_vconsts v\<^sub>1\<close> \<open>not_shadows_vconsts v\<^sub>2\<close>
            using \<open>vwelldefined' v\<^sub>1\<close> \<open>vwelldefined' v\<^sub>2\<close>
            unfolding \<open>v\<^sub>1 = _\<close>
            by auto

          have "closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))"
            using \<open>vclosed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            apply (auto simp: Sterm.closed_except_simps list_all_iff)
            apply (auto simp: closed_except_def)
            done

          have "consts (Sabs cs) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) |\<union>| C"
            using \<open>vwelldefined' v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            unfolding sconsts_sabs
            by (auto simp: list_all_iff)

          have "\<not> shadows_consts (Sabs cs)"
            using \<open>not_shadows_vconsts v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            by (auto simp: list_all_iff list_ex_iff)

          have "fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)"
            using \<open>vwelldefined' v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            by simp

          have "if_rval (\<lambda>ml_v. \<exists>v. fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> \<turnstile>\<^sub>v Sabs cs $\<^sub>s Svar (Name n) \<down> v \<and> related_v v ml_v) bv"
            proof (rule app1(2))
              show "fmrel_on_fset (ids (Sabs cs $\<^sub>s Svar (Name n))) related_v (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) (fmap_of_ns (sem_env.v env'))"
                unfolding closure'
                apply (simp del: frees_sterm.simps(3) consts_sterm.simps(3) name.sel add: ids_def split!: sem_env.splits)
                apply (rule fmrel_on_fset_updateI)
                 apply (fold ids_def)
                using \<open>fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma>\<^sub>\<Lambda> _\<close> apply simp
                apply (rule \<open>related_v v\<^sub>2 ml_v\<^sub>2\<close>)
                done
            next
              show "wellformed (Sabs cs $\<^sub>s Svar (Name n))"
                using \<open>vwellformed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
                by simp
            next
              show "related_exp (Sabs cs $\<^sub>s Svar (Name n)) exp'"
                unfolding \<open>exp' = _\<close>
                using \<open>list_all2 (rel_prod related_pat related_exp) cs ml_cs\<close>
                by (auto intro:related_exp.intros simp del: name.sel)
            next
              show "closed_except (Sabs cs $\<^sub>s Svar (Name n)) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))"
                using \<open>closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))\<close> by (simp add: closed_except_def)
            next
              show "\<not> shadows_consts (Sabs cs $\<^sub>s Svar (Name n))"
                using \<open>\<not> shadows_consts (Sabs cs)\<close> \<open>Name n |\<notin>| all_consts\<close> by simp
            next
              show "consts (Sabs cs $\<^sub>s Svar (Name n)) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) |\<union>| C"
                using \<open>consts (Sabs cs) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) |\<union>| C\<close> by simp
            next
              show "fdisjnt C (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))"
                using \<open>Name n |\<notin>| all_consts\<close> \<open>fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)\<close>
                unfolding fdisjnt_alt_def all_consts_def by auto
            qed fact+
          then obtain v where "fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> \<turnstile>\<^sub>v Sabs cs $\<^sub>s Svar (Name n) \<down> v" "related_v v ml_v"
            unfolding \<open>bv = _\<close>
            by auto

          then obtain env pat rhs
            where "vfind_match cs v\<^sub>2 = Some (env, pat, rhs)"
              and "fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v"
            by (auto elim: veval'_sabs_svarE)
          hence "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) v\<^sub>2 = Some env"
            by (metis vfind_match_elem)+
          hence "linear pat" "wellformed rhs"
            using \<open>vwellformed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            by (auto simp: list_all_iff)
          hence "frees pat = patvars (mk_pat pat)"
            by (simp add: mk_pat_frees)
          hence "fmdom env = frees pat"
            apply simp
            apply (rule vmatch_dom)
            apply (rule \<open>vmatch (mk_pat pat) v\<^sub>2 = Some env\<close>)
            done

          obtain v' where "\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v'" "v' \<approx>\<^sub>e v"
            proof (rule veval'_agree_eq)
              show "fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v" by fact
            next
              have *: "Name n |\<notin>| ids rhs" if "Name n |\<notin>| fmdom env"
                proof
                  assume "Name n |\<in>| ids rhs"
                  thus False
                    unfolding ids_def
                    proof (cases rule: funion_strictE)
                      case A
                      moreover have "Name n |\<notin>| frees pat"
                        using that unfolding \<open>fmdom env = frees pat\<close> .
                      ultimately have "Name n |\<in>| frees (Sabs cs)"
                        apply auto
                        unfolding ffUnion_alt_def
                        apply simp
                        apply (rule fBexI[where x = "(pat, rhs)"])
                         apply (auto simp: fset_of_list_elem)
                        apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                        done
                      thus ?thesis
                        using \<open>Name n |\<notin>| ids (Sabs cs)\<close> unfolding ids_def
                        by blast
                    next
                      case B
                      hence "Name n |\<in>| consts (Sabs cs)"
                        apply auto
                        unfolding ffUnion_alt_def
                        apply simp
                        apply (rule fBexI[where x = "(pat, rhs)"])
                         apply (auto simp: fset_of_list_elem)
                        apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                        done
                      thus ?thesis
                        using \<open>Name n |\<notin>| ids (Sabs cs)\<close> unfolding ids_def
                        by blast
                    qed
                qed

              show "fmrel_on_fset (ids rhs) erelated (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
                apply rule
                apply auto
                   apply (rule option.rel_refl; rule erelated_refl)
                using * apply auto[]
                 apply (rule option.rel_refl; rule erelated_refl)+
                done
            next
              show "closed_venv (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
                apply rule
                 apply fact
                apply (rule vclosed.vmatch_env)
                 apply fact
                apply fact
                done
            next
              show "wellformed_venv (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
                apply rule
                 apply fact
                apply (rule vwellformed.vmatch_env)
                 apply fact
                apply fact
                done
            next
              show "closed_except rhs (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
                using \<open>fmdom env = frees pat\<close> \<open>(pat, rhs) \<in> set cs\<close>
                using \<open>closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))\<close>
                by (auto simp: Sterm.closed_except_simps list_all_iff)
            next
              show "wellformed rhs" by fact
            next
              show "consts rhs |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) |\<union>| C"
                using \<open>consts (Sabs cs) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) |\<union>| C\<close> \<open>(pat, rhs) \<in> set cs\<close>
                unfolding sconsts_sabs
                by (auto simp: list_all_iff)
            next
              have "fdisjnt C (fmdom env)"
                using \<open>(pat, rhs) \<in> set cs\<close> \<open>\<not> shadows_consts (Sabs cs)\<close>
                unfolding \<open>fmdom env = frees pat\<close>
                by (auto simp: list_ex_iff fdisjnt_alt_def all_consts_def)
              thus "fdisjnt C (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env))"
                using \<open>Name n |\<notin>| all_consts\<close> \<open>fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)\<close>
                unfolding fdisjnt_alt_def
                by (auto simp: all_consts_def)
            next
              show "\<not> shadows_consts rhs"
                using \<open>(pat, rhs) \<in> set cs\<close> \<open>\<not> shadows_consts (Sabs cs)\<close>
                by (auto simp: list_ex_iff)
            next
              have "not_shadows_vconsts_env env"
                by (rule not_shadows_vconsts.vmatch_env) fact+
              thus "not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
                using \<open>not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)\<close> by blast
            next
              have "fmpred (\<lambda>_. vwelldefined') env"
                by (rule vmatch_welldefined') fact+
              thus "fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env)"
                using \<open>fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>)\<close> by blast
            qed blast

          show ?thesis
            apply (intro exI conjI)
            unfolding \<open>t = _\<close>
             apply (rule veval'.comb)
            using \<open>\<Gamma> \<turnstile>\<^sub>v t\<^sub>1 \<down> v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
                apply blast
               apply fact
              apply fact+
            apply (rule related_v_ext)
             apply fact+
            done
        next
          case (recclosure env\<^sub>\<Lambda> funs name n)
          with recclosure have recclosure':
            "ml_v\<^sub>1 = Recclosure env\<^sub>\<Lambda> funs name"
            "env' = update_v (\<lambda>_. nsBind (as_string (Name n)) ml_v\<^sub>2 (build_rec_env funs env\<^sub>\<Lambda> (sem_env.v env\<^sub>\<Lambda>))) env\<^sub>\<Lambda>"
            unfolding \<open>ml_vs = _\<close> by auto
          obtain \<Gamma>\<^sub>\<Lambda> css
            where "v\<^sub>1 = Vrecabs css (Name name) \<Gamma>\<^sub>\<Lambda>"
              and "fmrel_on_fset (fbind (fmran css) (ids \<circ> Sabs)) related_v \<Gamma>\<^sub>\<Lambda> (fmap_of_ns (sem_env.v env\<^sub>\<Lambda>))"
              and "fmrel (\<lambda>cs (n, e). related_fun cs n e) css (fmap_of_list (map (map_prod Name (map_prod Name id)) funs))"
            using \<open>related_v v\<^sub>1 ml_v\<^sub>1\<close> unfolding \<open>ml_v\<^sub>1 = _\<close>
            by cases auto
          from \<open>fmrel _ _ _\<close> have "rel_option (\<lambda>cs (n, e). related_fun cs (Name n) e) (fmlookup css (Name name)) (find_recfun name funs)"
            apply -
            apply (subst option.rel_sel)
            apply auto
              apply (drule fmrel_fmdom_eq)
              apply (drule fmdom_notI)
            using \<open>v\<^sub>1 = Vrecabs css (Name name) \<Gamma>\<^sub>\<Lambda>\<close> \<open>vwellformed v\<^sub>1\<close> apply auto[1]
            using recclosure(3) apply auto[1]
            apply (erule fmrel_cases[where x = "Name name"])
             apply simp
            apply (subst (asm) fmlookup_of_list)
            apply (simp add: name.map_of_rekey')
            by blast

          then obtain cs where "fmlookup css (Name name) = Some cs" "related_fun cs (Name n) exp'"
            using \<open>find_recfun _ _ = _\<close>
            by cases auto

          then obtain ml_cs
            where "exp' = Mat (Var (Short (as_string (Name n)))) ml_cs" "Name n |\<notin>| ids (Sabs cs)" "Name n |\<notin>| all_consts"
              and "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
            by (auto elim: related_funE)

          hence "cupcake_evaluate_single env' (Mat (Var (Short n)) ml_cs) (Rval ml_v)"
            using \<open>cupcake_evaluate_single env' exp' bv\<close>
            unfolding \<open>bv = _\<close>
            by simp

          then obtain m_env v' ml_rhs ml_pat
            where "cupcake_evaluate_single env' (Var (Short n)) (Rval v')"
              and "cupcake_match_result (sem_env.c env') v' ml_cs Bindv = Rval (ml_rhs, ml_pat, m_env)"
              and "cupcake_evaluate_single (env' \<lparr> sem_env.v := nsAppend (alist_to_ns m_env) (sem_env.v env') \<rparr>) ml_rhs (Rval ml_v)"
            by cases auto

          have "closed_venv (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))"
            using \<open>vclosed v\<^sub>1\<close> \<open>vclosed v\<^sub>2\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            unfolding \<open>v\<^sub>1 = _\<close> mk_rec_env_def
            apply auto
            apply rule
             apply rule
              apply (auto intro: fmdomI)
            done
          have "wellformed_venv (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))"
            using \<open>vwellformed v\<^sub>1\<close> \<open>vwellformed v\<^sub>2\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            unfolding \<open>v\<^sub>1 = _\<close> mk_rec_env_def
            apply auto
            apply rule
             apply rule
              apply (auto intro: fmdomI)
            done
          have "not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))"
            using \<open>not_shadows_vconsts v\<^sub>1\<close> \<open>not_shadows_vconsts v\<^sub>2\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            unfolding \<open>v\<^sub>1 = _\<close> mk_rec_env_def
            apply auto
            apply rule
             apply rule
              apply (auto intro: fmdomI)
            done
          have "fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))"
            using \<open>vwelldefined' v\<^sub>1\<close> \<open>vwelldefined' v\<^sub>2\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            unfolding \<open>v\<^sub>1 = _\<close> mk_rec_env_def
            apply auto
            apply rule
             apply rule
              apply (auto intro: fmdomI)
            done

          have "closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))"
            using \<open>vclosed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            apply (auto simp: Sterm.closed_except_simps list_all_iff)
            using \<open>fmlookup css (Name name) = Some cs\<close>
            apply (auto simp: closed_except_def dest!: fmpredD[where m = css])
            done

          have "consts (Sabs cs) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>) |\<union>| (C |\<union>| fmdom css)"
            using \<open>vwelldefined' v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            unfolding sconsts_sabs
            using \<open>fmlookup css (Name name) = Some cs\<close>
            by (auto simp: list_all_iff dest!: fmpredD[where m = css])

          have "\<not> shadows_consts (Sabs cs)"
            using \<open>not_shadows_vconsts v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            by (auto simp: list_all_iff list_ex_iff)

          have "fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)"
            using \<open>vwelldefined' v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            by auto

          have "if_rval (\<lambda>ml_v. \<exists>v. fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) \<turnstile>\<^sub>v Sabs cs $\<^sub>s Svar (Name n) \<down> v \<and> related_v v ml_v) bv"
            proof (rule app1(2))
              have "fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma>\<^sub>\<Lambda> (fmap_of_ns (sem_env.v env\<^sub>\<Lambda>))"
                apply (rule fmrel_on_fsubset)
                 apply fact
                apply (subst funion_image_bind_eq[symmetric])
                apply (rule ffUnion_subset_elem)
                apply (subst fimage_iff)
                apply (rule fBexI)
                 apply simp
                apply (rule fmranI)
                apply fact
                done

              have "fmrel_on_fset (ids (Sabs cs)) related_v (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) (cake_mk_rec_env funs env\<^sub>\<Lambda>)"
                apply rule
                apply (rule mk_rec_env_related[THEN fmrelD])
                 apply (rule \<open>fmrel _ css _\<close>)
                apply (rule \<open>fmrel_on_fset (fbind _ _) related_v \<Gamma>\<^sub>\<Lambda> _\<close>)
                done

              show "fmrel_on_fset (ids (Sabs cs $\<^sub>s Svar (Name n))) related_v (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>)) (fmap_of_ns (sem_env.v env'))"
                unfolding recclosure'
                apply (simp del: frees_sterm.simps(3) consts_sterm.simps(3) name.sel add: ids_def split!: sem_env.splits)
                apply (rule fmrel_on_fset_updateI)
                unfolding build_rec_env_fmap
                 apply (rule fmrel_on_fset_addI)
                  apply (fold ids_def)
                subgoal
                  using \<open>fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma>\<^sub>\<Lambda> _\<close> by simp
                subgoal
                  using \<open>fmrel_on_fset (ids (Sabs cs)) related_v (mk_rec_env css \<Gamma>\<^sub>\<Lambda>) _\<close> by simp
                apply (rule \<open>related_v v\<^sub>2 ml_v\<^sub>2\<close>)
                done
            next
              show "wellformed (Sabs cs $\<^sub>s Svar (Name n))"
                using \<open>vwellformed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
                using \<open>fmlookup css (Name name) = Some cs\<close>
                by auto
            next
              show "related_exp (Sabs cs $\<^sub>s Svar (Name n)) exp'"
                unfolding \<open>exp' = _\<close>
                apply (rule related_exp.intros)
                 apply fact
                apply (rule related_exp.intros)
                done
            next
              show "closed_except (Sabs cs $\<^sub>s Svar (Name n)) (fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>)))"
                using \<open>closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))\<close>
                by (auto simp: list_all_iff closed_except_def)
            next
              show "\<not> shadows_consts (Sabs cs $\<^sub>s Svar (Name n))"
                using \<open>\<not> shadows_consts (Sabs cs)\<close> \<open>Name n |\<notin>| all_consts\<close> by simp
            next
              show "consts (Sabs cs $\<^sub>s Svar (Name n)) |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>)) |\<union>| C"
                using \<open>consts (Sabs cs) |\<subseteq>| _\<close> unfolding mk_rec_env_def
                by auto
            next
              show "fdisjnt C (fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>)))"
                using \<open>Name n |\<notin>| all_consts\<close> \<open>fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)\<close> \<open>vwelldefined' v\<^sub>1\<close>
                unfolding mk_rec_env_def \<open>v\<^sub>1 = _\<close>
                by (auto simp: fdisjnt_alt_def all_consts_def)
            qed fact+
          then obtain v
            where "fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) \<turnstile>\<^sub>v Sabs cs $\<^sub>s Svar (Name n) \<down> v" "related_v v ml_v"
            unfolding \<open>bv = _\<close>
            by auto

          then obtain env pat rhs
            where "vfind_match cs v\<^sub>2 = Some (env, pat, rhs)"
              and "fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v"
            by (auto elim: veval'_sabs_svarE)
          hence "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) v\<^sub>2 = Some env"
            by (metis vfind_match_elem)+
          hence "linear pat" "wellformed rhs"
            using \<open>vwellformed v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
            using \<open>fmlookup css (Name name) = Some cs\<close>
            by (auto simp: list_all_iff)
          hence "frees pat = patvars (mk_pat pat)"
            by (simp add: mk_pat_frees)
          hence "fmdom env = frees pat"
            apply simp
            apply (rule vmatch_dom)
            apply (rule \<open>vmatch (mk_pat pat) v\<^sub>2 = Some env\<close>)
            done

          obtain v' where "\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v'" "v' \<approx>\<^sub>e v"
            proof (rule veval'_agree_eq)
              show "fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> v" by fact
            next
              have *: "Name n |\<notin>| ids rhs" if "Name n |\<notin>| fmdom env"
                proof
                  assume "Name n |\<in>| ids rhs"
                  thus False
                    unfolding ids_def
                    proof (cases rule: funion_strictE)
                      case A
                      moreover have "Name n |\<notin>| frees pat"
                        using that unfolding \<open>fmdom env = frees pat\<close> .
                      ultimately have "Name n |\<in>| frees (Sabs cs)"
                        apply auto
                        unfolding ffUnion_alt_def
                        apply simp
                        apply (rule fBexI[where x = "(pat, rhs)"])
                         apply (auto simp: fset_of_list_elem)
                        apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                        done
                      thus ?thesis
                        using \<open>Name n |\<notin>| ids (Sabs cs)\<close> unfolding ids_def
                        by blast
                    next
                      case B
                      hence "Name n |\<in>| consts (Sabs cs)"
                        apply auto
                        unfolding ffUnion_alt_def
                        apply simp
                        apply (rule fBexI[where x = "(pat, rhs)"])
                         apply (auto simp: fset_of_list_elem)
                        apply (rule \<open>(pat, rhs) \<in> set cs\<close>)
                        done
                      thus ?thesis
                        using \<open>Name n |\<notin>| ids (Sabs cs)\<close> unfolding ids_def
                        by blast
                    qed
                qed

                show "fmrel_on_fset (ids rhs) erelated (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda> ++\<^sub>f env) (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env)"
                  apply rule
                  apply auto
                         apply (rule option.rel_refl; rule erelated_refl)
                  using * apply auto[]
                       apply (rule option.rel_refl; rule erelated_refl)+
                  using * apply auto[]
                   apply (rule option.rel_refl; rule erelated_refl)+
                  done
              next
                show "closed_venv (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env)"
                  apply rule
                   apply fact
                  apply (rule vclosed.vmatch_env)
                   apply fact
                  apply fact
                  done
              next
                show "wellformed_venv (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env)"
                  apply rule
                   apply fact
                  apply (rule vwellformed.vmatch_env)
                   apply fact
                  apply fact
                  done
              next
                show "closed_except rhs (fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env))"
                  using \<open>fmdom env = frees pat\<close> \<open>(pat, rhs) \<in> set cs\<close>
                  using \<open>closed_except (Sabs cs) (fmdom (fmupd (Name n) v\<^sub>2 \<Gamma>\<^sub>\<Lambda>))\<close>
                  apply (auto simp: Sterm.closed_except_simps list_all_iff)
                  apply (erule ballE[where x = "(pat, rhs)"])
                   apply (auto simp: closed_except_def)
                  done
            next
              show "wellformed rhs" by fact
            next
              show "consts rhs |\<subseteq>| fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env) |\<union>| C"
                using \<open>consts (Sabs cs) |\<subseteq>| _\<close> \<open>(pat, rhs) \<in> set cs\<close>
                unfolding sconsts_sabs mk_rec_env_def
                by (auto simp: list_all_iff)
            next
              have "fdisjnt C (fmdom env)"
                using \<open>(pat, rhs) \<in> set cs\<close> \<open>\<not> shadows_consts (Sabs cs)\<close>
                unfolding \<open>fmdom env = frees pat\<close>
                by (auto simp: list_ex_iff all_consts_def fdisjnt_alt_def)
              moreover have "fdisjnt C (fmdom css)"
                using \<open>vwelldefined' v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close>
                by simp
              ultimately show "fdisjnt C (fmdom (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env))"
                using \<open>Name n |\<notin>| all_consts\<close> \<open>fdisjnt C (fmdom \<Gamma>\<^sub>\<Lambda>)\<close>
                unfolding fdisjnt_alt_def mk_rec_env_def
                by (auto simp: all_consts_def)
            next
              show "\<not> shadows_consts rhs"
                using \<open>(pat, rhs) \<in> set cs\<close> \<open>\<not> shadows_consts (Sabs cs)\<close>
                by (auto simp: list_ex_iff)
            next
              have "not_shadows_vconsts_env env"
                by (rule not_shadows_vconsts.vmatch_env) fact+
              thus "not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env)"
                using \<open>not_shadows_vconsts_env (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))\<close> by blast
            next
              have "fmpred (\<lambda>_. vwelldefined') env"
                by (rule vmatch_welldefined') fact+
              thus "fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>) ++\<^sub>f env)"
                using \<open>fmpred (\<lambda>_. vwelldefined') (fmupd (Name n) v\<^sub>2 (\<Gamma>\<^sub>\<Lambda> ++\<^sub>f mk_rec_env css \<Gamma>\<^sub>\<Lambda>))\<close> by blast
            qed simp

          show ?thesis
            apply (intro exI conjI)
            unfolding \<open>t = _\<close>
             apply (rule veval'.rec_comb)
            using \<open>\<Gamma> \<turnstile>\<^sub>v t\<^sub>1 \<down> v\<^sub>1\<close> unfolding \<open>v\<^sub>1 = _\<close> apply blast
                apply fact+
            apply (rule related_v_ext)
             apply fact+
            done
        qed
    qed
next
  case (mat1 env ml_scr ml_scr' ml_cs ml_rhs ml_pat env' ml_res)

  obtain scr cs
    where "t = Sabs cs $\<^sub>s scr" "related_exp scr ml_scr"
      and "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
    using \<open>related_exp t (Mat ml_scr ml_cs)\<close>
    by cases

  have "sem_env.c env = as_static_cenv"
    using \<open>is_cupcake_all_env env\<close>
    by (auto elim: is_cupcake_all_envE)

  obtain scr' where "\<Gamma> \<turnstile>\<^sub>v scr \<down> scr'" "related_v scr' ml_scr'"
    using mat1(4) unfolding if_rval.simps
    proof
      show
        "is_cupcake_all_env env" "related_exp scr ml_scr" "wellformed_venv \<Gamma>"
        "closed_venv \<Gamma>" "fmpred (\<lambda>_. vwelldefined') \<Gamma>" "fdisjnt C (fmdom \<Gamma>)"
        "not_shadows_vconsts_env \<Gamma>"
        by fact+
    next
      show "fmrel_on_fset (ids scr) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
        apply (rule fmrel_on_fsubset)
         apply fact
        unfolding \<open>t = _\<close> ids_def
        apply auto
        done
    next
      show
        "wellformed scr" "consts scr |\<subseteq>| fmdom \<Gamma> |\<union>| C"
        "closed_except scr (fmdom \<Gamma>)" "\<not> shadows_consts scr"
        using mat1 unfolding \<open>t = _\<close> by (auto simp: closed_except_def)
    qed blast

  have "list_all (\<lambda>(pat, _). linear pat) cs"
    using mat1 unfolding \<open>t = _\<close> by (auto simp: list_all_iff)

  obtain rhs pat \<Gamma>'
    where "ml_pat = mk_ml_pat (mk_pat pat)" "related_exp rhs ml_rhs"
      and "vfind_match cs scr' = Some (\<Gamma>', pat, rhs)"
      and "var_env \<Gamma>' env'"
    using \<open>list_all2 _ cs ml_cs\<close> \<open>list_all _ cs\<close> \<open>related_v scr' ml_scr'\<close> mat1(2)
    unfolding \<open>sem_env.c env = as_static_cenv\<close>
    by (auto elim: match_all_related)

  hence "vmatch (mk_pat pat) scr' = Some \<Gamma>'"
    by (auto dest: vfind_match_elem)
  hence "patvars (mk_pat pat) = fmdom \<Gamma>'"
    by (auto simp: vmatch_dom)

  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact

  have "linear pat"
    using \<open>(pat, rhs) \<in> set cs\<close> \<open>wellformed t\<close> unfolding \<open>t = _\<close>
    by (auto simp: list_all_iff)
  hence "fmdom \<Gamma>' = frees pat"
    using \<open>patvars (mk_pat pat) = fmdom \<Gamma>'\<close>
    by (simp add: mk_pat_frees)

  show ?case
    proof (rule if_rvalI)
      fix ml_rhs'
      assume "ml_res = Rval ml_rhs'"

      obtain rhs' where "\<Gamma> ++\<^sub>f \<Gamma>' \<turnstile>\<^sub>v rhs \<down> rhs'" "related_v rhs' ml_rhs'"
        using mat1(5) unfolding \<open>ml_res = _\<close> if_rval.simps
        proof
          show "is_cupcake_all_env (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>)"
            proof (rule cupcake_v_update_preserve)
              have "list_all (is_cupcake_value \<circ> snd) env'"
                proof (rule match_all_preserve)
                  show "cupcake_c_ns (sem_env.c env)"
                    unfolding \<open>sem_env.c env = _\<close> by (rule static_cenv)
                next
                  have "is_cupcake_exp (Mat ml_scr ml_cs)"
                    apply (rule related_exp_is_cupcake)
                    using mat1 by auto
                  thus "cupcake_clauses ml_cs"
                    by simp

                  show "is_cupcake_value ml_scr'"
                    apply (rule cupcake_single_preserve)
                      apply (rule mat1)
                     apply (rule mat1)
                    using \<open>is_cupcake_exp (Mat ml_scr ml_cs)\<close> by simp
                qed fact+
              hence "is_cupcake_ns (alist_to_ns env')"
                by (rule cupcake_alist_to_ns_preserve)
              moreover have "is_cupcake_ns (sem_env.v env)"
                by (rule is_cupcake_all_envD) fact
              ultimately show "is_cupcake_ns (nsAppend (alist_to_ns env') (sem_env.v env))"
                by (rule cupcake_nsAppend_preserve)
          qed fact
        next
          show "related_exp rhs ml_rhs"
            by fact
        next
          have *: "fmdom (fmap_of_list (map (map_prod Name id) env')) = fmdom \<Gamma>'"
            using \<open>var_env \<Gamma>' env'\<close>
            by (metis fmrel_fmdom_eq)

          have **: "id |\<in>| ids t" if "id |\<in>| ids rhs" "id |\<notin>| fmdom \<Gamma>'" for id
            using \<open>id |\<in>| ids rhs\<close> unfolding ids_def
            proof (cases rule: funion_strictE)
              case A
              from that have "id |\<notin>| frees pat"
                unfolding \<open>fmdom \<Gamma>' = frees pat\<close> by simp
              hence "id |\<in>| frees t"
                using \<open>(pat, rhs) \<in> set cs\<close>
                unfolding \<open>t = _\<close>
                apply auto
                apply (subst ffUnion_alt_def)
                apply simp
                apply (rule fBexI[where x = "(pat, rhs)"])
                using A apply (auto simp: fset_of_list_elem)
                done
              thus "id |\<in>| frees t |\<union>| consts t" by simp
            next
              case B
              hence "id |\<in>| consts t"
                using \<open>(pat, rhs) \<in> set cs\<close>
                unfolding \<open>t = _\<close>
                apply auto
                apply (subst ffUnion_alt_def)
                apply simp
                apply (rule fBexI[where x = "(pat, rhs)"])
                 apply (auto simp: fset_of_list_elem)
                done
              thus "id |\<in>| frees t |\<union>| consts t" by simp
            qed

          have "fmrel_on_fset (ids rhs) related_v (\<Gamma> ++\<^sub>f \<Gamma>') (fmap_of_ns (sem_env.v env) ++\<^sub>f fmap_of_list (map (map_prod Name id) env'))"
            apply rule
            apply simp
            apply safe
            subgoal
              apply (rule fmrelD)
              apply (rule \<open>var_env \<Gamma>' env'\<close>)
              done
            subgoal using * by simp
            subgoal using *
              by (metis (no_types, hide_lams) comp_def fimageI fmdom_fmap_of_list fset_of_list_map fst_comp_map_prod)
            subgoal using **
              by (metis fmlookup_ns fmrel_on_fsetD mat1.prems(2))
            done

          thus "fmrel_on_fset (ids rhs) related_v (\<Gamma> ++\<^sub>f \<Gamma>') (fmap_of_ns (sem_env.v (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>)))"
            by (auto split: sem_env.splits)
        next
          show "wellformed_venv (\<Gamma> ++\<^sub>f \<Gamma>')"
            apply rule
             apply fact
            apply (rule vwellformed.vmatch_env)
             apply fact
            apply (rule veval'_wellformed)
              apply fact
            using mat1 unfolding \<open>t = _\<close> by auto
        next
          show "closed_venv (\<Gamma> ++\<^sub>f \<Gamma>')"
            apply rule
             apply fact
            apply (rule vclosed.vmatch_env)
             apply fact
            apply (rule veval'_closed)
                apply fact
            using mat1 unfolding \<open>t = _\<close> by (auto simp: closed_except_def)
        next
          show "fmpred (\<lambda>_. vwelldefined') (\<Gamma> ++\<^sub>f \<Gamma>')"
            apply rule
             apply fact
            apply (rule vmatch_welldefined')
             apply fact
            apply (rule veval'_welldefined')
                   apply fact
            using mat1 unfolding \<open>t = _\<close> by auto
        next
          show "not_shadows_vconsts_env (\<Gamma> ++\<^sub>f \<Gamma>')"
            apply rule
             apply fact
            apply (rule not_shadows_vconsts.vmatch_env)
             apply fact
            apply (rule veval'_shadows)
              apply fact
            using mat1 unfolding \<open>t = _\<close> by auto
        next
          show "wellformed rhs"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>wellformed t\<close> unfolding \<open>t = _\<close>
            by (auto simp: list_all_iff)
        next
          show "closed_except rhs (fmdom (\<Gamma> ++\<^sub>f \<Gamma>'))"
            apply simp
            unfolding \<open>fmdom \<Gamma>' = frees pat\<close>
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>closed_except t (fmdom \<Gamma>)\<close> unfolding \<open>t = _\<close>
            by (auto simp: Sterm.closed_except_simps list_all_iff)
        next
          have "consts (Sabs cs) |\<subseteq>| fmdom \<Gamma> |\<union>| C"
            using mat1 unfolding \<open>t = _\<close> by auto
          show "consts rhs |\<subseteq>| fmdom (\<Gamma> ++\<^sub>f \<Gamma>') |\<union>| C"
            apply simp
            unfolding \<open>fmdom \<Gamma>' = frees pat\<close>
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>consts (Sabs cs) |\<subseteq>| _\<close>
            unfolding sconsts_sabs
            by (auto simp: list_all_iff)
        next
          have "fdisjnt C (fmdom \<Gamma>')"
            unfolding \<open>fmdom \<Gamma>' = frees pat\<close>
            using \<open>\<not> shadows_consts t\<close> \<open>(pat, rhs) \<in> set cs\<close>
            unfolding \<open>t = _\<close>
            by (auto simp: list_ex_iff fdisjnt_alt_def all_consts_def)

          thus "fdisjnt C (fmdom (\<Gamma> ++\<^sub>f \<Gamma>'))"
            using \<open>fdisjnt C (fmdom \<Gamma>)\<close>
            unfolding fdisjnt_alt_def by auto
        next
          show "\<not> shadows_consts rhs"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>\<not> shadows_consts t\<close> unfolding \<open>t = _\<close>
            by (auto simp: list_ex_iff)
        qed blast

      show "\<exists>t'. \<Gamma> \<turnstile>\<^sub>v t \<down> t' \<and> related_v t' ml_rhs'"
        unfolding \<open>t = _\<close>
        apply (intro exI conjI seval.intros)
         apply (rule veval'.intros)
            apply (rule veval'.intros)
           apply fact+
        done
    qed
qed auto

theorem semantic_correctness:
  fixes exp
  assumes "cupcake_evaluate_single env exp (Rval ml_v)" "is_cupcake_all_env env"
  assumes "fmrel_on_fset (ids t) related_v \<Gamma> (fmap_of_ns (sem_env.v env))"
  assumes "related_exp t exp"
  assumes "wellformed t" "wellformed_venv \<Gamma>"
  assumes "closed_venv \<Gamma>" "closed_except t (fmdom \<Gamma>)"
  assumes "fmpred (\<lambda>_. vwelldefined') \<Gamma>" "consts t |\<subseteq>| fmdom \<Gamma> |\<union>| C"
  assumes "fdisjnt C (fmdom \<Gamma>)"
  assumes "\<not> shadows_consts t" "not_shadows_vconsts_env \<Gamma>"
  obtains v where "\<Gamma> \<turnstile>\<^sub>v t \<down> v" "related_v v ml_v"
using semantic_correctness0[OF assms]
by auto

end end

end