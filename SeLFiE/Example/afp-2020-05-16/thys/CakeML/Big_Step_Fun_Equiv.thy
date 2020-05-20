section "Equivalence to the functional semantics"

theory Big_Step_Fun_Equiv
imports
  Big_Step_Determ
  Big_Step_Total
  Evaluate_Clock
begin

locale eval =
  fixes
    eval :: "v sem_env \<Rightarrow> exp \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v, v) result" and
    eval_list :: "v sem_env \<Rightarrow> exp list \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v list, v) result" and
    eval_match :: "v sem_env \<Rightarrow> v \<Rightarrow> (pat \<times> exp) list \<Rightarrow> v \<Rightarrow> 'a state \<Rightarrow> 'a state \<times> (v, v) result"

  assumes
    valid_eval: "evaluate True env s e (eval env e s)" and
    valid_eval_list: "evaluate_list True env s es (eval_list env es s)" and
    valid_eval_match: "evaluate_match True env s v pes err_v (eval_match env v pes err_v s)"
begin

lemmas eval_all = valid_eval valid_eval_list valid_eval_match

lemma evaluate_iff:
  "evaluate True env st e r \<longleftrightarrow> (r = eval env e st)"
  "evaluate_list True env st es r' \<longleftrightarrow> (r' = eval_list env es st)"
  "evaluate_match True env st v pes v' r \<longleftrightarrow> (r = eval_match env v pes v' st)"
by (metis eval_all evaluate_determ)+

lemma evaluate_iff_sym:
  "evaluate True env st e r \<longleftrightarrow> (eval env e st = r)"
  "evaluate_list True env st es r' \<longleftrightarrow> (eval_list env es st = r')"
  "evaluate_match True env st v pes v' r \<longleftrightarrow> (eval_match env v pes v' st = r)"
by (auto simp: evaluate_iff)

lemma other_eval_eq:
  assumes "Big_Step_Fun_Equiv.eval eval' eval_list' eval_match'"
  shows "eval' = eval" "eval_list' = eval_list" "eval_match' = eval_match"
proof -
  interpret other: Big_Step_Fun_Equiv.eval eval' eval_list' eval_match' by fact

  show "eval' = eval"
    apply (rule ext)+
    using evaluate_iff other.evaluate_iff
    by (metis evaluate_determ)

  show "eval_list' = eval_list"
    apply (rule ext)+
    using evaluate_iff other.evaluate_iff
    by (metis evaluate_determ)

  show "eval_match' = eval_match"
    apply (rule ext)+
    using evaluate_iff other.evaluate_iff
    by (metis evaluate_determ)
qed

lemma eval_list_singleton:
  "eval_list env [e] st = map_prod id list_result (eval env e st)"
proof -
  define res where "res = eval_list env [e] st"
  then have e: "evaluate_list True env st [e] res"
    by (metis evaluate_iff)
  then obtain st' r where "res = (st', r)"
    by (metis surj_pair)
  then have "map_prod id list_result (eval env e st) = (st', r)"
    proof (cases r)
      case (Rval vs)
      with e obtain v where "vs = [v]" "evaluate True env st e (st', Rval v)"
        unfolding \<open>res = (st', r)\<close> by (metis evaluate_list_singleton_valE)
      then have "eval env e st = (st', Rval v)"
        by (metis evaluate_iff_sym)
      then show ?thesis
        unfolding \<open>r = _\<close> \<open>vs = _\<close> by auto
    next
      case (Rerr err)
      with e have "evaluate True env st e (st', Rerr err)"
        unfolding \<open>res = (st', r)\<close> by (metis evaluate_list_singleton_errD)
      then have "eval env e st = (st', Rerr err)"
        by (metis evaluate_iff_sym)
      then show ?thesis
        unfolding \<open>r = _\<close> by (cases err) auto
    qed
  then show ?thesis
    using res_def \<open>res = (st', r)\<close>
    by metis
qed

lemma eval_eqI:
  assumes "\<And>r. evaluate True env st1 e1 r \<longleftrightarrow> evaluate True env st2 e2 r"
  shows "eval env e1 st1 = eval env e2 st2"
using assms by (metis evaluate_iff)

lemma eval_match_eqI:
  assumes "\<And>r. evaluate_match True env1 st1 v1 pes1 err_v1 r \<longleftrightarrow> evaluate_match True env2 st2 v2 pes2 err_v2 r"
  shows "eval_match env1 v1 pes1 err_v1 st1 = eval_match env2 v2 pes2 err_v2 st2"
using assms by (metis evaluate_iff)

lemma eval_tannot[simp]: "eval env (Tannot e t1) st = eval env e st"
by (rule eval_eqI) (auto elim: evaluate.cases intro: evaluate_match_evaluate_list_evaluate.intros)

lemma eval_lannot[simp]: "eval env (Lannot e t1) st = eval env e st"
by (rule eval_eqI) (auto elim: evaluate.cases intro: evaluate_match_evaluate_list_evaluate.intros)

lemma eval_match[simp]:
  "eval env (Mat e pes) st =
    (case eval env e st of
      (st', Rval v) \<Rightarrow> eval_match env v pes Bindv st'
    | (st', Rerr err) \<Rightarrow> (st', Rerr err))"
apply (subst evaluate_iff_sym[symmetric])
apply (simp only: split!: prod.splits result.splits)
subgoal
  apply (subst (asm) evaluate_iff_sym[symmetric])
  apply (rule mat1, rule)
  apply assumption
  apply (subst Bindv_def)
  apply (metis valid_eval_match)
  done
subgoal
  apply (subst (asm) evaluate_iff_sym[symmetric])
  by (auto intro: evaluate_match_evaluate_list_evaluate.intros)
done

lemma eval_match_empty[simp]: "eval_match env v2 [] err_v st = (st, Rerr (Rraise err_v))"
by (subst evaluate_iff_sym[symmetric]) (auto intro: evaluate_match_evaluate_list_evaluate.intros)

end

lemma run_eval: "\<exists>run_eval. \<forall>env e s. evaluate True env s e (run_eval env e s)"
proof -
  define f where "f env_e_s = (case env_e_s of (env, e, s::'a state) \<Rightarrow> evaluate True env s e)" for env_e_s
  have "\<exists>g. \<forall>env_e_s. f env_e_s (g env_e_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env e
      fix s :: "'a state"
      obtain s' r where "evaluate True env s e (s', r)"
        by (metis evaluate_total)
      then show "\<exists>r. evaluate True env s e r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

lemma run_eval_list: "\<exists>run_eval_list. \<forall>env es s. evaluate_list True env s es (run_eval_list env es s)"
proof -
  define f where "f env_es_s = (case env_es_s of (env, es, s::'a state) \<Rightarrow> evaluate_list True env s es)" for env_es_s
  have "\<exists>g. \<forall>env_es_s. f env_es_s (g env_es_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env es
      fix s :: "'a state"
      obtain s' r where "evaluate_list True env s es (s', r)"
        by (metis evaluate_list_total)
      then show "\<exists>r. evaluate_list True env s es r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

lemma run_eval_match: "\<exists>run_eval_match. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (run_eval_match env v pes err_v s)"
proof -
  define f where "f env_v_pes_err_v_s = (case env_v_pes_err_v_s of (env, v, pes, err_v, s::'a state) \<Rightarrow> evaluate_match True env s v pes err_v)" for env_v_pes_err_v_s
  have "\<exists>g. \<forall>env_es_s. f env_es_s (g env_es_s)"
    proof (rule choice, safe, unfold f_def prod.case)
      fix env v pes err_v
      fix s :: "'a state"
      obtain s' r where "evaluate_match True env s v pes err_v (s', r)"
        by (metis evaluate_match_total)
      then show "\<exists>r. evaluate_match True env s v pes err_v r"
        by auto
    qed
  then show ?thesis
    unfolding f_def
    by force
qed

global_interpretation run: eval
  "SOME f. \<forall>env e s. evaluate True env s e (f env e s)"
  "SOME f. \<forall>env es s. evaluate_list True env s es (f env es s)"
  "SOME f. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (f env v pes err_v s)"
  defines
    run_eval = "SOME f. \<forall>env e s. evaluate True env s e (f env e s)" and
    run_eval_list = "SOME f. \<forall>env es s. evaluate_list True env s es (f env es s)" and
    run_eval_match = "SOME f. \<forall>env v pes err_v s. evaluate_match True env s v pes err_v (f env v pes err_v s)"
proof (standard, goal_cases)
  case 1
  show ?case
    using someI_ex[OF run_eval, rule_format] .
next
  case 2
  show ?case
    using someI_ex[OF run_eval_list, rule_format] .
next
  case 3
  show ?case
    using someI_ex[OF run_eval_match, rule_format] .
qed

hide_fact run_eval
hide_fact run_eval_list
hide_fact run_eval_match

lemma fun_evaluate:
  "evaluate_match True env s v pes err_v (map_prod id (map_result hd id) (fun_evaluate_match s env v pes err_v))"
  "evaluate_list True env s es (fun_evaluate s env es)"
proof (induction rule: fun_evaluate_induct)
  case (5 st env e pes)
  from 5(1) show ?case
    apply (rule evaluate_list_singleton_cases)
    subgoal
      apply simp
      apply (rule evaluate_match_evaluate_list_evaluate.cons1)
      apply (intro conjI)
      apply (rule handle1)
      apply assumption
      apply (rule evaluate_match_evaluate_list_evaluate.empty)
      done
    subgoal for s' err
      apply (simp split!: error_result.splits)
      subgoal for exn
        apply (cases "fun_evaluate_match s' env exn pes exn" rule: prod_result_cases; simp only:)
        subgoal premises prems
          using prems(4)
          apply (rule fun_evaluate_matchE)
          apply simp
          apply (rule evaluate_match_evaluate_list_evaluate.cons1)
          apply (intro conjI)
          apply (rule handle2)
          apply (intro conjI)
          apply (rule prems)
          using 5(2)[OF prems(1)[symmetric] refl refl, unfolded prems(4)]
          apply simp
          by (rule evaluate_match_evaluate_list_evaluate.empty)
        subgoal premises prems
          apply (rule evaluate_match_evaluate_list_evaluate.cons2)
          apply (rule handle2)
          apply (intro conjI)
          apply (rule prems)
          supply error_result.map_ident[simp]
          using 5(2)[OF prems(1)[symmetric] refl refl, unfolded prems(4), simplified] .
        done
      subgoal
        apply (rule evaluate_match_evaluate_list_evaluate.cons2)
        apply (rule handle3)
        by assumption
      done
    done
next
  case (6 st env cn es)
  show ?case
    proof (cases "do_con_check (c env) cn (length es)")
      case True
      then show ?thesis
        apply simp
        apply (frule 6)
        apply (cases "fun_evaluate st env (rev es)" rule: prod_result_cases; simp)
        subgoal for _ vs
          apply (frule do_con_check_build_conv[where vs = "rev vs"], auto split: option.splits)
          apply (rule evaluate_match_evaluate_list_evaluate.cons1)
          apply (intro conjI)
          apply (rule con1)
          apply (intro conjI)
          apply assumption+
          by (rule evaluate_match_evaluate_list_evaluate.empty)
        subgoal
          by (auto intro: evaluate_match_evaluate_list_evaluate.intros)
        done
    next
      case False
      then show ?thesis
        apply simp
        apply (rule evaluate_match_evaluate_list_evaluate.cons2)
        apply (rule con2)
        by assumption
    qed
next
  case (9 st env op es)
  note do_app.simps[simp del]
  show ?case
    apply (cases "fun_evaluate st env (rev es)" rule: prod_result_cases; simp)
    subgoal
      apply (safe; simp split!: option.splits)
      subgoal using 9 by (auto intro: evaluate_match_evaluate_list_evaluate.intros)
      subgoal premises prems
        apply (rule conjI)
        using 9 prems apply (fastforce intro: evaluate_match_evaluate_list_evaluate.intros)
        apply safe
        using 9(2)[OF prems(1)[symmetric] refl prems(2) prems(3) refl]
        apply (cases rule: evaluate_list_singleton_cases)
        subgoal by simp
        subgoal
          apply simp
          apply (rule evaluate_match_evaluate_list_evaluate.cons1)
          using 9 prems
          by (auto intro: evaluate_match_evaluate_list_evaluate.intros simp: dec_clock_def)
        subgoal
          apply simp
          apply (rule evaluate_match_evaluate_list_evaluate.cons2)
          using 9 prems
          by (auto intro: evaluate_match_evaluate_list_evaluate.intros simp: dec_clock_def)
        done
      subgoal using 9 by (auto intro: evaluate_match_evaluate_list_evaluate.intros)
      subgoal
        apply (rule evaluate_list_singletonI)
        apply (rule app4)
        apply (intro conjI)
        using 9 by auto
      done
    subgoal
      apply (rule evaluate_match_evaluate_list_evaluate.cons2)
      apply (rule app6)
      using 9(1) by simp
    done
next
  case (12 st env e pes)
  from 12(1) show ?case
    apply (rule evaluate_list_singleton_cases)
    subgoal for s' v
      apply simp
      apply (cases "fun_evaluate_match s' env v pes Bindv" rule: prod_result_cases; simp only:)
      subgoal premises prems
        using prems(3)
        apply (rule fun_evaluate_matchE)
        apply simp
        apply (rule evaluate_match_evaluate_list_evaluate.cons1)
        apply (intro conjI)
        apply (rule mat1)
        apply (fold Bindv_def)
        apply (intro conjI)
        apply (rule prems)
        supply error_result.map_ident[simp]
        using 12(2)[OF prems(1)[symmetric] refl, simplified, unfolded prems(3), simplified]
        apply simp
        by (rule evaluate_match_evaluate_list_evaluate.empty)
      subgoal premises prems
        apply (rule evaluate_match_evaluate_list_evaluate.cons2)
        apply (rule mat1)
        apply (fold Bindv_def)
        apply (intro conjI)
        apply (rule prems)
        supply error_result.map_ident[simp]
        using 12(2)[OF prems(1)[symmetric] refl, simplified, unfolded prems(3), simplified] .
      done
    subgoal
      apply simp
      apply (rule evaluate_match_evaluate_list_evaluate.cons2)
      apply (rule mat2)
      by assumption
    done
next
  case (14 st env funs e)
  then show ?case
    by (cases "allDistinct (map (\<lambda>(x, y, z). x) funs)")
       (fastforce intro: evaluate_match_evaluate_list_evaluate.intros elim: evaluate_list_singleton_cases)+
next
  case (18 st env v2 p e pes err_v)
  show ?case
    proof (cases "allDistinct (pat_bindings p [])")
      case True
      show ?thesis
        proof (cases "pmatch (c env) (refs st) p v2 []")
          case No_match
          with True show ?thesis
            apply (simp del: id_apply)
            apply (rule mat_cons2)
            apply (intro conjI)
            apply assumption+
            apply (rule 18)
            apply assumption+
            done
        next
          case Match_type_error
          with True show ?thesis
            apply simp
            apply (rule mat_cons3)
            apply assumption+
            done
        next
          case Match
          with True show ?thesis
            apply (simp del: id_apply)
            apply (rule mat_cons1)
            apply (intro conjI)
            apply assumption+
            using 18(2)
            apply (rule evaluate_list_singleton_cases)
            apply assumption+
            apply (auto simp: error_result.map_ident)
            done
        qed
    next
      case False
      show ?thesis
        using False by (auto intro: mat_cons4)
    qed
qed (fastforce
      intro: evaluate_match_evaluate_list_evaluate.intros
      elim: evaluate_list_singleton_cases
      split: option.splits prod.splits result.splits if_splits exp_or_val.splits)+

global_interpretation "fun": eval
  "\<lambda>env e s. map_prod id (map_result hd id) (fun_evaluate s env [e])"
  "\<lambda>env es s. fun_evaluate s env es"
  "\<lambda>env v pes err_v s. map_prod id (map_result hd id) (fun_evaluate_match s env v pes err_v)"
proof (standard, goal_cases)
  case (1 env s e)
  have "evaluate_list True env s [e] (fun_evaluate s env [e])"
    by (metis fun_evaluate)
  then show ?case
    by (rule evaluate_list_singleton_cases) (auto simp: error_result.map_id)
next
  case (2 env s es)
  show ?case
    by (rule fun_evaluate)
next
  case (3 env s v pes err_v)
  show ?case
    by (rule fun_evaluate)
qed

lemmas big_fun_equivalence =
  fun.other_eval_eq[OF run.eval_axioms]
\<comment> \<open>@{thm [display] big_fun_equivalence}\<close>

end