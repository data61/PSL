section "Totality"

theory Big_Step_Total
imports Semantic_Extras
begin

context begin

private lemma evaluate_list_total0:
  fixes s :: "'a state"
  assumes "\<And>e env s'::'a state. e \<in> set es \<Longrightarrow> clock s' \<le> clock s \<Longrightarrow> \<exists>s'' r. evaluate True env s' e (s'', r)"
  shows "\<exists>s' r. evaluate_list True env s es (s', r)"
using assms proof (induction es arbitrary: env s)
  case Nil
  show ?case by (metis evaluate_match_evaluate_list_evaluate.empty)
next
  case (Cons e es)
  then obtain s' r where e: "evaluate True env s e (s', r)"
    by fastforce
  then have clock: "clock s' \<le> clock s"
    by (metis evaluate_clock_mono)

  show ?case
    proof (cases r)
      case (Rval v)

      have "\<exists>s'' r. evaluate_list True env s' es (s'', r)"
        using Cons clock by auto
      then obtain s'' r where "evaluate_list True env s' es (s'', r)"
        by auto

      with e Rval show ?thesis
        by (cases r)
           (metis evaluate_match_evaluate_list_evaluate.cons1 evaluate_match_evaluate_list_evaluate.cons3)+
    next
      case Rerr
      with e show ?thesis by (metis evaluate_match_evaluate_list_evaluate.cons2)
    qed
qed

private lemma evaluate_match_total0:
  fixes s :: "'a state"
  assumes "\<And>p e env s'::'a state. (p, e) \<in> set pes \<Longrightarrow> clock s' \<le> clock s \<Longrightarrow> \<exists>s'' r. evaluate True env s' e (s'', r)"
  shows "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
using assms proof (induction pes arbitrary: env s)
  case Nil
  show ?case by (metis mat_empty)
next
  case (Cons pe pes)
  then obtain p e where "pe = (p, e)" by force

  show ?case
    proof (cases "allDistinct (pat_bindings p [])")
      case distinct: True
      show ?thesis
        proof (cases "pmatch (c env) (refs s) p v []")
          case No_match

          have "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
            apply (rule Cons)
            apply (rule Cons)
            by auto
          then obtain s' r where "evaluate_match True env s v pes v' (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons2)
            apply safe
            by fact+
        next
          case Match_type_error
          then show ?thesis
            unfolding \<open>pe = _\<close> by (metis mat_cons3)
        next
          case (Match env')

          have "\<exists>s' r. evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            apply (rule Cons)
            unfolding \<open>pe = _\<close> by auto
          then obtain s' r where "evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons1)
            apply safe
            apply fact+
            done
        qed
    next
      case False
      then show ?thesis
        unfolding \<open>pe = _\<close> by (metis mat_cons4)
    qed
qed

lemma evaluate_total: "\<exists>s' r. evaluate True env s e (s', r)"
proof -
  have "wf (less_than <*lex*> measure (size::exp \<Rightarrow> nat))"
    by auto
  then show ?thesis
    proof (induction "(clock s, e)" arbitrary: env s e)
      case less
      show ?case
        proof (cases e)
          case (Raise e')
          then have "\<exists>s' r. evaluate True env s e' (s', r)"
            using less by auto
          then obtain s' r where "evaluate True env s e' (s', r)"
            by auto
          then show ?thesis
            unfolding Raise by (cases r) (metis raise1 raise2)+
        next
          case (Con cn es)
          show ?thesis
            proof (cases "do_con_check (c env) cn (length es)")
              case True
              have "\<exists>s' vs. evaluate_list True env s (rev es) (s', vs)"
                apply (rule evaluate_list_total0)
                apply (rule less)
                unfolding Con
                apply auto
                using Con apply (auto simp: less_eq_Suc_le)
                apply (rule size_list_estimation')
                apply assumption
                by simp
              then obtain r s' where es: "evaluate_list True env s (rev es) (s', r)"
                by auto

              show ?thesis
                proof (cases r)
                  case (Rval vs)
                  moreover obtain v where "build_conv (c env) cn (rev vs) = Some v"
                    using True
                    by (cases cn) (auto split: option.splits)
                  ultimately show ?thesis
                    using True es unfolding Con by (metis con1)
                next
                  case Rerr
                  with True es show ?thesis unfolding Con by (metis con3)
                qed
            next
              case False
              with Con show ?thesis by (metis con2)
            qed
        next
          case (Var n)
          then show ?thesis
            by (cases "nsLookup (sem_env.v env) n") (metis var1 var2)+
        next
          case (App op es)
          have "\<exists>s' vs. evaluate_list True env s (rev es) (s', vs)"
            apply (rule evaluate_list_total0)
            apply (rule less)
            unfolding App apply (auto simp: less_eq_Suc_le)
            apply (rule size_list_estimation')
            apply assumption
            by simp
          then obtain r s2 where es: "evaluate_list True env s (rev es) (s2, r)"
            by auto
          then have clock: "clock s2 \<le> clock s"
            by (metis evaluate_clock_mono)

          show ?thesis
            proof (cases r)
              case (Rval vs)
              show ?thesis
                proof (cases "op = Opapp")
                  case opapp: True
                  show ?thesis
                    proof (cases "do_opapp (rev vs)")
                      case None
                      with App opapp Rval es show ?thesis by (metis app3)
                    next
                      case (Some r)
                      obtain env' e' where "r = (env', e')"
                        by (metis surj_pair)

                      show ?thesis
                        proof (cases "clock s2 = 0")
                          case True
                          show ?thesis
                            unfolding \<open>op = _\<close> App
                            apply (intro exI)
                            apply (rule app2)
                            apply (intro conjI)
                            using es unfolding Rval apply assumption
                            using Some unfolding \<open>r = _\<close> apply assumption
                            apply fact ..
                        next
                          case False

                          have "\<exists>s' r. evaluate True env' (s2 \<lparr> clock := clock s2 - Suc 0 \<rparr>) e' (s', r)"
                            apply (rule less)
                            using False clock by (auto simp: datatype_record_update split: state.splits)
                          then obtain s' r' where "evaluate True env' (s2 \<lparr> clock := clock s2 - Suc 0 \<rparr>) e' (s', r')"
                            by auto

                          show ?thesis
                            unfolding \<open>op = _\<close> App
                            apply (intro exI)
                            apply (rule app1)
                            apply (intro conjI)
                            using es unfolding Rval apply assumption
                            using Some unfolding \<open>r = _\<close> apply assumption
                            using False apply metis
                            apply simp
                            apply fact
                            done
                        qed
                    qed
                next
                  case False
                  show ?thesis
                    proof (cases "do_app ((refs   s2),(ffi   s2)) op (rev vs)")
                      case None
                      show ?thesis
                        unfolding App
                        apply (intro exI)
                        apply (rule app5)
                        apply (intro conjI)
                        using es unfolding Rval apply assumption
                        by fact+
                    next
                      case (Some r)
                      obtain refs' ffi' res where "r = ((refs', ffi'), res)"
                        by (metis surj_pair)

                      show ?thesis
                        unfolding App
                        apply (intro exI)
                        apply (rule app4)
                        apply (intro conjI)
                        using es unfolding Rval apply assumption
                        using Some unfolding \<open>r = _\<close> apply assumption
                        by fact
                    qed
                qed
            next
              case Rerr
              with es App show ?thesis by (metis app6)
            qed
        next
          case (Log op e1 e2)
          with less have "\<exists>s' r. evaluate True env s e1 (s', r)" by simp
          then obtain s' r where e1: "evaluate True env s e1 (s', r)"
            by blast
          then have clock: "clock s' \<le> clock s"
            by (metis evaluate_clock_mono)

          show ?thesis
            proof (cases r)
              case (Rval v)
              with e1 Log show ?thesis
                proof (cases op v e2 rule: do_log_cases)
                  case none
                  then show ?thesis
                    unfolding Log
                    using e1 Rval by (metis log3)
                next
                  case val
                  then show ?thesis
                    unfolding Log
                    using e1 Rval by (metis log2)
                next
                  case exp
                  have "\<exists>s'' r. evaluate True env s' e2 (s'', r)"
                    apply (rule less)
                    using clock Log by auto
                  then obtain s'' r where "evaluate True env s' e2 (s'', r)"
                    by auto
                  show ?thesis
                    unfolding Log
                    apply (intro exI)
                    apply (rule log1)
                    apply (intro conjI)
                    using Rval e1 apply force
                    by fact+
                qed
            next
              case Rerr
              with e1 show ?thesis
                unfolding Log by (metis log4)
            qed
        next
          case (If e1 e2 e3)
          with less have "\<exists>s' r. evaluate True env s e1 (s', r)" by simp
          then obtain s' r where e1: "evaluate True env s e1 (s', r)" by auto
          then have clock: "clock s' \<le> clock s"
            by (metis evaluate_clock_mono)

          show ?thesis
            proof (cases r)
              case (Rval v1)
              show ?thesis
                proof (cases v1 e2 e3 rule: do_if_cases)
                  case none
                  show ?thesis
                    unfolding If
                    apply (intro exI)
                    apply (rule if2)
                    apply (intro conjI)
                    using Rval e1 apply force
                    by fact
                next
                  case true
                  have "\<exists>s'' r. evaluate True env s' e2 (s'', r)"
                    apply (rule less)
                    using clock If by auto
                  then obtain s'' r where "evaluate True env s' e2 (s'', r)"
                    by auto
                  show ?thesis
                    unfolding If
                    apply (intro exI)
                    apply (rule if1)
                    apply (intro conjI)
                    using Rval e1 apply force
                    by fact+
                next
                  case false
                  have "\<exists>s'' r. evaluate True env s' e3 (s'', r)"
                    apply (rule less)
                    using clock If by auto
                  then obtain s'' r where "evaluate True env s' e3 (s'', r)"
                    by auto
                  show ?thesis
                    unfolding If
                    apply (intro exI)
                    apply (rule if1)
                    apply (intro conjI)
                    using Rval e1 apply force
                    by fact+
                qed
            next
              case Rerr
              with e1 show ?thesis unfolding If by (metis if3)
            qed
        next
          case (Handle e' pes)
          with less have "\<exists>s' r. evaluate True env s e' (s', r)" by simp
          then obtain s' r where e': "evaluate True env s e' (s', r)" by auto
          then have clock: "clock s' \<le> clock s"
            by (metis evaluate_clock_mono)

          show ?thesis
            proof (cases r)
              case Rval
              with e' show ?thesis
                unfolding Handle by (metis handle1)
            next
              case (Rerr err)
              show ?thesis
                proof (cases err)
                  case (Rraise exn)

                  have "\<exists>s'' r. evaluate_match True env s' exn pes exn (s'', r)"
                    apply (rule evaluate_match_total0)
                    apply (rule less)
                    using Handle clock apply (auto simp: less_eq_Suc_le)
                    apply (rule trans_le_add1)
                    apply (rule size_list_estimation')
                    apply assumption
                    by auto
                  then obtain s'' r where "evaluate_match True env s' exn pes exn (s'', r)"
                    by auto

                  show ?thesis
                    unfolding Handle
                    apply (intro exI)
                    apply (rule handle2)
                    apply safe
                    using e' unfolding Rerr Rraise apply assumption
                    by fact
                next
                  case (Rabort x2)
                  with e' Rerr show ?thesis
                    unfolding Handle
                    by (metis handle3)
                qed
            qed
        next
          case (Mat e' pes)
          with less have "\<exists>s' r. evaluate True env s e' (s', r)" by simp
          then obtain s' r where e': "evaluate True env s e' (s', r)" by auto
          then have clock: "clock s' \<le> clock s"
            by (metis evaluate_clock_mono)

          show ?thesis
            proof (cases r)
              case (Rval v)

              have "\<exists>s'' r. evaluate_match True env s' v pes (Conv (Some (''Bind'', TypeExn (Short ''Bind''))) []) (s'', r)"
                apply (rule evaluate_match_total0)
                apply (rule less)
                unfolding Mat using clock apply (auto simp: less_eq_Suc_le)
                apply (rule trans_le_add1)
                apply (rule size_list_estimation')
                apply assumption
                by auto
              then obtain s'' r where "evaluate_match True env s' v pes (Conv (Some (''Bind'', TypeExn (Short ''Bind''))) []) (s'', r)"
                by auto

              show ?thesis
                unfolding Mat
                apply (intro exI)
                apply (rule mat1)
                apply safe
                using e' unfolding Rval
                apply assumption
                apply fact
                done
            next
              case Rerr
              with e' show ?thesis
                unfolding Mat
                by (metis mat2)
            qed
        next
          case (Let n e1 e2)
          then have "\<exists>s' r. evaluate True env s e1 (s', r)"
            using less by auto
          then obtain s' r where e1: "evaluate True env s e1 (s', r)"
            by auto
          then have clock: "clock s' \<le> clock s"
            by (metis evaluate_clock_mono)
          show ?thesis
            proof (cases r)
              case (Rval v)
              have "\<exists>s'' r. evaluate True (env \<lparr> sem_env.v := nsOptBind n v (sem_env.v env) \<rparr>) s' e2 (s'', r)"
                apply (rule less)
                using Let clock by auto
              then show ?thesis
                unfolding Let
                using e1 Rval by (metis let1)
            next
              case Rerr
              with e1 show ?thesis
                unfolding Let
                by (metis let2)
            qed
        next
          case (Letrec funs e')
          then have "\<exists>s' r. evaluate True (env \<lparr> sem_env.v := build_rec_env funs env (sem_env.v env) \<rparr>) s e' (s', r)"
            using less by auto
          then show ?thesis
            unfolding Letrec
            by (cases "allDistinct (map (\<lambda>x. case x of (x, y, z) \<Rightarrow> x) funs)")
               (metis letrec1 letrec2)+
        next
          case (Tannot e')
          with less have "\<exists>s' r. evaluate True env s e' (s', r)" by simp
          then show ?thesis
            unfolding \<open>e = _\<close>
            by (fastforce intro: evaluate_match_evaluate_list_evaluate.intros)
        next
          case (Lannot e')
          with less have "\<exists>s' r. evaluate True env s e' (s', r)" by simp
          then show ?thesis
            unfolding \<open>e = _\<close>
            by (fastforce intro: evaluate_match_evaluate_list_evaluate.intros)
        qed (fastforce intro: evaluate_match_evaluate_list_evaluate.intros)+
    qed
qed

end

text \<open>
  The following are pretty much the same proofs as above, but without additional assumptions;
  instead using @{thm [source=true] evaluate_total} directly.
\<close>

lemma evaluate_list_total: "\<exists>s' r. evaluate_list True env s es (s', r)"
proof (induction es arbitrary: env s)
  case Nil
  show ?case by (metis evaluate_match_evaluate_list_evaluate.empty)
next
  case (Cons e es)
  obtain s' r where e: "evaluate True env s e (s', r)"
    by (metis evaluate_total)
  show ?case
    proof (cases r)
      case (Rval v)
      have "\<exists>s'' r. evaluate_list True env s' es (s'', r)"
        using Cons by auto
      then obtain s'' r where "evaluate_list True env s' es (s'', r)"
        by auto

      with e Rval show ?thesis
        by (cases r)
           (metis evaluate_match_evaluate_list_evaluate.cons1 evaluate_match_evaluate_list_evaluate.cons3)+
    next
      case Rerr
      with e show ?thesis
        by (metis evaluate_match_evaluate_list_evaluate.cons2)
    qed
qed

lemma evaluate_match_total: "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
proof (induction pes arbitrary: env s)
  case Nil
  show ?case by (metis mat_empty)
next
  case (Cons pe pes)
  then obtain p e where "pe = (p, e)" by force

  show ?case
    proof (cases "allDistinct (pat_bindings p [])")
      case distinct: True
      show ?thesis
        proof (cases "pmatch (c env) (refs s) p v []")
          case No_match

          have "\<exists>s' r. evaluate_match True env s v pes v' (s', r)"
            by (rule Cons)
          then obtain s' r where "evaluate_match True env s v pes v' (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons2)
            apply safe
            by fact+
        next
          case Match_type_error
          then show ?thesis
            unfolding \<open>pe = _\<close> by (metis mat_cons3)
        next
          case (Match env')

          have "\<exists>s' r. evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            by (metis evaluate_total)
          then obtain s' r where "evaluate True (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>) s e (s', r)"
            by auto

          show ?thesis
            unfolding \<open>pe = _\<close>
            apply (intro exI)
            apply (rule mat_cons1)
            apply safe
            apply fact+
            done
        qed
    next
      case False
      then show ?thesis
        unfolding \<open>pe = _\<close> by (metis mat_cons4)
    qed
qed

end