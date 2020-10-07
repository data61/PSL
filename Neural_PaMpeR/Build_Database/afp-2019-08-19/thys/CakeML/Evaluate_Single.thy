section "Simplifiying the definition: no mutual recursion"

theory Evaluate_Single
imports Evaluate_Clock
begin

fun evaluate_list ::
  "('ffi state \<Rightarrow> exp \<Rightarrow> 'ffi state*(v, v) result) \<Rightarrow>
    'ffi state \<Rightarrow> exp list \<Rightarrow> 'ffi state*(v list, v) result" where

Nil:
"evaluate_list eval s [] = (s, Rval [])" |

Cons:
"evaluate_list eval s (e#es) =
  (case fix_clock s (eval s e) of
    (s', Rval v) \<Rightarrow>
      (case evaluate_list eval s' es of
        (s'', Rval vs) \<Rightarrow> (s'', Rval (v#vs))
      | res \<Rightarrow> res)
  |  (s', Rerr err) \<Rightarrow> (s', Rerr err))"

lemma evaluate_list_cong[fundef_cong]:
  assumes "\<And>e s. e \<in> set es1 \<Longrightarrow> clock s \<le> clock s1 \<Longrightarrow> eval1 s e = eval2 s e" "s1 = s2" "es1 = es2"
  shows "evaluate_list eval1 s1 es1 = evaluate_list eval2 s2 es2"
using assms by (induction es1 arbitrary: es2 s1 s2) (fastforce simp: fix_clock_alt_def split: prod.splits result.splits)+

function (sequential)
evaluate :: " v sem_env \<Rightarrow>'ffi state \<Rightarrow> exp \<Rightarrow> 'ffi state*(v,v) result" where

Lit:
"evaluate env s (Lit l) = (s, Rval (Litv l))" |

Raise:
"evaluate env s (Raise e) =
  (case evaluate env s e of
    (s', Rval v) \<Rightarrow> (s', Rerr (Rraise (v)))
  | res \<Rightarrow> res)" |

Handle:
"evaluate env s (Handle e pes) =
  (case evaluate env s e of
    (s', Rerr (Rraise v)) \<Rightarrow>
      (case match_result env s' v pes v of
        (Rval (e', env')) \<Rightarrow>
          evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s' e'
      | (Rerr err) \<Rightarrow> (s', Rerr err))
  | res \<Rightarrow> res)" |

Con:
"evaluate env s (Con cn es) =
  (if do_con_check (c env) cn (length es) then
    (case evaluate_list (evaluate env) s (rev es) of
      (s', Rval vs) \<Rightarrow>
        (case build_conv (c env) cn (rev vs) of
          Some v \<Rightarrow> (s', Rval v)
        | None \<Rightarrow> (s', Rerr (Rabort Rtype_error)))
    | (s', Rerr err) \<Rightarrow> (s', Rerr err))
  else (s, Rerr (Rabort Rtype_error)))" |

Var:
"evaluate env s (Var n) =
  (case nsLookup (sem_env.v env) n of
    Some v \<Rightarrow> (s, Rval v)
  | None \<Rightarrow> (s, Rerr (Rabort Rtype_error)))" |

Fun:
"evaluate env s (Fun n e) = (s, Rval (Closure env n e))" |

App:
"evaluate env s (App op0 es) =
  (case evaluate_list (evaluate env) s (rev es) of
    (s', Rval vs) \<Rightarrow>
      (if op0 = Opapp then
        (case do_opapp (rev vs) of
          Some (env', e) \<Rightarrow>
            (if (clock s' = 0) then
              (s', Rerr (Rabort Rtimeout_error))
            else
              evaluate env' (dec_clock s') e)
        | None \<Rightarrow> (s', Rerr (Rabort Rtype_error)))
      else
        (case do_app (refs s', ffi s') op0 (rev vs) of
          Some ((refs',ffi'), res) \<Rightarrow> (s' \<lparr>refs:=refs',ffi:=ffi'\<rparr>, res)
        | None \<Rightarrow> (s', Rerr (Rabort Rtype_error))))
  | (s', Rerr err) \<Rightarrow> (s', Rerr err))" |

Log:
"evaluate env s (Log op0 e1 e2) =
  (case evaluate env s e1 of
    (s', Rval v) \<Rightarrow>
      (case do_log op0 v e2 of
        Some (Exp e') \<Rightarrow> evaluate env s' e'
      | Some (Val bv) \<Rightarrow> (s', Rval bv)
      | None \<Rightarrow> (s', Rerr (Rabort Rtype_error)))
  | res \<Rightarrow> res)" |

If:
"evaluate env s (If e1 e2 e3) =
  (case evaluate env s e1 of
    (s', Rval v) \<Rightarrow>
      (case do_if v e2 e3 of
        Some e' \<Rightarrow> evaluate env s' e'
      | None \<Rightarrow> (s', Rerr (Rabort Rtype_error)))
  | res \<Rightarrow> res)" |

Mat:
"evaluate env s (Mat e pes) =
  (case evaluate env s e of
    (s', Rval v) \<Rightarrow>
      (case match_result env s' v pes Bindv of
        Rval (e', env') \<Rightarrow>
          evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s' e'
      | Rerr err \<Rightarrow> (s', Rerr err))
  | res \<Rightarrow> res)" |

Let:
"evaluate env s (Let n e1 e2) =
  (case evaluate env s e1 of
    (s', Rval v) \<Rightarrow>
      evaluate ( env \<lparr> sem_env.v := (nsOptBind n v(sem_env.v env)) \<rparr>) s' e2
  | res \<Rightarrow> res)" |

Letrec:
"evaluate env s (Letrec funs e) =
  (if distinct (List.map (\<lambda>x. (case  x of (x,y,z) => x )) funs) then
    evaluate ( env \<lparr> sem_env.v := (build_rec_env funs env(sem_env.v env)) \<rparr>) s e
  else
    (s, Rerr (Rabort Rtype_error)))" |

Tannot:
"evaluate env s (Tannot e t0) = evaluate env s e" |

Lannot:
"evaluate env s (Lannot e l) = evaluate env s e"
  by pat_completeness auto

context
  notes do_app.simps[simp del]
begin

lemma match_result_elem:
  assumes "match_result env s v0 pes err_v = Rval (e, env')"
  shows "\<exists>pat. (pat, e) \<in> set pes"
  using assms proof (induction pes)
  case Nil
  then show ?case by auto
next
  case (Cons pe pes)
  then obtain p e where "pe = (p, e)" by force
  show ?case
    using Cons(2)
    apply (simp add:match_result_alt_def)
    unfolding \<open>pe = _\<close>
    apply (cases "allDistinct (pat_bindings p [])")
    apply (cases "pmatch (c env) (refs s) p v0 []")
    using Cons(1) by auto+
qed

private lemma evaluate_list_clock_monotone: "clock (fst (evaluate_list eval s es)) \<le> clock s"
  apply (induction es arbitrary: s)
  apply (auto split:prod.splits result.splits simp add:fix_clock_alt_def dest!:fstI intro:le_trans)
  apply (metis state.record_simps(1))+
  done

private lemma evaluate_clock_monotone:
  assumes "evaluate_dom (env, s, e)"
  shows "clock (fst (evaluate env s e)) \<le> clock s"
using assms
by induction
   (fastforce simp add:evaluate.psimps do_con_check_build_conv evaluate_list_clock_monotone
              split:prod.splits result.splits option.splits exp_or_val.splits error_result.splits
              dest:fstI intro:i_hate_words_helper[THEN le_trans])+

private definition fun_evaluate_single_relation where
"fun_evaluate_single_relation = inv_image (less_than <*lex*> less_than) (\<lambda>x.
  case x of (_, s, e) \<Rightarrow> (clock s, size_exp' e))"

private lemma pat_elem_less_size:
  "(pat, e) \<in> set pes \<Longrightarrow> size_exp' e < (size_list (size_prod size size_exp') pes)"
by (induction pes) auto

private lemma elem_less_size: "e \<in> set es \<Longrightarrow> size_exp' e \<le> size_list size_exp' es"
by (induction es) auto

lemma evaluate_total: "All evaluate_dom"
proof (relation "fun_evaluate_single_relation", unfold fun_evaluate_single_relation_def, goal_cases)
  case 7
  then show ?case
    using evaluate_list_clock_monotone "7"(1)[symmetric]
    by (auto dest!: fstI simp add:evaluate_list_clock_monotone Suc_le_lessD)
qed (auto simp add: less_Suc_eq_le Suc_le_lessD do_if_def do_log_alt_def evaluate_list_clock_monotone elem_less_size
          split:lop.splits v.splits option.splits tid_or_exn.splits if_splits id0.splits list.splits
          dest!:evaluate_clock_monotone match_result_elem fstI dest:sym pat_elem_less_size intro:le_neq_implies_less)

termination evaluate by (rule evaluate_total)

lemma evaluate_clock_monotone': "evaluate eval s e = (s', r) \<Longrightarrow>  clock s' \<le> clock s"
  using fst_conv evaluate_clock_monotone evaluate_total
  by metis

fun evaluate_list' :: "v sem_env \<Rightarrow> 'ffi state \<Rightarrow> exp list \<Rightarrow> 'ffi state*(v list, v) result" where
"evaluate_list' env s [] = (s, Rval [])" |
"evaluate_list' env s (e#es) =
  (case evaluate env s e of
    (s', Rval v) \<Rightarrow>
      (case evaluate_list' env s' es of
        (s'', Rval vs) \<Rightarrow> (s'', Rval (v#vs))
      | res \<Rightarrow> res)
  |  (s', Rerr err) \<Rightarrow> (s', Rerr err))"

lemma fix_clock_evaluate[simp]: "fix_clock s (evaluate eval s e) = evaluate eval s e"
  unfolding fix_clock_alt_def
  apply (auto simp: datatype_record_update split: state.splits prod.splits)
  using evaluate_clock_monotone' by fastforce

lemma evaluate_list_eq[simp]: "evaluate_list (evaluate env) = evaluate_list' env"
  apply (rule ext)+
  subgoal for s es
    by (induction rule:evaluate_list'.induct) (auto split:prod.splits result.splits)
  done

declare evaluate_list.simps[simp del]

lemma fun_evaluate_equiv:
  "fun_evaluate_match s env v pes err_v = (case match_result env s v pes err_v of
      Rerr err \<Rightarrow> (s, Rerr err)
    | Rval (e, env') \<Rightarrow> evaluate_list (evaluate (env \<lparr> sem_env.v := (nsAppend (alist_to_ns env') (sem_env.v env)) \<rparr>)) s [e])"
  "fun_evaluate s env es = evaluate_list (evaluate env) s es"
  by (induction rule: fun_evaluate_induct)
     (auto split: prod.splits result.splits match_result.splits option.splits exp_or_val.splits
                  if_splits match_result.splits error_result.splits
           simp: all_distinct_alt_def)

corollary fun_evaluate_equiv':
  "evaluate env s e = map_prod id (map_result hd id) (fun_evaluate s env [e])"
by (subst fun_evaluate_equiv) (simp split: prod.splits result.splits add: error_result.map_id)

end

end