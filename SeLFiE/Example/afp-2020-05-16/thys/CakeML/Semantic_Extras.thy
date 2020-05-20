chapter "Adaptations for Isabelle"

theory Semantic_Extras
imports
  "generated/CakeML/BigStep"
  "generated/CakeML/SemanticPrimitivesAuxiliary"
  "generated/CakeML/AstAuxiliary"
  "generated/CakeML/Evaluate"
  "HOL-Library.Simps_Case_Conv"
begin

type_synonym exp = exp0

hide_const (open) sem_env.v

code_pred
  (modes: evaluate: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as compute
      and evaluate_list: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool
      and evaluate_match: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate .

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate_dec .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate_decs .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate_top .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as compute_prog) evaluate_prog .

termination pmatch_list by lexicographic_order
termination do_eq_list by lexicographic_order

lemma all_distinct_alt_def: "allDistinct = distinct"
proof
  fix xs :: "'a list"
  show "allDistinct xs = distinct xs"
    by (induct xs) auto
qed

lemma find_recfun_someD:
  assumes "find_recfun n funs = Some (x, e)"
  shows "(n, x, e) \<in> set funs"
using assms
by (induct funs) (auto split: if_splits)

lemma find_recfun_alt_def[simp]: "find_recfun n funs = map_of funs n"
by (induction funs) auto

lemma size_list_rev[simp]: "size_list f (rev xs) = size_list f xs"
by (auto simp: size_list_conv_sum_list rev_map[symmetric])

lemma do_if_cases:
  obtains
    (none) "do_if v e1 e2 = None"
  | (true) "do_if v e1 e2 = Some e1"
  | (false) "do_if v e1 e2 = Some e2"
unfolding do_if_def
by meson

case_of_simps do_log_alt_def: do_log.simps
case_of_simps do_con_check_alt_def: do_con_check.simps
case_of_simps list_result_alt_def: list_result.simps

context begin

private fun_cases do_logE: "do_log op v e = res"

lemma do_log_exp: "do_log op v e = Some (Exp e') \<Longrightarrow> e = e'"
by (erule do_logE)
   (auto split: v.splits option.splits if_splits tid_or_exn.splits id0.splits list.splits)

end

lemma c_of_merge[simp]: "c (extend_dec_env env2 env1) = nsAppend (c env2) (c env1)"
by (cases env1; cases env2; simp add: extend_dec_env_def)

lemma v_of_merge[simp]: "sem_env.v (extend_dec_env env2 env1) = nsAppend (sem_env.v env2) (sem_env.v env1)"
by (cases env1; cases env2; simp add: extend_dec_env_def)

lemma nsEmpty_nsAppend[simp]: "nsAppend e nsEmpty = e" "nsAppend nsEmpty e = e"
by (cases e; auto simp: nsEmpty_def)+

lemma do_log_cases:
  obtains
    (none) "do_log op v e = None"
  | (val) v' where "do_log op v e = Some (Val v')"
  | (exp) "do_log op v e = Some (Exp e)"
proof (cases "do_log op v e")
  case None
  then show ?thesis using none by metis
next
  case (Some res)
  with val exp show ?thesis
    by (cases res) (metis do_log_exp)+
qed

context begin

private fun_cases do_opappE: "do_opapp vs = Some res"

lemma do_opapp_cases:
  assumes "do_opapp vs = Some (env', exp')"
  obtains (closure) env n v0
            where "vs = [Closure env n exp', v0]"
                  "env' = (env \<lparr> sem_env.v := nsBind n v0 (sem_env.v env) \<rparr> )"
        | (recclosure) env funs name n v0
            where "vs = [Recclosure env funs name, v0]"
              and "allDistinct (map (\<lambda>(f, _, _). f) funs)"
              and "find_recfun name funs = Some (n, exp')"
              and "env' = (env \<lparr> sem_env.v := nsBind n v0 (build_rec_env funs env (sem_env.v env)) \<rparr> )"
proof -
  show thesis
    using assms
    apply (rule do_opappE)
    apply (rule closure; auto)
    apply (auto split: if_splits option.splits)
    apply (rule recclosure)
    apply auto
    done
qed

end

lemmas evaluate_induct =
  evaluate_match_evaluate_list_evaluate.inducts[split_format(complete)]

lemma evaluate_clock_mono:
  "evaluate_match ck env s v pes v' (s', r1) \<Longrightarrow> clock s' \<le> clock s"
  "evaluate_list ck env s es (s', r2) \<Longrightarrow> clock s' \<le> clock s"
  "evaluate ck env s e (s', r3) \<Longrightarrow> clock s' \<le> clock s"
 by (induction rule: evaluate_induct)
    (auto simp del: do_app.simps simp: datatype_record_update split: state.splits if_splits)

lemma evaluate_list_singleton_valE:
  assumes "evaluate_list ck env s [e] (s', Rval vs)"
  obtains v where "vs = [v]" "evaluate ck env s e (s', Rval v)"
using assms
by (auto elim: evaluate_list.cases)

lemma evaluate_list_singleton_errD:
  assumes "evaluate_list ck env s [e] (s', Rerr err)"
  shows "evaluate ck env s e (s', Rerr err)"
using assms
by (auto elim: evaluate_list.cases)

lemma evaluate_list_singleton_cases:
  assumes "evaluate_list ck env s [e] res"
  obtains (val) s' v where "res = (s', Rval [v])" "evaluate ck env s e (s', Rval v)"
        | (err) s' err where "res = (s', Rerr err)" "evaluate ck env s e (s', Rerr err)"
using assms
apply -
apply (ind_cases "evaluate_list ck env s [e] res")
apply auto
apply (ind_cases "evaluate_list ck env s2 [] (s3, Rval vs)" for s2 s3 vs)
apply auto
apply (ind_cases " evaluate_list ck env s2 [] (s3, Rerr err) " for s2 s3 err)
done

lemma evaluate_list_singletonI:
  assumes "evaluate ck env s e (s', r)"
  shows "evaluate_list ck env s [e] (s', list_result r)"
using assms
by (cases r) (auto intro: evaluate_match_evaluate_list_evaluate.intros)

lemma prod_result_cases:
  obtains (val) s v where "r = (s, Rval v)"
        | (err) s err where "r = (s, Rerr err)"
apply (cases r)
subgoal for _ b
  apply (cases b)
  by auto
done

lemma do_con_check_build_conv: "do_con_check (c env) cn (length es) \<Longrightarrow> build_conv (c env) cn vs \<noteq> None"
by (cases cn) (auto split: option.splits)

fun match_result :: "(v)sem_env \<Rightarrow> 'ffi state \<Rightarrow> v \<Rightarrow>(pat*exp)list \<Rightarrow> v \<Rightarrow> (exp \<times> (char list \<times> v) list, v)result" where
"match_result _ _ _ [] err_v = Rerr (Rraise err_v)" |
"match_result env s v0 ((p, e) # pes) err_v =
  (if Lem_list.allDistinct (pat_bindings p []) then
    (case pmatch (sem_env.c env) (refs s) p v0 [] of
      Match env' \<Rightarrow> Rval (e, env') |
      No_match \<Rightarrow> match_result env s v0 pes err_v |
      Match_type_error \<Rightarrow> Rerr (Rabort Rtype_error))
   else
      Rerr (Rabort Rtype_error))"

case_of_simps match_result_alt_def: match_result.simps

lemma match_result_sound:
  "case match_result env s v0 pes err_v of
    Rerr err \<Rightarrow> evaluate_match ck env s v0 pes err_v (s, Rerr err)
  | Rval (e, env') \<Rightarrow>
      \<forall>bv.
        evaluate ck (env \<lparr> sem_env.v := nsAppend (alist_to_ns env')(sem_env.v env) \<rparr>) s e bv \<longrightarrow>
             evaluate_match ck env s v0 pes err_v bv"
by (induction rule: match_result.induct)
   (auto intro: evaluate_match_evaluate_list_evaluate.intros split: match_result.splits result.splits)

lemma match_result_sound_val:
  assumes "match_result env s v0 pes err_v = Rval (e, env')"
  assumes "evaluate ck (env \<lparr> sem_env.v := nsAppend (alist_to_ns env')(sem_env.v env) \<rparr>) s e bv"
  shows "evaluate_match ck env s v0 pes err_v bv"
proof -
  note match_result_sound[where env = env and s = s and ?v0.0 = v0 and pes = pes and err_v = err_v, unfolded assms result.case prod.case]
  with assms show ?thesis by blast
qed

lemma match_result_sound_err:
  assumes "match_result env s v0 pes err_v = Rerr err"
  shows "evaluate_match ck env s v0 pes err_v (s, Rerr err)"
proof -
  note match_result_sound[where env = env and s = s and ?v0.0 = v0 and pes = pes and err_v = err_v, unfolded assms result.case prod.case]
  then show ?thesis by blast
qed

lemma match_result_correct:
  assumes "evaluate_match ck env s v0 pes err_v (s', bv)"
  shows "case bv of
          Rval v \<Rightarrow>
            \<exists>e env'. match_result env s v0 pes err_v = Rval (e, env') \<and> evaluate ck (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s e (s', Rval v)
        | Rerr err \<Rightarrow>
            (match_result env s v0 pes err_v = Rerr err) \<or>
            (\<exists>e env'. match_result env s v0 pes err_v = Rval (e, env') \<and> evaluate ck (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s e (s', Rerr err))"
using assms
proof (induction pes)
  case (Cons pe pes)
  from Cons.prems show ?case
    proof cases
      case (mat_cons1 env' p e)
      then show ?thesis
        by (cases bv) auto
    next
      case (mat_cons2 p e)
      then show ?thesis
        using Cons.IH
        by (cases bv) auto
    qed auto
qed (auto elim: evaluate_match.cases)

end