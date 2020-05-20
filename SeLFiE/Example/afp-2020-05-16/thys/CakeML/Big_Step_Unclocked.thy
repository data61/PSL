section "A simpler version with no clock parameter and factored-out matching"

theory Big_Step_Unclocked
imports
  Semantic_Extras
  Big_Step_Determ
begin

inductive

evaluate_list  :: " (v)sem_env \<Rightarrow> 'ffi state \<Rightarrow>(exp)list \<Rightarrow> 'ffi state*(((v)list),(v))result \<Rightarrow> bool "
      and
evaluate  :: " (v)sem_env \<Rightarrow> 'ffi state \<Rightarrow> exp \<Rightarrow> 'ffi state*((v),(v))result \<Rightarrow> bool "  where

"lit" : " \<And> env l s.

evaluate env s (Lit l) (s, Rval (Litv l))"

|

"raise1" : " \<And> env e s1 s2 v1.
evaluate s1 env e (s2, Rval v1)
==>
evaluate s1 env (Raise e) (s2, Rerr (Rraise v1))"

|

"raise2" : " \<And> env e s1 s2 err.
evaluate s1 env e (s2, Rerr err)
==>
evaluate s1 env (Raise e) (s2, Rerr err)"

|

"handle1" : " \<And> s1 s2 env e v1 pes.
evaluate s1 env e (s2, Rval v1)
==>
evaluate s1 env (Handle e pes) (s2, Rval v1)"

|

"handle2" : " \<And> s1 s2 env e pes v1 bv.
evaluate env s1 e (s2, Rerr (Rraise v1)) \<Longrightarrow>
match_result env s2 v1 pes v1 = Rval (e', env') \<Longrightarrow>
evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e' bv
==>
evaluate env s1 (Handle e pes) bv "

|

"handle2b" : " \<And> s1 s2 env e pes v1.
evaluate env s1 e (s2, Rerr (Rraise v1)) \<Longrightarrow>
match_result env s2 v1 pes v1 = Rerr err
==>
evaluate env s1 (Handle e pes) (s2, Rerr err)"

|

"handle3" : " \<And> s1 s2 env e pes a.
evaluate env s1 e (s2, Rerr (Rabort a))
==>
evaluate env s1 (Handle e pes) (s2, Rerr (Rabort a))"

|

"con1" : " \<And> env cn es vs s s' v1.
do_con_check(c   env) cn (List.length es) \<Longrightarrow>
build_conv(c   env) cn (List.rev vs) = Some v1 \<Longrightarrow>
evaluate_list env s (List.rev es) (s', Rval vs)
==>
evaluate env s (Con cn es) (s', Rval v1)"

|

"con2" : " \<And> env cn es s.
\<not> (do_con_check(c   env) cn (List.length es))
==>
evaluate env s (Con cn es) (s, Rerr (Rabort Rtype_error))"

|

"con3" : " \<And> env cn es err s s'.
do_con_check(c   env) cn (List.length es) \<Longrightarrow>
evaluate_list env s (List.rev es) (s', Rerr err)
==>
evaluate env s (Con cn es) (s', Rerr err)"

|

"var1" : " \<And> env n v1 s.
nsLookup(sem_env.v   env) n = Some v1
==>
evaluate env s (Var n) (s, Rval v1)"

|

"var2" : " \<And> env n s.
nsLookup(sem_env.v   env) n = None
==>
evaluate env s (Var n) (s, Rerr (Rabort Rtype_error))"

|

"fn" : " \<And> env n e s.

evaluate env s (Fun n e) (s, Rval (Closure env n e))"

|

"app1" : " \<And> env es vs env' e bv s1 s2.
evaluate_list env s1 (List.rev es) (s2, Rval vs) \<Longrightarrow>
do_opapp (List.rev vs) = Some (env', e) \<Longrightarrow>
evaluate env' s2 e bv
==>
evaluate env s1 (App Opapp es) bv "

|

"app3" : " \<And> env es vs s1 s2.
evaluate_list env s1 (List.rev es) (s2, Rval vs) \<Longrightarrow>
(do_opapp (List.rev vs) = None)
==>
evaluate env s1 (App Opapp es) (s2, Rerr (Rabort Rtype_error))"

|

"app4" : " \<And> env op0 es vs res s1 s2 refs' ffi'.
evaluate_list env s1 (List.rev es) (s2, Rval vs) \<Longrightarrow>
do_app ((refs   s2),(ffi   s2)) op0 (List.rev vs) = Some ((refs',ffi'), res) \<Longrightarrow>
op0 \<noteq> Opapp
==>
evaluate env s1 (App op0 es) (( s2 (| refs := refs', ffi :=ffi' |)), res)"

|

"app5" : " \<And> env op0 es vs s1 s2.
evaluate_list env s1 (List.rev es) (s2, Rval vs) \<Longrightarrow>
do_app ((refs   s2),(ffi   s2)) op0 (List.rev vs) = None \<Longrightarrow>
op0 \<noteq> Opapp
==>
evaluate env s1 (App op0 es) (s2, Rerr (Rabort Rtype_error))"

|

"app6" : " \<And> env op0 es err s1 s2.
evaluate_list env s1 (List.rev es) (s2, Rerr err)
==>
evaluate env s1 (App op0 es) (s2, Rerr err)"

|

"log1" : " \<And> env op0 e1 e2 v1 e' bv s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
do_log op0 v1 e2 = Some (Exp e') \<Longrightarrow>
evaluate env s2 e' bv
==>
evaluate env s1 (Log op0 e1 e2) bv "

|

"log2" : " \<And> env op0 e1 e2 v1 bv s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
(do_log op0 v1 e2 = Some (Val bv))
==>
evaluate env s1 (Log op0 e1 e2) (s2, Rval bv)"

|

"log3" : " \<And> env op0 e1 e2 v1 s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
(do_log op0 v1 e2 = None)
==>
evaluate env s1 (Log op0 e1 e2) (s2, Rerr (Rabort Rtype_error))"

|

"log4" : " \<And> env op0 e1 e2 err s s'.
evaluate env s e1 (s', Rerr err)
==>
evaluate env s (Log op0 e1 e2) (s', Rerr err)"

|

"if1" : " \<And> env e1 e2 e3 v1 e' bv s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
do_if v1 e2 e3 = Some e' \<Longrightarrow>
evaluate env s2 e' bv
==>
evaluate env s1 (If e1 e2 e3) bv "

|

"if2" : " \<And> env e1 e2 e3 v1 s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
(do_if v1 e2 e3 = None)
==>
evaluate env s1 (If e1 e2 e3) (s2, Rerr (Rabort Rtype_error))"

|

"if3" : " \<And> env e1 e2 e3 err s s'.
evaluate env s e1 (s', Rerr err)
==>
evaluate env s (If e1 e2 e3) (s', Rerr err)"

|

"mat1" : " \<And> env e pes v1 bv s1 s2.
evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
match_result env s2 v1 pes Bindv = Rval (e', env') \<Longrightarrow>
evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e' bv
==>
evaluate env s1 (Mat e pes) bv "

|

"mat1b" : " \<And> env e pes v1 s1 s2.
evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
match_result env s2 v1 pes Bindv = Rerr err
==>
evaluate env s1 (Mat e pes) (s2, Rerr err)"

|

"mat2" : " \<And> env e pes err s s'.
evaluate env s e (s', Rerr err)
==>
evaluate env s (Mat e pes) (s', Rerr err)"

|

"let1" : " \<And> env n e1 e2 v1 bv s1 s2.
evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
evaluate ( env (| sem_env.v := (nsOptBind n v1(sem_env.v   env)) |)) s2 e2 bv
==>
evaluate env s1 (Let n e1 e2) bv "

|

"let2" : " \<And> env n e1 e2 err s s'.
evaluate env s e1 (s', Rerr err)
==>
evaluate env s (Let n e1 e2) (s', Rerr err)"

|

"letrec1" : " \<And> env funs e bv s.
distinct (List.map ( \<lambda>x .
  (case  x of (x,y,z) => x )) funs) \<Longrightarrow>
evaluate ( env (| sem_env.v := (build_rec_env funs env(sem_env.v   env)) |)) s e bv
==>
evaluate env s (Letrec funs e) bv "

|

"letrec2" : " \<And> env funs e s.
\<not> (distinct (List.map ( \<lambda>x .
  (case  x of (x,y,z) => x )) funs))
==>
evaluate env s (Letrec funs e) (s, Rerr (Rabort Rtype_error))"

|

"tannot" : " \<And> env e t0 s bv.
evaluate env s e bv
==>
evaluate env s (Tannot e t0) bv "

|

"locannot" : " \<And> env e l s bv.
evaluate env s e bv
==>
evaluate env s (Lannot e l) bv "

|

"empty" : " \<And> env s.

evaluate_list env s [] (s, Rval [])"

|

"cons1" : " \<And> env e es v1 vs s1 s2 s3.
evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
evaluate_list env s2 es (s3, Rval vs)
==>
evaluate_list env s1 (e # es) (s3, Rval (v1 # vs))"

|

"cons2" : " \<And> env e es err s s'.
evaluate env s e (s', Rerr err)
==>
evaluate_list env s (e # es) (s', Rerr err)"

|

"cons3" : " \<And> env e es v1 err s1 s2 s3.
evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
evaluate_list env s2 es (s3, Rerr err)
==>
evaluate_list env s1 (e # es) (s3, Rerr err)"

lemma unclocked_sound:
  "evaluate_list v s es bv \<Longrightarrow> BigStep.evaluate_list False v s es bv"
  "evaluate v s e bv' \<Longrightarrow> BigStep.evaluate False v s e bv'"
proof (induction rule: evaluate_list_evaluate.inducts)
  case (handle2 e' env' s1 s2 env e pes v1 bv)
  show ?case
    apply (rule BigStep.handle2, intro conjI)
    apply fact
    apply (rule match_result_sound_val)
    apply fact+
    done
next
  case (handle2b err s1 s2 env e pes v1)
  show ?case
    apply (rule BigStep.handle2, intro conjI)
    apply fact
    apply (rule match_result_sound_err)
    apply fact
    done
next
  case (mat1 e' env' env e pes v1 bv s1 s2)
  show ?case
    apply (rule BigStep.mat1, fold Bindv_def, intro conjI)
    apply fact
    apply (rule match_result_sound_val)
    apply fact+
    done
next
  case (mat1b err env e pes v1 s1 s2)
  show ?case
    apply (rule BigStep.mat1, fold Bindv_def, intro conjI)
    apply fact
    apply (rule match_result_sound_err)
    apply fact
    done
qed (fastforce simp: all_distinct_alt_def[symmetric] intro: evaluate_match_evaluate_list_evaluate.intros)+

context begin

private lemma unclocked_complete0:
  "BigStep.evaluate_match ck env s v0 pes err_v (s', bv) \<Longrightarrow> \<not> ck \<Longrightarrow> (
    case bv of
        Rval v \<Rightarrow>
          \<exists>e env'.
            match_result env s v0 pes err_v = Rval (e, env') \<and>
            evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s e (s', Rval v)
      | Rerr err \<Rightarrow>
          (match_result env s v0 pes err_v = Rerr err) \<or>
          (\<exists>e env'.
            match_result env s v0 pes err_v = Rval (e, env') \<and>
            evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s e (s', Rerr err)))"
  "BigStep.evaluate_list ck v s es (s', bv0) \<Longrightarrow> \<not> ck \<Longrightarrow> evaluate_list v s es (s', bv0)"
  "BigStep.evaluate ck v s e (s', bv) \<Longrightarrow> \<not> ck \<Longrightarrow> evaluate v s e (s', bv)"
proof (induction rule: evaluate_induct)
  case (handle2 ck s1 s2 env e pes v1 s3 bv)
  show ?case
    proof (cases bv)
      case (Rval v)
      with handle2 obtain e env' where
        "match_result env s2 v1 pes v1 = Rval (e, env')"
        "evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e (s3, Rval v)"
        by auto

      show ?thesis
        unfolding \<open>bv = _\<close>
        apply (rule evaluate_list_evaluate.handle2)
        using handle2 apply blast
        by fact+
    next
      case (Rerr err)
      with handle2 consider
        (match_err) "match_result env s2 v1 pes v1 = Rerr err" |
        (eval_err) e env' where
          "match_result env s2 v1 pes v1 = Rval (e, env')"
          "evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e (s3, Rerr err)"
        by auto
      then show ?thesis
        proof cases
          case match_err
          then have "evaluate_match ck env s2 v1 pes v1 (s2, Rerr err)"
            by (metis match_result_sound_err)
          moreover have "evaluate_match ck env s2 v1 pes v1 (s3, Rerr err)"
            using handle2 unfolding \<open>bv = _\<close> by blast
          ultimately have "s2 = s3"
            by (metis evaluate_determ fst_conv)

          show ?thesis
            unfolding \<open>bv = _\<close>
            apply (rule evaluate_list_evaluate.handle2b)
            using handle2 unfolding \<open>s2 = _\<close> apply blast
            using match_err unfolding \<open>s2 = _\<close> .
        next
          case eval_err
          show ?thesis
            unfolding \<open>bv = _\<close>
            apply (rule evaluate_list_evaluate.handle2)
            using handle2 apply blast
            by fact+
        qed
    qed
next
  case (mat1 ck env e pes v1 s3 v' s1 s2)
  then show ?case
    (* this is the same proof as above, but with less Isar and more apply *)
    apply (auto split: result.splits simp: Bindv_def[symmetric])
    subgoal by (rule evaluate_list_evaluate.mat1) auto
    subgoal
      apply (frule match_result_sound_err)
      apply (subgoal_tac "s2 = s3")
      apply (rule evaluate_list_evaluate.mat1b)
      apply force
      apply force
      apply (drule evaluate_determ)
      apply assumption
      by auto
    subgoal by (rule evaluate_list_evaluate.mat1) auto
    done
next
  case (mat_cons1 ck env env' v1 p pes e a b err_v s)
  then show ?case
    by (auto split: result.splits)
next
  case (mat_cons2 ck env v1 p e pes a b s err_v)
  then show ?case
    by (auto split: result.splits)
qed (fastforce simp: all_distinct_alt_def intro: evaluate_list_evaluate.intros)+

lemma unclocked_complete:
  "BigStep.evaluate_list False v s es bv' \<Longrightarrow> evaluate_list v s es bv'"
  "BigStep.evaluate False v s e bv \<Longrightarrow> evaluate v s e bv"
apply (cases bv'; metis unclocked_complete0)
apply (cases bv; metis unclocked_complete0)
done

end

lemma unclocked_eq:
  "evaluate_list = BigStep.evaluate_list False"
  "evaluate = BigStep.evaluate False"
by (auto intro: unclocked_sound unclocked_complete intro!: ext)

lemma unclocked_determ:
  "evaluate_list env s es r2a \<Longrightarrow> evaluate_list env s es r2b \<Longrightarrow> r2a = r2b"
  "evaluate env s e r3a \<Longrightarrow> evaluate env s e r3b \<Longrightarrow> r3a = r3b"
by (metis unclocked_eq evaluate_determ)+

end