section "An even simpler version without mutual induction"

theory Big_Step_Unclocked_Single
  imports Big_Step_Unclocked Big_Step_Clocked Evaluate_Single Big_Step_Fun_Equiv
begin

inductive evaluate_list ::
  "('ffi state \<Rightarrow> exp \<Rightarrow> 'ffi state*(v,v) result \<Rightarrow> bool) \<Rightarrow>
    'ffi state \<Rightarrow> exp list \<Rightarrow> 'ffi state*(v list, v)result \<Rightarrow> bool" for P where
empty:
  "evaluate_list P s [] (s,Rval [])" |

cons1:
  "P s1 e (s2, Rval v) \<Longrightarrow>
   evaluate_list P s2 es (s3, Rval vs) \<Longrightarrow>
   evaluate_list P s1 (e#es) (s3, Rval (v#vs))" |

cons2:
  "P s1 e (s2, Rerr err) \<Longrightarrow>
   evaluate_list P s1 (e#es) (s2, Rerr err)" |

cons3:
  "P s1 e (s2, Rval v) \<Longrightarrow>
   evaluate_list P s2 es (s3, Rerr err) \<Longrightarrow>
   evaluate_list P s1 (e#es) (s3, Rerr err)"

lemma evaluate_list_mono_strong[intro?]:
  assumes "evaluate_list R s es r"
  assumes "\<And>s e r. e \<in> set es \<Longrightarrow> R s e r \<Longrightarrow> Q s e r"
  shows "evaluate_list Q s es r"
using assms by (induction; fastforce intro: evaluate_list.intros)

lemma evaluate_list_mono[mono]:
  assumes "R \<le> Q"
  shows "evaluate_list R \<le> evaluate_list Q"
using assms unfolding le_fun_def le_bool_def
by (metis evaluate_list_mono_strong)

inductive evaluate :: "v sem_env \<Rightarrow> 'ffi state \<Rightarrow> exp \<Rightarrow> 'ffi state*(v,v) result \<Rightarrow> bool" where

lit:
  "evaluate env s (Lit l) (s, Rval (Litv l))" |

raise1:
  "evaluate env s1 e (s2, Rval v) \<Longrightarrow>
   evaluate env s1 (Raise e) (s2, Rerr (Rraise v))" |

raise2:
  "evaluate env s1 e (s2, Rerr err) \<Longrightarrow>
   evaluate env s1 (Raise e) (s2, Rerr err)" |

handle1:
  "evaluate env s1 e (s2, Rval v) \<Longrightarrow>
   evaluate env s1 (Handle e pes) (s2, Rval v)" |

handle2:
  "evaluate env s1 e (s2, Rerr (Rraise v)) \<Longrightarrow>
   match_result env s2 v pes v = Rval (e', env') \<Longrightarrow>
   evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e' bv \<Longrightarrow>
   evaluate env s1 (Handle e pes) bv" |

handle2b:
  "evaluate env s1 e (s2, Rerr (Rraise v)) \<Longrightarrow>
   match_result env s2 v pes v = Rerr err \<Longrightarrow>
   evaluate env s1 (Handle e pes) (s2, Rerr err)" |

handle3:
  "evaluate env s1 e (s2, Rerr (Rabort a)) \<Longrightarrow>
   evaluate env s1 (Handle e pes) (s2, Rerr (Rabort a))" |

con1:
  "do_con_check (c env) cn (length es) \<Longrightarrow>
   build_conv (c env) cn (rev vs) = Some v \<Longrightarrow>
   evaluate_list (evaluate env) s1 (rev es) (s2, Rval vs) \<Longrightarrow>
   evaluate env s1 (Con cn es) (s2, Rval v)" |

con2:
  "\<not>(do_con_check (c env) cn (length es)) \<Longrightarrow>
   evaluate env s (Con cn es) (s, Rerr (Rabort Rtype_error))" |

con3:
  "do_con_check (c env) cn (length es) \<Longrightarrow>
   evaluate_list (evaluate env) s1 (rev es) (s2, Rerr err) \<Longrightarrow>
   evaluate env s1 (Con cn es) (s2, Rerr err)" |

var1:
  "nsLookup (sem_env.v env) n = Some v \<Longrightarrow>
   evaluate env s (Var n) (s, Rval v)" |

var2:
  "nsLookup (sem_env.v env) n = None \<Longrightarrow>
   evaluate env s (Var n) (s, Rerr (Rabort Rtype_error))" |

fn:
  "evaluate env s (Fun n e) (s, Rval (Closure env n e))" |

app1:
  "evaluate_list (evaluate env) s1 (rev es) (s2, Rval vs) \<Longrightarrow>
   do_opapp (rev vs) = Some (env', e) \<Longrightarrow>
   evaluate env' s2 e bv \<Longrightarrow>
   evaluate env s1 (App Opapp es) bv" |

app3:
  "evaluate_list (evaluate env) s1 (rev es) (s2, Rval vs) \<Longrightarrow>
   (do_opapp (rev vs) = None) \<Longrightarrow>
   evaluate env s1 (App Opapp es) (s2, Rerr (Rabort Rtype_error))" |

app4:
  "evaluate_list (evaluate env) s1 (rev es) (s2, Rval vs) \<Longrightarrow>
   do_app (refs s2, ffi s2) op0 (rev vs) = Some ((refs',ffi'), res) \<Longrightarrow>
   op0 \<noteq> Opapp \<Longrightarrow>
   evaluate env s1 (App op0 es) (s2 \<lparr>refs:=refs',ffi:=ffi'\<rparr>, res)" |

app5:
  "evaluate_list (evaluate env) s1 (rev es) (s2, Rval vs) \<Longrightarrow>
   do_app (refs s2, ffi s2) op0 (rev vs) = None \<Longrightarrow>
   op0 \<noteq> Opapp \<Longrightarrow>
   evaluate env s1 (App op0 es) (s2, Rerr (Rabort Rtype_error))" |

app6:
  "evaluate_list (evaluate env) s1 (rev es) (s2, Rerr err) \<Longrightarrow>
   evaluate env s1 (App op0 es) (s2, Rerr err)" |

log1:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   do_log op0 v1 e2 = Some (Exp e') \<Longrightarrow>
   evaluate env s2 e' bv \<Longrightarrow>
   evaluate env s1 (Log op0 e1 e2) bv " |

log2:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   (do_log op0 v1 e2 = Some (Val bv)) \<Longrightarrow>
   evaluate env s1 (Log op0 e1 e2) (s2, Rval bv)" |

log3:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   (do_log op0 v1 e2 = None) \<Longrightarrow>
   evaluate env s1 (Log op0 e1 e2) (s2, Rerr (Rabort Rtype_error))" |

log4:
  "evaluate env s e1 (s', Rerr err) \<Longrightarrow>
   evaluate env s (Log op0 e1 e2) (s', Rerr err)" |

if1:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   do_if v1 e2 e3 = Some e' \<Longrightarrow>
   evaluate env s2 e' bv \<Longrightarrow>
   evaluate env s1 (If e1 e2 e3) bv " |

if2:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   (do_if v1 e2 e3 = None) \<Longrightarrow>
   evaluate env s1 (If e1 e2 e3) (s2, Rerr (Rabort Rtype_error))" |

if3:
  "evaluate env s e1 (s', Rerr err) \<Longrightarrow>
   evaluate env s (If e1 e2 e3) (s', Rerr err)" |

mat1:
  "evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
   match_result env s2 v1 pes Bindv = Rval (e', env') \<Longrightarrow>
   evaluate (env \<lparr> sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) \<rparr>) s2 e' bv \<Longrightarrow>
   evaluate env s1 (Mat e pes) bv " |

mat1b:
  "evaluate env s1 e (s2, Rval v1) \<Longrightarrow>
   match_result env s2 v1 pes Bindv = Rerr err \<Longrightarrow>
   evaluate env s1 (Mat e pes) (s2, Rerr err)" |

mat2:
  "evaluate env s e (s', Rerr err) \<Longrightarrow>
   evaluate env s (Mat e pes) (s', Rerr err)" |

let1:
  "evaluate env s1 e1 (s2, Rval v1) \<Longrightarrow>
   evaluate ( env \<lparr> sem_env.v := (nsOptBind n v1(sem_env.v env)) \<rparr>) s2 e2 bv \<Longrightarrow>
   evaluate env s1 (Let n e1 e2) bv " |

let2:
  "evaluate env s e1 (s', Rerr err) \<Longrightarrow>
   evaluate env s (Let n e1 e2) (s', Rerr err)" |

letrec1:
  "distinct (List.map ( \<lambda>x .
     (case  x of (x,y,z) => x )) funs) \<Longrightarrow>
   evaluate ( env \<lparr> sem_env.v := (build_rec_env funs env(sem_env.v env)) \<rparr>) s e bv \<Longrightarrow>
   evaluate env s (Letrec funs e) bv " |

letrec2:
  "\<not> (distinct (List.map ( \<lambda>x .
     (case  x of (x,y,z) => x )) funs)) \<Longrightarrow>
   evaluate env s (Letrec funs e) (s, Rerr (Rabort Rtype_error))" |

tannot:
  "evaluate env s e bv \<Longrightarrow>
   evaluate env s (Tannot e t0) bv " |

locannot:
  "evaluate env s e bv \<Longrightarrow>
   evaluate env s (Lannot e l) bv "

lemma unclocked_single_list_sound:
  "evaluate_list (Big_Step_Unclocked.evaluate v) s es bv \<Longrightarrow> Big_Step_Unclocked.evaluate_list v s es bv"
by (induction rule: evaluate_list.induct) (auto intro: evaluate_list_evaluate.intros)

lemma unclocked_single_sound:
  "evaluate v s e bv \<Longrightarrow> Big_Step_Unclocked.evaluate v s e bv"
by (induction rule:evaluate.induct)
   (auto simp del: do_app.simps intro: Big_Step_Unclocked.evaluate_list_evaluate.intros unclocked_single_list_sound
         evaluate_list_mono_strong)

lemma unclocked_single_complete:
  "Big_Step_Unclocked.evaluate_list v s es bv1 \<Longrightarrow> evaluate_list (evaluate v) s es bv1"
  "Big_Step_Unclocked.evaluate v s e bv2 \<Longrightarrow> evaluate v s e bv2"
by (induction rule: evaluate_list_evaluate.inducts)
   (auto intro: evaluate.intros evaluate_list.intros)

corollary unclocked_single_eq:
  "evaluate = Big_Step_Unclocked.evaluate"
by (rule ext)+ (metis unclocked_single_sound unclocked_single_complete)

corollary unclocked_single_eq':
  "evaluate = BigStep.evaluate False"
by (simp add: unclocked_single_eq unclocked_eq)

corollary unclocked_single_determ:
  "evaluate env s e r3a \<Longrightarrow> evaluate env s e r3b \<Longrightarrow> r3a = r3b"
by (metis unclocked_single_eq unclocked_determ)

lemma unclocked_single_fun_eq:
  "((\<exists>k. Evaluate_Single.evaluate env (s \<lparr> clock:= k \<rparr>) e = (s', r)) \<and> r \<noteq>  Rerr (Rabort Rtimeout_error) \<and> (clock s) = (clock s')) =
    evaluate env s e (s',r)"
  apply (subst fun_evaluate_equiv')
  apply (subst unclocked_single_eq)
  apply (subst unclocked_eq)
  apply (subst fun.evaluate_iff_sym(1)[symmetric])
  apply (subst big_clocked_unclocked_equiv)
  using clocked_evaluate by metis

end