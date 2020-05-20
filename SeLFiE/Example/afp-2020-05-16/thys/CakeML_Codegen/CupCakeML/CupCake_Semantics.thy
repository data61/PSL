section \<open>CupCake semantics\<close>

theory CupCake_Semantics
imports
  CupCake_Env
  CakeML.Matching
  CakeML.Big_Step_Unclocked_Single
begin

fun cupcake_nsLookup :: "('m,'n,'v)namespace \<Rightarrow> 'n \<Rightarrow> 'v option "  where
"cupcake_nsLookup (Bind v1 _) n = map_of v1 n"

lemma cupcake_nsLookup_eq[simp]: "nsLookup ns (Short n) = cupcake_nsLookup ns n"
by (cases ns) auto

fun cupcake_pmatch :: "((string),(string),(nat*tid_or_exn))namespace \<Rightarrow> pat \<Rightarrow> v \<Rightarrow>(string*v)list \<Rightarrow>((string*v)list)match_result " where
"cupcake_pmatch cenv (Pvar x) v0 env = Match ((x, v0)# env)" |
"cupcake_pmatch cenv (Pcon (Some (Short n)) ps) (Conv (Some (n', t')) vs) env =
  (case cupcake_nsLookup cenv n of
      Some (l, t)=>
        if same_tid t t' \<and> (List.length ps = l) then
          if same_ctor (n, t) (n',t') then
            Matching.fold2 (\<lambda>p v m. case m of
               Match env \<Rightarrow> cupcake_pmatch cenv p v env
            | m \<Rightarrow> m) Match_type_error ps vs (Match env)
          else
            No_match
        else
          Match_type_error
    | _ => Match_type_error)" |
"cupcake_pmatch cenv _ _ _ = Match_type_error"

fun cupcake_match_result :: "_ \<Rightarrow> v \<Rightarrow>(pat*exp)list \<Rightarrow> v \<Rightarrow> (exp \<times> pat \<times> (char list \<times> v) list, v)result" where
"cupcake_match_result _ _ [] err_v = Rerr (Rraise err_v)" |
"cupcake_match_result cenv v0 ((p, e) # pes) err_v =
  (if distinct (pat_bindings p []) then
    (case cupcake_pmatch cenv p v0 [] of
      Match env' \<Rightarrow> Rval (e, p, env') |
      No_match \<Rightarrow> cupcake_match_result cenv v0 pes err_v |
      Match_type_error \<Rightarrow> Rerr (Rabort Rtype_error))
   else
      Rerr (Rabort Rtype_error))"

lemma cupcake_match_resultE:
  assumes "cupcake_match_result cenv v0 pes err_v = Rval (e, p, env')"
  obtains init rest
    where "pes = init @ (p, e) # rest"
      and "distinct (pat_bindings p [])"
      and "list_all (\<lambda>(p, e). cupcake_pmatch cenv p v0 [] = No_match \<and> distinct (pat_bindings p [])) init"
      and "cupcake_pmatch cenv p v0 [] = Match env'"
using assms
proof (induction pes)
  case (Cons pe pes)
  obtain p0 e0 where "pe = (p0, e0)"
    by fastforce

  show thesis
    proof (cases "distinct (pat_bindings p0 [])")
      case True
      thus ?thesis
        proof (cases "cupcake_pmatch cenv p0 v0 []")
          case No_match
          show ?thesis
            proof (rule Cons)
              fix init rest
              assume "pes = init @ (p, e) # rest"
              assume "list_all (\<lambda>(p, e). cupcake_pmatch cenv p v0 [] = No_match \<and> distinct (pat_bindings p [])) init"
              assume "distinct (pat_bindings p [])"
              assume "cupcake_pmatch cenv p v0 [] = Match env'"

              moreover have "pe # pes = ((p0, e0) # init) @ (p, e) # rest"
                unfolding \<open>pes = _\<close> \<open>pe = _\<close> by simp

              moreover have "list_all (\<lambda>(p, e). cupcake_pmatch cenv p v0 [] = No_match \<and> distinct (pat_bindings p [])) ((p0, e0) # init)"
                apply auto
                subgoal by fact
                subgoal using True by simp
                subgoal using \<open>list_all _ _\<close> by simp
                done

              moreover have "distinct (pat_bindings p [])"
                by fact

              ultimately show thesis
                using Cons by blast
            next
              show "cupcake_match_result cenv v0 pes err_v = Rval (e, p, env')"
                using Cons No_match True unfolding \<open>pe = _\<close> by auto
            qed
        next
          case Match
          with Cons show ?thesis
            using True unfolding \<open>pe = _\<close> by force
        next
          case Match_type_error
          with Cons show ?thesis
            using True unfolding \<open>pe = _\<close> by force
        qed
    next
      case False
      hence False
        using Cons unfolding \<open>pe = _\<close> by force
      thus ?thesis ..
    qed
qed simp

lemma cupcake_pmatch_eq:
  "is_cupcake_pat pat \<Longrightarrow> pmatch_single envC s pat v0 env = cupcake_pmatch envC pat v0 env"
proof (induct rule: pmatch_single.induct)
  case 4
  from is_cupcake_pat.elims(2)[OF 4(2)] show ?case
    proof cases
      case 2
      then show ?thesis
        using 4(1) apply -
        apply simp
        apply (auto split: option.splits match_result.splits)
        apply (rule Matching.fold2_cong)
            apply (auto simp: fun_eq_iff split: match_result.splits)
        apply (metis in_set_conv_decomp_last list.pred_inject(2) list_all_append)
        done
    qed simp
qed auto

lemma cupcake_match_result_eq:
  "cupcake_clauses pes \<Longrightarrow>
    match_result env s v pes err_v =
      map_result (\<lambda>(e, _, env'). (e, env')) id (cupcake_match_result (c env) v pes err_v)"
by (induction pes) (auto split: match_result.splits simp: cupcake_pmatch_eq pmatch_single_equiv)

context cakeml_static_env begin

lemma cupcake_nsBind_preserve:
  "is_cupcake_ns ns \<Longrightarrow> is_cupcake_value v0 \<Longrightarrow> is_cupcake_ns (nsBind k v0 ns)"
by (cases ns) (auto elim: is_cupcake_ns.elims)

lemma cupcake_build_rec_preserve:
  assumes "is_cupcake_all_env cl_env" "is_cupcake_ns env" "list_all (\<lambda>(_, _, e). is_cupcake_exp e) fs"
  shows "is_cupcake_ns (build_rec_env fs cl_env env)"
proof -
  have "is_cupcake_ns (foldr (\<lambda>(f, _) env'. nsBind f (Recclosure cl_env fs0 f) env') fs env)"
    if "list_all (\<lambda>(_, _, e). is_cupcake_exp e) fs0"
    for fs0
    using \<open>is_cupcake_ns env\<close>
    proof (induction fs arbitrary: env)
      case (Cons f fs)
      show ?case
        apply (cases f, simp)
        apply (rule cupcake_nsBind_preserve)
         apply (rule Cons.IH)
         apply (rule Cons)
        using that assms by auto
    qed auto
  thus ?thesis
    unfolding build_rec_env_def
    using assms
    by (simp add: cond_case_prod_eta)
qed

lemma cupcake_v_update_preserve:
  assumes "is_cupcake_all_env env" "is_cupcake_ns (f (sem_env.v env))"
  shows "is_cupcake_all_env (sem_env.update_v f env)"
using assms
  by (metis is_cupcake_all_env.simps(1) is_cupcake_all_envE is_cupcake_nsE sem_env.collapse sem_env.record_simps(1) sem_env.record_simps(2) sem_env.sel(2))

lemma cupcake_nsAppend_preserve: "is_cupcake_ns ns1 \<Longrightarrow> is_cupcake_ns ns2 \<Longrightarrow> is_cupcake_ns (nsAppend ns1 ns2)"
by (auto elim!: is_cupcake_ns.elims)

lemma cupcake_alist_to_ns_preserve: "list_all (is_cupcake_value \<circ> snd) env \<Longrightarrow> is_cupcake_ns (alist_to_ns env)"
unfolding alist_to_ns_def
by simp

lemma cupcake_opapp_preserve:
  assumes "do_opapp vs = Some (env, e)" "list_all is_cupcake_value vs"
  shows "is_cupcake_all_env env" "is_cupcake_exp e"
proof -
  obtain cl v0 where "vs = [cl, v0]"
    using assms
    by (cases vs rule: do_opapp.cases) auto
  with assms have "is_cupcake_value cl" "is_cupcake_value v0"
    by auto

  have "is_cupcake_all_env env \<and> is_cupcake_exp e"
    using \<open>do_opapp vs = _\<close> proof (cases rule: do_opapp_cases)
      case (closure env' n arg)
      then show ?thesis
        using \<open>is_cupcake_value cl\<close> \<open>is_cupcake_value v0\<close> \<open>vs = [cl, v0]\<close>
        by (auto intro: cupcake_v_update_preserve cupcake_nsBind_preserve dest:is_cupcake_all_envD(1))
    next
      case (recclosure env' funs name n)
      hence "is_cupcake_all_env env'"
        using \<open>is_cupcake_value cl\<close> \<open>vs = [cl, v0]\<close> by simp
      have "(name, n, e) \<in> set funs"
        using recclosure by (auto dest: map_of_SomeD)
      hence "is_cupcake_exp e"
        using \<open>is_cupcake_value cl\<close> \<open>vs = [cl, v0]\<close> recclosure
        by (auto simp: list_all_iff)
      thus ?thesis
        using \<open>is_cupcake_all_env env'\<close> \<open>is_cupcake_value cl\<close> \<open>is_cupcake_value v0\<close> \<open>vs = [cl, v0]\<close> recclosure
        unfolding \<open>env = _\<close>
        using cupcake_build_rec_preserve cupcake_nsBind_preserve cupcake_v_update_preserve is_cupcake_all_envD(1)
        by auto
    qed

  thus "is_cupcake_all_env env" "is_cupcake_exp e"
    by simp+
qed

context begin

lemma cup_pmatch_list_length_neq:
  "length vs \<noteq> length ps \<Longrightarrow> Matching.fold2(\<lambda>p v m. case m of
       Match env \<Rightarrow> cupcake_pmatch cenv p v env
        | m \<Rightarrow> m) Match_type_error ps vs m = Match_type_error"
  by (induction ps vs arbitrary:m rule:List.list_induct2') auto

lemma cup_pmatch_list_nomatch:
  "length vs = length ps \<Longrightarrow>  Matching.fold2(\<lambda>p v m. case m of
       Match env \<Rightarrow> cupcake_pmatch cenv p v env
        | m \<Rightarrow> m) Match_type_error ps vs No_match = No_match"
  by (induction ps vs  rule:List.list_induct2') auto

lemma cup_pmatch_list_typerr:
  "length vs = length ps \<Longrightarrow> Matching.fold2(\<lambda>p v m. case m of
       Match env \<Rightarrow> cupcake_pmatch cenv p v env
        | m \<Rightarrow> m) Match_type_error ps vs Match_type_error = Match_type_error"
  by (induction ps vs  rule:List.list_induct2') auto

private lemma cupcake_pmatch_list_preserve:
  assumes " \<And>p v env. p \<in> set ps \<and> v \<in> set vs \<longrightarrow> list_all (is_cupcake_value \<circ> snd) env \<longrightarrow> if_match (list_all (is_cupcake_value \<circ> snd)) (cupcake_pmatch cenv p v env)" "list_all (is_cupcake_value \<circ> snd) env"
  shows "if_match (list_all (\<lambda>a. is_cupcake_value (snd a))) (Matching.fold2
            (\<lambda>p v m. case m of
               Match env \<Rightarrow> cupcake_pmatch cenv p v env
            | m \<Rightarrow> m)
            Match_type_error ps vs (Match env))"
  using assms proof (induction ps vs arbitrary: env rule:list_induct2')
  case (4 p ps v vs)
  show ?case
  proof (cases "cupcake_pmatch cenv p v env")
    case No_match
    then show ?thesis
      by (cases "length ps = length vs") (auto simp:cup_pmatch_list_nomatch cup_pmatch_list_length_neq)
  next
    case Match_type_error
    then show ?thesis
      by (cases "length ps = length vs") (auto simp:cup_pmatch_list_typerr cup_pmatch_list_length_neq)
  next
    case (Match env')
    then have env': "list_all (is_cupcake_value \<circ> snd) env'"
      using 4 by fastforce
      then show ?thesis
      apply (cases "length ps = length vs")
      using 4 Match by fastforce+
  qed
qed (auto simp: comp_def)

private lemma cupcake_pmatch_preserve0:
  "is_cupcake_pat pat \<Longrightarrow>
    is_cupcake_value v0 \<Longrightarrow>
     list_all (is_cupcake_value \<circ> snd) env \<Longrightarrow>
      cupcake_c_ns envC \<Longrightarrow>
       if_match (list_all (is_cupcake_value \<circ> snd)) (cupcake_pmatch envC pat v0 env)"
proof (induction rule: cupcake_pmatch.induct)
  case (2 cenv n ps n' t' vs env)
  have p:"p \<in> set ps \<Longrightarrow> is_cupcake_pat p" for p
    using 2 by (metis Ball_set is_cupcake_pat.simps(2))
  have v:"v \<in> set vs \<Longrightarrow> is_cupcake_value v" for v
    using 2 by (metis Ball_set is_cupcake_value.elims(2) v.distinct(11) v.distinct(13) v.inject(2))
  show ?case
   by (auto intro!: cupcake_pmatch_list_preserve split:if_splits option.splits) (metis 2 p v)+
qed (auto split: option.splits if_splits elim: is_cupcake_pat.elims is_cupcake_value.elims)

lemma cupcake_pmatch_preserve:
  "is_cupcake_pat pat \<Longrightarrow>
    is_cupcake_value v0 \<Longrightarrow>
     list_all (is_cupcake_value \<circ> snd) env \<Longrightarrow>
      cupcake_c_ns envC \<Longrightarrow>
       cupcake_pmatch envC pat v0 env = Match env' \<Longrightarrow>
        list_all (is_cupcake_value \<circ> snd) env'"
by (metis if_match.simps(1) cupcake_pmatch_preserve0)+

end

lemma cupcake_match_result_preserve:
  "cupcake_c_ns envC \<Longrightarrow>
    cupcake_clauses pes \<Longrightarrow>
      is_cupcake_value v \<Longrightarrow>
        if_rval (\<lambda>(e, p, env'). is_cupcake_pat p \<and> is_cupcake_exp e \<and> list_all (is_cupcake_value \<circ> snd) env')
          (cupcake_match_result envC v pes err_v)"
  apply (induction pes)
   apply (auto split: match_result.splits)
  apply (rule cupcake_pmatch_preserve)
      apply auto
  done

lemma static_cenv_lookup:
  assumes "cupcake_nsLookup static_cenv i = Some (len, b)"
  obtains name where "b = TypeId (Short name)"
using assms static_cenv
apply (cases static_cenv; cases b)
apply (auto simp: list_all_iff split: prod.splits tid_or_exn.splits id0.splits dest!: map_of_SomeD elim!: ballE allE)
using static_cenv
apply (auto simp: list_all_iff split: prod.splits tid_or_exn.splits id0.splits dest!: map_of_SomeD elim!: ballE allE)
done

lemma cupcake_build_conv_preserve:
  fixes v
  assumes "list_all is_cupcake_value vs" "build_conv static_cenv (Some (Short i)) vs = Some v"
  shows "is_cupcake_value v"
using assms
by (auto simp: build_conv.simps split: option.splits elim: static_cenv_lookup)

lemma cupcake_nsLookup_preserve:
  assumes "is_cupcake_ns ns" "nsLookup ns n = Some v0"
  shows "is_cupcake_value v0"
proof -
  obtain vs where "list_all (is_cupcake_value \<circ> snd) vs" "ns = Bind vs []"
    using assms
    by (auto elim: is_cupcake_ns.elims)
  show ?thesis
    proof (cases n)
      case (Short id)
      hence "(id, v0) \<in> set vs"
        using assms unfolding \<open>ns = _\<close> by (auto dest: map_of_SomeD)
      thus ?thesis
        using \<open>list_all (is_cupcake_value \<circ> snd) vs\<close>
        by (auto simp: list_all_iff)
    next
      case Long
      hence "nsLookup ns n = None"
        unfolding \<open>ns = _\<close> by simp
      thus ?thesis
        using assms by auto
    qed
qed

corollary match_all_preserve:
  assumes "cupcake_match_result cenv v0 pes err_v = Rval (e, p, env')" "cupcake_c_ns cenv"
  assumes "is_cupcake_value v0" "cupcake_clauses pes"
  shows "list_all (is_cupcake_value \<circ> snd) env'" "is_cupcake_exp e" "is_cupcake_pat p"
proof -
  from assms obtain init rest
    where "pes = init @ (p, e) # rest" and "cupcake_pmatch cenv p v0 [] = Match env'"
    by (elim cupcake_match_resultE)
  hence "(p, e) \<in> set pes"
    by simp
  thus "is_cupcake_exp e" "is_cupcake_pat p"
    using assms by (auto simp: list_all_iff)

  show "list_all (is_cupcake_value \<circ> snd) env'"
    by (rule cupcake_pmatch_preserve[where env = "[]"]) (fact | simp)+
qed

end

fun list_all2_shortcircuit where
"list_all2_shortcircuit P (x # xs) (y # ys) \<longleftrightarrow> (case y of Rval _ \<Rightarrow> P x y \<and> list_all2_shortcircuit P xs ys | Rerr _ \<Rightarrow> P x y)" |
"list_all2_shortcircuit P [] [] \<longleftrightarrow> True" |
"list_all2_shortcircuit P _ _ \<longleftrightarrow> False"

lemma list_all2_shortcircuit_induct[consumes 1, case_names nil cons_val cons_err]:
  assumes "list_all2_shortcircuit P xs ys"
  assumes "R [] []"
  assumes "\<And>x xs y ys. P x (Rval y) \<Longrightarrow> list_all2_shortcircuit P xs ys \<Longrightarrow> R xs ys \<Longrightarrow> R (x # xs) (Rval y # ys)"
  assumes "\<And>x xs y ys. P x (Rerr y) \<Longrightarrow> R (x # xs) (Rerr y # ys)"
  shows "R xs ys"
using assms
proof (induction P xs ys rule: list_all2_shortcircuit.induct)
  case (1 P x xs y ys)
  thus ?case
    by (cases y) auto
qed auto

lemma list_all2_shortcircuit_mono[mono]:
  assumes "R \<le> Q"
  shows "list_all2_shortcircuit R \<le> list_all2_shortcircuit Q"
proof
  fix xs ys
  assume "list_all2_shortcircuit R xs ys"
  thus "list_all2_shortcircuit Q xs ys"
    using assms by (induction xs ys rule: list_all2_shortcircuit_induct) auto
qed

lemma list_all2_shortcircuit_weaken: "list_all2_shortcircuit P xs ys \<Longrightarrow> (\<And>xs ys. P xs ys \<Longrightarrow> Q xs ys) \<Longrightarrow> list_all2_shortcircuit Q xs ys"
by (metis list_all2_shortcircuit_mono predicate2I rev_predicate2D)

lemma list_all2_shortcircuit_rval[simp]:
  "list_all2_shortcircuit P xs (map Rval ys) \<longleftrightarrow> list_all2 (\<lambda>x y. P x (Rval y)) xs ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
    by (induction "map Rval ys::('b, 'c) result list" arbitrary: ys rule: list_all2_shortcircuit_induct) auto
next
  assume ?rhs thus ?lhs
    by (induction rule: list_all2_induct) auto
qed

inductive cupcake_evaluate_single :: "all_env \<Rightarrow> exp \<Rightarrow> (v, v) result \<Rightarrow> bool" where
con1:
  "do_con_check (c env) cn (length es) \<Longrightarrow>
   list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs \<Longrightarrow>
   sequence_result rs = Rval vs \<Longrightarrow>
   build_conv (c env) cn (rev vs) = Some v0 \<Longrightarrow>
   cupcake_evaluate_single env (Con cn es) (Rval v0)" |
con2:
  "\<not> do_con_check (c env) cn (List.length es) \<Longrightarrow>
   cupcake_evaluate_single env (Con cn es) (Rerr (Rabort Rtype_error))" |
con3:
  "do_con_check (c env) cn (List.length es) \<Longrightarrow>
   list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs \<Longrightarrow>
   sequence_result rs = Rerr err \<Longrightarrow>
   cupcake_evaluate_single env (Con cn es) (Rerr err)" |
var1:
  "nsLookup (sem_env.v env) n = Some v0 \<Longrightarrow> cupcake_evaluate_single env (Var n) (Rval v0)" |
var2:
  "nsLookup (sem_env.v env) n = None \<Longrightarrow> cupcake_evaluate_single env (Var n) (Rerr (Rabort Rtype_error))" |
fn:
  "cupcake_evaluate_single env (Fun n e) (Rval (Closure env n e))" |
app1:
  "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs \<Longrightarrow>
   sequence_result rs = Rval vs \<Longrightarrow>
   do_opapp (rev vs) = Some (env', e) \<Longrightarrow>
   cupcake_evaluate_single env' e bv \<Longrightarrow>
   cupcake_evaluate_single env (App Opapp es) bv" |
app3:
  "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs \<Longrightarrow>
   sequence_result rs = Rval vs \<Longrightarrow>
   do_opapp (rev vs) = None \<Longrightarrow>
   cupcake_evaluate_single env (App Opapp es) (Rerr (Rabort Rtype_error))" |
app6:
  "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs \<Longrightarrow>
   sequence_result rs = Rerr err \<Longrightarrow>
   cupcake_evaluate_single env (App op0 es) (Rerr err)" |
mat1:
  "cupcake_evaluate_single env e (Rval v0) \<Longrightarrow>
   cupcake_match_result (c env) v0 pes Bindv = Rval (e', _, env') \<Longrightarrow>
   cupcake_evaluate_single (env (| sem_env.v := nsAppend (alist_to_ns env') (sem_env.v env) |)) e' bv \<Longrightarrow>
   cupcake_evaluate_single env (Mat e pes) bv" |
mat1error:
  "cupcake_evaluate_single env e (Rval v0) \<Longrightarrow>
   cupcake_match_result (c env) v0 pes Bindv = Rerr err \<Longrightarrow>
   cupcake_evaluate_single env (Mat e pes) (Rerr err)" |
mat2:
  "cupcake_evaluate_single env e (Rerr err) \<Longrightarrow>
   cupcake_evaluate_single env (Mat e pes) (Rerr err)"

context cakeml_static_env begin

context begin

private lemma cupcake_list_preserve0:
  "list_all2_shortcircuit
     (\<lambda>e r. cupcake_evaluate_single env e r \<and> (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> if_rval is_cupcake_value r)) es rs \<Longrightarrow>
  is_cupcake_all_env env \<Longrightarrow> list_all is_cupcake_exp es \<Longrightarrow> sequence_result rs = Rval vs \<Longrightarrow> list_all is_cupcake_value vs"
proof (induction es rs arbitrary: vs rule:list_all2_shortcircuit_induct)
  case (cons_val _ _ _ rs)
  thus ?case
    by (cases "sequence_result rs") auto
qed auto

private lemma cupcake_single_preserve0:
  "cupcake_evaluate_single env e res \<Longrightarrow> is_cupcake_all_env env \<Longrightarrow> is_cupcake_exp e \<Longrightarrow> if_rval is_cupcake_value res"
proof (induction rule:cupcake_evaluate_single.induct)
  case (con1 env cn es rs vs v0)
  then obtain tid where cn: "cn = Some (Short tid)" and "list_all is_cupcake_exp (rev es)"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  hence "list_all is_cupcake_value (rev vs)" and "c env = static_cenv"
    using cupcake_list_preserve0 con1
    by (fastforce elim:is_cupcake_all_envE)+

  then show ?case
    using cupcake_build_conv_preserve con1 cn
    by fastforce
next
  case (app1 env es rs vs env' e bv)
  hence "list_all is_cupcake_exp (rev es)"
    by fastforce
  hence "list_all is_cupcake_value (rev vs)"
    using app1 cupcake_list_preserve0 by force
  hence "is_cupcake_exp e" and "is_cupcake_all_env env'"
    using app1 cupcake_opapp_preserve by blast+
  then show ?case
    using app1 by blast
next
  case (mat1 env e v0 pes e' uu env' bv)
  hence "cupcake_c_ns (c env)" "cupcake_clauses pes" "is_cupcake_value v0"
    by (auto dest: is_cupcake_all_envD)
  hence "list_all (is_cupcake_value \<circ> snd) env'" and e': "is_cupcake_exp e'"
    using cupcake_match_result_preserve[where envC = "c env" and v = v0 and pes = pes and err_v = Bindv, unfolded mat1, simplified]
    by auto
  have "is_cupcake_all_env (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env)"
    apply (rule cupcake_v_update_preserve)
     apply fact
    apply (rule cupcake_nsAppend_preserve)
     apply (rule cupcake_alist_to_ns_preserve)
     apply fact
    apply (rule is_cupcake_all_envD)
    apply fact
    done
  then show ?case
    using mat1 e' by blast
qed (auto intro: cupcake_nsLookup_preserve dest: is_cupcake_all_envD)

lemma cupcake_single_preserve:
  "cupcake_evaluate_single env e (Rval res) \<Longrightarrow> is_cupcake_all_env env \<Longrightarrow> is_cupcake_exp e \<Longrightarrow> is_cupcake_value res"
  by (fastforce dest:cupcake_single_preserve0)

lemma cupcake_list_preserve:
  "list_all2_shortcircuit (cupcake_evaluate_single env) es rs \<Longrightarrow>
  is_cupcake_all_env env \<Longrightarrow> list_all is_cupcake_exp es \<Longrightarrow> sequence_result rs = Rval vs \<Longrightarrow> list_all is_cupcake_value vs"
  by (induction es rs arbitrary:vs rule:list_all2_shortcircuit_induct) (fastforce dest:cupcake_single_preserve)+

private lemma cupcake_list_correct_rval:
  assumes "list_all2_shortcircuit
     (\<lambda>e r.
         cupcake_evaluate_single env e r \<and>
         (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> (\<forall>(s::'a state). \<exists>s'. evaluate env s e (s', r))))
     es rs" "is_cupcake_all_env env" "list_all is_cupcake_exp es" "sequence_result rs = Rval vs"
  shows " \<exists>s'. evaluate_list (evaluate env) (s::'a state) es (s',Rval vs)"
using assms proof (induction es rs arbitrary: s vs rule:list_all2_shortcircuit_induct)
  case (cons_val e es y ys)
  have e: "is_cupcake_exp e" "list_all is_cupcake_exp es"
    using cons_val by fastforce+
  then obtain vs' where ys: "sequence_result ys = Rval vs'"
    using cons_val by fastforce
  hence vs: "Rval vs = Rval (y # vs')"
    using cons_val by fastforce

  from e obtain s' where "evaluate env s e (s', Rval y)"
    using cons_val by fastforce
  from e ys obtain s'' where "evaluate_list (evaluate env) s' es (s'', Rval vs')"
    using cons_val by fastforce

  show ?case
    unfolding vs
    by (rule; rule evaluate_list.cons1) fact+
qed (auto intro:evaluate_list.intros)

private lemma cupcake_list_correct_rerr:
  assumes "list_all2_shortcircuit
     (\<lambda>e r.
         cupcake_evaluate_single env e r \<and>
         (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> (\<forall>(s::'a state). \<exists>s'. evaluate env s e (s', r))))
     es rs" "is_cupcake_all_env env" "list_all is_cupcake_exp es" "sequence_result rs = Rerr err"
  shows " \<exists>s'. evaluate_list (evaluate env) (s::'a state) es (s',Rerr err)"
using assms proof (induction es rs arbitrary: s err rule:list_all2_shortcircuit_induct)
  case (cons_val e es y ys)
  then have "is_cupcake_exp e" "list_all is_cupcake_exp es"
    by fastforce+
  moreover have err: "sequence_result ys = Rerr err"
    using cons_val
    by (cases "sequence_result ys") (auto simp: error_result.map_id)

  ultimately show ?case
    using cons3 cons_val
    by fast
qed (auto intro:evaluate_list.intros)

private lemma cupcake_list_correct0:
  assumes "list_all2_shortcircuit
     (\<lambda>e r.
         cupcake_evaluate_single env e r \<and>
         (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> (\<forall>(s::'a state). \<exists>s'. evaluate env s e (s', r))))
     es rs" "is_cupcake_all_env env" "list_all is_cupcake_exp es"
  shows " \<exists>s'. evaluate_list (evaluate env) (s::'a state) es (s',sequence_result rs)"
  using assms by (cases "sequence_result rs") (fastforce intro: cupcake_list_correct_rval cupcake_list_correct_rerr)+

lemma cupcake_single_correct:
  assumes "cupcake_evaluate_single env e res" "is_cupcake_all_env env" "is_cupcake_exp e"
  shows "\<exists>s'. Big_Step_Unclocked_Single.evaluate env s e (s',res)"
using assms proof (induction arbitrary:s rule:cupcake_evaluate_single.induct)
  case (con1 env cn es rs vs v0)
  then have "list_all is_cupcake_exp (rev es)"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  then show ?case
    using cupcake_list_correct_rval evaluate.con1 con1
    by blast
next
  case (con3 env cn es rs err)
    then have "list_all is_cupcake_exp (rev es)"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  then show ?case
    using cupcake_list_correct_rerr con3 evaluate.con3
    by blast
next
  case (app1 env es rs vs env' e bv)
  hence es: "list_all is_cupcake_exp (rev es)"
    by fastforce
  hence "list_all is_cupcake_value (rev vs)"
    using app1 cupcake_list_preserve list_all2_shortcircuit_weaken
    by (metis (no_types, lifting) list_all_rev)
  hence "is_cupcake_exp e" and "is_cupcake_all_env env'"
    using app1 cupcake_opapp_preserve by blast+

  then show ?case
    using cupcake_list_correct_rval es app1 evaluate.app1
    by blast
next
  case (app3 env es rs vs)
  hence "list_all is_cupcake_exp (rev es)"
    by simp
  then show ?case
    using cupcake_list_correct_rval evaluate.app3 app3
    by blast
next
  case (app6 env es rs err op0)
  hence "list_all is_cupcake_exp (rev es)"
    by simp
  then show ?case
    using cupcake_list_correct_rerr app6 evaluate.app6
    by blast
next
  case (mat1 env e v0 pes e' uu env' bv)
  hence e: "is_cupcake_exp e" and "cupcake_c_ns (c env)" and pes: "cupcake_clauses pes" and "is_cupcake_value v0"
    by (fastforce dest: is_cupcake_all_envD cupcake_single_preserve)+
  hence "list_all (is_cupcake_value \<circ> snd) env'" and e': "is_cupcake_exp e'"
    using cupcake_match_result_preserve[where envC = "c env" and v = v0 and pes = pes and err_v = Bindv, unfolded mat1, simplified]
     by blast+
   have env': "is_cupcake_all_env (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env)"
     apply (rule cupcake_v_update_preserve)
      apply fact
     apply (rule cupcake_nsAppend_preserve)
      apply (rule cupcake_alist_to_ns_preserve)
      apply fact
     apply (rule is_cupcake_all_envD)
     apply fact
     done

  from e obtain s' where "evaluate env s e (s', Rval v0)"
    using mat1 by blast
  have "match_result env s' v0 pes Bindv = Rval (e', env')"
    using mat1 cupcake_match_result_eq[OF pes, where env = env and v = v0 and err_v = Bindv and s = s']
    by fastforce
  from e' env' obtain s'' where "evaluate (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env) s' e' (s'', bv)"
    using mat1 by blast

  show ?case
    by rule+ fact+
next
  case (mat1error env e v0 pes err)
  hence "is_cupcake_exp e" and pes: "cupcake_clauses pes"
    by (auto dest: is_cupcake_all_envD)

  then obtain s' where "Big_Step_Unclocked_Single.evaluate env s e (s', Rval v0)"
    using mat1error by blast
  hence "match_result env s' v0 pes Bindv = Rerr err"
    using cupcake_match_result_eq[OF pes, where env = env and s = s' and v = v0 and err_v = Bindv] unfolding mat1error
    by (simp add: error_result.map_id)

  show ?case
    by (rule; rule evaluate.mat1b) fact+
next
  case (mat2 _ e)
  hence "is_cupcake_exp e"
    by simp
  then show ?case
    using mat2 evaluate.mat2 by blast
qed (blast intro:evaluate.intros)+

lemma cupcake_list_correct:
  assumes "list_all2_shortcircuit (cupcake_evaluate_single env) es rs" "is_cupcake_all_env env" "list_all is_cupcake_exp es"
  shows " \<exists>s'. evaluate_list (evaluate env) (s::'a state) es (s',sequence_result rs)"
  using assms by (fastforce intro:cupcake_list_correct0 list_all2_shortcircuit_weaken cupcake_single_correct)+

private lemma cupcake_list_complete0:
  "evaluate_list
     (\<lambda>s e r. evaluate env s e r \<and> (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> cupcake_evaluate_single env e (snd r))) s1 es res \<Longrightarrow>
    is_cupcake_all_env env \<Longrightarrow> list_all is_cupcake_exp es  \<Longrightarrow>  \<exists>rs. list_all2_shortcircuit (cupcake_evaluate_single env) es rs \<and> sequence_result rs = (snd res)"
proof (induction rule:evaluate_list.induct)
  case empty
  have "list_all2_shortcircuit (cupcake_evaluate_single env) [] []"
    by fastforce
  then show ?case
    by fastforce
next
  case (cons1 s1 e s2 v es s3 vs)
  then obtain rs where "list_all2_shortcircuit (cupcake_evaluate_single env) es rs"
    and "sequence_result rs = Rval vs"
    and "list_all2_shortcircuit (cupcake_evaluate_single env) (e # es) (Rval v # rs)"
    by fastforce+
  then show ?case
    by fastforce
next
  case (cons2 s1 e s2 err es)
  hence "list_all2_shortcircuit (cupcake_evaluate_single env) (e # es) [Rerr err]"
    by simp
  then show ?case
    by fastforce
next
  case (cons3 s1 e s2 v es s3 err)
  then obtain rs where "list_all2_shortcircuit (cupcake_evaluate_single env) es rs"
    and err:"sequence_result rs = Rerr err"
    and "list_all2_shortcircuit (cupcake_evaluate_single env) (e # es) (Rval v # rs)"
    by fastforce
  moreover have "sequence_result (Rval v # rs) = Rerr err"
    by (auto simp: error_result.map_id err)
  ultimately show ?case
    by fastforce
qed

private lemma cupcake_single_complete0:
"evaluate env s e res \<Longrightarrow> is_cupcake_all_env env \<Longrightarrow> is_cupcake_exp e \<Longrightarrow> cupcake_evaluate_single env e (snd res)"
proof (induction rule:evaluate.induct)
  case (con1 env cn es vs v s1 s2)
  hence "list_all is_cupcake_exp (rev es)"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  hence "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) (map Rval vs)"
    using cupcake_list_complete0 con1 by fastforce
  show ?case
    by (simp|rule|fact)+
next
  case (con3 env cn es s1 s2 err)
  hence "list_all is_cupcake_exp (rev es)"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  then obtain rs where "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs" "sequence_result rs = Rerr err"
    using con3 by (fastforce dest:cupcake_list_complete0)
  show ?case
    by (simp;rule cupcake_evaluate_single.con3) fact+
next
  case (app1 env s1 es s2 vs env' e bv)
  then obtain rs where rs: "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs" "sequence_result rs = Rval vs"
    by (fastforce dest:cupcake_list_complete0)
  hence "list_all is_cupcake_exp (rev es)"
    using app1 by fastforce
  hence "list_all is_cupcake_value vs" "list_all is_cupcake_value (rev vs)"
    using cupcake_list_preserve app1 rs by fastforce+
  hence "is_cupcake_exp e" "is_cupcake_all_env env'"
    using app1 cupcake_opapp_preserve by fastforce+
  hence "cupcake_evaluate_single env' e (snd bv)"
    using app1 by fastforce
  show ?case
    by rule fact+
next
  case (app3 env s1 es s2 vs)
  hence "list_all is_cupcake_exp (rev es)"
    by simp
  obtain rs where " list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs" "sequence_result rs = Rval vs"
    using app3 cupcake_list_complete0 by fastforce
  show ?case
    by (simp|rule|fact)+
next
  case (app6 env s1 es s2 err op0)
  obtain rs where " list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs" "sequence_result rs = Rerr err"
    using cupcake_list_complete0 app6 by fastforce
  show ?case
    by (simp|rule|fact)+
next
  case (mat1 env s1 e s2 v1 pes e' env' bv)
  hence "is_cupcake_exp e" and "cupcake_c_ns (c env)" and pes:"cupcake_clauses pes" and "is_cupcake_value v1"
    by (fastforce dest: is_cupcake_all_envD cupcake_single_preserve)+

  moreover obtain uu where "cupcake_match_result (c env) v1 pes Bindv = Rval (e', uu, env')"
    using cupcake_match_result_eq[OF pes,where env = env and s= s2 and v = v1 and err_v = Bindv, unfolded mat1]
    by (cases "cupcake_match_result (c env) v1 pes Bindv") auto

  ultimately have "list_all (is_cupcake_value \<circ> snd) env'" "is_cupcake_exp e'"
    using cupcake_match_result_preserve[where envC = "c env" and v = v1 and pes = pes and err_v = Bindv]
    by fastforce+
  moreover have "is_cupcake_all_env (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env)"
    apply (rule cupcake_v_update_preserve)
     apply fact
    apply (rule cupcake_nsAppend_preserve)
     apply (rule cupcake_alist_to_ns_preserve)
     apply fact
    apply (rule is_cupcake_all_envD)
    apply fact
    done

  ultimately have "cupcake_evaluate_single env e (Rval v1)"
    and "cupcake_evaluate_single (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env) e' (snd bv)"
    using mat1 by fastforce+

  show ?case
    by (rule cupcake_evaluate_single.mat1) fact+
next
  case (mat1b env s1 e s2 v1 pes err)
  hence "is_cupcake_exp e" and pes: "cupcake_clauses pes"
    by (auto dest: is_cupcake_all_envD)

  have "cupcake_evaluate_single env e (Rval v1)"
    using mat1b by fastforce
  have "cupcake_match_result (c env) v1 pes Bindv = Rerr err"
    using cupcake_match_result_eq[OF pes, where env = env and s = s2 and v = v1 and err_v = Bindv] unfolding mat1b
    by (cases "(cupcake_match_result (c env) v1 pes Bindv)") (auto simp:error_result.map_id)
  show ?case
    by (simp; rule cupcake_evaluate_single.mat1error) fact+
qed (fastforce intro: cupcake_evaluate_single.intros)+

lemma cupcake_single_complete:
  "evaluate env s e (s', res) \<Longrightarrow> is_cupcake_all_env env \<Longrightarrow> is_cupcake_exp e \<Longrightarrow> cupcake_evaluate_single env e res"
  by (fastforce dest:cupcake_single_complete0)

lemma cupcake_list_complete:
  "evaluate_list (evaluate env) s1 es res \<Longrightarrow>
    is_cupcake_all_env env \<Longrightarrow> list_all is_cupcake_exp es  \<Longrightarrow>  \<exists>rs. list_all2_shortcircuit (cupcake_evaluate_single env) es rs \<and> sequence_result rs = (snd res)"
  by (fastforce intro:cupcake_list_complete0 cupcake_single_complete evaluate_list_mono_strong)

private lemma cupcake_list_state_preserve0:
  assumes "evaluate_list (\<lambda>s e res. Big_Step_Unclocked_Single.evaluate env s e res \<and> (is_cupcake_all_env env \<longrightarrow> is_cupcake_exp e \<longrightarrow> s = fst res)) s es res"
          "list_all is_cupcake_exp es" "is_cupcake_all_env env"
        shows "s = (fst res)"
  using assms by (induction rule:evaluate_list.induct) auto

lemma cupcake_state_preserve:
  assumes "Big_Step_Unclocked_Single.evaluate env s e res" "is_cupcake_all_env env" "is_cupcake_exp e"
  shows "s = (fst res)"
  using assms proof (induction arbitrary: rule: evaluate.induct)
  case (con1 env cn es vs v s1 s2)
  hence "list_all is_cupcake_exp es"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  then show ?case
    using con1 by (fastforce dest:cupcake_list_state_preserve0)
next
  case (con3 env cn es s1 s2 err)
  hence "list_all is_cupcake_exp es"
    by (cases rule: is_cupcake_exp.cases[where x = "Con cn es"]) auto
  then show ?case
    using con3 by (fastforce dest:cupcake_list_state_preserve0)
next
  case (app1 env s1 es s2 vs env' e bv)
  have "list_all is_cupcake_exp (rev es)"
    using app1 by fastforce
  then obtain rs where rs: "list_all2_shortcircuit (cupcake_evaluate_single env) (rev es) rs" "sequence_result rs = Rval vs"
    using app1 by (fastforce dest:evaluate_list_mono_strong[THEN cupcake_list_complete])
  hence "list_all is_cupcake_value vs" "list_all is_cupcake_value (rev vs)"
    using cupcake_list_preserve app1 rs by fastforce+
  hence "is_cupcake_exp e" "is_cupcake_all_env env'"
    using app1 cupcake_opapp_preserve by fastforce+
  then show ?case
    using app1 by (fastforce dest:cupcake_list_state_preserve0)
next
  case (mat1 env s1 e s2 v1 pes e' env' bv)
  hence "is_cupcake_exp e" and "cupcake_c_ns (c env)" and pes:"cupcake_clauses pes" and "is_cupcake_value v1"
    by (fastforce dest: is_cupcake_all_envD cupcake_single_complete cupcake_single_preserve)+

  moreover obtain uu where "cupcake_match_result (c env) v1 pes Bindv = Rval (e', uu, env')"
    using cupcake_match_result_eq[OF pes,where env = env and s= s2 and v = v1 and err_v = Bindv, unfolded mat1]
    by (cases "cupcake_match_result (c env) v1 pes Bindv") auto

  ultimately have "list_all (is_cupcake_value \<circ> snd) env'" "is_cupcake_exp e'"
    using cupcake_match_result_preserve[where envC = "c env" and v = v1 and pes = pes and err_v = Bindv]
    by fastforce+
  moreover have "is_cupcake_all_env (update_v (\<lambda>_. nsAppend (alist_to_ns env') (sem_env.v env)) env)"
    apply (rule cupcake_v_update_preserve)
     apply fact
    apply (rule cupcake_nsAppend_preserve)
     apply (rule cupcake_alist_to_ns_preserve)
     apply fact
    apply (rule is_cupcake_all_envD)
    apply fact
    done
  ultimately show ?case
    using mat1 by fastforce
qed (fastforce dest:cupcake_list_state_preserve0)+

corollary cupcake_single_correct_strong:
  assumes "cupcake_evaluate_single env e res" "is_cupcake_all_env env" "is_cupcake_exp e"
  shows "Big_Step_Unclocked_Single.evaluate env s e (s,res)"
  using assms cupcake_single_correct cupcake_state_preserve by fastforce

corollary cupcake_single_complete_weak:
  "evaluate env s e (s, res) \<Longrightarrow> is_cupcake_all_env env \<Longrightarrow> is_cupcake_exp e \<Longrightarrow> cupcake_evaluate_single env e res"
  using cupcake_single_complete by fastforce

end end

hide_const (open) c

end