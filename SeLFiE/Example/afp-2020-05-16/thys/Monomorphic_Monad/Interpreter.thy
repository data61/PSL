section \<open>Examples\<close>

subsection \<open>Monadic interpreter\<close>

theory Interpreter imports Monomorphic_Monad begin

declare [[show_variants]]

definition "apply" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where "apply f x = f x"

lemma apply_eq_onp: includes lifting_syntax shows "(eq_onp P ===> (=) ===> (=)) apply apply"
by(simp add: rel_fun_def eq_onp_def)

subsubsection \<open>Basic interpreter\<close>

datatype (vars: 'v) exp = Var 'v | Const int | Plus "'v exp" "'v exp" | Div "'v exp" "'v exp"

lemma rel_exp_simps [simp]:
  "rel_exp V (Var x) e' \<longleftrightarrow> (\<exists>y. e' = Var y \<and> V x y)"
  "rel_exp V (Const n) e' \<longleftrightarrow> e' = Const n"
  "rel_exp V (Plus e1 e2) e' \<longleftrightarrow> (\<exists>e1' e2'. e' = Plus e1' e2' \<and> rel_exp V e1 e1' \<and> rel_exp V e2 e2')"
  "rel_exp V (Div e1 e2) e' \<longleftrightarrow> (\<exists>e1' e2'. e' = Div e1' e2' \<and> rel_exp V e1 e1' \<and> rel_exp V e2 e2')"
  "rel_exp V e (Var y) \<longleftrightarrow> (\<exists>x. e = Var x \<and> V x y)"
  "rel_exp V e (Const n) \<longleftrightarrow> e = Const n"
  "rel_exp V e (Plus e1' e2') \<longleftrightarrow> (\<exists>e1 e2. e = Plus e1 e2 \<and> rel_exp V e1 e1' \<and> rel_exp V e2 e2')"
  "rel_exp V e (Div e1' e2') \<longleftrightarrow> (\<exists>e1 e2. e = Div e1 e2 \<and> rel_exp V e1 e1' \<and> rel_exp V e2 e2')"
by(auto elim: exp.rel_cases)

lemma finite_vars [simp]: "finite (vars e)"
by induction auto

locale exp_base = monad_fail_base return bind fail
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
begin

context fixes E :: "'v \<Rightarrow> 'm" begin
primrec eval :: "'v exp \<Rightarrow> 'm"
where
  "eval (Var x) = E x"
| "eval (Const i) = return i"
| "eval (Plus e1 e2) = bind (eval e1) (\<lambda>i. bind (eval e2) (\<lambda>j. return (i + j)))"
| "eval (Div e1 e2) = bind (eval e1) (\<lambda>i. bind (eval e2) (\<lambda>j. if j = 0 then fail else return (i div j)))"

end

context fixes \<sigma> :: "'v \<Rightarrow> 'w exp" begin
primrec subst :: "'v exp \<Rightarrow> 'w exp"
where
  "subst (Const n) = Const n"
| "subst (Var x) = \<sigma> x"
| "subst (Plus e1 e2) = Plus (subst e1) (subst e2)"
| "subst (Div e1 e2) = Div (subst e1) (subst e2)"
end

lemma compositional: "eval E (subst \<sigma> e) = eval (eval E \<circ> \<sigma>) e"
by induction simp_all

end

lemma eval_parametric [transfer_rule]:
  includes lifting_syntax shows
  "(((=) ===> M) ===> (M ===> ((=) ===> M) ===> M) ===> M ===> (V ===> M) ===> rel_exp V ===> M)
   exp_base.eval exp_base.eval"
unfolding exp_base.eval_def by transfer_prover

declare exp_base.eval.simps [code]

context exp_base begin

lemma eval_cong:
  assumes "\<And>x. x \<in> vars e \<Longrightarrow> E x = E' x"
  shows "eval E e = eval E' e"
  including lifting_syntax
proof -
  define V where "V \<equiv> eq_onp (\<lambda>x. x \<in> vars e)"
  have [transfer_rule]: "rel_exp V e e" by(rule exp.rel_refl_strong)(simp add: V_def eq_onp_def)
  have [transfer_rule]: "(V ===> (=)) E E'" using assms by(auto simp add: V_def rel_fun_def eq_onp_def)
  show ?thesis by transfer_prover
qed

end

subsubsection \<open>Memoisation\<close>

lemma case_option_apply: "case_option none some x y = case_option (none y) (\<lambda>a. some a y) x"
by(simp split: option.split)

lemma (in monad_base) bind_if2:
  "bind m (\<lambda>x. if b then t x else e x) = (if b then bind m t else bind m e)"
by simp

lemma (in monad_base) bind_case_option2:
  "bind m (\<lambda>x. case_option (none x) (some x) y) = case_option (bind m none) (\<lambda>a. bind m (\<lambda>x. some x a)) y"
by(simp split: option.split)

locale memoization_base = monad_state_base return bind get put
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and get :: "('k \<rightharpoonup> 'a, 'm) get"
  and put :: "('k \<rightharpoonup> 'a, 'm) put"
begin

definition memo :: "('k \<Rightarrow> 'm) \<Rightarrow> 'k \<Rightarrow> 'm"
where
  "memo f x = 
   get (\<lambda>table. 
   case table x of Some y \<Rightarrow> return y 
   | None \<Rightarrow> bind (f x) (\<lambda>y. update (\<lambda>m. m(x \<mapsto> y)) (return y)))"

lemma memo_cong [cong, fundef_cong]: "\<lbrakk> x = y; f y = g y \<rbrakk> \<Longrightarrow> memo f x = memo g y"
by(simp add: memo_def cong del: option.case_cong_weak)

end

declare memoization_base.memo_def [code]

locale memoization = memoization_base return bind get put + monad_state return bind get put
  for return :: "('a, 'm) return"
  and bind :: "('a, 'm) bind"
  and get :: "('k \<rightharpoonup> 'a, 'm) get"
  and put :: "('k \<rightharpoonup> 'a, 'm) put"
begin

lemma memo_idem: "memo (memo f) x = memo f x"
proof -
  have "memo (memo f) x = get 
    (\<lambda>table. case table x of 
       None \<Rightarrow> get (\<lambda>table'. bind (case table' x of None \<Rightarrow> bind (f x) (\<lambda>y. update (\<lambda>m. m(x \<mapsto> y)) (return y))
                                                | Some x \<Rightarrow> return x)
                             (\<lambda>y. update (\<lambda>m. m ++ [x \<mapsto> y]) (return y)))
      | Some y \<Rightarrow> get (\<lambda>_. return y))"
    by(simp add: memo_def get_const bind_get cong del: option.case_cong_weak)
  also have "\<dots> = memo f x"
    by(simp add: option.case_distrib[where h="get", symmetric] get_get case_option_apply bind_assoc update_update bind_update return_bind o_def memo_def cong: option.case_cong)
  finally show ?thesis .
qed

lemma memo_same:
  "bind (memo f x) (\<lambda>a. bind (memo f x) (g a)) = bind (memo f x) (\<lambda>a. g a a)"
apply(simp cong: option.case_cong add: memo_def bind_get option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc bind_update return_bind update_get o_def get_const)
apply(subst (3) get_const[symmetric])
apply(subst option.case_distrib[where h=get, symmetric])
apply(subst get_get)
apply(simp add: case_option_apply cong: option.case_cong)
done

lemma memo_commute:
  assumes f_bind: "\<And>m x g. bind m (\<lambda>a. bind (f x) (g a)) = bind (f x) (\<lambda>b. bind m (\<lambda>a. g a b))"
    and f_get: "\<And>x g. get (\<lambda>s. bind (f x) (g s)) = bind (f x) (\<lambda>a. get (\<lambda>s. g s a))"
  shows "bind (memo f x) (\<lambda>a. bind (memo f y) (g a)) = bind (memo f y) (\<lambda>b. bind (memo f x) (\<lambda>a. g a b))"
proof -
  note option.case_cong[cong]
  have update_f: "update F (bind (f x) g) = bind (f x) (\<lambda>a. update F (g a))" for F x g
  proof -
    fix UU
    have "update F (bind (f x) g) = bind (update F (return UU)) (\<lambda>_. bind (f x) g)"
      by(simp add: bind_update return_bind)
    also have "\<dots> = bind (f x) (\<lambda>a. bind (update F (return UU)) (\<lambda>_. g a))"
      by(rule f_bind) 
    also have "\<dots> = bind (f x) (\<lambda>a. update F (g a))"
      by(simp add: bind_update return_bind)
    finally show ?thesis .
  qed
  show ?thesis
    apply(clarsimp simp add: memo_def bind_get option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc bind_update return_bind update_get o_def f_get[symmetric] option.case_distrib[where h="get", symmetric] get_get case_option_apply if_distrib[where f="case_option _ _"] if_distrib[where f="update _"] option.case_distrib[where h="update _"] update_f update_update cong: if_cong)
    apply(clarsimp intro!: arg_cong[where f="get"] ext split!: option.split simp add: bind_if2)
    apply(subst f_bind)
    apply(simp add: fun_upd_twist)
    done
qed

end

subsubsection \<open>Probabilistic interpreter\<close>

locale memo_exp_base =
  exp_base return bind fail +
  memoization_base return bind get put
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
begin

definition lookup :: "'v \<Rightarrow> 'm"
where "lookup x = get (\<lambda>s. case s x of None \<Rightarrow> fail | Some y \<Rightarrow> return y)"

lemma lookup_alt_def: "lookup x = get (\<lambda>s. case apply s x of None \<Rightarrow> fail | Some y \<Rightarrow> return y)"
by(simp add: apply_def lookup_def)

end

locale prob_exp_base =
  memo_exp_base return bind fail get put +
  monad_prob_base return bind sample
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and sample :: "(int, 'm) sample"
begin

definition sample_var :: "('v \<Rightarrow> int pmf) \<Rightarrow> 'v \<Rightarrow> 'm"
where "sample_var X x = sample (X x) return"

definition lazy :: "('v \<Rightarrow> int pmf) \<Rightarrow> 'v exp \<Rightarrow> 'm"
where "lazy X \<equiv> eval (memo (sample_var X))"

definition sample_vars :: "('v \<Rightarrow> int pmf) \<Rightarrow> 'v set \<Rightarrow> 'm \<Rightarrow> 'm"
where "sample_vars X A m = Finite_Set.fold (\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m)) m A"

definition eager :: "('v \<Rightarrow> int pmf) \<Rightarrow> 'v exp \<Rightarrow> 'm" where
  "eager p e = sample_vars p (vars e) (eval lookup e)"

end

lemmas [code] =
  prob_exp_base.sample_var_def
  prob_exp_base.lazy_def
  prob_exp_base.eager_def

locale prob_exp = prob_exp_base return bind fail get put sample + 
  memoization return bind get put +
  monad_state_prob return bind get put sample +
  monad_fail return bind fail
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and sample :: "(int, 'm) sample"
begin

lemma comp_fun_commute_sample_var: "comp_fun_commute (\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m))"
by unfold_locales(auto intro!: memo_commute simp add: fun_eq_iff sample_var_def bind_sample1 bind_sample2 return_bind sample_get)

interpretation sample_var: comp_fun_commute "\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m)"
  rewrites "\<And>X m A. Finite_Set.fold (\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m)) m A \<equiv> sample_vars X A m"
  for X
by(rule comp_fun_commute_sample_var)(simp add: sample_vars_def)

lemma comp_fun_idem_sample_var: "comp_fun_idem (\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m))"
by unfold_locales(simp add: fun_eq_iff memo_same)

interpretation sample_var: comp_fun_idem "\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m)"
  rewrites "\<And>X m A. Finite_Set.fold (\<lambda>x m. bind (memo (sample_var X) x) (\<lambda>_. m)) m A \<equiv> sample_vars X A m"
  for X
  by(rule comp_fun_idem_sample_var)(simp add: sample_vars_def)

lemma sample_vars_empty [simp]: "sample_vars X {} m = m"
by(simp add: sample_vars_def)

lemma sample_vars_insert: 
  "finite A \<Longrightarrow> sample_vars X (insert x A) m = bind (memo (sample_var X) x) (\<lambda>_. sample_vars X A m)"
by(fact sample_var.fold_insert_idem)

lemma sample_vars_insert2: 
  "finite A \<Longrightarrow> sample_vars X (insert x A) m = sample_vars X A (bind (memo (sample_var X) x) (\<lambda>_. m))"
by(fact sample_var.fold_insert_idem2)

lemma sample_vars_union:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> sample_vars X (A \<union> B) m = sample_vars X A (sample_vars X B m)"
by(subst Un_commute)(rule sample_var.fold_set_union)

lemma memo_lookup:
  "bind (memo f x) (\<lambda>i. bind (lookup x) (g i)) = bind (memo f x) (\<lambda>i. g i i)"
apply(simp cong del: option.case_cong_weak add: lookup_def memo_def bind_get option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc bind_update return_bind update_get o_def get_const)
apply(subst (3) get_const[symmetric])
apply(subst option.case_distrib[where h=get, symmetric])
apply(simp add: get_get case_option_apply cong: option.case_cong)
done

lemma lazy_eq_eager:
  assumes put_fail: "\<And>s. put s fail = fail"
  shows "lazy X e = eager X e"
proof -
  note option.case_cong [cong]
  have sample_var_get: "bind (sample_var X x) (\<lambda>i. get (f i)) = get (\<lambda>s. bind (sample_var X x) (\<lambda>i. f i s))" for x f
    by(simp add: sample_var_def bind_sample1 return_bind sample_get)
  have update_fail [simp]: "update f fail = fail" for f
    by(simp add: update_def put_fail get_const)
  have sample_vars_fail: "sample_vars X A fail = fail" if "finite A" for A using that
    by induction(simp_all add: memo_def bind_get option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc bind_update return_bind sample_var_def bind_sample1 sample_const case_option_collapse get_const cong del: option.case_cong_weak)
  have sample_var_const: "bind (sample_var X x) (\<lambda>_. m) = m" for x m
    by(simp add: sample_var_def bind_sample1 return_bind sample_const)
  have sample_var_lookup_same: "bind (memo (sample_var X) x) (\<lambda>i. bind (lookup x) (f i)) = bind (memo (sample_var X) x) (\<lambda>i. f i i)" for x f
    by(simp add: lookup_def bind_get memo_def option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc bind_update return_bind update_get sample_var_get option.case_distrib[where h=get, symmetric] get_get case_option_apply)
  have sample_var_lookup_other: "bind (memo (sample_var X) y) (\<lambda>i. bind (lookup x) (f i)) = bind (lookup x) (\<lambda>j. bind (memo (sample_var X) y) (\<lambda>i. f i j))"
    if "x \<noteq> y" for x y f using that
    apply(simp add: lookup_def memo_def bind_get option.case_distrib[where h="\<lambda>x. bind x _"] bind_assoc return_bind bind_update update_get sample_var_get fail_bind option.case_distrib[where h=get, symmetric] get_get case_option_apply)
    apply(subst (13) get_const[symmetric])
    apply(clarsimp simp add: option.case_distrib[where h=get, symmetric] get_get case_option_apply fun_eq_iff sample_var_const intro!: arg_cong[where f=get] split: option.split)
    done
  have sample_vars_lookup: "sample_vars X V (bind (lookup x) f) = bind (lookup x) (\<lambda>i. sample_vars X V (f i))" 
    if "finite V" "x \<notin> V" for V x f using that
    by(induction)(auto simp add: sample_var_lookup_other bind_return)

  have lazy_sample_vars: "sample_vars X V (bind (lazy X e) f) = bind (lazy X e) (\<lambda>i. sample_vars X V (f i))"
    if "finite V" for f e V using that unfolding lazy_def
  proof(induction e arbitrary: f)
    case (Var x)
    have "bind (memo (sample_var X) x) (\<lambda>i. sample_vars X V (f i)) = sample_vars X V (bind (memo (sample_var X) x) f)" (is "?lhs V = ?rhs V")
      using Var
    proof(cases "x \<in> V")
      { fix V
        assume False: "x \<notin> V" and fin: "finite V"
        have "?lhs V = bind (memo (sample_var X) x) (\<lambda>_. bind (lookup x) (\<lambda>i. sample_vars X V (f i)))"
          by(simp add: sample_var_lookup_same)
        also have "\<dots> = bind (memo (sample_var X) x) (\<lambda>_. sample_vars X V (bind (lookup x) f))"
          using fin False by(simp add: sample_vars_lookup)
        also have "\<dots> = sample_vars X (insert x V) (bind (lookup x) f)" using fin
          by(simp add: sample_vars_insert)
        also have "\<dots> = sample_vars X V (bind (memo (sample_var X) x) (\<lambda>_. bind (lookup x) f))" using fin
          by(simp only: sample_vars_insert2)
        also have "\<dots> = ?rhs V"
          by(simp add: sample_var_lookup_same)
        finally show "?lhs V = ?rhs V" . }
      note False = this

      case True
      hence V: "V = insert x (V - {x})" by auto
      have "?lhs V = bind (memo (sample_var X) x) (\<lambda>i. bind (memo (sample_var X) x) (\<lambda>_. sample_vars X (V - {x}) (f i)))"
        using Var by(subst V)(simp add: sample_vars_insert del: Diff_insert0 insert_Diff_single) 
      also have "\<dots> = bind (memo (sample_var X) x) (\<lambda>_. bind (memo (sample_var X) x) (\<lambda>i. sample_vars X (V - {x}) (f i)))"
        by(simp add: memo_same)
      also have "\<dots> = bind (memo (sample_var X) x) (\<lambda>_. sample_vars X (V - {x}) (bind (memo (sample_var X) x) f))"
        using Var by(subst False)(simp_all)
      also have "\<dots> = ?rhs V" using Var 
        by(rewrite in "_ = \<hole>" V)(simp add: sample_vars_insert del: Diff_insert0 insert_Diff_single)
      finally show ?thesis .
    qed
    then show ?case by simp
  next
    case (Const x)
    then show ?case by(simp add: return_bind)
  next
    case (Plus e1 e2)
    then show ?case
      by(simp add: bind_assoc return_bind)
  next
    case (Div e1 e2)
    then show ?case
      apply(simp add: bind_assoc if_distrib[where f="\<lambda>x. bind x _"] fail_bind return_bind cong del: if_weak_cong)
      apply(subst (6) sample_vars_fail[OF \<open>finite V\<close>, symmetric])
      apply(simp add: if_distrib[where f="sample_vars _ _", symmetric])
      done
  qed

  define V where "V \<equiv> vars e"
  then have "vars e \<subseteq> V" "finite V" by simp_all
  then have "sample_vars X V (bind (eval lookup e) f) = sample_vars X V (bind (lazy X e) f)" for f
    unfolding lazy_def
  proof(induction e arbitrary: f)
    case (Var x)
    then have V: "V = insert x (V - {x})" by auto
    show ?case using Var
      apply(subst (1 2) V)
      apply(subst (1 2) sample_vars_insert2)
      apply(simp_all add: memo_same memo_lookup)
      done
  qed(simp_all add: bind_assoc lazy_sample_vars[unfolded lazy_def])
  note this[of return, unfolded V_def]
  also have "sample_vars X (vars e) (bind (lazy X e) f) = bind (lazy X e) f" for f unfolding lazy_def
  proof(induction e arbitrary: f)
    { case Var   show ?case by(simp add: memo_same bind_return) }
    { case Const show ?case by(simp add: bind_return) }
    { case Plus  show ?case
        by(simp add: bind_assoc sample_vars_union lazy_sample_vars[unfolded lazy_def] Plus.IH) }
    { case Div   show ?case
        by(simp add: bind_assoc sample_vars_union lazy_sample_vars[unfolded lazy_def] Div.IH) }
  qed
  finally show ?thesis by(simp add: bind_return V_def eager_def)
qed

end

interpretation F: exp_base
  "return_option return_id"
  "bind_option return_id bind_id"
  "fail_option return_id"
.

value [code] "F.eval (\<lambda>x. return_option return_id 5) (Plus (Var ''a'') (Const 7))"

subsubsection \<open>Moving between monad instances\<close>

global_interpretation SFI: memo_exp_base
  "return_state (return_option (return_id :: ((int \<times> ('b \<rightharpoonup> int)) option, _) return))"
  "bind_state (bind_option return_id bind_id)"
  "fail_state (fail_option return_id)"
  "get_state"
  "put_state"
  defines SFI_lookup = SFI.lookup 
.

interpretation SFI: memoization
  "return_state (return_option (return_id :: ((int \<times> ('b \<rightharpoonup> int)) option, _) return))"
  "bind_state (bind_option return_id bind_id)"
  "get_state"
  "put_state"
..

global_interpretation SFP: prob_exp
  "return_state (return_option return_pmf)"
  "bind_state (bind_option return_pmf bind_pmf)"
  "fail_state (fail_option return_pmf)"
  "get_state"
  "put_state"
  "sample_state (sample_option bind_pmf)"
  defines SFP_lookup = SFP.lookup
..

interpretation FSP: prob_exp
  "return_option (return_state (return_pmf :: (int option \<times> ('b \<rightharpoonup> int), _) return))"
  "bind_option (return_state return_pmf) (bind_state bind_pmf)"
  "fail_option (return_state return_pmf)"
  "get_option get_state"
  "put_option put_state"
  "sample_option (sample_state bind_pmf)"
..


locale reader_exp_base = exp_base return bind fail + monad_reader_base return bind ask
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and ask :: "('v \<rightharpoonup> int, 'm) ask"
begin

definition lookup :: "'v \<Rightarrow> 'm" where
  "lookup x = ask (\<lambda>s. case s x of None \<Rightarrow> fail | Some y \<Rightarrow> return y)"

lemma lookup_alt_def:
  "lookup x = ask (\<lambda>s. case apply s x of None \<Rightarrow> fail | Some y \<Rightarrow> return y)"
by(simp add: lookup_def apply_def)

end


locale exp_commute = exp_base return bind fail + monad_commute return bind
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
begin

lemma eval_reverse:
  "eval E (Var x) = E x"
  "eval E (Const i) = return i"
  "eval E (Plus e1 e2) = bind (eval E e2) (\<lambda>j. bind (eval E e1) (\<lambda>i. return (i + j)))"
  "eval E (Div e1 e2) = bind (eval E e2) (\<lambda>j. bind (eval E e1) (\<lambda>i. if j = 0 then fail else return (i div j)))"
by(simp; rule bind_commute)+

end

global_interpretation RFI: reader_exp_base 
  "return_env (return_option return_id)"
  "bind_env (bind_option return_id bind_id)"
  "fail_env (fail_option return_id)"
  ask_env
  defines RFI_lookup = RFI.lookup
.

context includes lifting_syntax begin

lemma cr_id_prob_eval:
  notes [transfer_rule] = cr_id_prob_transfer shows
  "rel_stateT (=) (rel_optionT (cr_id_prob (=)))
     (SFI.eval SFI_lookup e)
     (SFP.eval SFP_lookup e)"
unfolding SFP.lookup_def SFI.lookup_def by transfer_prover

lemma cr_envT_stateT_lookup':
  notes [transfer_rule] = cr_envT_stateT_transfer apply_eq_onp shows
  "((=) ===> cr_envT_stateT X (rel_optionT (rel_id (rel_option (cr_prod1 X (=))))))
   RFI_lookup SFI_lookup"
unfolding RFI.lookup_alt_def SFI.lookup_alt_def by transfer_prover

lemma cr_envT_stateT_eval':
  notes [transfer_rule] = cr_envT_stateT_transfer cr_envT_stateT_lookup' shows
  "((=) ===> cr_envT_stateT X (rel_optionT (rel_id (rel_option (cr_prod1 X (=))))))
  (RFI.eval RFI_lookup) (SFI.eval SFI_lookup)"
by transfer_prover

lemma cr_envT_stateT_lookup [cr_envT_stateT_transfer]:
  notes [transfer_rule] = cr_id_prob_transfer cr_envT_stateT_transfer apply_eq_onp shows
  "((=) ===> cr_envT_stateT X (rel_optionT (cr_id_prob (rel_option (cr_prod1 X (=))))))
   RFI_lookup SFP_lookup"
unfolding RFI.lookup_alt_def SFP.lookup_alt_def by transfer_prover

lemma cr_envT_stateT_eval [cr_envT_stateT_transfer]:
  notes [transfer_rule] = cr_id_prob_transfer cr_envT_stateT_transfer shows
  "((=) ===> cr_envT_stateT X (rel_optionT (cr_id_prob (rel_option (cr_prod1 X (=))))))
  (RFI.eval RFI_lookup) (SFP.eval SFP_lookup)"
by transfer_prover

lemma prob_eval_lookup:
  "run_state (SFP.eval SFP_lookup e) E = 
   map_optionT (return_pmf \<circ> map_option (\<lambda>b. (b, E)) \<circ> extract) (run_env (RFI.eval RFI_lookup e) E)"
by(rule cr_envT_stateT_eval[of E, THEN rel_funD, OF refl, unfolded eq_alt, unfolded cr_prod1_Grp option.rel_Grp cr_id_prob_Grp rel_optionT_Grp, simplified, THEN cr_envT_stateTD, unfolded BNF_Def.Grp_def, THEN conjunct1])

end

subsection \<open>Non-deterministic interpreter\<close>

locale choose_base = monad_altc_base return bind altc
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and altc :: "(int, 'm) altc"
begin

definition choose_var :: "('v \<Rightarrow> int cset) \<Rightarrow> 'v \<Rightarrow> 'm" where
  "choose_var X x = altc (X x) return"

end

declare choose_base.choose_var_def [code]

locale nondet_exp_base = choose_base return bind altc
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and altc :: "(int, 'm) altc"
begin

sublocale memo_exp_base return bind fail get put .

definition lazy where "lazy X = eval (memo (choose_var X))"

end

locale nondet_exp =
  monad_state_altc return bind get put altc +
  nondet_exp_base return bind get put altc + 
  memoization return bind get put
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and altc :: "(int, 'm) altc"
begin

sublocale monad_fail return bind fail by(rule monad_fail)

end

global_interpretation NI: cset_nondetM return_id bind_id merge_id merge_id 
  defines NI_return = NI.return_nondet
    and NI_bind = NI.bind_nondet
    and NI_altc = NI.altc_nondet
  ..

global_interpretation SNI: nondet_exp
  "return_state NI_return"
  "bind_state NI_bind"
  "get_state"
  "put_state"
  "altc_state NI_altc"
  defines SNI_lazy = SNI.lazy
  ..

value "run_state (SNI_lazy (\<lambda>x. cinsert 0 (cinsert 1 cempty)) (Div (Const 2) (Var (CHR ''x'')))) Map.empty"

locale nondet_fail_exp_base = choose_base return bind altc
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and altc :: "(int, 'm) altc"
begin

sublocale memo_exp_base return bind fail get put .

definition lazy where "lazy X = eval (memo (choose_var X))"

end

locale nondet_fail_exp =
  monad_state_altc return bind get put altc +
  nondet_fail_exp_base return bind fail get put altc + 
  memoization return bind get put +
  fail: monad_fail return bind fail
  for return :: "(int, 'm) return"
  and bind :: "(int, 'm) bind"
  and fail :: "'m fail"
  and get :: "('v \<rightharpoonup> int, 'm) get"
  and put :: "('v \<rightharpoonup> int, 'm) put"
  and altc :: "(int, 'm) altc"

global_interpretation SFNI: nondet_fail_exp
  "return_state (return_option NI_return)"
  "bind_state (bind_option NI_return NI_bind)"
  "fail_state (fail_option NI_return)"
  "get_state"
  "put_state"
  "altc_state (altc_option NI_altc)"
  defines SFNI_lazy = SFNI.lazy
  ..

value "run_state (SFP.lazy (\<lambda>x. pmf_of_set {0, 1}) (Div (Const 2) (Var (CHR ''x'')))) Map.empty"

value "run_state (SFNI_lazy (\<lambda>x. cinsert 0 (cinsert 1 cempty)) (Div (Const 2) (Var (CHR ''x'')))) Map.empty"

end
