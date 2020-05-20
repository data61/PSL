theory Abstract_Reachability_Analysis
  imports
  Abstract_Rigorous_Numerics
  Affine_Arithmetic.Affine_Arithmetic
  "../Refinement/Refine_String"
  "../Refinement/Refine_Folds"
  Ordinary_Differential_Equations.Flow
  Runge_Kutta
begin


subsection \<open>Misc\<close>

lemma nth_concat_exists:
  "\<exists>k j. concat xs ! i = xs ! k ! j \<and> k < length xs \<and> j < length (xs ! k)"
  if "i < length (concat xs)"
  using that
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons xs xss)
  from Cons.prems consider "i < length xs"
    | "i \<ge> length xs" "i < length xs + length (concat xss)"
    by (cases "i < length xs") auto
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by (force simp: nth_append intro: exI[where x=i] exI[where x=0])
  next
    case 2
    then have "i - length xs < length (concat xss)" by arith
    with Cons.IH[of "i - length xs"]
    obtain k j where
      "concat xss ! (i - length xs) = xss ! k ! j" "k < length xss" "j < length (xss ! k)"
      by auto
    then show ?thesis
      using 2
      by (fastforce simp: nth_append nth_Cons split: nat.splits
          intro: exI[where x=j] exI[where x="k + 1"])
  qed
qed

lemma nth_concatE:
  assumes "i < length (concat xs)"
  obtains k j where "concat xs ! i = xs ! k ! j" "k < length xs" "j < length (xs ! k)"
  apply atomize_elim
  using assms nth_concat_exists by blast

lemma max_Var_floatariths_concat:
  "max_Var_floatariths (concat xs) \<le> k"
  if "\<And>x. x \<in> set xs \<Longrightarrow> max_Var_floatariths x \<le> k"
  using that max_Var_floatarith_le_max_Var_floatariths_nthI
  by (fastforce simp: in_set_conv_nth intro!: max_Var_floatariths_leI
      elim!: nth_concatE)

lemma max_Var_floatariths_list_update:
  "max_Var_floatariths (xs[xa := y]) \<le> k"
  if "max_Var_floatariths (xs) \<le> k"
  and "max_Var_floatarith y \<le> k"
  by (metis neq_le_trans linorder_le_cases list_update_beyond
      max_Var_floatariths_list_updateI that)

lemma max_Var_floatarith_0[simp]: "max_Var_floatarith 0 = 0"
  and max_Var_floatarith_1[simp]: "max_Var_floatarith 1 = 0"
  by (auto simp: zero_floatarith_def one_floatarith_def)

lemma list_set_rel_br: "\<langle>Id\<rangle>list_set_rel = br set distinct"
  by (auto simp: list_set_rel_def)

lemma
  br_list_relD:
  shows "(x, y) \<in> \<langle>br a i\<rangle>list_set_rel \<Longrightarrow> y = a ` set x \<and> list_all i x"
  apply (auto simp: list_set_rel_def br_def list_rel_def)
  subgoal premises prems for s t
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  subgoal premises prems for s t
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  subgoal premises prems for s
    using prems
    by (induction arbitrary: y rule: list.rel_induct) auto
  done

lemma sctn_rel_br: "\<langle>br a I\<rangle>sctn_rel = br (\<lambda>x. case x of Sctn n p \<Rightarrow> Sctn (a n) p) (\<lambda>x. I (normal x))"
  apply (auto simp: sctn_rel_def br_def in_rel_def[abs_def] split: sctn.splits)
  subgoal for b x1 x2 by (cases b) auto
  subgoal for a b by (cases a; cases b) auto
  done

lemma br_list_rel: "\<langle>br a I\<rangle>list_rel = br (map a) (list_all I)"
  by (fastforce simp: list_rel_def br_def list_all2_iff Ball_def in_set_zip list_all_length
      intro!: nth_equalityI)

lemma list_set_rel_brp: "\<langle>br a I\<rangle>list_set_rel = br (\<lambda>xs. a ` set xs) (\<lambda>xs. list_all I xs \<and> distinct (map a xs))"
  unfolding list_set_rel_def br_list_rel br_chain o_def o_def
  by (auto)


declare INF_cong_simp [cong] SUP_cong_simp [cong] image_cong_simp [cong del]

context auto_ll_on_open begin

definition "stable_on CX trap \<longleftrightarrow>
  (\<forall>t x0. flow0 x0 t \<in> trap \<longrightarrow> t \<in> existence_ivl0 x0 \<longrightarrow> t > 0 \<longrightarrow>
    (\<forall>s\<in>{0<..t}. flow0 x0 s \<in> CX) \<longrightarrow> x0 \<in> trap)"

lemma stable_onD:
  "\<And>t x0. flow0 x0 t \<in> trap \<Longrightarrow> t \<in> existence_ivl0 x0 \<Longrightarrow> t > 0 \<Longrightarrow>
      (\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x0 s \<in> CX) \<Longrightarrow>
      x0 \<in> trap"
  if "stable_on CX trap"
  using that by (auto simp: stable_on_def)

lemma nonneg_interval_mem_existence_ivlI[intro]:\<comment> \<open>TODO: move!\<close>
  "0 \<le> t1 \<Longrightarrow> t1 \<le> t2 \<Longrightarrow> t2 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
  "t1 \<le> t2 \<Longrightarrow> t2 \<le> 0 \<Longrightarrow> t1 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
  "t1 \<le> 0 \<Longrightarrow> 0 \<le> t2 \<Longrightarrow> t1 \<in> existence_ivl0 x0 \<Longrightarrow> t2 \<in> existence_ivl0 x0 \<Longrightarrow> {t1..t2} \<subseteq> existence_ivl0 x0"
    apply auto
  apply (drule ivl_subset_existence_ivl) apply auto
  apply (drule ivl_subset_existence_ivl') apply auto
  apply (drule segment_subset_existence_ivl, assumption)
  apply (auto simp: closed_segment_eq_real_ivl)
  done

lemma interval_subset_existence_ivl:
  "t \<in> existence_ivl0 x0 \<Longrightarrow> s \<in> existence_ivl0 x0 \<Longrightarrow> t \<le> s \<Longrightarrow> {t .. s} \<subseteq> existence_ivl0 x0"
  using segment_subset_existence_ivl[of s x0 t]
  by (auto simp: closed_segment_eq_real_ivl)

end

lemma(in c1_on_open_euclidean) diff_existence_ivl_iff[simp]:\<comment> \<open>TODO: move!, also to @{term auto_ll_on_open}\<close>
  "t2 - t1 \<in> existence_ivl0 (flow0 x0 t1) \<longleftrightarrow> t2 \<in> existence_ivl0 x0"
  if "t1 \<le> t2" "t1 \<in> existence_ivl0 x0"
  apply auto
   apply (drule existence_ivl_trans[OF that(2)])
   apply (auto intro!: diff_existence_ivl_trans that)
  done

lemma (in auto_ll_on_open) flow_trans':
  "flow0 (flow0 x0 t1) t2 = flow0 x0 (t1 + t2)"
  if "t1 \<in> existence_ivl0 x0" "t1 + t2 \<in> existence_ivl0 x0"
  apply (subst flow_trans)
  using that
  by (auto intro!: existence_ivl_trans')

context auto_ll_on_open begin

definition "flowpipe0 X0 hl hu CX X1 \<longleftrightarrow> 0 \<le> hl \<and> hl \<le> hu \<and> X0 \<subseteq> X \<and> CX \<subseteq> X \<and> X1 \<subseteq> X \<and>
  (\<forall>(x0) \<in> X0. \<forall>h \<in> {hl .. hu}. h \<in> existence_ivl0 x0 \<and> (flow0 x0 h) \<in> X1 \<and> (\<forall>h' \<in> {0 .. h}. (flow0 x0 h') \<in> CX))"

lemma flowpipe0D:
  assumes "flowpipe0 X0 hl hu CX X1"
  shows flowpipe0_safeD: "X0 \<union> CX \<union> X1 \<subseteq> X"
    and flowpipe0_nonneg: "0 \<le> hl" "hl \<le> hu"
    and flowpipe0_exivl: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> h \<in> existence_ivl0 x0"
    and flowpipe0_discrete: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> (flow0 x0 h) \<in> X1"
    and flowpipe0_cont: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0) \<in> X0 \<Longrightarrow> 0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> (flow0 x0 h') \<in> CX"
  using assms
  by (auto simp: flowpipe0_def)

lemma flowpipe0_source_subset: "flowpipe0 X0 hl hu CX X1 \<Longrightarrow> X0 \<subseteq> CX"
  apply (auto dest: bspec[where x=hl] bspec[where x=0] simp: flowpipe0_def)
  apply (drule bspec)
   apply (assumption)
  apply (drule bspec[where x=hl])
   apply auto
  apply (drule bspec[where x=0])
  by (auto simp: flow_initial_time_if)

end

subsection \<open>Options\<close>

definition [refine_vcg_def]: "precision_spec = SPEC (\<lambda>prec::nat. True)"
definition [refine_vcg_def]: "adaptive_atol_spec = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def]: "adaptive_rtol_spec = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def]: "method_spec = SPEC (\<lambda>m::nat. True)"
definition [refine_vcg_def]: "start_stepsize_spec = SPEC (\<lambda>x::real. x > 0)"
definition [refine_vcg_def]: "iterations_spec = SPEC (\<lambda>n::nat. True)"
definition [refine_vcg_def]: "halve_stepsizes_spec = SPEC (\<lambda>n::nat. True)"
definition [refine_vcg_def]: "widening_mod_spec = SPEC (\<lambda>n::nat. True)"
definition [refine_vcg_def]: "rk2_param_spec = SPEC (\<lambda>r::real. 0 < r \<and> r \<le> 1)"

typedef ode_ops = "{(ode_e::floatarith list, safe_form::form).
  open_form safe_form \<and>
  max_Var_floatariths ode_e \<le> length ode_e \<and>
  max_Var_form safe_form \<le> length ode_e}" \<comment> \<open>ode on open domain, welldefined\<close>
  by (auto intro!: exI[where x="[floatarith.Num 0]"]
      exI[where x="Less (floatarith.Num 0) (floatarith.Num 1)"])
setup_lifting type_definition_ode_ops

lift_definition ode_expression::"ode_ops \<Rightarrow> floatarith list" is fst .
lift_definition safe_form_expr::"ode_ops \<Rightarrow> form" is snd .
    \<comment> \<open>TODO: should better called it domain of definition of ODE,
                its main use is to exclude e.g. division by zero on the rhs.\<close>

lemma open_form_ode_op[intro, simp]: "open_form (safe_form_expr odo)"
  and max_Var_ode_expression: "max_Var_floatariths (ode_expression odo) \<le> length (ode_expression odo)"
  and max_Var_form_safe_form_expr: "max_Var_form (safe_form_expr odo) \<le> length (ode_expression odo)"
  by (transfer, auto)+

lift_definition (code_dt) mk_ode_ops::"floatarith list \<Rightarrow> form \<Rightarrow> ode_ops option" is
  "\<lambda>ode_e safe_form.
    if (open_form safe_form \<and> max_Var_floatariths ode_e \<le> length ode_e \<and> max_Var_form safe_form \<le> length ode_e)
    then Some (ode_e, safe_form) else None"
  by (auto simp:)

lemma
  assumes "mk_ode_ops e s = Some odo"
  shows ode_expression_mk_ode_ops: "ode_expression odo = e"
    and safe_form_expr_mk_ode_ops: "safe_form_expr odo = s"
  using assms
  by (transfer, simp split: if_splits prod.splits)+

locale ode_operations = fixes ode_ops::ode_ops begin

definition "ode_e = ode_expression ode_ops"
definition "safe_form = safe_form_expr ode_ops"

definition ode::"'a \<Rightarrow> 'a::executable_euclidean_space"
  where "ode x = eucl_of_list (interpret_floatariths ode_e (list_of_eucl x))"

definition "ode_d_expr_nth N n i =
    FDERIV_floatarith
     (FDERIV_n_floatarith (ode_e  ! i) [0..<N] (map floatarith.Var [N..<2 * N]) n) [0..<N]
         (map floatarith.Var [2 * N..<3 * N])"

definition "ode_d_expr N n =
    (FDERIV_floatariths
      (FDERIV_n_floatariths ode_e [0..<N] (map floatarith.Var [N..<2 * N]) n)
      [0..<N]
      (map floatarith.Var [2 * N..< 3 * N]))"

definition ode_d_raw::"nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a::executable_euclidean_space"
  where "ode_d_raw n x dn d =
    eucl_of_list (interpret_floatariths (ode_d_expr DIM('a) n) (list_of_eucl x @ list_of_eucl dn @ list_of_eucl d))"

definition "ode_fa_nth xs i = subst_floatarith (\<lambda>i. xs ! i) (ode_e ! i)"

definition "ode_fa xs = map (subst_floatarith (\<lambda>i. xs ! i)) ode_e"

definition "ode_d_fa_nth n xs ds i = subst_floatarith (\<lambda>i. (xs@ds@ds) ! i) (ode_d_expr_nth (length xs) n i)"

definition "ode_d_fa n xs ds = map (subst_floatarith (\<lambda>i. (xs@ds@ds) ! i)) (ode_d_expr (length xs) n)"

definition safe::"'a::executable_euclidean_space \<Rightarrow> bool"
  where "safe x \<longleftrightarrow>
    length ode_e = DIM('a) \<and>
    max_Var_floatariths ode_e \<le> DIM('a) \<and>
    open_form safe_form \<and>
    max_Var_form safe_form \<le> DIM('a) \<and>
    interpret_form safe_form (list_of_eucl x) \<and>
    isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"

definition "Csafe = Collect safe"

definition "euler_incr_fas_nth X0 h CX i = X0 ! i + h * (ode_fa_nth CX i)"

definition "euler_incr_fas X0 h CX = map (euler_incr_fas_nth X0 h CX) [0..<length X0]"

definition "euler_err_fas_nth X0 h CX i = ((h ^\<^sub>e 2) / floatarith.Num 2) * ode_d_fa_nth 0 CX (ode_fa CX) i"

definition "euler_err_fas X0 h CX = map (euler_err_fas_nth X0 h CX) [0..<length X0]"

definition "euler_fas X0 h CX =
  map (\<lambda>i. (euler_incr_fas_nth X0 h X0 i + euler_err_fas_nth X0 h CX i)) [0..<length X0] @
  euler_err_fas X0 h CX"

definition "rk2_fas_err_nth rkp x0 h cx s2 i =
  ((((h ^\<^sub>e 3 / 6) *
        (ode_d_fa_nth 1 cx (ode_fa cx) i +
         ode_d_fa_nth 0 cx (ode_d_fa 0 cx (ode_fa cx)) i)))
      - ((h ^\<^sub>e 3 * rkp / 4) *
          ode_d_fa_nth 1 (euler_incr_fas x0 (s2 * h * rkp) x0) (ode_fa x0) i))"

definition "rk2_fas_err rkp x0 h cx s2 = map (rk2_fas_err_nth rkp x0 h cx s2) [0..<length x0]"

definition "rk2_fas rkp x0 h cx s2 =
  (map (\<lambda>i.
      ((x0 ! i +
        h * ((1 - (1 / (rkp * 2))) * ode_fa_nth x0 i +
          (1 / (rkp * 2)) * ode_fa_nth (euler_incr_fas x0 (h * rkp) x0) i))
      + rk2_fas_err_nth rkp x0 h cx s2 i)) [0..<length x0]) @ rk2_fas_err rkp x0 h cx s2"


lemma ode_d_expr_nth: "i < length ode_e \<Longrightarrow> ode_d_expr_nth N n i = ode_d_expr N n ! i "
  by (auto simp: ode_d_expr_nth_def ode_d_expr_def
      FDERIV_n_floatariths_nth)

lemma length_ode_d_expr[simp]: "length (ode_d_expr f n) = length ode_e"
  by (induction n) (auto simp: ode_d_expr_def FDERIV_n_floatariths_def)

lemma ode_fa_nth: "i < length ode_e \<Longrightarrow> ode_fa xs ! i = ode_fa_nth xs i"
  by (auto simp: ode_fa_nth_def ode_fa_def)

lemma ode_d_fa_nth: "i < length ode_e \<Longrightarrow> ode_d_fa_nth n xs ds i = ode_d_fa n xs ds ! i"
  by (auto simp: ode_d_fa_def ode_d_fa_nth_def ode_d_expr_nth)

lemma length_ode_d_fa[simp]: "length (ode_d_fa n xs ds) = length ode_e"
  by (auto simp: ode_d_fa_def FDERIV_n_floatariths_def)

lemma length_rk2_fas_err[simp]: "length (rk2_fas_err rkp x0 h cx s2) = length x0"
  by (simp add: rk2_fas_err_def)

lemma length_euler_incr_fas[simp]: "length (euler_incr_fas X0 h CX) = length X0"
  by (auto simp: euler_incr_fas_def)

lemma length_euler_err_fas[simp]: "length (euler_err_fas X0 h CX) = length X0"
  by (auto simp: euler_err_fas_def)

lemma length_euler_floatarith[simp]: "length (euler_fas X0 h CX) = 2 * length X0"
  by (auto simp: euler_fas_def)

lemma length_rk2_fas[simp]: "length (rk2_fas rkp x0 h cx s2) = 2 * length x0"
  by (simp add: rk2_fas_def)

lemma open_safe: "open Csafe"
proof -
  have leq: "list_updates [0..<DIM('a)] (list_of_eucl x) (replicate DIM('a) 0) = list_of_eucl x" for x::'a
    by (auto intro!: nth_equalityI simp: list_updates_nth)
  have "(Csafe::'a set) =
    (if length ode_e = DIM('a) \<and> max_Var_floatariths ode_e \<le> DIM('a) \<and> max_Var_form safe_form \<le> DIM('a) \<and> open_form safe_form then
      {x. interpret_form safe_form (list_of_eucl x)} \<inter>
      {x. isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)}
    else {})"
    by (auto simp: Csafe_def safe_def)
  also have "open \<dots>"
    apply (auto intro!: open_Int)
    subgoal premises prems using open_form[OF prems(4), where 'a='a, of "[0..<DIM('a)]" "replicate (DIM('a)) 0"]
      by (auto simp: leq)
    subgoal
      apply (rule isFDERIV_open)
      apply (rule order_trans)
      apply assumption
      apply arith
      done
    done
  finally show ?thesis .
qed

lemma safeD:
  fixes x::"'a::executable_euclidean_space"
  assumes "x \<in> Csafe"
  shows "interpret_form safe_form (list_of_eucl x)"
    and safe_isFDERIV: "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
  using assms
  by (auto simp: Csafe_def safe_def)

lemma
  fixes x::"'a::executable_euclidean_space"
  shows safe_max_Var: "x \<in> Csafe \<Longrightarrow> max_Var_floatariths ode_e \<le> DIM('a)"
    and safe_length: "x \<in> Csafe \<Longrightarrow> length ode_e = DIM('a)"
    and safe_max_Var_form: "x \<in> Csafe \<Longrightarrow> max_Var_form safe_form \<le> DIM('a)"
  by (auto simp: safe_def Csafe_def)

lemma safe_isFDERIV_append:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<in> Csafe \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ xs)"
  apply (rule isFDERIV_max_Var_congI)
   apply (rule safe_isFDERIV)
   apply assumption
  using safe_max_Var[of x]
  by (auto simp: nth_append)

lemma ode_d_raw_0:
  assumes "x \<in> Csafe"
  shows "(ode has_derivative ode_d_raw 0 x d) (at x)"
  using assms safe_max_Var[OF assms] safe_length[OF assms]
  unfolding ode_def ode_d_raw_def ode_d_expr_def
  apply (intro interpret_floatarith_FDERIV_floatariths[THEN has_derivative_eq_rhs])
     apply (auto simp: isFDERIV_def FDERIV_n_floatariths_def safe_max_Var nth_append
      max_Var_floatariths_Max Csafe_def safe_def
      intro!: arg_cong[where f=eucl_of_list] ext interpret_floatariths_FDERIV_floatariths_cong
        freshs_floatariths_max_Var_floatarithsI 
        max_Var_floatarith_le_max_Var_floatariths[le])
  apply (rule interpret_floatariths_max_Var_cong)
  apply (auto simp: max_Var_floatariths_Max Max_gr_iff nth_append
      dest!: less_le_trans[OF _ max_Var_floatarith_DERIV_floatarith])
   apply (drule max_Var_floatariths_lessI) apply simp
  apply (auto dest!: less_le_trans[OF _ safe_max_Var[OF assms]])
   apply (drule max_Var_floatariths_lessI) apply simp
  apply (auto dest!: less_le_trans[OF _ safe_max_Var[OF assms]])
  done

lemma not_fresh_odeD: "x \<in> Csafe \<Longrightarrow> \<not>fresh_floatariths ode_e i \<Longrightarrow> i < DIM('a)" for x::"'a::executable_euclidean_space"
  using fresh_floatariths_max_Var[of ode_e i] safe_max_Var[of x] by arith

lemma safe_isnFDERIV:
  fixes x::"'a::executable_euclidean_space"
  assumes "x \<in> Csafe"
  shows "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl x @ ys) n"
  apply (rule isFDERIV_imp_isnFDERIV)
     apply (rule isFDERIV_max_Var_congI)
      apply (rule safe_isFDERIV[OF assms])
  using safe_max_Var[OF assms] safe_length[OF assms]
  by (auto simp: nth_append)

lemma safe_isnFDERIVI:
  assumes "(eucl_of_list xs::'a::executable_euclidean_space) \<in> Csafe"
  assumes [simp]: "length xs = DIM('a)" "length ds = DIM('a)"
  shows "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (xs@ds) n"
proof -
  have "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl (eucl_of_list xs::'a)@ds) n"
    by (rule safe_isnFDERIV; fact)
  also
  have "list_of_eucl (eucl_of_list xs::'a) = xs"
    by (auto intro!: nth_equalityI)
  finally show ?thesis .
qed

lemma dest_Num_eq_Some_iff[simp]: "dest_Num_fa fa = (Some x) \<longleftrightarrow> fa = floatarith.Num x"
  by (cases fa) auto

lemma ode_d_raw_Suc:
  includes floatarith_notation
  assumes "x \<in> Csafe"
  shows "((\<lambda>x. ode_d_raw n x d d) has_derivative ode_d_raw (Suc n) x d) (at x)"
proof -
  let ?shift = "\<lambda>x. floatarith.Var (if 2 * DIM('a) \<le> x \<and> x < 3 * DIM('a) then x - DIM('a) else x)"
  have subst_ode_e[simp]: "map (subst_floatarith ?shift) ode_e = ode_e"
    apply (auto intro!: nth_equalityI)
    apply (rule subst_floatarith_Var_max_Var_floatarith)
    by (auto dest!: max_Var_floatariths_lessI
        less_le_trans[OF _ safe_max_Var[OF assms]])
  have map_shift[simp]:
    "(map ?shift [DIM('a)..<2 * DIM('a)]) = (map floatarith.Var [DIM('a)..<2 * DIM('a)])"
    "(map ?shift [2 * DIM('a)..<3 * DIM('a)]) =
        (map floatarith.Var [DIM('a)..<2 * DIM('a)])"
    by (auto intro!: nth_equalityI)

  show ?thesis
    unfolding ode_def ode_d_raw_def ode_d_expr_def
    apply (rule interpret_floatarith_FDERIV_floatariths_append[THEN has_derivative_eq_rhs])
    subgoal
    proof -
      let ?shift = "\<lambda>x. if 2 * DIM('a) \<le> x \<and> x < 3 * DIM('a) then x - DIM('a) else x"
      have mv: "max_Var_floatariths
          (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
          [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])) \<le> 3 * DIM('a)"
        and mv2: "max_Var_floatariths
              (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
                [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)])) \<le> 2 * DIM('a)"
        by (auto intro!:
            max_Var_floatarith_FDERIV_floatariths[le]
            max_Var_floatarith_FDERIV_n_floatariths[le]
            safe_max_Var[OF assms, le])
      have eq: "(map (subst_floatarith (\<lambda>i. floatarith.Var (if 2 * DIM('a) \<le> i \<and> i < 3 * DIM('a) then i - DIM('a) else i)))
       ((FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
         [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])))) =
      (FDERIV_floatariths (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n)
          [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]))"
        apply (rule nth_equalityI)
         apply auto defer
        apply (subst subst_floatarith_Var_FDERIV_floatarith[where 'a='a], force, force, force)
        apply (subst subst_floatarith_Var_FDERIV_n_nth[where 'a='a], force, force, force, force)
        by (simp add: o_def)
      show ?thesis
        apply (subst isFDERIV_subst_Var_floatarith[symmetric, where s="?shift"])
        subgoal by (auto intro!: mv[le] max_Var_floatariths_fold_const_fa[le])
        subgoal by (auto simp: nth_append)
        subgoal by (auto intro!: mv[le])
        subgoal
        proof -
          have "isnFDERIV DIM('a) ode_e [0..<DIM('a)] [DIM('a)..<2*DIM('a)] (list_of_eucl x @ list_of_eucl d) (Suc (Suc n))"
            apply (rule safe_isnFDERIVI)
            using assms
            by auto
          from this[simplified, THEN conjunct1]
          show ?thesis
            unfolding eq isnFDERIV.simps
            apply (rule isFDERIV_max_Var_congI)
            apply (frule less_le_trans[OF _ mv2])
            apply (auto simp: nth_append)
            done
        qed
        done
    qed
    subgoal
      by (auto intro!: safe_max_Var[OF assms, le]
          max_Var_floatarith_FDERIV_floatariths[le]
          max_Var_floatarith_FDERIV_n_floatariths[le])
    subgoal using safe_length assms by simp
    subgoal
      apply (auto simp add: nth_append
          intro!: ext arg_cong[where f=eucl_of_list] interpret_floatariths_FDERIV_floatariths_cong
          freshs_floatariths_max_Var_floatarithsI
          safe_max_Var[OF assms, le]
          max_Var_floatarith_FDERIV_floatariths[le]
          max_Var_floatarith_FDERIV_n_floatariths[le])
      apply (rule nth_equalityI)
       apply auto
      subgoal premises prems for h i j
      proof -
        have *: "(list_of_eucl x @ list_of_eucl d @ list_of_eucl d @ list_of_eucl h) =
        (map (\<lambda>i. interpret_floatarith (?shift i)
             (list_of_eucl x @ list_of_eucl d @ list_of_eucl d @ list_of_eucl h)) [0..<4 * DIM('a)])"
          by (auto intro!: nth_equalityI simp: nth_append)
        have mv_le: "max_Var_floatarith
                (DERIV_floatarith j
                  (FDERIV_floatarith
                    (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n ! i)
                    [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]))) \<le>
                2 * DIM('a)"
          "max_Var_floatarith
     (DERIV_floatarith j
       (FDERIV_floatarith (FDERIV_n_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]) n ! i)
         [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)])))
      \<le> 3 * DIM('a)"
          by (auto intro!: prems
              safe_max_Var[OF assms, le]
              max_Var_floatarith_le_max_Var_floatariths_nth[le]
              max_Var_floatarith_DERIV_floatarith[le]
              max_Var_floatarith_FDERIV_floatarith[le]
              max_Var_floatarith_FDERIV_n_floatariths[le])
        show ?thesis
          apply (subst *)
          apply (subst interpret_floatarith_subst_floatarith[symmetric])
           apply (auto intro!: prems mv_le[le])
          apply (subst subst_floatarith_Var_DERIV_floatarith, use prems in force)
          apply (subst subst_floatarith_Var_FDERIV_floatarith[where 'a='a], force, force, force)
          apply (subst subst_floatarith_Var_FDERIV_n_nth[where 'a='a], force, force, force, use prems in force)
          apply (auto simp: o_def prems nth_append intro!: interpret_floatarith_max_Var_cong
              dest!: less_le_trans[OF _ mv_le(1)])
          done
      qed
      done
    done
qed

lift_definition ode_d::"nat \<Rightarrow> 'a::executable_euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a" is
  "\<lambda>n x dn d. if x \<in> Csafe
    then ode_d_raw n x dn d
    else 0"
  subgoal for n x dn
    apply (cases n)
    subgoal
      by (cases "x \<in> Csafe")
       (auto intro: has_derivative_bounded_linear[OF ode_d_raw_0])
    subgoal for n'
      apply (cases "x \<in> Csafe")
      subgoal
        apply (simp del: isnFDERIV.simps)
        apply (rule has_derivative_bounded_linear)
        apply (rule ode_d_raw_Suc)
        apply assumption
        done
      subgoal by (simp del: isnFDERIV.simps)
      done
    done
  done

definition "ode_d1 x = ode_d 0 x 0"

lemma ode_has_derivative:
  assumes "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
  assumes "(x::'a::executable_euclidean_space) \<in> Csafe"
  shows "(ode has_derivative ode_d1 x) (at x)"
proof -
  from assms(1) have *: "x \<in> Csafe \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl (0::'a))"
    apply (rule isFDERIV_max_Var_congI)
    using safe_max_Var[of x]
    by (auto simp: nth_append)
  show ?thesis
    unfolding ode_d1_def
    apply (transfer fixing: x)
    apply (rule ode_d_raw_0[THEN has_derivative_eq_rhs])
    by (auto intro!: * assms)
qed

lemma ode_has_derivative_safeI:
  assumes "x \<in> Csafe"
  shows "(ode has_derivative ode_d1 x) (at x)"
  using assms
  by (auto simp: safe_def Csafe_def intro!: ode_has_derivative)

lemma ode_d1_eq: "ode_d1 x = ode_d 0 x j"
  unfolding ode_d1_def
proof (transfer fixing: x j, rule ext, cases "x \<in> Csafe", clarsimp_all, goal_cases)
  case (1 d)
  have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl (0::'a)) =
    isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x @ list_of_eucl j)"
    by (rule isFDERIV_max_Var_cong)
       (auto dest!: less_le_trans[OF _ safe_max_Var[OF 1]] simp: nth_append)
  moreover
  have "interpret_floatariths (FDERIV_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)]))
     (list_of_eucl x @ list_of_eucl (0::'a) @ list_of_eucl d) =
    interpret_floatariths (FDERIV_floatariths ode_e [0..<DIM('a)] (map floatarith.Var [2 * DIM('a)..<3 * DIM('a)]))
     (list_of_eucl x @ list_of_eucl j @ list_of_eucl d)"
    using 1
    by (intro interpret_floatariths_fresh_cong)
      (auto dest!: not_fresh_FDERIV_floatariths not_fresh_odeD
        simp: nth_append)
  ultimately show ?case
    by (auto simp: ode_d_raw_def ode_d_expr_def)
qed

lemma eventually_Collect_open:
  assumes "P x" "open (Collect P)"
  shows "eventually P (at x)"
  using assms(1) assms(2) eventually_at_topological by blast

lemma ode_d_has_derivative:
  assumes "x \<in> Csafe"
  shows "((\<lambda>x. ode_d n x d d) has_derivative ode_d (Suc n) x d) (at x)"
  apply (transfer fixing: n d x)
  using assms
  apply (simp del: isnFDERIV.simps)
  apply (rule if_eventually_has_derivative)
  subgoal by (rule ode_d_raw_Suc)
  subgoal
    by (rule eventually_Collect_open)
      (auto simp: safe_max_Var[OF assms] open_safe intro!: safe_max_Var[OF assms, le])
  subgoal by (simp add: isnFDERIV.simps)
  subgoal by simp
  done

lemma ode_d1_has_derivative:
  assumes "x \<in> Csafe"
  shows "(ode_d1 has_derivative ode_d (Suc 0) x) (at x)"
proof (rule blinfun_has_derivative_componentwiseI[THEN has_derivative_eq_rhs])
  fix i::'a assume "i \<in> Basis"
  show "((\<lambda>x. blinfun_apply (ode_d1 x) i) has_derivative ode_d (Suc 0) x i) (at x)"
    unfolding ode_d1_eq[of _ i]
    apply (rule ode_d_has_derivative)
    apply fact
    done
next
  show "(\<lambda>xa. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (blinfun_apply (ode_d (Suc 0) x i) xa)) = ode_d (Suc 0) x"
    apply (rule ext)
    apply (auto intro!: ext euclidean_eqI[where 'a='a] blinfun_euclidean_eqI
        simp: blinfun.bilinear_simps inner_sum_left inner_Basis if_distrib if_distribR
        sum.delta' cong: if_cong)
    apply (rule arg_cong[where f="\<lambda>x. x \<bullet> b" for b])
  proof goal_cases
    case (1 j i b)
    from eventually_isFDERIV[where params=Nil, simplified, OF safe_isFDERIV[OF assms] order_trans[OF safe_max_Var[of x]]]
    have "\<forall>\<^sub>F x in at x. isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl x)"
      by (auto simp: assms)
    then obtain S where S: "x \<in> S" "open S" "S \<subseteq> Csafe"
      and "\<And>xa. xa \<in> S \<Longrightarrow> xa \<noteq> x \<Longrightarrow> isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl xa)"
      using assms open_safe safe_isFDERIV by auto
    then have S_FDERIV: "\<And>s. s \<in> S \<Longrightarrow>
      isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl s)"
      using safe_isFDERIV[OF assms]
      by auto
    interpret second_derivative_on_open "ode" ode_d1 "ode_d (Suc 0) x" x S
    proof standard
      fix a assume "a \<in> S"
      with S have "a \<in> Csafe" by auto
      from S_FDERIV[OF \<open>a \<in> S\<close>]
      have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl a)" by simp
      then have "isFDERIV DIM('a) [0..<DIM('a)] ode_e (list_of_eucl a)"
        apply (rule isFDERIV_max_Var_congI)
        using safe_max_Var[of x]
        by (auto simp: nth_append)
      then show "(ode has_derivative blinfun_apply (ode_d1 a)) (at a)"
        using \<open>a \<in> Csafe\<close>
        by (rule ode_has_derivative)
    next
      fix i
      interpret linear "ode_d (Suc 0) x"
      proof
        fix y z
        have 1: "((\<lambda>x. ode_d 0 x (y + z) (y + z)) has_derivative ode_d (Suc 0) x (y + z)) (at x)"
          apply (rule ode_d_has_derivative)
          apply (rule assms)
          done
        have *: "ode_d 0 x (y + z) (y + z) = ode_d 0 x y y + ode_d 0 x z z" for x
          by (auto simp: blinfun.bilinear_simps ode_d1_eq[symmetric])
        have 2: "((\<lambda>x. ode_d 0 x (y + z) (y + z)) has_derivative
            ode_d (Suc 0) x y + ode_d (Suc 0) x z) (at x)"
          apply (subst *)
          apply (rule derivative_eq_intros)
            apply (rule ode_d_has_derivative)
            apply fact
           apply (rule ode_d_has_derivative)
           apply fact
          apply (auto simp: blinfun.bilinear_simps)
          done
        from has_derivative_unique[OF 1 2]
        show "ode_d (Suc 0) x (y + z) = ode_d (Suc 0) x y + ode_d (Suc 0) x z"
          by (auto intro!: blinfun_eqI)
      next
        fix r y
        have 1: "((\<lambda>x. ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y)) has_derivative ode_d (Suc 0) x (r *\<^sub>R y)) (at x)"
          by (rule ode_d_has_derivative; fact)
        have *: "ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y) = r *\<^sub>R ode_d 0 x y y" for x
          by (auto simp: blinfun.bilinear_simps ode_d1_eq[symmetric])
        have 2: "((\<lambda>x. ode_d 0 x (r *\<^sub>R y) (r *\<^sub>R y)) has_derivative
            r *\<^sub>R ode_d (Suc 0) x y) (at x)"
          apply (subst *)
          apply (rule derivative_eq_intros)
          apply (rule ode_d_has_derivative; fact)
          apply (auto simp: blinfun.bilinear_simps)
          done
        from has_derivative_unique[OF 1 2]
        show "(ode_d (Suc 0) x (r *\<^sub>R y)) = (r *\<^sub>R ode_d (Suc 0) x y)"
          by (auto intro!: blinfun_eqI)
      qed
      show "((\<lambda>x. blinfun_apply (ode_d1 x) i) has_derivative blinfun_apply (ode_d (Suc 0) x i))
          (at x)"
        apply (subst euclidean_representation[of i, symmetric])
        apply (subst (2) euclidean_representation[of i, symmetric])
        apply (auto simp: blinfun.bilinear_simps)
        apply (rule derivative_eq_intros)
         apply (rule derivative_eq_intros)
          apply (subst_tac j = i in ode_d1_eq)
          apply (rule ode_d_has_derivative)
          apply (rule assms)
        apply force
        apply (auto simp: blinfun.bilinear_simps[symmetric]
            intro!: ext euclidean_eqI[where 'a='a] blinfun_euclidean_eqI)
        apply (rule arg_cong[where f="\<lambda>x. x \<bullet> b" for b])
        by (auto simp: sum scaleR)
    next
      show "x \<in> S" "open S" by fact+
    qed
    show ?case
      by (rule symmetric_second_derivative) fact
  qed
qed

lemma ode_d1_has_derivative_safeI:
  assumes "x \<in> Csafe"
  shows "(ode_d1 has_derivative ode_d (Suc 0) x) (at x)"
  apply (rule ode_d1_has_derivative)
  using assms by (auto simp: safe_def)

sublocale c1_on_open_euclidean ode ode_d1 Csafe
  by unfold_locales
    (auto simp: continuous_on_eq_continuous_within at_within_open[OF _ open_safe]
      intro!: derivative_eq_intros  continuous_at_imp_continuous_on open_safe
        ode_has_derivative_safeI continuous_blinfun_componentwiseI
        has_derivative_continuous ode_d1_has_derivative_safeI)

definition ivlflows ::
    "'a::executable_euclidean_space sctn set
     \<Rightarrow> (('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set
         \<Rightarrow> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set \<times> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set)
        \<Rightarrow> ('a \<times> 'a \<Rightarrow>\<^sub>L 'a) set \<Rightarrow> 'a sctn \<Rightarrow> bool"
where "ivlflows stops stopcont trap rsctn =
  (\<forall>ivl. ivl \<subseteq> \<Union>(plane_of ` stops) \<times> UNIV \<longrightarrow>
      ivl \<subseteq> (snd (stopcont ivl)) \<and>
      fst (stopcont ivl) \<subseteq> snd (stopcont ivl) \<and>
      (fst (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV \<and>
      (snd (stopcont ivl)) \<subseteq> sbelow_halfspace rsctn \<times> UNIV \<and>
      flowsto (ivl) {0..} ((snd (stopcont ivl))) ((fst (stopcont ivl)) \<union> trap))"

lift_definition ode_d2::"'a::executable_euclidean_space \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'a \<Rightarrow>\<^sub>L 'a" is "\<lambda>x.
  if x \<in> Csafe then ode_d 1 x else (\<lambda>_. 0)"
  by (auto intro!: has_derivative_bounded_linear ode_d1_has_derivative)

definition ode_na::"real \<times> _ \<Rightarrow> _" where "ode_na = (\<lambda>a. ode (snd a))"

definition ode_d_na::"real \<times> _ \<Rightarrow> (real \<times> _) \<Rightarrow>\<^sub>L _" where "ode_d_na = (\<lambda>tx. ode_d1 (snd tx) o\<^sub>L snd_blinfun)"
definition ode_d2_na::"real \<times> _ \<Rightarrow> (real \<times> _) \<Rightarrow>\<^sub>L (real \<times> _) \<Rightarrow>\<^sub>L _" where
  "ode_d2_na = (\<lambda>tx. flip_blinfun (flip_blinfun (ode_d2 (snd tx) o\<^sub>L snd_blinfun) o\<^sub>L snd_blinfun))"

definition "euler_incr_fas' D = (map fold_const_fa (euler_incr_fas (map floatarith.Var [0..<D]) (floatarith.Var (D))
      (map floatarith.Var [Suc D..<Suc (2*D)])))"
definition "euler_fas' D = (map fold_const_fa (euler_fas  (map floatarith.Var [0..<D])
    (floatarith.Var (2*D)) (map floatarith.Var [D..<2*D])))"
definition "rk2_fas' D = (map fold_const_fa (rk2_fas
    (floatarith.Var (2*D))
    (map floatarith.Var [0..<D])
    (floatarith.Var (2*D+1))
    (map floatarith.Var [D..<2*D])
    (floatarith.Var (2*D+2))))"
lemma [autoref_rules]: "(euler_incr_fas', euler_incr_fas') \<in> nat_rel \<rightarrow> fas_rel"
  "(euler_fas', euler_fas') \<in> nat_rel \<rightarrow> fas_rel"
  "(rk2_fas', rk2_fas') \<in> nat_rel \<rightarrow> fas_rel"
  by auto

definition "solve_poincare_fas n =
  (let D = length ode_e in
  map floatarith.Var [0..<D] @ concat (map (\<lambda>i \<comment> \<open>(row)\<close>. map (\<lambda>j \<comment> \<open>(column)\<close>.
    (if i \<noteq> n then floatarith.Var (D + i * D + j) - (floatarith.Var(D + n * D + j) * (ode_e ! i) / (ode_e ! n))
    else 0)
  ) [0..<D]) [0..<D]))"

end

definition "nonempty X \<longleftrightarrow> X \<noteq> {}"

definition pad_zeroes :: "nat \<Rightarrow> real list set \<Rightarrow> real list set"
  where [simp]: "pad_zeroes n X = (\<lambda>xs. xs @ replicate n (0::real)) ` X"

locale approximate_sets_ode = approximate_sets where ops = ops + ode_operations
  where ode_ops = ode_ops
  for ops:: "'b approximate_set_ops"
    and ode_ops::"ode_ops"
begin

definition "D = (length ode_e)"
definition "ode_slp = slp_of_fas ode_e"
definition "euler_slp = slp_of_fas (euler_fas' D)"
definition "euler_incr_slp = slp_of_fas (euler_incr_fas' D)"
definition "rk2_slp = slp_of_fas (rk2_fas' D)"
definition "solve_poincare_slp = map (\<lambda>i. slp_of_fas (map fold_const_fa (solve_poincare_fas i))) [0..<D]"

definition safe_set
  where "safe_set (X::'a::executable_euclidean_space set) = do {
    b1 \<leftarrow> approx_form_spec safe_form (list_of_eucl ` X);
    b2 \<leftarrow> isFDERIV_spec D [0..<D] ode_e (list_of_eucl ` X);
    RETURN (b1 \<and> b2)
  }"

definition "wd TYPE('a::executable_euclidean_space) \<longleftrightarrow> length ode_e = DIM('a)"
  \<comment> \<open>TODO: should be renamed\<close>

lemma open_safe_form[intro, simp]: "open_form safe_form"
  by (auto simp: safe_form_def)

lemma max_Var_floatariths_ode_e_le: "max_Var_floatariths ode_e \<le> D"
  and max_Var_form_safe_form_le: "max_Var_form safe_form \<le> D"
  using max_Var_ode_expression[of ode_ops] max_Var_form_safe_form_expr[of ode_ops]
  by (auto simp: ode_e_def safe_form_def D_def)

lemma wdD:
  assumes "wd TYPE('a::executable_euclidean_space)"
  shows "length ode_e = DIM('a)" "max_Var_floatariths ode_e \<le> DIM('a)"
    "max_Var_form safe_form \<le> DIM('a)"
    "ode_e \<noteq> []" "D = DIM('a)"
  using assms max_Var_floatariths_ode_e_le max_Var_form_safe_form_le
  by (auto simp: wd_def D_def safe_form_def ode_e_def)

definition "mk_safe (X::'a::executable_euclidean_space set) = do {
    ASSERT (wd TYPE('a));
    s \<leftarrow> safe_set (X:::appr_rel::'a set);
    if s then RETURN (X:::appr_rel) else SUCCEED
  }"

definition
  "mk_safe_coll X = do {
      XS \<leftarrow> (sets_of_coll X);
      FORWEAK XS (RETURN op_empty_coll)
        (\<lambda>x. do {
          s \<leftarrow> mk_safe (x);
          RETURN (mk_coll s)
        })
        (\<lambda>b c. RETURN (b \<union> c))
    }"

definition ode_set::"'a::executable_euclidean_space set \<Rightarrow> 'a set nres" where "ode_set X = do {
  _ \<leftarrow> mk_safe X;
  approx_slp_appr ode_e ode_slp (list_of_eucl ` (X))
  }"

definition
  "Picard_step X0 t0 h X = SPEC (\<lambda>R.
    case R of
      Some R \<Rightarrow>
        nonempty R \<and> compact R \<and> (R \<subseteq> Csafe) \<and>
        (\<forall>x0 \<in> X0. \<forall>h'\<in>{t0 .. t0 + h}. \<forall>phi\<in>cfuncset t0 h' X.
          x0 + integral {t0 .. h'} (\<lambda>t. ode (phi t)) \<in> R)
      | None \<Rightarrow> True)"

lemmas [refine_vcg_def] = approx_form_spec_def isFDERIV_spec_def

lemma safe_set_spec[THEN order.trans, refine_vcg]:
  assumes "wd TYPE('a::executable_euclidean_space)"
  shows "safe_set X \<le> SPEC (\<lambda>r. r \<longrightarrow> (X::'a set) \<subseteq> Csafe)"
  unfolding safe_set_def
  by (refine_vcg) (auto simp del: isnFDERIV.simps simp add: Csafe_def safe_def replicate_eq_list_of_eucl_zero wdD[OF \<open>wd _\<close>])


definition Picard_step_ivl :: "'a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> 'a set option nres" where
  "Picard_step_ivl X0 t0 h X = do {
    ASSERT (0 \<le> h);
    ASSERT (wd TYPE('a));
    let H = lv_ivl [0] [h];
    let D = DIM('a);
    let env = concat ` listset [list_of_eucl ` X0, H, list_of_eucl ` X];
    env \<leftarrow> approx_slp_spec (euler_incr_fas' D) D euler_incr_slp env;
    (case env of
      Some env \<Rightarrow>
        do {
          (l, u) \<leftarrow> op_ivl_rep_of_set ((eucl_of_list ` env::'a set));
          ASSERT (l \<le> u);
          r \<leftarrow> mk_safe ({l .. u}:::appr_rel);
          RETURN (Some (r:::appr_rel))
        }
    | None \<Rightarrow> RETURN None)
  }"

definition "do_widening_spec (i::nat) = SPEC (\<lambda>b::bool. True)"

primrec P_iter::"'a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> ('a) set \<Rightarrow> ('a) set option nres" where
  "P_iter X0 h 0 X = do {
    let _ = trace_set (ST ''P_iter failed (0)'') (Some (X));
    RETURN None
  }"
| "P_iter X0 h (Suc i) X = do {
    ASSERT (0 \<le> h);
    (l, u) \<leftarrow> op_ivl_rep_of_set (X);
    ASSERT (l \<le> u);
    ivl \<leftarrow> mk_safe ({l .. u}:::appr_rel);
    X' \<leftarrow> Picard_step_ivl X0 0 h ivl;
    (case X' of
      Some X' \<Rightarrow> do {
        (l', u') \<leftarrow> op_ivl_rep_of_set (X');
        do_widening \<leftarrow> do_widening_spec i;
        let l' = inf l' l - (if do_widening then abs (l' - l) else 0);
        let u' = sup u' u + (if do_widening then abs (u' - u) else 0);
        ASSERT (l' \<le> u');
        ivl' \<leftarrow> mk_safe {l' .. u'};
        if (l \<le> l' \<and> u' \<le> u) then RETURN (Some ivl)
        else P_iter X0 h i ivl'
      }
    | None \<Rightarrow> do {
        let _ = trace_set (ST ''P_iter failed (Picard_step)'') (Some (X));
        RETURN None
      }
    )
  }"


context fixes m::"('a::executable_euclidean_space set \<Rightarrow> real \<Rightarrow> real \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'c) option nres)"
begin

primrec cert_stepsize::
  "'a set \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (real \<times> 'a set \<times> 'a set \<times> 'c) nres"
where
  "cert_stepsize X0 h n 0 = do { let _ = trace_set (ST ''cert_stepsize failed'') (Some (X0)); SUCCEED}"
| "cert_stepsize X0 h n (Suc i) = do {
    (l, u) \<leftarrow> op_ivl_rep_of_set (X0);
    ASSERT (0 \<le> h);
    ASSERT (l \<le> u);
    ivl \<leftarrow> mk_safe {l .. u};
    ASSERT (ivl \<noteq> {});
    X' \<leftarrow> P_iter X0 h n ivl;
    case X' of Some X' \<Rightarrow>
      do {
        r1 \<leftarrow> m X0 h h X';
        r2 \<leftarrow> m X0 0 h X';
        (case (r1, r2) of
          (Some (res, err), Some (res_ivl, _)) \<Rightarrow>
            do {
              _ \<leftarrow> mk_safe res;
              _ \<leftarrow> mk_safe res_ivl;
              RETURN (h, res, res_ivl, err)
            }
        | _ \<Rightarrow>
            do {
              let _ = trace_set (ST ''cert_stepsize method failed'') (Some (X'));
              cert_stepsize X0 (h / 2) n i
            }
       )
      }
    | None \<Rightarrow> cert_stepsize X0 (h / 2) n i
    }"
end

definition "one_step_method m \<longleftrightarrow> (\<forall>X0 CX hl hu. m X0 hl hu CX \<le>
    SPEC (\<lambda>r. case r of None \<Rightarrow> True | Some (res, err) \<Rightarrow> nonempty res \<and>
      (\<forall>x0 \<in> X0. \<forall>h \<in> {hl .. hu}. x0 \<in> Csafe \<longrightarrow> h \<ge> 0 \<longrightarrow> h \<in> existence_ivl0 x0 \<longrightarrow>
      (\<forall>h' \<in> {0 .. h}. flow0 x0 h' \<in> CX) \<longrightarrow> x0 + h *\<^sub>R ode x0 \<in> CX \<longrightarrow> flow0 x0 h \<in> res)))"

definition "one_step X0 h m = do {
  CHECKs ''one_step nonneg'' (0 < h);
  its \<leftarrow> iterations_spec;
  halvs \<leftarrow> halve_stepsizes_spec;
  (h, res, res_ivl, err) \<leftarrow> cert_stepsize m X0 h its halvs;
  ASSERT (0 < h);
  RETURN (h, err, res_ivl, res)
  }"

definition [refine_vcg_def]: "default_reduce_argument_spec = SPEC (\<lambda>x::unit. True)"

definition "euler_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
   do {
    let H = lv_ivl [min hl hu] [max hl hu];
    _ \<leftarrow> mk_safe CX;
    let env = concat ` listset [list_of_eucl ` X0, list_of_eucl ` CX, H];
    env \<leftarrow> approx_slp_spec (euler_fas' DIM('a)) (2 * DIM('a)) euler_slp env;
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      let res' = take DIM('a) ` env;
      ASSERT (env_len res' DIM('a));
      let res = (eucl_of_list ` res');
      ASSUME (ncc res);
      let err' = drop DIM('a) ` take (DIM('a) * 2) ` env;
      ASSERT (env_len err' DIM('a));
      let err = (eucl_of_list ` err'::'a::executable_euclidean_space set);
      ra \<leftarrow> default_reduce_argument_spec;
      res \<leftarrow> reduce_spec ra res;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then
      do {
        res \<leftarrow> mk_safe res;
        RETURN (Some (res::'a set, err))
      } else RETURN None
    }
  })"

definition "rk2_step X0 h = one_step X0 h (\<lambda>X0 hl hu CX.
  do {
    let H = lv_ivl [min hl hu] [max hl hu];
    rps \<leftarrow> rk2_param_spec;
    let rkp = lv_ivl [rps] [rps];
    let s2 = lv_ivl [0] [1];
    _ \<leftarrow> mk_safe CX;
    ASSUME (ncc CX);
    let env = concat ` listset [list_of_eucl ` X0, list_of_eucl ` CX, rkp, H, s2];
    env \<leftarrow> approx_slp_spec (rk2_fas' DIM('a)) (2 * DIM('a)) rk2_slp env;
    case env of None \<Rightarrow> RETURN None
    | Some env \<Rightarrow> do {
      let res' = take DIM('a) ` env;
      ASSERT (env_len res' DIM('a));
      let res = (eucl_of_list ` res'::'a::executable_euclidean_space set);
      ASSUME (ncc res);
      let err' = drop DIM('a) ` take (DIM('a) * 2) ` env;
      ASSERT (env_len err' DIM('a));
      let err = (eucl_of_list ` err'::'a set);
      ra \<leftarrow> default_reduce_argument_spec;
      res \<leftarrow> reduce_spec ra res;
      ASSUME (ncc res);
      s \<leftarrow> safe_set res;
      if s then
      do {
        res \<leftarrow> mk_safe res;
        RETURN (Some (res, err))
      } else RETURN None
    }
  })"

definition "choose_step X0 h = do {
  mid \<leftarrow> method_spec;
  (if mid = 2 then rk2_step X0 h else euler_step X0 h)
}"

definition "ode_e' = (ode_e @
  mmult_fa D D D (concat (map (\<lambda>j. map (\<lambda>i.
      (FDERIV_floatarith (ode_e ! j) [0..<D] ((replicate D 0)[i := 1]))) [0..<D]) [0..<D]))
    (map floatarith.Var [D..<D + D*D]))"

definition "transversal_directions f =
  do {
    (I, S) \<leftarrow> op_ivl_rep_of_set f;
    RETURN (sum_list (map (\<lambda>b. (if I \<bullet> b \<le> 0 then if S \<bullet> b \<le> 0 then S \<bullet> b else 0 else if S \<bullet> b \<ge> 0 then I \<bullet> b else 0) *\<^sub>R b)
      (Basis_list::'a::executable_euclidean_space list)))
  }"

definition "intersects_sctns X' sctns = do {
    ASSUME (finite sctns);
    FOREACH\<^bsup>\<lambda>sctns' b. \<not>b \<longrightarrow> X' \<inter> \<Union>(plane_of ` (sctns - sctns')) = {}\<^esup> sctns
          (\<lambda>sctn b. do {b' \<leftarrow> op_intersects ( X') sctn; RETURN (b \<or> b')}) False
   }"

definition "trace_sets s X = do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel (appr_rel)); FORWEAK XS (RETURN ()) (\<lambda>X. RETURN (trace_set s (Some X))) (\<lambda>_ _. RETURN ())
  }"

definition "print_sets s X = do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel (appr_rel)); FORWEAK XS (RETURN ()) (\<lambda>X. RETURN (print_set s (X))) (\<lambda>_ _. RETURN ())
  }"

definition "intersects_sctns_spec_clw R sctns = do {
    Rs \<leftarrow> sets_of_coll ((R:::clw_rel appr_rel):::clw_rel(appr_rel));
    FORWEAK Rs (RETURN False) (\<lambda>R. intersects_sctns R sctns) (\<lambda>a b. RETURN (a \<or> b))
  }"

definition [simp]: "nonneg_reals = ({0..}::real set)"
definition [simp]: "pos_reals = ({0<..}::real set)"

definition "nonzero_component s X n = do {
    I \<leftarrow> Inf_inner X n;
    S \<leftarrow> Sup_inner X n;
    CHECKs s (I > 0 \<or> S < 0)
  }"

definition "disjoints_spec X Y = do {
    Xi \<leftarrow> ivls_of_sets X;
    IS \<leftarrow> inter_overappr (Xi:::clw_rel lvivl_rel) (Y:::clw_rel lvivl_rel);
    RETURN (is_empty IS)
  }"

definition subset_spec_plane :: "'a::executable_euclidean_space set \<Rightarrow> 'a sctn \<Rightarrow> bool nres" where
"subset_spec_plane X sctn = do {
    CHECKs ''subset_spec_plane: not in Basis'' (abs (normal sctn) \<in> set Basis_list);
    (i, s) \<leftarrow> ivl_rep X;
    RETURN (i \<bullet> normal sctn = pstn sctn \<and> s \<bullet> normal sctn = pstn sctn)
  }"

definition "op_eventually_within_sctn X sctn S = do {
    (l, u) \<leftarrow> ivl_rep S;
    (xl, xu) \<leftarrow> op_ivl_rep_of_set X;
    CHECKs (ST ''op_eventually_within_sctn: empty ivl'') (l \<le> u);
    CHECKs (ST ''op_eventually_within_sctn: not in Basis'') (abs (normal sctn) \<in> set Basis_list);
    b \<leftarrow> subset_spec_plane S sctn;
    CHECKs (ST ''op_eventually_within_sctn: subset_spec_plane 1'') b;
    b \<leftarrow> subset_spec_plane ({xl .. xu}:::lvivl_rel) sctn;
    CHECKs (ST ''op_eventually_within_sctn: subset_spec_plane 2'') b;
    RETURN (b \<and> (\<forall>i \<in> set Basis_list - {abs (normal sctn)}. l \<bullet> i < xl \<bullet> i \<and> xu \<bullet> i < u \<bullet> i))
  }"

definition [simp]: "uninfo X = X"

definition [simp]: "op_subset_ivl a b \<longleftrightarrow> a \<subseteq> b"

definition [simp]: "op_eq_ivl a b \<longleftrightarrow> a = b"

abbreviation "iplane_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>plane_rel\<rangle>inter_rel"
abbreviation "isbelow_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>sbelow_rel\<rangle>inter_rel"
abbreviation "isbelows_rel \<equiv> \<lambda>A. \<langle>A, \<langle>lv_rel\<rangle>sbelows_rel\<rangle>inter_rel"

definition [refine_vcg_def]: "get_plane X = SPEC (\<lambda>sctn. X = plane_of sctn)"

definition "tolerate_error Y E =
  do {
    (ei, es) \<leftarrow> op_ivl_rep_of_set (E);
    (yi, ys) \<leftarrow> op_ivl_rep_of_set (Y);
    let ea = sup (abs ei) (abs es);
    let ya = sup (abs yi) (abs ys);
    rtol \<leftarrow> adaptive_rtol_spec;
    atol \<leftarrow> adaptive_atol_spec;
    let errtol = sup (rtol *\<^sub>R ya) (atol *\<^sub>R sum_list Basis_list);
    RETURN (ea \<le> errtol, infnorm ea)
  }"

definition "adapt_stepsize_fa rtol m e h' =
  floatarith.Num (float_of h') *
  floatarith.Powr (floatarith.Num (float_of (rtol)) / floatarith.Num (float_of e))
    (inverse (floatarith.Num (float_of (real_of_nat m) + 1)))"

end


text \<open>With ODE operations for variational equation\<close>

locale approximate_sets_ode' = approximate_sets_ode\<comment> \<open>TODO: this prevents infinite chain of interpretations (?!)\<close>
  where ops = ops
    and ode_ops = ode_ops
  for ops :: "'b approximate_set_ops"
    and ode_ops
begin

lift_definition var_ode_ops::ode_ops is "(ode_e', safe_form)"
  using max_Var_floatariths_ode_e_le max_Var_form_safe_form_le
  by (auto simp: ode_e'_def D_def length_concat o_def sum_list_triv
      intro!: max_Var_floatariths_mmult_fa[le] max_Var_floatariths_concat max_Var_floatariths_mapI
      max_Var_floatarith_FDERIV_floatarith[le] max_Var_floatariths_list_update
      max_Var_floatariths_replicateI
      max_Var_floatarith_le_max_Var_floatariths_nth[le])

sublocale var: approximate_sets_ode where ode_ops = var_ode_ops
  by unfold_locales

end

lifting_update ode_ops.lifting
lifting_forget ode_ops.lifting

end