theory Concrete_Reachability_Analysis
imports
  Concrete_Rigorous_Numerics
  Abstract_Reachability_Analysis
begin

abbreviation "num_optns_rel \<equiv> (Id::'b numeric_options rel)"

consts i_flow1::interface
consts i_appr1::interface

abbreviation "float10_rel \<equiv> Id::(float10 \<times> float10) set"

lemma inj_on_nat_add_square: "inj_on (\<lambda>a::nat. a + a * a) S"
  by (rule strict_mono_imp_inj_on) (auto intro!: strict_monoI add_strict_mono mult_strict_mono)

lemma add_sq_eq[simp]: "a + a * a = b + b * b \<longleftrightarrow> a = b" for a b::nat
  using inj_on_nat_add_square[of UNIV, unfolded inj_on_def, rule_format, of a b]
  by auto

context includes autoref_syntax begin
lemma [autoref_rules]:
  "(precision, precision)\<in>num_optns_rel \<rightarrow> nat_rel"
  "(start_stepsize, start_stepsize)\<in>num_optns_rel \<rightarrow> rnv_rel"
  "(iterations, iterations)\<in> num_optns_rel\<rightarrow> nat_rel"
  "(halve_stepsizes, halve_stepsizes)\<in> (num_optns_rel) \<rightarrow> nat_rel"
  "(widening_mod, widening_mod)\<in> (num_optns_rel) \<rightarrow>nat_rel"
  "(rk2_param, rk2_param)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(method_id, method_id)\<in> (num_optns_rel) \<rightarrow> nat_rel"
  "(adaptive_atol, adaptive_atol)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(adaptive_rtol, adaptive_rtol)\<in> (num_optns_rel) \<rightarrow> rnv_rel"
  "(printing_fun, printing_fun)\<in> (num_optns_rel) \<rightarrow> bool_rel \<rightarrow> I \<rightarrow> unit_rel"
  "(tracing_fun, tracing_fun)\<in> (num_optns_rel) \<rightarrow> string_rel \<rightarrow> \<langle>I\<rangle>option_rel \<rightarrow> unit_rel"
  by auto

end

lemma [autoref_op_pat_def]:
  includes autoref_syntax
  shows
    "(\<lambda>xs. xs @ replicate D 0) ` X \<equiv> OP (pad_zeroes D) $ X"
    "pad_zeroes D X \<equiv> OP (pad_zeroes D) $ X"
  by simp_all

subsection \<open>Relation Implementing \<open>ode_ops\<close>: Caching \<open>slp_of\<close>-Programs.\<close>

definition "ode_slps_of ode_ops =
  (approximate_sets_ode.ode_slp ode_ops,
    approximate_sets_ode.euler_incr_slp ode_ops,
    approximate_sets_ode.euler_slp ode_ops,
    approximate_sets_ode.rk2_slp ode_ops,
    approximate_sets_ode.D ode_ops)"

definition "init_ode_ops poincare c1 ode_ops =
  (ode_ops, ode_slps_of ode_ops,
    (if poincare then Some(approximate_sets_ode.solve_poincare_slp ode_ops) else None),
    (if c1 then Some(ode_slps_of (approximate_sets_ode'.var_ode_ops ode_ops)) else None))"

definition "ode_ops_rel =
  {(init, ode_ops). init = init_ode_ops True True ode_ops
    \<or> init = init_ode_ops True False ode_ops
    \<or> init = init_ode_ops False False ode_ops }"

consts i_ode_ops::interface
lemmas [autoref_rel_intf] = REL_INTFI[of ode_ops_rel i_ode_ops]
lemmas [autoref_tyrel] = TYRELI[of ode_ops_rel]


context approximate_sets begin

unbundle autoref_syntax

lemma print_set_impl[autoref_rules]:
  shows "(printing_fun optns, print_set) \<in> bool_rel \<rightarrow> A \<rightarrow> Id"
  by auto

lemma trace_set_impl[autoref_rules]:
  shows "(tracing_fun optns, trace_set) \<in> string_rel \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> Id"
  by auto

definition "print_msg_impl s = tracing_fun optns s None"

lemma print_msg_impl[autoref_rules]:
  shows "(print_msg_impl, print_msg) \<in> string_rel \<rightarrow> unit_rel"
  unfolding print_msg_def
  by auto

definition "start_stepsize_impl = (if start_stepsize optns > 0 then start_stepsize optns else 1)"
definition "rk2_param_impl = (let rk = rk2_param optns in if rk > 0 \<and> rk \<le> 1 then rk else 1)"

lemma options_impl[autoref_rules]:
  "(RETURN (precision optns), precision_spec) \<in> \<langle>nat_rel\<rangle>nres_rel"
  "(RETURN (adaptive_atol optns), adaptive_atol_spec) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN (adaptive_rtol optns), adaptive_rtol_spec) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN (method_id optns), method_spec) \<in> \<langle>nat_rel\<rangle>nres_rel"
  "(RETURN start_stepsize_impl, start_stepsize_spec) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  "(RETURN (iterations optns), iterations_spec) \<in> \<langle>nat_rel\<rangle>nres_rel"
  "(RETURN (widening_mod optns), widening_mod_spec) \<in> \<langle>nat_rel\<rangle>nres_rel"
  "(RETURN (halve_stepsizes optns), halve_stepsizes_spec) \<in> \<langle>nat_rel\<rangle>nres_rel"
  "(RETURN (rk2_param_impl), rk2_param_spec) \<in> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def
      precision_spec_def
      adaptive_atol_spec_def
      adaptive_rtol_spec_def
      method_spec_def
      start_stepsize_spec_def start_stepsize_impl_def
      iterations_spec_def
      widening_mod_spec_def
      halve_stepsizes_spec_def
      rk2_param_spec_def rk2_param_impl_def Let_def)

sublocale approximate_sets_ode where ode_ops = ode_ops for ode_ops :: ode_ops ..

schematic_goal trace_sets_impl:
  assumes [autoref_rules]: "(si, s) \<in> string_rel" "(Xi, X) \<in> clw_rel appr_rel"
  shows "(RETURN ?f, trace_sets s X) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding trace_sets_def
  by (subst rel_ANNOT_eq[of X "clw_rel appr_rel"]) (autoref_monadic (plain))
concrete_definition trace_sets_impl for si Xi uses trace_sets_impl
lemmas [autoref_rules] = trace_sets_impl.refine[autoref_higher_order_rule]

schematic_goal print_sets_impl:
  assumes [autoref_rules]: "(si, s) \<in> bool_rel" "(Xi, X) \<in> clw_rel appr_rel"
  shows "(RETURN ?f, print_sets s X) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding print_sets_def
  by (subst rel_ANNOT_eq[of X "clw_rel appr_rel"]) (autoref_monadic (plain))
concrete_definition print_sets_impl for si Xi uses print_sets_impl
lemmas [autoref_rules] = print_sets_impl.refine[autoref_higher_order_rule]

definition "ode_slp_impl ode_ops =        (case ode_ops of (_, (x, _, _, _, _), _, _) \<Rightarrow> x)"
definition "euler_incr_slp_impl ode_ops = (case ode_ops of (_, (_, x, _, _, _), _, _) \<Rightarrow> x)"
definition "euler_slp_impl ode_ops =      (case ode_ops of (_, (_, _, x, _, _), _, _) \<Rightarrow> x)"
definition "rk2_slp_impl ode_ops =        (case ode_ops of (_, (_, _, _, x, _), _, _) \<Rightarrow> x)"
definition "D_impl ode_ops =              (case ode_ops of (_, (_, _, _, _, x), _, _) \<Rightarrow> x)"
definition "poincare_slp_impl ode_ops =   (case ode_ops of (ode_ops, (_, _, _, _, _), x, _) \<Rightarrow>
  (case x of
    None \<Rightarrow> let _ = print_msg_impl (''ODE solver not initialized: pslp missing'') in solve_poincare_slp ode_ops
  | Some pslp \<Rightarrow> pslp))"

lemma autoref_parameters[autoref_rules]:
  "(ode_slp_impl, ode_slp) \<in> ode_ops_rel \<rightarrow> slp_rel"
  "(euler_incr_slp_impl, euler_incr_slp) \<in> ode_ops_rel \<rightarrow> slp_rel"
  "(euler_slp_impl, euler_slp) \<in> ode_ops_rel \<rightarrow> slp_rel"
  "(rk2_slp_impl, rk2_slp) \<in> ode_ops_rel \<rightarrow> slp_rel"
  "(poincare_slp_impl, solve_poincare_slp) \<in> ode_ops_rel \<rightarrow> \<langle>slp_rel\<rangle>list_rel"
  "(D_impl, D) \<in> ode_ops_rel \<rightarrow> nat_rel"
  by (auto simp: ode_ops_rel_def ode_slp_impl_def euler_incr_slp_def D_impl_def init_ode_ops_def
      euler_incr_slp_impl_def euler_slp_impl_def rk2_slp_impl_def poincare_slp_impl_def
      ode_slps_of_def
      split: option.splits prod.splits)

definition "ode_e_impl = (\<lambda>(ode_ops, _). ode_expression ode_ops)"
lemma ode_e_impl[autoref_rules]: "(ode_e_impl, ode_e) \<in> ode_ops_rel \<rightarrow> fas_rel"
  by (auto simp: ode_e_impl_def ode_e_def ode_ops_rel_def init_ode_ops_def)

definition "safe_form_impl = (\<lambda>(ode_ops, _). safe_form ode_ops)"
lemma safe_form_impl[autoref_rules]: "(safe_form_impl, safe_form) \<in> ode_ops_rel \<rightarrow> Id"
  by (auto simp: safe_form_impl_def ode_ops_rel_def init_ode_ops_def)

schematic_goal safe_set_appr:
  assumes [autoref_rules]: "(Xi, X::'a::executable_euclidean_space set) \<in> appr_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of ?f, safe_set odo X) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding safe_set_def
  including art
  by autoref_monadic
concrete_definition safe_set_appr for odoi Xi uses safe_set_appr
lemmas safe_set_appr_refine[autoref_rules] = safe_set_appr.refine[autoref_higher_order_rule]

schematic_goal mk_safe_impl:
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(Ri, R) \<in> appr_rel"
  shows "(nres_of ?f, mk_safe odo (R::'a::executable_euclidean_space set)) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding mk_safe_def
  including art
  by autoref_monadic
concrete_definition mk_safe_impl for odoi Ri uses mk_safe_impl
lemmas mk_safe_impl_refine[autoref_rules] = mk_safe_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def mk_safe .

schematic_goal mk_safe_coll_impl:
  assumes [autoref_rules]: "(ISi, IS) \<in> clw_rel appr_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of (?f), mk_safe_coll odo (IS::'a::executable_euclidean_space set)) \<in> \<langle>clw_rel appr_rel\<rangle>nres_rel"
  unfolding mk_safe_coll_def
  by autoref_monadic
concrete_definition mk_safe_coll_impl for ISi uses mk_safe_coll_impl
lemmas mk_safe_coll_impl_refine[autoref_rules] = mk_safe_coll_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def mk_safe_coll .

schematic_goal ode_set_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of ?f, ode_set odo X::'a set nres) \<in> \<langle>appr_rel\<rangle>nres_rel"
  unfolding ode_set_def[abs_def]
  including art
  by autoref_monadic
concrete_definition ode_set_impl for E odoi Xi uses ode_set_impl
lemmas ode_set_impl_refine[autoref_rules] = ode_set_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def ode_set .

schematic_goal Picard_step_ivl_impl:
  fixes h::real
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(X0i,X0)\<in>appr_rel" "(hi, h) \<in> rnv_rel" "(t0i, t0) \<in> rnv_rel" "(PHIi,PHI)\<in>appr_rel"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of ?f, Picard_step_ivl odo X0 t0 h PHI::'a set option nres) \<in> \<langle>\<langle>appr_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding Picard_step_ivl_def
  including art
  by autoref_monadic
concrete_definition Picard_step_ivl_impl for X0i t0i hi PHIi uses Picard_step_ivl_impl
lemmas Picard_step_ivl_impl_refine[autoref_rules] =
  Picard_step_ivl_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def Picard_step_ivl .

lemma [autoref_rules]:
  "(abs, abs:: 'a \<Rightarrow> 'a::executable_euclidean_space) \<in> rnv_rel \<rightarrow> rnv_rel"
  by simp_all

lemma widening_spec[autoref_rules]:
  "(\<lambda>i. RETURN (widening_mod optns mod i = 0), do_widening_spec) \<in> nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: do_widening_spec_def nres_rel_def)

schematic_goal P_iter_impl:
  fixes h::real and i::nat
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  assumes [autoref_rules]: "(X0i,X0)\<in>appr_rel" "(PHIi,PHI)\<in>appr_rel"
    "(hi, h) \<in> Id" "(i_i, i) \<in> Id"
  notes [autoref_rules] = autoref_parameters
  shows "(nres_of (?f::?'r dres), P_iter odo X0 h i PHI::'a set option nres) \<in> ?R"
  unfolding P_iter_def uncurry_rec_nat APP_def
  including art
  by autoref_monadic

concrete_definition P_iter_impl for E odoi X0i hi i_i PHIi uses P_iter_impl
lemmas [autoref_rules] = P_iter_impl.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def P_iter .

schematic_goal cert_stepsize_impl_nres:
  fixes h::real and i n::nat
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]:
    "(mi, m)\<in>(appr_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> appr_rel \<rightarrow> \<langle>\<langle>appr_rel \<times>\<^sub>r R\<rangle> option_rel\<rangle>nres_rel)"
    "(X0i,X0)\<in>appr_rel" "(hi, h) \<in> rnv_rel" "(ni, n) \<in> nat_rel" "(i_i, i) \<in> nat_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(?f::?'r nres, cert_stepsize odo m (X0::'a set) h n i) \<in> ?R"
  unfolding cert_stepsize_def uncurry_rec_nat autoref_tag_defs
  by autoref
concrete_definition cert_stepsize_impl_nres for mi X0i hi ni i_i uses cert_stepsize_impl_nres
lemmas [autoref_rules] = cert_stepsize_impl_nres.refine[autoref_higher_order_rule(1)]
sublocale autoref_op_pat_def cert_stepsize .

schematic_goal cert_stepsize_impl_dres[refine_transfer]:
  assumes [refine_transfer]: "\<And>a b c d. nres_of (m a b c d) \<le> m' a b c d"
  shows "nres_of ?f \<le> cert_stepsize_impl_nres E odo m' x h n i"
  unfolding cert_stepsize_impl_nres_def
  by (refine_transfer)

concrete_definition cert_stepsize_impl_dres for E m x h n i uses cert_stepsize_impl_dres
lemmas [refine_transfer] = cert_stepsize_impl_dres.refine

lemma DIM_obvious[autoref_rules_raw]: "DIM_precond TYPE('a) DIM('a::executable_euclidean_space)"
  by (auto simp: )

lemma default_reduce_argument_spec_impl[autoref_rules]:
  "(RETURN (default_reduce optns), default_reduce_argument_spec) \<in> \<langle>reduce_argument_rel TYPE('b)\<rangle>nres_rel"
  by (auto simp: nres_rel_def default_reduce_argument_spec_def reduce_argument_rel_def
      intro!: RETURN_RES_refine)

schematic_goal euler_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes ncc: "ncc_precond TYPE('a::executable_euclidean_space)"
  notes [simp] = ncc_precondD[OF ncc]
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(hi, h) \<in> Id"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of (?f::?'r dres), euler_step odo (X::'a set) h) \<in> ?R"
  unfolding one_step_def euler_step_def[abs_def]
  including art
  by autoref_monadic
concrete_definition euler_step_impl for odoi Xi hi uses euler_step_impl
lemmas [autoref_rules] = euler_step_impl.refine[autoref_higher_order_rule(1 2)]
sublocale autoref_op_pat_def euler_step .

schematic_goal rk2_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes ncc: "ncc_precond TYPE('a::executable_euclidean_space)"
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(hi, h) \<in> Id"
  notes [simp] = ncc_precondD[OF ncc]
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of (?f::?'r dres), rk2_step odo (X::'a set) h) \<in> ?R"
  unfolding one_step_def rk2_step_def[abs_def]
  by autoref_monadic

concrete_definition rk2_step_impl for odoi Xi hi uses rk2_step_impl
lemmas [autoref_rules] = rk2_step_impl.refine[autoref_higher_order_rule (1 2)]
sublocale autoref_op_pat_def rk2_step .

schematic_goal choose_step_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules_raw]: "ncc_precond TYPE('a)"
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(hi, h) \<in> rnv_rel"
  assumes [autoref_rules]: "(odoi, odo) \<in> ode_ops_rel"
  shows "(nres_of (?f), choose_step odo (X::'a set) h) \<in> \<langle>rnv_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr_rel \<times>\<^sub>r appr_rel\<rangle>nres_rel"
  unfolding choose_step_def autoref_tag_defs if_distribR ncc_precond_def
  including art
  by autoref_monadic

concrete_definition choose_step_impl for Xi hi uses choose_step_impl
lemmas [autoref_rules] = choose_step_impl.refine[autoref_higher_order_rule (1 2)]
sublocale autoref_op_pat_def choose_step .

lemma [autoref_rules]: "(sgn, sgn) \<in> rnv_rel \<rightarrow> rnv_rel"
  by auto

schematic_goal strongest_direction_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [autoref_rules]: "(xs, x) \<in> lv_rel"
  shows "(?f, strongest_direction (x::'a)) \<in> lv_rel \<times>\<^sub>r rnv_rel"
  unfolding strongest_direction_def
  including art
  by autoref
concrete_definition strongest_direction_impl for xs uses strongest_direction_impl
lemmas [autoref_rules] = strongest_direction_impl.refine[autoref_higher_order_rule (1)]
sublocale autoref_op_pat_def strongest_direction .

lemma [autoref_rules]:
  "(real_divl, real_divl) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(truncate_down, truncate_down) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(eucl_truncate_down, eucl_truncate_down) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(truncate_up, truncate_up) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(eucl_truncate_up, eucl_truncate_up) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(max, max) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(min, min) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "((/), (/)) \<in> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  "(lfloat10, lfloat10) \<in> rnv_rel \<rightarrow> float10_rel"
  "(ufloat10, ufloat10) \<in> rnv_rel \<rightarrow> float10_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> int_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(shows_prec, shows_prec) \<in> nat_rel \<rightarrow> float10_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  "(int, int) \<in> nat_rel \<rightarrow> int_rel"
  by (auto simp: string_rel_def)

schematic_goal intersects_sctns_spec_impl:
  assumes [autoref_rules]: "(ai, a) \<in> appr_rel"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?x::_ dres), intersects_sctns (a::'a::executable_euclidean_space set) sctns) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding intersects_sctns_def
  by autoref_monadic
concrete_definition intersects_sctns_spec_impl for ai sctnsi uses intersects_sctns_spec_impl
lemmas intersects_sctns_refine[autoref_rules] = intersects_sctns_spec_impl.refine[autoref_higher_order_rule]
sublocale autoref_op_pat_def intersects_sctns .

lemma
  assumes "GEN_OP ws width_spec (A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel)"
  assumes "\<And>x. TRANSFER (RETURN (wsd x) \<le> ws x)"
  shows width_spec_invar_rel[autoref_rules]:
    "(\<lambda>(a, b). RETURN (wsd a), width_spec) \<in> \<langle>S, A\<rangle>invar_rel b \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    and width_spec_inter_rel[autoref_rules]:
    "(\<lambda>(a, b). RETURN (wsd a), width_spec) \<in> \<langle>S, A\<rangle>inter_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  using assms
  by (auto simp: nres_rel_def width_spec_def invar_rel_def dest!: fun_relD)

lemma width_spec_coll[autoref_rules]:
  assumes "GEN_OP ws width_spec (A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel)"
  assumes "\<And>x. TRANSFER (RETURN (wsd x) \<le> ws x)"
  shows "(\<lambda>xs. RETURN (sum_list (map wsd xs)), width_spec) \<in> clw_rel A \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def width_spec_def)

schematic_goal intersects_sections_spec_clw[autoref_rules]:
  assumes [autoref_rules]: "(Ri, R) \<in> clw_rel appr_rel" "(sctnsi, sctns) \<in> sctns_rel"
  shows "(nres_of (?r::_ dres), intersects_sctns_spec_clw $ R $ sctns) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding intersects_sctns_spec_clw_def
  including art
  by autoref_monadic

schematic_goal nonzero_component_impl:
  assumes [autoref_rules]: "(Xi, X) \<in> appr_rel" "(ni, n) \<in> lv_rel" "(si, s) \<in> string_rel"
  shows "(nres_of ?f, nonzero_component s X n) \<in> \<langle>unit_rel\<rangle>nres_rel"
  unfolding nonzero_component_def autoref_tag_defs
  by autoref_monadic
concrete_definition nonzero_component_impl for si Xi ni uses nonzero_component_impl
lemmas nonzero_component_impl_refine[autoref_rules] = nonzero_component_impl.refine[autoref_higher_order_rule]
lemma
  take_set_of_apprI:
  assumes "xs \<in> set_of_appr XS" "tXS = take d XS" "d < length xs"
  shows "take d xs \<in> set_of_appr tXS"
  using set_of_appr_project[OF assms(1), of "[0..<d]"]
  apply (auto simp: assms take_eq_map_nth length_set_of_appr)
  using assms(1) assms(3) length_set_of_appr take_eq_map_nth by fastforce


lemma sv_appr_rell[relator_props]: "single_valued appr_rell"
  by (auto simp: appr_rell_internal)

lemma single_valued_union:
  shows "single_valued X \<Longrightarrow> single_valued Y \<Longrightarrow> Domain X \<inter> Domain Y = {} \<Longrightarrow> single_valued (X \<union> Y)"
  by (auto simp: single_valued_def)

lemma is_empty_ivl_rel[autoref_rules]:
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(x, y). \<not> le x y, is_empty) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (auto simp: ivl_rel_def br_def set_of_ivl_def)
  subgoal premises prems for a b c d
    using le[OF prems(2, 3)] prems(1,4-) order_trans
    by auto
  subgoal premises prems for a b c d
    using le[OF prems(3,4)] prems(1,2) order_trans
    by auto
  done

lemma real_autoref[autoref_rules]:
  "(real, real) \<in> nat_rel \<rightarrow> rnv_rel"
  by auto

lemma map_option_autoref[autoref_rules]: "(map_option, map_option) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>option_rel \<rightarrow> \<langle>B\<rangle>option_rel"
  by (rule map_option_param)

lemma sv_plane_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>plane_rel)"
  by (auto simp: plane_rel_def intro!: relator_props)
lemma sv_below_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>below_rel)"
  by (auto simp: below_rel_def intro!: relator_props)
lemma sv_sbelow_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sbelow_rel)"
  by (auto simp: sbelow_rel_def intro!: relator_props)
lemma sv_sbelows_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>sbelows_rel)"
  by (auto simp: sbelows_rel_def intro!: relator_props)

lemma closed_ivl_rel[intro, simp]:  "(a, b) \<in> lvivl_rel \<Longrightarrow> closed b"
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

lemma [autoref_rules]:
  "(float_of, float_of) \<in> rnv_rel \<rightarrow> Id"
  "(approx, approx) \<in> nat_rel \<rightarrow> Id \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>option_rel"
  by auto

lemma uninfo_autoref[autoref_rules]:
  assumes "PREFER single_valued X"
  assumes "PREFER single_valued R"
  shows "(map snd, uninfo) \<in> clw_rel (\<langle>R, X\<rangle>info_rel) \<rightarrow> clw_rel X"
  using assms
  apply (auto simp: lw_rel_def Union_rel_br info_rel_def br_chain br_rel_prod elim!: single_valued_as_brE
      dest!: brD
      intro!: brI)
  apply force
  apply force
  apply force
  done

lemma [autoref_op_pat]: "(\<subseteq>) \<equiv> OP op_subset_ivl"
  by (force intro!: eq_reflection)

lemma op_subset_ivl:
  assumes le[THEN GEN_OP_D, autoref_rules, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(a, b) (c, d). le a b \<longrightarrow> le c a \<and> le b d, op_subset_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (clarsimp dest!: brD simp: ivl_rel_def)
  subgoal for a b c d e f g h
    using le[of a c b d]
    using le[of e g a c]
    using le[of b d f h]
    by (auto simp: set_of_ivl_def)
  done
concrete_definition op_subset_ivl_impl uses op_subset_ivl
lemmas [autoref_rules] = op_subset_ivl_impl.refine

lemma [autoref_op_pat]: "(=) \<equiv> OP op_eq_ivl"
  by (force intro!: eq_reflection)
lemma eq_ivl_impl:
  assumes le[THEN GEN_OP_D, autoref_rules, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>(a, b) (c, d). (le a b \<longrightarrow> le c a \<and> le b d) \<and> (le c d \<longrightarrow> le a c \<and> le d b), op_eq_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> bool_rel"
  apply (clarsimp dest!: brD simp: )
  subgoal premises prems for a b c d e f
    using op_subset_ivl[param_fo, OF assms prems(1,2)]
      op_subset_ivl[param_fo, OF assms prems(2,1)]
    by (auto simp: )
  done
concrete_definition eq_ivl_impl uses eq_ivl_impl
lemmas [autoref_rules] = eq_ivl_impl.refine

lemma [autoref_rules]: "(RETURN, get_plane) \<in> \<langle>A\<rangle>plane_rel \<rightarrow> \<langle>\<langle>A\<rangle>sctn_rel\<rangle>nres_rel"
  by (auto simp: plane_rel_def get_plane_def nres_rel_def dest!: brD intro!: RETURN_SPEC_refine)

lemma [autoref_op_pat_def del]: "get_inter p \<equiv> OP (get_inter p)" by auto

lemma inform_autoref[autoref_rules]:
  "(\<lambda>x. Max (abs ` set x), (infnorm::'a::executable_euclidean_space\<Rightarrow>real)) \<in> lv_rel \<rightarrow> rnv_rel"
  apply (auto simp: lv_rel_def br_def infnorm_def eucl_of_list_inner
      intro!: Max_eqI le_cSup_finite)
  subgoal for a y
    apply (rule exI[where x="Basis_list ! index a y"])
    by (auto simp: eucl_of_list_inner)
  subgoal
    apply (rule rev_subsetD)
     apply (rule closed_contains_Sup)
       apply (auto intro!: finite_imp_closed)
    apply (rule imageI)
    apply (auto simp: eucl_of_list_inner)
    done
  done

schematic_goal tolerate_error_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) dd"
  assumes [autoref_rules]: "(Yi, Y::'a::executable_euclidean_space set) \<in> appr_rel"
  assumes [autoref_rules]: "(Ei, E) \<in> appr_rel"
  shows "(nres_of ?r, tolerate_error Y E) \<in> \<langle>bool_rel \<times>\<^sub>r rnv_rel\<rangle>nres_rel"
  unfolding tolerate_error_def
  including art
  by autoref_monadic
concrete_definition tolerate_error_impl for dd Yi Ei uses tolerate_error_impl
lemmas tolerate_error_refine[autoref_rules] = tolerate_error_impl.refine[autoref_higher_order_rule (1)]

lemma adapt_stepsize_fa_autoref[autoref_rules]:
  "(adapt_stepsize_fa, adapt_stepsize_fa) \<in> rnv_rel \<rightarrow> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> Id"
  by auto

lemma
  list_wset_rel_finite:
  assumes "single_valued A"
  shows "(xs, X) \<in> \<langle>A\<rangle>list_wset_rel \<Longrightarrow> finite X"
  using assms
  by (auto simp: list_wset_rel_def set_rel_br dest!: brD elim!: single_valued_as_brE)

lemma [autoref_rules_raw del]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> Id"
  and [autoref_itype del]: "norm2_slp ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_of_rel (Id::(floatarith list \<times> floatarith list) set)"
  by auto

lemma [autoref_rules]: "(norm2_slp, norm2_slp) \<in> nat_rel \<rightarrow> slp_rel"
  by auto

lemma [autoref_rules_raw]: "DIM_precond TYPE(real) (Suc 0)"
  by auto
lemma [autoref_rules]:
  "(real_divr, real_divr) \<in> nat_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel \<rightarrow> rnv_rel"
  by auto

lemma length_norm2_slp_ge: "length (norm2_slp E) \<ge> 1"
  unfolding norm2_slp_def
  by (auto simp: slp_of_fas_def split: prod.splits)

lemma blinfun_of_vmatrix_scaleR: "blinfun_of_vmatrix (c *\<^sub>R e) = c *\<^sub>R blinfun_of_vmatrix e"
  including blinfun.lifting
  by transfer (vector sum_distrib_left algebra_simps matrix_vector_mult_def fun_eq_iff)

lemma closed_clw_rel_iplane_rel:
  "(xi, x) \<in> clw_rel (iplane_rel lvivl_rel) \<Longrightarrow> closed x"
  unfolding lvivl_rel_br
  by (force simp: lv_rel_def plane_rel_br inter_rel_br clw_rel_br set_of_ivl_def
      dest!: brD)

lemma closed_ivl_prod3_list_rel:
  assumes "(y, x') \<in> clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r A"
  assumes "(xa, x'a) \<in> \<langle>clw_rel (iplane_rel lvivl_rel) \<times>\<^sub>r B\<rangle>list_rel"
  shows "\<forall>(guard, ro)\<in>set (x' # x'a). closed guard"
  using assms closed_clw_rel_iplane_rel
  apply (auto simp: list_rel_def prod_rel_def in_set_conv_nth list_all2_conv_all_nth)
  apply (drule spec)
  by auto

lemma
  rec_list_fun_eq1:
  assumes "\<And>x xs a. snd (h x xs a) = snd a"
  shows "rec_list z (\<lambda>x xs r xa. f x xs xa (r (h x xs xa))) xs ab =
    rec_list (\<lambda>a. z (a, snd ab)) (\<lambda>x xs r a. f x xs (a, snd ab) (r (fst (h x xs (a, snd ab))))) xs (fst ab)"
  using assms
  unfolding split_beta'
  by (induction xs arbitrary: ab) (auto simp: split_beta')

lemma
  rec_list_fun_eq2:
  assumes "\<And>x xs a. fst (h x xs a) = fst a"
  shows "rec_list z (\<lambda>x xs r xa. f x xs xa (r (h x xs xa))) xs ab =
    rec_list (\<lambda>b. z (fst ab, b)) (\<lambda>x xs r b. f x xs (fst ab, b) (r (snd (h x xs (fst ab, b))))) xs (snd ab)"
  using assms
  unfolding split_beta'
  by (induction xs arbitrary: ab) (auto simp: split_beta')

lemma [autoref_itype]: "compact ::\<^sub>i A \<rightarrow>\<^sub>i i_bool"
  by auto

lemma lvivl_rel_compact[autoref_rules]:
  "(\<lambda>_::_\<times>_. True, compact) \<in> lvivl_rel \<rightarrow> bool_rel"
  "(\<lambda>_::(_\<times>_)list. True, compact) \<in> clw_rel lvivl_rel \<rightarrow> bool_rel"
  by (auto simp: lvivl_rel_br set_of_ivl_def lw_rel_def Union_rel_br dest!: brD)

end

end