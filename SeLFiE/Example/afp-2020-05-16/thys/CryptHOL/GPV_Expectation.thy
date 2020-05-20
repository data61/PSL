(* Title: GPV_Expectation.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Expectation transformer semantics\<close>

theory GPV_Expectation imports
  Generative_Probabilistic_Value
begin

lemma le_enn2realI: "\<lbrakk> ennreal x \<le> y; y = \<top> \<Longrightarrow> x \<le> 0 \<rbrakk> \<Longrightarrow> x \<le> enn2real y"
by(cases y) simp_all

lemma enn2real_leD: "\<lbrakk> enn2real x < y; x \<noteq> \<top> \<rbrakk> \<Longrightarrow> x < ennreal y"
by(cases x)(simp_all add: ennreal_lessI)

lemma ennreal_mult_le_self2I: "\<lbrakk> y > 0 \<Longrightarrow> x \<le> 1 \<rbrakk> \<Longrightarrow> x * y \<le> y" for x y :: ennreal
apply(cases x; cases y)
apply(auto simp add: top_unique ennreal_top_mult ennreal_mult[symmetric] intro: ccontr)
using mult_left_le_one_le by force

lemma ennreal_leI: "x \<le> enn2real y \<Longrightarrow> ennreal x \<le> y"
by(cases y) simp_all

lemma enn2real_INF: "\<lbrakk> A \<noteq> {}; \<forall>x\<in>A. f x < \<top> \<rbrakk> \<Longrightarrow> enn2real (INF x\<in>A. f x) = (INF x\<in>A. enn2real (f x))"
apply(rule antisym)
 apply(rule cINF_greatest)
  apply simp
 apply(rule enn2real_mono)
  apply(erule INF_lower)
 apply simp
apply(rule le_enn2realI)
 apply simp_all
apply(rule INF_greatest)
apply(rule ennreal_leI)
apply(rule cINF_lower)
apply(rule bdd_belowI[where m=0])
apply auto
done

lemma monotone_times_ennreal1: "monotone (\<le>) (\<le>) (\<lambda>x. x * y :: ennreal)"
by(auto intro!: monotoneI mult_right_mono)

lemma monotone_times_ennreal2: "monotone (\<le>) (\<le>) (\<lambda>x. y * x :: ennreal)"
by(auto intro!: monotoneI mult_left_mono)

lemma mono2mono_times_ennreal[THEN lfp.mono2mono2, cont_intro, simp]:
  shows monotone_times_ennreal: "monotone (rel_prod (\<le>) (\<le>)) (\<le>) (\<lambda>(x, y). x * y :: ennreal)"
by(simp add: monotone_times_ennreal1 monotone_times_ennreal2)

lemma mcont_times_ennreal1: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. x * y :: ennreal)"
by(auto intro!: mcontI contI simp add: SUP_mult_left_ennreal[symmetric])

lemma mcont_times_ennreal2: "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. y * x :: ennreal)"
by(subst mult.commute)(rule mcont_times_ennreal1)

lemma mcont2mcont_times_ennreal [cont_intro, simp]:
  "\<lbrakk> mcont lub ord Sup (\<le>) (\<lambda>x. f x);
    mcont lub ord Sup (\<le>) (\<lambda>x. g x) \<rbrakk>
  \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. f x * g x :: ennreal)"
by(best intro: ccpo.mcont2mcont'[OF complete_lattice_ccpo] mcont_times_ennreal1 mcont_times_ennreal2 ccpo.mcont_const[OF complete_lattice_ccpo])

lemma ereal_INF_cmult: "0 < c \<Longrightarrow> (INF i\<in>I. c * f i) = ereal c * (INF i\<in>I. f i)"
using ereal_Inf_cmult[where P="\<lambda>x. \<exists>i\<in>I. x = f i", of c]
by(rule box_equals)(auto intro!: arg_cong[where f="Inf"] arg_cong2[where f="(*)"])

lemma ereal_INF_multc: "0 < c \<Longrightarrow> (INF i\<in>I. f i * c) = (INF i\<in>I. f i) * ereal c"
using ereal_INF_cmult[of c f I] by(simp add: mult.commute)

lemma INF_mult_left_ennreal: 
  assumes "I = {} \<Longrightarrow> c \<noteq> 0"
  and "\<lbrakk> c = \<top>; \<exists>i\<in>I. f i > 0 \<rbrakk> \<Longrightarrow> \<exists>p>0. \<forall>i\<in>I. f i \<ge> p"
  shows "c * (INF i\<in>I. f i) = (INF i\<in>I. c * f i ::ennreal)"
proof -
  consider (empty) "I = {}" | (top) "c = \<top>" | (zero) "c = 0" | (normal) "I \<noteq> {}" "c \<noteq> \<top>" "c \<noteq> 0" by auto
  then show ?thesis
  proof cases
    case empty then show ?thesis by(simp add: ennreal_mult_top assms(1))
  next
    case top
    show ?thesis
    proof(cases "\<exists>i\<in>I. f i > 0")
      case True
      with assms(2) top obtain p where "p > 0" and p: "\<And>i. i \<in> I \<Longrightarrow> f i \<ge> p" by auto
      then have *: "\<And>i. i \<in> I \<Longrightarrow> f i > 0" by(auto intro: less_le_trans)
      note \<open>0 < p\<close> also from p have "p \<le> (INF i\<in>I. f i)" by(rule INF_greatest)
      finally show ?thesis using top by(auto simp add: ennreal_top_mult dest: *)
    next
      case False
      hence "f i = 0" if "i \<in> I" for i using that by auto
      thus ?thesis using top by(simp add: INF_constant ennreal_mult_top)
    qed
  next
    case zero
    then show ?thesis using assms(1) by(auto simp add: INF_constant)
  next
    case normal
    then show ?thesis including ennreal.lifting
      apply transfer
      subgoal for I c f by(cases c)(simp_all add: top_ereal_def ereal_INF_cmult)
      done
  qed
qed

lemma pmf_map_spmf_None: "pmf (map_spmf f p) None = pmf p None"
by(simp add: pmf_None_eq_weight_spmf)

lemma nn_integral_try_spmf:
  "nn_integral (measure_spmf (try_spmf p q)) f = nn_integral (measure_spmf p) f + nn_integral (measure_spmf q) f * pmf p None"
by(simp add: nn_integral_measure_spmf spmf_try_spmf distrib_right nn_integral_add ennreal_mult mult.assoc nn_integral_cmult)
  (simp add: mult.commute)

lemma INF_UNION: "(INF z \<in> \<Union>x\<in>A. B x. f z) = (INF x\<in>A. INF z\<in>B x. f z)" for f :: "_ \<Rightarrow> 'b::complete_lattice"
by(auto intro!: antisym INF_greatest intro: INF_lower2)


definition nn_integral_spmf :: "'a spmf \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> ennreal" where
  "nn_integral_spmf p = nn_integral (measure_spmf p)"

lemma nn_integral_spmf_parametric [transfer_rule]:
  includes lifting_syntax
  shows "(rel_spmf A ===> (A ===> (=)) ===> (=)) nn_integral_spmf nn_integral_spmf"
  unfolding nn_integral_spmf_def
proof(rule rel_funI)+
  fix p q and f g :: "_ \<Rightarrow> ennreal"
  assume pq: "rel_spmf A p q" and fg: "(A ===> (=)) f g"
  from pq obtain pq where pq [rule_format]: "\<forall>(x, y)\<in>set_spmf pq. A x y"
    and p: "p = map_spmf fst pq" and q: "q = map_spmf snd pq"
    by(cases rule: rel_spmfE) auto
  show "nn_integral (measure_spmf p) f = nn_integral (measure_spmf q) g"
    by(simp add: p q)(auto simp add: nn_integral_measure_spmf spmf_eq_0_set_spmf dest!: pq rel_funD[OF fg] intro: ennreal_mult_left_cong intro!: nn_integral_cong)
qed

lemma weight_spmf_mcont2mcont [THEN lfp.mcont2mcont, cont_intro]:
  shows weight_spmf_mcont: "mcont (lub_spmf) (ord_spmf (=)) Sup (\<le>) (\<lambda>p. ennreal (weight_spmf p))"
apply(simp add: mcont_def cont_def weight_spmf_def measure_spmf.emeasure_eq_measure[symmetric] emeasure_lub_spmf)
apply(rule call_mono[THEN lfp.mono2mono])
apply(unfold fun_ord_def)
apply(rule monotone_emeasure_spmf[unfolded le_fun_def])
done

lemma mono2mono_nn_integral_spmf [THEN lfp.mono2mono, cont_intro]:
  shows monotone_nn_integral_spmf: "monotone (ord_spmf (=)) (\<le>) (\<lambda>p. integral\<^sup>N (measure_spmf p) f)"
by(rule monotoneI)(auto simp add: nn_integral_measure_spmf intro!: nn_integral_mono mult_right_mono dest: monotone_spmf[THEN monotoneD])

lemma cont_nn_integral_spmf:
  "cont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p :: 'a spmf. nn_integral (measure_spmf p) f)"
proof
  fix Y :: "'a spmf set"
  assume Y: "Complete_Partial_Order.chain (ord_spmf (=)) Y" "Y \<noteq> {}"
  let ?M = "count_space (set_spmf (lub_spmf Y))"
  have "nn_integral (measure_spmf (lub_spmf Y)) f = \<integral>\<^sup>+ x. ennreal (spmf (lub_spmf Y) x) * f x \<partial>?M"
    by(simp add: nn_integral_measure_spmf')
  also have "\<dots> = \<integral>\<^sup>+ x. (SUP p\<in>Y. ennreal (spmf p x) * f x) \<partial>?M"
    by(simp add: spmf_lub_spmf Y ennreal_SUP[OF SUP_spmf_neq_top'] SUP_mult_right_ennreal)
  also have "\<dots> = (SUP p\<in>Y. \<integral>\<^sup>+ x. ennreal (spmf p x) * f x \<partial>?M)"
  proof(rule nn_integral_monotone_convergence_SUP_countable)
    show "Complete_Partial_Order.chain (\<le>) ((\<lambda>i x. ennreal (spmf i x) * f x) ` Y)"
      using Y(1) by(rule chain_imageI)(auto simp add: le_fun_def intro!: mult_right_mono dest: monotone_spmf[THEN monotoneD])
  qed(simp_all add: Y(2))
  also have "\<dots> = (SUP p\<in>Y. nn_integral (measure_spmf p) f)"
    by(auto simp add: nn_integral_measure_spmf Y nn_integral_count_space_indicator set_lub_spmf spmf_eq_0_set_spmf split: split_indicator intro!: SUP_cong nn_integral_cong)
  finally show "nn_integral (measure_spmf (lub_spmf Y)) f = (SUP p\<in>Y. nn_integral (measure_spmf p) f)" .
qed

lemma mcont2mcont_nn_integral_spmf [THEN lfp.mcont2mcont, cont_intro]:
  shows mcont_nn_integral_spmf:
  "mcont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p :: 'a spmf. nn_integral (measure_spmf p) f)"
by(rule mcontI)(simp_all add: cont_nn_integral_spmf)
 

lemma nn_integral_mono2mono:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> monotone ord (\<le>) (\<lambda>f. F f x)"
  shows "monotone ord (\<le>) (\<lambda>f. nn_integral M (F f))"
  by(rule monotoneI nn_integral_mono monotoneD[OF assms])+

lemma nn_integral_mono_lfp [partial_function_mono]:
  \<comment> \<open>@{ML Partial_Function.mono_tac} does not like conditional assumptions (more precisely the case splitter)\<close>
  "(\<And>x. lfp.mono_body (\<lambda>f. F f x)) \<Longrightarrow> lfp.mono_body (\<lambda>f. nn_integral M (F f))"
  by(rule nn_integral_mono2mono)

lemma INF_mono_lfp [partial_function_mono]:
  "(\<And>x. lfp.mono_body (\<lambda>f. F f x)) \<Longrightarrow> lfp.mono_body (\<lambda>f. INF x\<in>M. F f x)"
  by(rule monotoneI)(blast dest: monotoneD intro: INF_mono)

lemmas parallel_fixp_induct_1_2 = parallel_fixp_induct_uc[
  of _ _ _ _ "\<lambda>x. x" _ "\<lambda>x. x" "case_prod" _ "curry",
  where P="\<lambda>f g. P f (curry g)",
  unfolded case_prod_curry curry_case_prod curry_K,
  OF _ _ _ _ _ _ refl refl]
  for P

lemma monotone_ennreal_add1: "monotone (\<le>) (\<le>) (\<lambda>x. x + y :: ennreal)"
by(auto intro!: monotoneI)

lemma monotone_ennreal_add2: "monotone (\<le>) (\<le>) (\<lambda>y. x + y :: ennreal)"
by(auto intro!: monotoneI)

lemma mono2mono_ennreal_add[THEN lfp.mono2mono2, cont_intro, simp]:
  shows monotone_eadd: "monotone (rel_prod (\<le>) (\<le>)) (\<le>) (\<lambda>(x, y). x + y :: ennreal)"
by(simp add: monotone_ennreal_add1 monotone_ennreal_add2)

lemma ennreal_add_partial_function_mono [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord (\<le>)) (\<le>) f; monotone (fun_ord (\<le>)) (\<le>) g \<rbrakk>
  \<Longrightarrow> monotone (fun_ord (\<le>)) (\<le>) (\<lambda>x. f x + g x :: ennreal)"
by(rule mono2mono_ennreal_add)

context
  fixes fail :: ennreal
  and \<I> :: "('out, 'ret) \<I>"
  and f :: "'a \<Rightarrow> ennreal"
  notes [[function_internals]]
begin

partial_function (lfp_strong) expectation_gpv :: "('a, 'out, 'ret) gpv \<Rightarrow> ennreal" where
  "expectation_gpv gpv = 
  (\<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> f x 
              | IO out c \<Rightarrow> INF r\<in>responses_\<I> \<I> out. expectation_gpv (c r)) \<partial>measure_spmf (the_gpv gpv))
   + fail * pmf (the_gpv gpv) None"

lemma expectation_gpv_fixp_induct [case_names adm bottom step]:
  assumes "lfp.admissible P"
    and "P (\<lambda>_. 0)"
    and "\<And>expectation_gpv'. \<lbrakk> \<And>gpv. expectation_gpv' gpv \<le> expectation_gpv gpv; P expectation_gpv' \<rbrakk> \<Longrightarrow>
         P (\<lambda>gpv. (\<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> f x | IO out c \<Rightarrow> INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv gpv)) + fail * pmf (the_gpv gpv) None)"
  shows "P expectation_gpv"
  by(rule expectation_gpv.fixp_induct)(simp_all add: bot_ennreal_def assms fun_ord_def)
  
lemma expectation_gpv_Done [simp]: "expectation_gpv (Done x) = f x"
  by(subst expectation_gpv.simps)(simp add: measure_spmf_return_spmf nn_integral_return)

lemma expectation_gpv_Fail [simp]: "expectation_gpv Fail = fail"
  by(subst expectation_gpv.simps) simp

lemma expectation_gpv_lift_spmf [simp]: 
  "expectation_gpv (lift_spmf p) = (\<integral>\<^sup>+ x. f x \<partial>measure_spmf p) + fail * pmf p None"
  by(subst expectation_gpv.simps)(auto simp add: o_def pmf_map vimage_def measure_pmf_single)

lemma expectation_gpv_Pause [simp]:
  "expectation_gpv (Pause out c) = (INF r\<in>responses_\<I> \<I> out. expectation_gpv (c r))"
  by(subst expectation_gpv.simps)(simp add: measure_spmf_return_spmf nn_integral_return)

end

context begin
private definition "weight_spmf' p = weight_spmf p"
lemmas weight_spmf'_parametric = weight_spmf_parametric[folded weight_spmf'_def]
lemma expectation_gpv_parametric':
  includes lifting_syntax notes weight_spmf'_parametric[transfer_rule]
  shows "((=) ===> rel_\<I> C R ===> (A ===> (=)) ===> rel_gpv'' A C R ===> (=)) expectation_gpv expectation_gpv"
  unfolding expectation_gpv_def
  apply(rule rel_funI)
  apply(rule rel_funI)
  apply(rule rel_funI)
  apply(rule fixp_lfp_parametric_eq[OF expectation_gpv.mono expectation_gpv.mono])
  apply(fold nn_integral_spmf_def Set.is_empty_def pmf_None_eq_weight_spmf[symmetric])
  apply(simp only: weight_spmf'_def[symmetric])
  subgoal premises [transfer_rule] supply the_gpv_parametric'[transfer_rule] by transfer_prover
  done
end

lemma expectation_gpv_parametric [transfer_rule]:
  includes lifting_syntax
  shows "((=) ===> rel_\<I> C (=) ===> (A ===> (=)) ===> rel_gpv A C ===> (=)) expectation_gpv expectation_gpv"
using expectation_gpv_parametric'[of C "(=)" A] by(simp add: rel_gpv_conv_rel_gpv'')

lemma expectation_gpv_cong:
  fixes fail fail'
  assumes fail: "fail = fail'"
  and \<I>: "\<I> = \<I>'"
  and gpv: "gpv = gpv'"
  and f: "\<And>x. x \<in> results_gpv \<I>' gpv' \<Longrightarrow> f x = g x"
  shows "expectation_gpv fail \<I> f gpv = expectation_gpv fail' \<I>' g gpv'"
using f unfolding \<I>[symmetric] gpv[symmetric] fail[symmetric]
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv' expectation_gpv'') show ?case
    by(rule arg_cong2[where f="(+)"] nn_integral_cong_AE)+(clarsimp simp add: step.prems results_gpv.intros split!: generat.split intro!: INF_cong[OF refl] step.IH)+
qed

lemma expectation_gpv_cong_fail:
  "colossless_gpv \<I> gpv \<Longrightarrow> expectation_gpv fail \<I> f gpv = expectation_gpv fail' \<I> f gpv" for fail
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv' expectation_gpv'')
  from colossless_gpv_lossless_spmfD[OF step.prems] show ?case
    by(auto simp add: lossless_iff_pmf_None intro!: nn_integral_cong_AE INF_cong step.IH intro: colossless_gpv_continuationD[OF step.prems] split: generat.split)
qed

lemma expectation_gpv_mono:
  fixes fail fail'
  assumes fail: "fail \<le> fail'"
  and fg: "f \<le> g"
  shows "expectation_gpv fail \<I> f gpv \<le> expectation_gpv fail' \<I> g gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv' expectation_gpv'')
  show ?case
    by(intro add_mono mult_right_mono fail nn_integral_mono_AE)
      (auto split: generat.split simp add: fg[THEN le_funD] INF_mono rev_bexI step.IH)
qed

lemma expectation_gpv_mono_strong:
  fixes fail fail'
  assumes fail: "\<not> colossless_gpv \<I> gpv \<Longrightarrow> fail \<le> fail'"
  and fg: "\<And>x. x \<in> results_gpv \<I> gpv \<Longrightarrow> f x \<le> g x"
  shows "expectation_gpv fail \<I> f gpv \<le> expectation_gpv fail' \<I> g gpv"
proof -
  let ?fail = "if colossless_gpv \<I> gpv then fail' else fail"
    and ?f = "\<lambda>x. if x \<in> results_gpv \<I> gpv then f x else g x"
  have "expectation_gpv fail \<I> f gpv = expectation_gpv ?fail \<I> f gpv" by(simp cong: expectation_gpv_cong_fail)
  also have "\<dots> = expectation_gpv ?fail \<I> ?f gpv" by(rule expectation_gpv_cong; simp)
  also have "\<dots> \<le> expectation_gpv fail' \<I> g gpv" using assms by(simp add: expectation_gpv_mono le_fun_def)
  finally show ?thesis .
qed

lemma expectation_gpv_bind [simp]:
  fixes \<I> f g fail
  defines "expectation_gpv1 \<equiv> expectation_gpv fail \<I> f"
  and "expectation_gpv2 \<equiv> expectation_gpv fail \<I> (expectation_gpv fail \<I> f \<circ> g)"
  shows "expectation_gpv1 (bind_gpv gpv g) = expectation_gpv2 gpv" (is "?lhs = ?rhs")
proof(rule antisym)
  note [simp] = case_map_generat o_def
    and [cong del] = generat.case_cong_weak
  show "?lhs \<le> ?rhs" unfolding expectation_gpv1_def
  proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step expectation_gpv')
    show ?case unfolding expectation_gpv2_def
      apply(rewrite bind_gpv.sel)
      apply(simp add: map_spmf_bind_spmf measure_spmf_bind)
      apply(rewrite nn_integral_bind[where B="measure_spmf _"])
        apply(simp_all add: space_subprob_algebra)
      apply(rewrite expectation_gpv.simps)
      apply(simp add: pmf_bind_spmf_None distrib_left nn_integral_eq_integral[symmetric] measure_spmf.integrable_const_bound[where B=1] pmf_le_1 nn_integral_cmult[symmetric] nn_integral_add[symmetric])
      apply(rule disjI2)
      apply(rule nn_integral_mono)
      apply(clarsimp split!: generat.split)
       apply(rewrite expectation_gpv.simps)
       apply simp
       apply(rule disjI2)
       apply(rule nn_integral_mono)
       apply(clarsimp split: generat.split)
       apply(rule INF_mono)
       apply(erule rev_bexI)
       apply(rule step.hyps)
      apply(clarsimp simp add: measure_spmf_return_spmf nn_integral_return)
      apply(rule INF_mono)
      apply(erule rev_bexI)
      apply(rule step.IH[unfolded expectation_gpv2_def o_def])
      done
  qed
  show "?rhs \<le> ?lhs" unfolding expectation_gpv2_def
  proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step expectation_gpv')
    show ?case unfolding expectation_gpv1_def
      apply(rewrite in "_ \<le> \<hole>" expectation_gpv.simps)
      apply(rewrite bind_gpv.sel)
      apply(simp add: measure_spmf_bind)
      apply(rewrite nn_integral_bind[where B="measure_spmf _"])
        apply(simp_all add: space_subprob_algebra)
      apply(simp add: pmf_bind_spmf_None distrib_left nn_integral_eq_integral[symmetric] measure_spmf.integrable_const_bound[where B=1] pmf_le_1 nn_integral_cmult[symmetric] nn_integral_add[symmetric])
      apply(rule disjI2)
      apply(rule nn_integral_mono)
      apply(clarsimp split!: generat.split)
       apply(rewrite expectation_gpv.simps)
       apply(simp cong del: if_weak_cong)
      apply(simp add: measure_spmf_return_spmf nn_integral_return)
      apply(rule INF_mono)
      apply(erule rev_bexI)
      apply(rule step.IH[unfolded expectation_gpv1_def])
      done
  qed
qed

lemma expectation_gpv_try_gpv [simp]:
  fixes fail \<I> f gpv'
  defines "expectation_gpv1 \<equiv> expectation_gpv fail \<I> f"
    and "expectation_gpv2 \<equiv> expectation_gpv (expectation_gpv fail \<I> f gpv') \<I> f"
  shows "expectation_gpv1 (try_gpv gpv gpv') = expectation_gpv2 gpv"
proof(rule antisym)
  show "expectation_gpv1 (try_gpv gpv gpv') \<le> expectation_gpv2 gpv" unfolding expectation_gpv1_def
  proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case step [unfolded expectation_gpv2_def]: (step expectation_gpv')
    show ?case unfolding expectation_gpv2_def
      apply(rewrite expectation_gpv.simps)
      apply(rewrite in "_ \<le> _ + \<hole>" expectation_gpv.simps)
      apply(simp add: pmf_map_spmf_None nn_integral_try_spmf o_def generat.map_comp case_map_generat distrib_right cong del: generat.case_cong_weak)
      apply(simp add: mult_ac add.assoc ennreal_mult)
      apply(intro disjI2 add_mono mult_left_mono nn_integral_mono; clarsimp split: generat.split intro!: INF_mono step elim!: rev_bexI)
      done
  qed
  show "expectation_gpv2 gpv \<le> expectation_gpv1 (try_gpv gpv gpv')" unfolding expectation_gpv2_def
  proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case step [unfolded expectation_gpv1_def]: (step expectation_gpv')
    show ?case unfolding expectation_gpv1_def
      apply(rewrite in "_ \<le> \<hole>" expectation_gpv.simps)
      apply(rewrite in "\<hole> \<le> _" expectation_gpv.simps)
      apply(simp add: pmf_map_spmf_None nn_integral_try_spmf o_def generat.map_comp case_map_generat distrib_left ennreal_mult mult_ac cong del: generat.case_cong_weak)
      apply(rule disjI2 nn_integral_mono)+
      apply(clarsimp split: generat.split intro!: INF_mono step(2) elim!: rev_bexI)
      done
  qed
qed

lemma expectation_gpv_restrict_gpv:
  "\<I> \<turnstile>g gpv \<surd> \<Longrightarrow> expectation_gpv fail \<I> f (restrict_gpv \<I> gpv) = expectation_gpv fail \<I> f gpv" for fail
proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv'')
  show ?case
    apply(simp add: pmf_map vimage_def)
    apply(rule arg_cong2[where f="(+)"])
    subgoal by(clarsimp simp add: measure_spmf_def nn_integral_distr nn_integral_restrict_space step.IH WT_gpv_ContD[OF step.prems] AE_measure_pmf_iff in_set_spmf[symmetric] WT_gpv_OutD[OF step.prems] split!: option.split generat.split intro!: nn_integral_cong_AE INF_cong[OF refl])
    apply(simp add: measure_pmf_single[symmetric])
    apply(rule arg_cong[where f="\<lambda>x. _ * ennreal x"])
    apply(rule measure_pmf.finite_measure_eq_AE)
    apply(auto simp add: AE_measure_pmf_iff in_set_spmf[symmetric] intro: WT_gpv_OutD[OF step.prems] split: option.split_asm generat.split_asm if_split_asm)
    done
qed

lemma expectation_gpv_const_le: "\<I> \<turnstile>g gpv \<surd> \<Longrightarrow> expectation_gpv fail \<I> (\<lambda>_. c) gpv \<le> max c fail" for fail
proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  have "integral\<^sup>N (measure_spmf (the_gpv gpv)) (case_generat (\<lambda>x. c) (\<lambda>out c. INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r))) \<le> integral\<^sup>N (measure_spmf (the_gpv gpv)) (\<lambda>_. max c fail)"
    using step.prems
    by(intro nn_integral_mono_AE)(auto 4 4 split: generat.split intro: INF_lower2 step.IH WT_gpv_ContD[OF step.prems] dest!: WT_gpv_OutD simp add: in_outs_\<I>_iff_responses_\<I>)
  also have "\<dots> + fail * pmf (the_gpv gpv) None \<le> \<dots> + max c fail * pmf (the_gpv gpv) None"
    by(intro add_left_mono mult_right_mono) simp_all
  also have "\<dots> \<le> max c fail"
    by(simp add: measure_spmf.emeasure_eq_measure pmf_None_eq_weight_spmf ennreal_minus[symmetric])
      (metis (no_types, hide_lams) add_diff_eq_iff_ennreal distrib_left ennreal_le_1 le_max_iff_disj max.cobounded2 mult.commute mult.left_neutral weight_spmf_le_1)
  finally show ?case by(simp add: add_mono)
qed

lemma expectation_gpv_no_results:
   "\<lbrakk> results_gpv \<I> gpv = {}; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> expectation_gpv 0 \<I> f gpv = 0"
proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  have "results_gpv \<I> (c x) = {}" if "IO out c \<in> set_spmf (the_gpv gpv)" "x \<in> responses_\<I> \<I> out"
    for out c x using that step.prems(1) by(auto intro: results_gpv.IO)
  then show ?case using step.prems
    by(auto 4 4 intro!: nn_integral_zero' split: generat.split intro: results_gpv.Pure cong: INF_cong simp add: step.IH WT_gpv_ContD INF_constant in_outs_\<I>_iff_responses_\<I> dest: WT_gpv_OutD)
qed

lemma expectation_gpv_cmult:
  fixes fail
  assumes "0 < c" and "c \<noteq> \<top>"
  shows "c * expectation_gpv fail \<I> f gpv = expectation_gpv (c * fail) \<I> (\<lambda>x. c * f x) gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by(simp add: bot_ennreal_def)
  case (step expectation_gpv' expectation_gpv'')
  show ?case using assms
    apply(simp add: distrib_left mult_ac nn_integral_cmult[symmetric] generat.case_distrib[where h="(*) _"])
    apply(subst INF_mult_left_ennreal, simp_all add: step.IH)
    done
qed

lemma expectation_gpv_le_exec_gpv:
  assumes callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (callee s x)"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and WT_callee: "\<And>s. \<I> \<turnstile>c callee s \<surd>"
  shows "expectation_gpv 0 \<I> f gpv \<le> \<integral>\<^sup>+ (x, s). f x \<partial>measure_spmf (exec_gpv callee gpv s)"
using WT_gpv
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_1_2[OF complete_lattice_partial_function_definitions partial_function_definitions_spmf expectation_gpv.mono exec_gpv.mono expectation_gpv_def exec_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by(simp add: bot_ennreal_def)
  case (step expectation_gpv'' exec_gpv')
  have *: "(INF r\<in>responses_\<I> \<I> out. expectation_gpv'' (c r)) \<le> \<integral>\<^sup>+ (x, s). f x \<partial>measure_spmf (bind_spmf (callee s out) (\<lambda>(r, s'). exec_gpv' (c r) s'))" (is "?lhs \<le> ?rhs")
    if "IO out c \<in> set_spmf (the_gpv gpv)" for out c 
  proof -
    from step.prems that have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
    have "?lhs = \<integral>\<^sup>+ _. ?lhs \<partial>measure_spmf (callee s out)" using callee[OF out, THEN lossless_weight_spmfD]
      by(simp add: measure_spmf.emeasure_eq_measure)
    also have "\<dots> \<le> \<integral>\<^sup>+ (r, s'). expectation_gpv'' (c r) \<partial>measure_spmf (callee s out)"
      by(rule nn_integral_mono_AE)(auto intro: WT_calleeD[OF WT_callee _ out] INF_lower)
    also have "\<dots> \<le> \<integral>\<^sup>+ (r, s'). \<integral>\<^sup>+ (x, _). f x \<partial>measure_spmf (exec_gpv' (c r) s') \<partial>measure_spmf (callee s out)"
      by(rule nn_integral_mono_AE)(auto intro!: step.IH intro: WT_gpv_ContD[OF step.prems that] WT_calleeD[OF WT_callee _ out])
    also have "\<dots> = ?rhs" by(simp add: measure_spmf_bind split_def nn_integral_bind[where B="measure_spmf _"] o_def space_subprob_algebra)
    finally show ?thesis .
  qed
  show ?case
    by(simp add: measure_spmf_bind nn_integral_bind[where B="measure_spmf _"] space_subprob_algebra)
      (simp split!: generat.split add: measure_spmf_return_spmf nn_integral_return * nn_integral_mono_AE)
qed

definition weight_gpv :: "('out, 'ret) \<I> \<Rightarrow> ('a, 'out, 'ret) gpv \<Rightarrow> real"
  where "weight_gpv \<I> gpv = enn2real (expectation_gpv 0 \<I> (\<lambda>_. 1) gpv)"

lemma weight_gpv_Done [simp]: "weight_gpv \<I> (Done x) = 1"
by(simp add: weight_gpv_def)

lemma weight_gpv_Fail [simp]: "weight_gpv \<I> Fail = 0"
by(simp add: weight_gpv_def)

lemma weight_gpv_lift_spmf [simp]: "weight_gpv \<I> (lift_spmf p) = weight_spmf p"
by(simp add: weight_gpv_def measure_spmf.emeasure_eq_measure)

lemma weight_gpv_Pause [simp]:
  "(\<And>r. r \<in> responses_\<I> \<I> out \<Longrightarrow> \<I> \<turnstile>g c r \<surd>)
   \<Longrightarrow> weight_gpv \<I> (Pause out c) = (if out \<in> outs_\<I> \<I> then INF r\<in>responses_\<I> \<I> out. weight_gpv \<I> (c r) else 0)"
apply(clarsimp simp add: weight_gpv_def in_outs_\<I>_iff_responses_\<I>)
apply(erule enn2real_INF)
apply(clarsimp simp add: expectation_gpv_const_le[THEN le_less_trans])
done

lemma weight_gpv_nonneg: "0 \<le> weight_gpv \<I> gpv"
by(simp add: weight_gpv_def)

lemma weight_gpv_le_1: "\<I> \<turnstile>g gpv \<surd> \<Longrightarrow> weight_gpv \<I> gpv \<le> 1"
using expectation_gpv_const_le[of \<I> gpv 0 1] by(simp add: weight_gpv_def enn2real_leI max_def)

theorem weight_exec_gpv:
  assumes callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (callee s x)"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and WT_callee: "\<And>s. \<I> \<turnstile>c callee s \<surd>"
  shows "weight_gpv \<I> gpv \<le> weight_spmf (exec_gpv callee gpv s)"
proof -
  have "expectation_gpv 0 \<I> (\<lambda>_. 1) gpv \<le> \<integral>\<^sup>+ (x, s). 1 \<partial>measure_spmf (exec_gpv callee gpv s)"
    using assms by(rule expectation_gpv_le_exec_gpv)
  also have "\<dots> = weight_spmf (exec_gpv callee gpv s)"
    by(simp add: split_def measure_spmf.emeasure_eq_measure)
  finally show ?thesis by(simp add: weight_gpv_def enn2real_leI)
qed

lemma (in callee_invariant_on) weight_exec_gpv:
  assumes callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> lossless_spmf (callee s x)"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "weight_gpv \<I> gpv \<le> weight_spmf (exec_gpv callee gpv s)"
including lifting_syntax
proof -
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr \<equiv> \<lambda>x y. x = Rep y"
    have [transfer_rule]: "bi_unique cr" "right_total cr" using td cr_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I" using type_definition_Domainp[OF td cr_def] by simp
    
    let ?C = "eq_onp (\<lambda>x. x \<in> outs_\<I> \<I>)"

    define callee' where "callee' \<equiv> (Rep ---> id ---> map_spmf (map_prod id Abs)) callee"
    have [transfer_rule]: "(cr ===> ?C ===> rel_spmf (rel_prod (=) cr)) callee callee'"
      by(auto simp add: callee'_def rel_fun_def cr_def spmf_rel_map prod.rel_map td.Abs_inverse eq_onp_def intro!: rel_spmf_reflI intro: td.Rep[simplified] dest: callee_invariant)
    define s' where "s' \<equiv> Abs s"
    have [transfer_rule]: "cr s s'" using I by(simp add: cr_def s'_def td.Abs_inverse)

    have [transfer_rule]: "rel_\<I> ?C (=) \<I> \<I>"
      by(rule rel_\<I>I)(auto simp add: rel_set_eq set_relator_eq_onp eq_onp_same_args dest: eq_onp_to_eq)
    note [transfer_rule] = bi_unique_eq_onp bi_unique_eq

    define gpv' where "gpv' \<equiv> restrict_gpv \<I> gpv"
    have [transfer_rule]: "rel_gpv (=) ?C gpv' gpv'"
      by(fold eq_onp_top_eq_eq)(auto simp add: gpv.rel_eq_onp eq_onp_same_args pred_gpv_def gpv'_def dest: in_outs'_restrict_gpvD)

    define weight_spmf' :: "('c \<times> 's') spmf \<Rightarrow> real" where "weight_spmf' \<equiv> weight_spmf"
    define weight_spmf'' :: "('c \<times> 's) spmf \<Rightarrow> real" where "weight_spmf'' \<equiv> weight_spmf"
    have [transfer_rule]: "(rel_spmf (rel_prod (=) cr) ===> (=)) weight_spmf'' weight_spmf'"
      by(simp add: weight_spmf'_def weight_spmf''_def weight_spmf_parametric)

    have [rule_format]: "\<And>s. \<forall>x \<in> outs_\<I> \<I>. lossless_spmf (callee' s x)"
      by(transfer)(blast intro: callee)
    moreover have "\<I> \<turnstile>g gpv' \<surd>" by(simp add: gpv'_def)
    moreover have "\<And>s. \<I> \<turnstile>c callee' s \<surd>" by transfer(rule WT_callee)
    ultimately have **: "weight_gpv \<I> gpv' \<le> weight_spmf' (exec_gpv callee' gpv' s')"
      unfolding weight_spmf'_def by(rule weight_exec_gpv)
    have [transfer_rule]: "((=) ===> ?C ===> rel_spmf (rel_prod (=) (=))) callee callee"
      by(simp add: rel_fun_def eq_onp_def prod.rel_eq)
    have "weight_gpv \<I> gpv' \<le> weight_spmf'' (exec_gpv callee gpv' s)" using ** by transfer
    also have "exec_gpv callee gpv' s = exec_gpv callee gpv s"
      unfolding gpv'_def using WT_gpv I by(rule exec_gpv_restrict_gpv_invariant)
    also have "weight_gpv \<I> gpv' = weight_gpv \<I> gpv" using WT_gpv 
      by(simp add: gpv'_def expectation_gpv_restrict_gpv weight_gpv_def)
    finally have ?thesis by(simp add: weight_spmf''_def) }
  from this[cancel_type_definition] I show ?thesis by blast
qed

subsection \<open>Probabilistic termination\<close>

definition pgen_lossless_gpv :: "ennreal \<Rightarrow> ('c, 'r) \<I> \<Rightarrow> ('a, 'c, 'r) gpv \<Rightarrow> bool"
where "pgen_lossless_gpv fail \<I> gpv = (expectation_gpv fail \<I> (\<lambda>_. 1) gpv = 1)" for fail

abbreviation plossless_gpv :: "('c, 'r) \<I> \<Rightarrow> ('a, 'c, 'r) gpv \<Rightarrow> bool"
where "plossless_gpv \<equiv> pgen_lossless_gpv 0"

abbreviation pfinite_gpv :: "('c, 'r) \<I> \<Rightarrow> ('a, 'c, 'r) gpv \<Rightarrow> bool"
where "pfinite_gpv \<equiv> pgen_lossless_gpv 1"

lemma pgen_lossless_gpvI [intro?]: "expectation_gpv fail \<I> (\<lambda>_. 1) gpv = 1 \<Longrightarrow> pgen_lossless_gpv fail \<I> gpv" for fail
by(simp add: pgen_lossless_gpv_def)

lemma pgen_lossless_gpvD: "pgen_lossless_gpv fail \<I> gpv \<Longrightarrow> expectation_gpv fail \<I> (\<lambda>_. 1) gpv = 1" for fail
by(simp add: pgen_lossless_gpv_def)

lemma lossless_imp_plossless_gpv:
  assumes "lossless_gpv \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
  shows "plossless_gpv \<I> gpv"
proof
  show "expectation_gpv 0 \<I> (\<lambda>_. 1) gpv = 1" using assms
  proof(induction rule: lossless_WT_gpv_induct)
    case (lossless_gpv p)
    have "expectation_gpv 0 \<I> (\<lambda>_. 1) (GPV p) = nn_integral (measure_spmf p) (case_generat (\<lambda>_. 1) (\<lambda>out c. INF r\<in>responses_\<I> \<I> out. 1))"
      by(subst expectation_gpv.simps)(clarsimp split: generat.split cong: INF_cong simp add: lossless_gpv.IH intro!: nn_integral_cong_AE)
    also have "\<dots> = nn_integral (measure_spmf p) (\<lambda>_. 1)"
      by(intro nn_integral_cong_AE)(auto split: generat.split dest!: lossless_gpv.hyps(2) simp add: in_outs_\<I>_iff_responses_\<I>)
    finally show ?case by(simp add: measure_spmf.emeasure_eq_measure lossless_weight_spmfD lossless_gpv.hyps(1))
  qed
qed

lemma finite_imp_pfinite_gpv:
  assumes "finite_gpv \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
  shows "pfinite_gpv \<I> gpv"
proof
  show "expectation_gpv 1 \<I> (\<lambda>_. 1) gpv = 1" using assms
  proof(induction rule: finite_gpv_induct)
    case (finite_gpv gpv)
    then have "expectation_gpv 1 \<I> (\<lambda>_. 1) gpv = nn_integral (measure_spmf (the_gpv gpv)) (case_generat (\<lambda>_. 1) (\<lambda>out c. INF r\<in>responses_\<I> \<I> out. 1)) + pmf (the_gpv gpv) None"
      by(subst expectation_gpv.simps)(clarsimp intro!: nn_integral_cong_AE INF_cong[OF refl] split!: generat.split simp add: WT_gpv_ContD)
    also have "\<dots> = nn_integral (measure_spmf (the_gpv gpv)) (\<lambda>_. 1) + pmf (the_gpv gpv) None"
      by(intro arg_cong2[where f="(+)"] nn_integral_cong_AE)
        (auto split: generat.split dest!: WT_gpv_OutD[OF finite_gpv.prems] simp add: in_outs_\<I>_iff_responses_\<I>)
    finally show ?case
      by(simp add: measure_spmf.emeasure_eq_measure ennreal_plus[symmetric] del: ennreal_plus)
        (simp add: pmf_None_eq_weight_spmf)
  qed
qed

lemma plossless_gpv_lossless_spmfD:
  assumes lossless: "plossless_gpv \<I> gpv"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  shows "lossless_spmf (the_gpv gpv)"
proof -
  have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv"
    using lossless by(auto dest: pgen_lossless_gpvD simp add: weight_gpv_def)
  also have "\<dots> = \<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> 1 | IO out c \<Rightarrow> INF r\<in>responses_\<I> \<I> out. expectation_gpv 0 \<I> (\<lambda>_. 1) (c r)) \<partial>measure_spmf (the_gpv gpv)"
    by(subst expectation_gpv.simps)(auto)
  also have "\<dots> \<le> \<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> 1 | IO out c \<Rightarrow> 1) \<partial>measure_spmf (the_gpv gpv)"
    apply(rule nn_integral_mono_AE)
    apply(clarsimp split: generat.split)
    apply(frule WT_gpv_OutD[OF WT])
    using expectation_gpv_const_le[of \<I> _ 0 1]
    apply(auto simp add: in_outs_\<I>_iff_responses_\<I> max_def intro: INF_lower2 WT_gpv_ContD[OF WT] dest: WT_gpv_OutD[OF WT])
    done
  also have "\<dots> = weight_spmf (the_gpv gpv)"
    by(auto simp add: weight_spmf_eq_nn_integral_spmf nn_integral_measure_spmf intro!: nn_integral_cong split: generat.split)
  finally show ?thesis using weight_spmf_le_1[of "the_gpv gpv"] by(simp add: lossless_spmf_def)
qed

lemma
  shows plossless_gpv_ContD:
  "\<lbrakk> plossless_gpv \<I> gpv; IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out; \<I> \<turnstile>g gpv \<surd> \<rbrakk>
  \<Longrightarrow> plossless_gpv \<I> (c input)"
  and pfinite_gpv_ContD:
  "\<lbrakk> pfinite_gpv \<I> gpv; IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out; \<I> \<turnstile>g gpv \<surd> \<rbrakk>
  \<Longrightarrow> pfinite_gpv \<I> (c input)"
proof(rule_tac [!] pgen_lossless_gpvI, rule_tac [!] antisym[rotated], rule_tac ccontr, rule_tac [3] ccontr)
  assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    and input: "input \<in> responses_\<I> \<I> out"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
  from WT IO input have WT': "\<I> \<turnstile>g c input \<surd>" by(rule WT_gpv_ContD)
  from expectation_gpv_const_le[OF this, of 0 1] expectation_gpv_const_le[OF this, of 1 1]
  show "expectation_gpv 0 \<I> (\<lambda>_. 1) (c input) \<le> 1"
    and "expectation_gpv 1 \<I> (\<lambda>_. 1) (c input) \<le> 1" by(simp_all add: max_def)

  have less: "expectation_gpv fail \<I> (\<lambda>_. 1) gpv < weight_spmf (the_gpv gpv) + fail * pmf (the_gpv gpv) None"
    if fail: "fail \<le> 1" and *: "\<not> 1 \<le> expectation_gpv fail \<I> (\<lambda>_. 1) (c input)" for fail :: ennreal
  proof -
    have "expectation_gpv fail \<I> (\<lambda>_. 1) gpv = (\<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> 1 | IO out c \<Rightarrow> INF r\<in>responses_\<I> \<I> out. expectation_gpv fail \<I> (\<lambda>_. 1) (c r)) * spmf (the_gpv gpv) generat * indicator (UNIV - {IO out c}) generat + (INF r\<in>responses_\<I> \<I> out. expectation_gpv fail \<I> (\<lambda>_. 1) (c r)) * spmf (the_gpv gpv) (IO out c) * indicator {IO out c} generat \<partial>count_space UNIV) + fail * pmf (the_gpv gpv) None"
      by(subst expectation_gpv.simps)(auto simp add: nn_integral_measure_spmf mult.commute intro!: nn_integral_cong split: split_indicator generat.split)
    also have "\<dots> = (\<integral>\<^sup>+ generat. (case generat of Pure x \<Rightarrow> 1 | IO out c \<Rightarrow> INF r\<in>responses_\<I> \<I> out. expectation_gpv fail \<I> (\<lambda>_. 1) (c r)) * spmf (the_gpv gpv) generat * indicator (UNIV - {IO out c}) generat \<partial>count_space UNIV) +
      (INF r\<in>responses_\<I> \<I> out. expectation_gpv fail \<I> (\<lambda>_. 1) (c r)) * spmf (the_gpv gpv) (IO out c) + fail * pmf (the_gpv gpv) None" (is "_ = ?rest + ?cr + _")
      by(subst nn_integral_add) simp_all
    also from calculation expectation_gpv_const_le[OF WT, of fail 1] fail have fin: "?rest \<noteq> \<infinity>"
      by(auto simp add: top_add top_unique max_def split: if_split_asm)
    have "?cr \<le> expectation_gpv fail \<I> (\<lambda>_. 1) (c input) * spmf (the_gpv gpv) (IO out c)"
      by(rule mult_right_mono INF_lower[OF input])+ simp
    also have "?rest + \<dots> < ?rest + 1 * ennreal (spmf (the_gpv gpv) (IO out c))"
      unfolding ennreal_add_left_cancel_less using * IO
      by(intro conjI fin ennreal_mult_strict_right_mono)(simp_all add: not_le weight_gpv_def in_set_spmf_iff_spmf)
    also have "?rest \<le> \<integral>\<^sup>+ generat. spmf (the_gpv gpv) generat * indicator (UNIV - {IO out c}) generat \<partial>count_space UNIV"
      apply(rule nn_integral_mono)
      apply(clarsimp split: generat.split split_indicator)
      apply(rule ennreal_mult_le_self2I)
      apply simp
      subgoal premises prems for out' c'
        apply(subgoal_tac "IO out' c' \<in> set_spmf (the_gpv gpv)")
         apply(frule WT_gpv_OutD[OF WT])
         apply(simp add: in_outs_\<I>_iff_responses_\<I>)
         apply safe
         apply(erule notE)
         apply(rule INF_lower2, assumption)
         apply(rule expectation_gpv_const_le[THEN order_trans])
          apply(erule (1) WT_gpv_ContD[OF WT])
         apply(simp add: fail)
        using prems by(simp add: in_set_spmf_iff_spmf)
      done
    also have "\<dots> + 1 * ennreal (spmf (the_gpv gpv) (IO out c)) = 
      (\<integral>\<^sup>+ generat. spmf (the_gpv gpv) generat * indicator (UNIV - {IO out c}) generat + ennreal (spmf (the_gpv gpv) (IO out c)) * indicator {IO out c} generat \<partial>count_space UNIV)"
      by(subst nn_integral_add)(simp_all)
    also have "\<dots> = \<integral>\<^sup>+ generat. spmf (the_gpv gpv) generat \<partial>count_space UNIV" 
      by(auto intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = weight_spmf (the_gpv gpv)" by(simp add: nn_integral_spmf measure_spmf.emeasure_eq_measure space_measure_spmf)
    finally show ?thesis using fail
      by(fastforce simp add: top_unique add_mono ennreal_plus[symmetric] ennreal_mult_eq_top_iff)
  qed
  
  show False if *: "\<not> 1 \<le> expectation_gpv 0 \<I> (\<lambda>_. 1) (c input)" and lossless: "plossless_gpv \<I> gpv"
    using less[OF _ *] plossless_gpv_lossless_spmfD[OF lossless WT] lossless[THEN pgen_lossless_gpvD]
    by(simp add: lossless_spmf_def)

  show False if *: "\<not> 1 \<le> expectation_gpv 1 \<I> (\<lambda>_. 1) (c input)" and finite: "pfinite_gpv \<I> gpv"
    using less[OF _ *] finite[THEN pgen_lossless_gpvD] by(simp add: ennreal_plus[symmetric] del: ennreal_plus)(simp add: pmf_None_eq_weight_spmf)
qed

lemma plossless_iff_colossless_pfinite:
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
  shows "plossless_gpv \<I> gpv \<longleftrightarrow> colossless_gpv \<I> gpv \<and> pfinite_gpv \<I> gpv"
proof(intro iffI conjI; (elim conjE)?)
  assume *: "plossless_gpv \<I> gpv"
  show "colossless_gpv \<I> gpv" using * WT
  proof(coinduction arbitrary: gpv)
    case (colossless_gpv gpv)
    have ?lossless_spmf using colossless_gpv by(rule plossless_gpv_lossless_spmfD)
    moreover have ?continuation using colossless_gpv
      by(auto intro: plossless_gpv_ContD WT_gpv_ContD)
    ultimately show ?case ..
  qed

  show "pfinite_gpv \<I> gpv" unfolding pgen_lossless_gpv_def
  proof(rule antisym)
    from expectation_gpv_const_le[OF WT, of 1 1] show "expectation_gpv 1 \<I> (\<lambda>_. 1) gpv \<le> 1" by simp
    have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv" using * by(simp add: pgen_lossless_gpv_def)
    also have "\<dots> \<le> expectation_gpv 1 \<I> (\<lambda>_. 1) gpv" by(rule expectation_gpv_mono) simp_all
    finally show "1 \<le> \<dots>" .
  qed
next
  show "plossless_gpv \<I> gpv" if "colossless_gpv \<I> gpv" and "pfinite_gpv \<I> gpv" using that
    by(simp add: pgen_lossless_gpv_def cong: expectation_gpv_cong_fail)
qed

lemma pgen_lossless_gpv_Done [simp]: "pgen_lossless_gpv fail \<I> (Done x)" for fail
by(simp add: pgen_lossless_gpv_def)

lemma pgen_lossless_gpv_Fail [simp]: "pgen_lossless_gpv fail \<I> Fail \<longleftrightarrow> fail = 1" for fail
by(simp add: pgen_lossless_gpv_def)

lemma pgen_lossless_gpv_PauseI [simp, intro!]: 
  "\<lbrakk> out \<in> outs_\<I> \<I>; \<And>r. r \<in> responses_\<I> \<I> out \<Longrightarrow> pgen_lossless_gpv fail \<I> (c r) \<rbrakk>
   \<Longrightarrow> pgen_lossless_gpv fail \<I> (Pause out c)" for fail
by(simp add: pgen_lossless_gpv_def weight_gpv_def in_outs_\<I>_iff_responses_\<I>)

lemma pgen_lossless_gpv_bindI [simp, intro!]:
  "\<lbrakk> pgen_lossless_gpv fail \<I> gpv; \<And>x. x \<in> results_gpv \<I> gpv \<Longrightarrow> pgen_lossless_gpv fail \<I> (f x) \<rbrakk>
  \<Longrightarrow> pgen_lossless_gpv fail \<I> (bind_gpv gpv f)" for fail
by(simp add: pgen_lossless_gpv_def weight_gpv_def o_def cong: expectation_gpv_cong)

lemma pgen_lossless_gpv_lift_spmf [simp]: 
  "pgen_lossless_gpv fail \<I> (lift_spmf p) \<longleftrightarrow> lossless_spmf p \<or> fail = 1" for fail
apply(cases fail)
subgoal
  by(simp add: pgen_lossless_gpv_def lossless_spmf_def measure_spmf.emeasure_eq_measure pmf_None_eq_weight_spmf ennreal_minus ennreal_mult[symmetric] weight_spmf_le_1 ennreal_plus[symmetric] del: ennreal_plus)
    (metis add_diff_cancel_left' diff_add_cancel eq_iff_diff_eq_0 mult_cancel_right1)
subgoal by(simp add: pgen_lossless_gpv_def measure_spmf.emeasure_eq_measure ennreal_top_mult lossless_spmf_def add_top weight_spmf_conv_pmf_None)
done

lemma expectation_gpv_top_pfinite:
  assumes "pfinite_gpv \<I> gpv"
  shows "expectation_gpv \<top> \<I> (\<lambda>_. \<top>) gpv = \<top>"
proof(rule ccontr)
  assume *: "\<not> ?thesis"
  have "1 = expectation_gpv 1 \<I> (\<lambda>_. 1) gpv" using assms by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> expectation_gpv \<top> \<I> (\<lambda>_. \<top>) gpv" by(rule expectation_gpv_mono)(simp_all add: le_fun_def)
  also have "\<dots> = 0"  using expectation_gpv_cmult[of "2" \<top> \<I> "\<lambda>_. \<top>" gpv] *
    by(simp add: ennreal_mult_top) (metis ennreal_mult_cancel_left mult.commute mult_numeral_1_right not_gr_zero numeral_eq_one_iff semiring_norm(85) zero_neq_numeral)
  finally show False by simp
qed

lemma pfinite_INF_le_expectation_gpv:
  fixes fail \<I> gpv f
  defines "c \<equiv> min (INF x\<in>results_gpv \<I> gpv. f x) fail"
  assumes fin: "pfinite_gpv \<I> gpv"
  shows "c \<le> expectation_gpv fail \<I> f gpv" (is "?lhs \<le> ?rhs")
proof(cases "c > 0")
  case True
  have "c = c * expectation_gpv 1 \<I> (\<lambda>_. 1) gpv" using assms by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> = expectation_gpv c \<I> (\<lambda>_. c) gpv" using fin True
    by(cases "c = \<top>")(simp_all add: expectation_gpv_top_pfinite ennreal_top_mult expectation_gpv_cmult, simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> ?rhs" by(rule expectation_gpv_mono_strong)(auto simp add: c_def min_def intro: INF_lower2)
  finally show ?thesis .
qed simp

lemma plossless_INF_le_expectation_gpv:
  fixes fail
  assumes "plossless_gpv \<I> gpv" and "\<I> \<turnstile>g gpv \<surd>"
  shows "(INF x\<in>results_gpv \<I> gpv. f x) \<le> expectation_gpv fail \<I> f gpv" (is "?lhs \<le> ?rhs")
proof -
  from assms have fin: "pfinite_gpv \<I> gpv" and co: "colossless_gpv \<I> gpv"
    by(simp_all add: plossless_iff_colossless_pfinite)
  have "?lhs \<le> min ?lhs \<top>" by(simp add: min_def)
  also have "\<dots> \<le> expectation_gpv \<top> \<I> f gpv" using fin by(rule pfinite_INF_le_expectation_gpv)
  also have "\<dots> = ?rhs" using co by(simp add: expectation_gpv_cong_fail)
  finally show ?thesis .
qed


lemma expectation_gpv_le_inline:
  fixes \<I>'
  defines "expectation_gpv2 \<equiv> expectation_gpv 0 \<I>'"
  assumes callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and callee': "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> results_gpv \<I>' (callee s x) \<subseteq> responses_\<I> \<I> x \<times> UNIV"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and WT_callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g callee s x \<surd>"
  shows "expectation_gpv 0 \<I> f gpv \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee gpv s)"
  using WT_gpv
proof(induction arbitrary: gpv s rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  { fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    with step.prems have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    have "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) = \<integral>\<^sup>+ generat. (INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))"
      using WT_callee[OF out, of s] callee[OF out, of s]
      by(clarsimp simp add: measure_spmf.emeasure_eq_measure plossless_iff_colossless_pfinite colossless_gpv_lossless_spmfD lossless_weight_spmfD)
    also have "\<dots> \<le> \<integral>\<^sup>+ generat. (case generat of Pure (x, s') \<Rightarrow>
            \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')
         | IO out' rpv \<Rightarrow> INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))
       \<partial>measure_spmf (the_gpv (callee s out))"
    proof(rule nn_integral_mono_AE; simp split!: generat.split)
      fix x s'
      assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
      hence "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
      with callee'[OF out, of s] have x: "x \<in> responses_\<I> \<I> out" by blast
      hence "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> expectation_gpv' (c x)" by(rule INF_lower)
      also have "\<dots> \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c x) s')"
        by(rule step.IH)(rule WT_gpv_ContD[OF step.prems(1) IO x] step.prems|assumption)+
      also have "\<dots> = \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')"
        unfolding expectation_gpv2_def
        by(subst expectation_gpv.simps)(auto simp add: inline_sel split_def o_def intro!: nn_integral_cong split: generat.split sum.split)
      finally show "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    next
      fix out' rpv
      assume IO': "IO out' rpv \<in> set_spmf (the_gpv (callee s out))"
      have "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> (INF (r, s')\<in>(\<Union>r'\<in>responses_\<I> \<I>' out'. results_gpv \<I>' (rpv r')). expectation_gpv' (c r))"
        using IO' callee'[OF out, of s] by(intro INF_mono)(auto intro: results_gpv.IO)
      also have "\<dots> = (INF r'\<in>responses_\<I> \<I>' out'. INF (r, s')\<in>results_gpv \<I>' (rpv r'). expectation_gpv' (c r))"
        by(simp add: INF_UNION)
      also have "\<dots> \<le> (INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))"
      proof(rule INF_mono, rule bexI)
        fix r'
        assume r': "r' \<in> responses_\<I> \<I>' out'"
        have "(INF (r, s')\<in>results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> (INF (r, s')\<in>results_gpv \<I>' (rpv r'). expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c r) s'))"
          using IO IO' step.prems out callee'[OF out, of s] r'
          by(auto intro!: INF_mono rev_bexI step.IH dest: WT_gpv_ContD intro: results_gpv.IO)
        also have "\<dots> \<le>  expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r')"
          unfolding expectation_gpv2_def using plossless_gpv_ContD[OF callee, OF out IO' r'] WT_callee[OF out, of s] IO' r'
          by(intro plossless_INF_le_expectation_gpv)(auto intro: WT_gpv_ContD)
        finally show "(INF (r, s')\<in>results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> \<dots>" .
      qed
      finally show "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    qed
    also note calculation }
  then show ?case unfolding expectation_gpv2_def
    apply(rewrite expectation_gpv.simps)
    apply(rewrite inline_sel)
    apply(simp add: o_def pmf_map_spmf_None)
    apply(rewrite sum.case_distrib[where h="case_generat _ _"])
    apply(simp cong del: sum.case_cong_weak)
    apply(simp add: split_beta o_def cong del: sum.case_cong_weak)
    apply(rewrite inline1.simps)
    apply(rewrite measure_spmf_bind)
    apply(rewrite nn_integral_bind[where B="measure_spmf _"])
      apply simp
     apply(simp add: space_subprob_algebra)
    apply(rule nn_integral_mono_AE)
    apply(clarsimp split!: generat.split)
     apply(simp add: measure_spmf_return_spmf nn_integral_return)
    apply(rewrite measure_spmf_bind)
    apply(simp add: nn_integral_bind[where B="measure_spmf _"] space_subprob_algebra)
    apply(subst generat.case_distrib[where h="measure_spmf"])
    apply(subst generat.case_distrib[where h="\<lambda>x. nn_integral x _"])
    apply(simp add: measure_spmf_return_spmf nn_integral_return split_def)
    done
qed

lemma plossless_inline:
  assumes lossless: "plossless_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and callee': "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> results_gpv \<I>' (callee s x) \<subseteq> responses_\<I> \<I> x \<times> UNIV"
    and WT_callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g callee s x \<surd>"
  shows "plossless_gpv \<I>' (inline callee gpv s)"
unfolding pgen_lossless_gpv_def
proof(rule antisym)
  have WT': "\<I>' \<turnstile>g inline callee gpv s \<surd>" using callee' WT_callee WT by(rule WT_gpv_inline)
  from expectation_gpv_const_le[OF WT', of 0 1]
  show "expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s) \<le> 1" by(simp add: max_def)

  have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv" using lossless by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s)"
    by(rule expectation_gpv_le_inline[unfolded split_def]; rule callee callee' WT WT_callee)
  finally show "1 \<le> \<dots>" .
qed

lemma plossless_exec_gpv:
  assumes lossless: "plossless_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (callee s x)"
    and callee': "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> set_spmf (callee s x) \<subseteq> responses_\<I> \<I> x \<times> UNIV"
  shows "lossless_spmf (exec_gpv callee gpv s)"
proof -
  have "plossless_gpv \<I>_full (inline (\<lambda>s x. lift_spmf (callee s x)) gpv s)"
    using lossless WT by(rule plossless_inline)(simp_all add: callee callee')
  from this[THEN plossless_gpv_lossless_spmfD] show ?thesis
    unfolding exec_gpv_conv_inline1 by(simp add: inline_sel)
qed

end
