(* Title: While_SPMF.thy
   Author: Andreas Lochbihler, ETH Zurich *)

theory While_SPMF imports
  MFMC_Countable.Rel_PMF_Characterisation
  "HOL-Types_To_Sets.Types_To_Sets"
  "HOL-Library.Complete_Partial_Order2"
begin

text \<open>
  This theory defines a probabilistic while combinator for discrete (sub-)probabilities and
  formalises rules for probabilistic termination similar to those by Hurd \cite{Hurd2002TPHOLs}
  and McIver and Morgan \cite{McIverMorgan2005}.
\<close>

section \<open>Miscellaneous library additions\<close>

fun map_option_set :: "('a \<Rightarrow> 'b option set) \<Rightarrow> 'a option \<Rightarrow> 'b option set"
where
  "map_option_set f None = {None}"
| "map_option_set f (Some x) = f x"

lemma None_in_map_option_set:
  "None \<in> map_option_set f x \<longleftrightarrow> None \<in> Set.bind (set_option x) f \<or> x = None"
by(cases x) simp_all

lemma None_in_map_option_set_None [intro!]: "None \<in> map_option_set f None"
by simp

lemma None_in_map_option_set_Some [intro!]: "None \<in> f x \<Longrightarrow> None \<in> map_option_set f (Some x)"
by simp

lemma Some_in_map_option_set [intro!]: "Some y \<in> f x \<Longrightarrow> Some y \<in> map_option_set f (Some x)"
by simp

lemma map_option_set_singleton [simp]: "map_option_set (\<lambda>x. {f x}) y = {Option.bind y f}"
by(cases y) simp_all

lemma Some_eq_bind_conv: "Some y = Option.bind x f \<longleftrightarrow> (\<exists>z. x = Some z \<and> f z = Some y)"
by(cases x) auto

lemma map_option_set_bind: "map_option_set f (Option.bind x g) = map_option_set (map_option_set f \<circ> g) x"
by(cases x) simp_all

lemma Some_in_map_option_set_conv: "Some y \<in> map_option_set f x \<longleftrightarrow> (\<exists>z. x = Some z \<and> Some y \<in> f z)"
by(cases x) auto


interpretation rel_spmf_characterisation by unfold_locales(rule rel_pmf_measureI)
hide_fact (open) rel_pmf_measureI

lemma Sup_conv_fun_lub: "Sup = fun_lub Sup"
  by(auto simp add: Sup_fun_def fun_eq_iff fun_lub_def intro: arg_cong[where f=Sup])

lemma le_conv_fun_ord: "(\<le>) = fun_ord (\<le>)"
  by(auto simp add: fun_eq_iff fun_ord_def le_fun_def)

lemmas parallel_fixp_induct_2_1 = parallel_fixp_induct_uc[
  of _ _ _ _ "case_prod" _ "curry" "\<lambda>x. x" _ "\<lambda>x. x",
  where P="\<lambda>f g. P (curry f) g",
  unfolded case_prod_curry curry_case_prod curry_K,
  OF _ _ _ _ _ _ refl refl]
  for P

lemma monotone_Pair:
  "\<lbrakk> monotone ord orda f; monotone ord ordb g \<rbrakk>
  \<Longrightarrow> monotone ord (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(simp add: monotone_def)

lemma cont_Pair:
  "\<lbrakk> cont lub ord luba orda f; cont lub ord lubb ordb g \<rbrakk>
  \<Longrightarrow> cont lub ord (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(rule contI)(auto simp add: prod_lub_def image_image dest!: contD)

lemma mcont_Pair:
  "\<lbrakk> mcont lub ord luba orda f; mcont lub ord lubb ordb g \<rbrakk>
  \<Longrightarrow> mcont lub ord (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. (f x, g x))"
by(rule mcontI)(simp_all add: monotone_Pair mcont_mono cont_Pair)

lemma mono2mono_emeasure_spmf [THEN lfp.mono2mono]:
  shows monotone_emeasure_spmf:
  "monotone (ord_spmf (=)) (\<le>) (\<lambda>p. emeasure (measure_spmf p))"
  by(rule monotoneI le_funI ord_spmf_eqD_emeasure)+

lemma cont_emeasure_spmf: "cont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. emeasure (measure_spmf p))"
  by (rule contI) (simp add: emeasure_lub_spmf fun_eq_iff image_comp)

lemma mcont2mcont_emeasure_spmf [THEN lfp.mcont2mcont, cont_intro]:
  shows mcont_emeasure_spmf: "mcont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. emeasure (measure_spmf p))"
  by(simp add: mcont_def monotone_emeasure_spmf cont_emeasure_spmf)

lemma mcont2mcont_emeasure_spmf' [THEN lfp.mcont2mcont, cont_intro]:
  shows mcont_emeasure_spmf': "mcont lub_spmf (ord_spmf (=)) Sup (\<le>) (\<lambda>p. emeasure (measure_spmf p) A)"
  using mcont_emeasure_spmf[unfolded Sup_conv_fun_lub le_conv_fun_ord]
  by(subst (asm) mcont_fun_lub_apply) blast

lemma mcont_bind_pmf [cont_intro]:
  assumes g: "\<And>y. mcont luba orda lub_spmf (ord_spmf (=)) (g y)"
  shows "mcont luba orda lub_spmf (ord_spmf (=)) (\<lambda>x. bind_pmf p (\<lambda>y. g y x))"
using mcont_bind_spmf[where f="\<lambda>_. spmf_of_pmf p" and g=g, OF _ assms] by(simp)

lemma ennreal_less_top_iff: "x < \<top> \<longleftrightarrow> x \<noteq> (\<top> :: ennreal)"
  by(cases x) simp_all

lemma type_definition_Domainp: 
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
  shows "Domainp T = (\<lambda>x. x \<in> A)"
proof -
  interpret type_definition Rep Abs A by(rule type)
  show ?thesis unfolding Domainp_iff[abs_def] T_def fun_eq_iff by(metis Abs_inverse Rep)
qed

context includes lifting_syntax begin

lemma weight_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> (=)) weight_spmf weight_spmf"
by(simp add: rel_fun_def rel_spmf_weightD)

lemma lossless_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> (=)) lossless_spmf lossless_spmf"
by(simp add: rel_fun_def lossless_spmf_def rel_spmf_weightD)

lemma UNIV_parametric_pred: "rel_pred R UNIV UNIV"
  by(auto intro!: rel_predI)
end

lemma bind_spmf_spmf_of_set:
  "\<And>A. \<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> bind_spmf (spmf_of_set A) = bind_pmf (pmf_of_set A)"
by(simp add: spmf_of_set_def fun_eq_iff del: spmf_of_pmf_pmf_of_set)

lemma set_pmf_bind_spmf: "set_pmf (bind_spmf M f) = set_pmf M \<bind> map_option_set (set_pmf \<circ> f)"
by(auto 4 3 simp add: bind_spmf_def split: option.splits intro: rev_bexI)

lemma set_pmf_spmf_of_set:
  "set_pmf (spmf_of_set A) = (if finite A \<and> A \<noteq> {} then Some ` A else {None})"
by(simp add: spmf_of_set_def spmf_of_pmf_def del: spmf_of_pmf_pmf_of_set)

definition measure_measure_spmf :: "'a spmf \<Rightarrow> 'a set \<Rightarrow> real"
where [simp]: "measure_measure_spmf p = measure (measure_spmf p)"

lemma measure_measure_spmf_parametric [transfer_rule]:
  includes lifting_syntax shows
  "(rel_spmf A ===> rel_pred A ===> (=)) measure_measure_spmf measure_measure_spmf"
unfolding measure_measure_spmf_def[abs_def] by(rule measure_spmf_parametric)

lemma of_nat_le_one_cancel_iff [simp]:
  fixes n :: nat shows "real n \<le> 1 \<longleftrightarrow> n \<le> 1"
by linarith

lemma of_int_ceiling_less_add_one [simp]: "of_int \<lceil>r\<rceil> < r + 1"
  by linarith

lemma lessThan_subset_Collect: "{..<x} \<subseteq> Collect P \<longleftrightarrow> (\<forall>y<x. P y)"
  by(auto simp add: lessThan_def)

lemma spmf_ub_tight:
  assumes ub: "\<And>x. spmf p x \<le> f x"
  and sum: "(\<integral>\<^sup>+ x. f x \<partial>count_space UNIV) = weight_spmf p"
  shows "spmf p x = f x"
proof -
  have [rule_format]: "\<forall>x. f x \<le> spmf p x"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where x: "spmf p x < f x" by(auto simp add: not_le)
    have *: "(\<integral>\<^sup>+ y. ennreal (f y) * indicator (- {x}) y \<partial>count_space UNIV) \<noteq> \<top>"
      by(rule neq_top_trans[where y="weight_spmf p"], simp)(auto simp add: sum[symmetric] intro!: nn_integral_mono split: split_indicator)
      
    have "weight_spmf p = \<integral>\<^sup>+ y. spmf p y \<partial>count_space UNIV"
      by(simp add: nn_integral_spmf space_measure_spmf measure_spmf.emeasure_eq_measure)
    also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (spmf p y) * indicator (- {x}) y \<partial>count_space UNIV) +
      (\<integral>\<^sup>+ y. spmf p y * indicator {x} y \<partial>count_space UNIV)"
      by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> \<le> (\<integral>\<^sup>+ y. ennreal (f y) * indicator (- {x}) y \<partial>count_space UNIV) + spmf p x"
      using ub by(intro add_mono nn_integral_mono)(auto split: split_indicator intro: ennreal_leI)
    also have "\<dots> < (\<integral>\<^sup>+ y. ennreal (f y) * indicator (- {x}) y \<partial>count_space UNIV) + (\<integral>\<^sup>+ y. f y * indicator {x} y \<partial>count_space UNIV)"
      using * x by(simp add: ennreal_less_iff)
    also have "\<dots> = (\<integral>\<^sup>+ y. ennreal (f y) \<partial>count_space UNIV)"
      by(subst nn_integral_add[symmetric])(auto intro: nn_integral_cong split: split_indicator)
    also have "\<dots> = weight_spmf p" using sum by simp
    finally show False by simp
  qed
  from this[of x] ub[of x] show ?thesis by simp
qed

section \<open>Probabilistic while loop\<close>

locale loop_spmf = 
  fixes guard :: "'a \<Rightarrow> bool"
  and body :: "'a \<Rightarrow> 'a spmf"
begin

context notes [[function_internals]] begin

partial_function (spmf) while :: "'a \<Rightarrow> 'a spmf"
where "while s = (if guard s then bind_spmf (body s) while else return_spmf s)"

end

lemma while_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible P"
  and "P (\<lambda>while. return_pmf None)"
  and "\<And>while'. P while' \<Longrightarrow> P (\<lambda>s. if guard s then body s \<bind> while' else return_spmf s)"
  shows "P while"
  using assms by(rule while.fixp_induct)

lemma while_simps:
  "guard s \<Longrightarrow> while s = bind_spmf (body s) while"
  "\<not> guard s \<Longrightarrow> while s = return_spmf s"
by(rewrite while.simps; simp; fail)+

end

lemma while_spmf_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((S ===> (=)) ===> (S ===> rel_spmf S) ===> S ===> rel_spmf S) loop_spmf.while loop_spmf.while"
unfolding loop_spmf.while_def[abs_def]
apply(rule rel_funI)
apply(rule rel_funI)
apply(rule fixp_spmf_parametric[OF loop_spmf.while.mono loop_spmf.while.mono])
subgoal premises [transfer_rule] by transfer_prover
done

lemma loop_spmf_while_cong:
  "\<lbrakk> guard = guard'; \<And>s. guard' s \<Longrightarrow> body s = body' s \<rbrakk>
  \<Longrightarrow> loop_spmf.while guard body = loop_spmf.while guard' body'"
unfolding loop_spmf.while_def[abs_def] by(simp cong: if_cong)

section \<open>Rules for probabilistic termination\<close>

context loop_spmf begin

subsection \<open>0/1 termination laws\<close>

lemma termination_0_1_immediate:
  assumes p: "\<And>s. guard s \<Longrightarrow> spmf (map_spmf guard (body s)) False \<ge> p"
  and p_pos: "0 < p"
  and lossless: "\<And>s. guard s \<Longrightarrow> lossless_spmf (body s)"
  shows "lossless_spmf (while s)"
proof -
  have "\<forall>s. lossless_spmf (while s)"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    then obtain s where s: "\<not> lossless_spmf (while s)" by blast
    hence True: "guard s" by(simp add: while.simps split: if_split_asm)

    from p[OF this] have p_le_1: "p \<le> 1" using pmf_le_1 by(rule order_trans)
    have new_bound: "p * (1 - k) + k \<le> weight_spmf (while s)" 
      if k: "0 \<le> k" "k \<le> 1" and k_le: "\<And>s. k \<le> weight_spmf (while s)" for k s
    proof(cases "guard s")
      case False
      have "p * (1 - k) + k \<le> 1 * (1 - k) + k" using p_le_1 k by(intro mult_right_mono add_mono; simp)
      also have "\<dots> \<le> 1" by simp
      finally show ?thesis using False by(simp add: while.simps)
    next
      case True
      let ?M = "\<lambda>s. measure_spmf (body s)"
      have bounded: "\<bar>\<integral> s''. weight_spmf (while s'') \<partial>?M s'\<bar> \<le> 1" for s'
        using integral_nonneg_AE[of "\<lambda>s''. weight_spmf (while s'')" "?M s'"]
        by(auto simp add: weight_spmf_nonneg weight_spmf_le_1 intro!: measure_spmf.nn_integral_le_const integral_real_bounded)
      have "p \<le> measure (?M s) {s'. \<not> guard s'}" using p[OF True]
        by(simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def)
      hence "p * (1 - k) + k \<le> measure (?M s) {s'. \<not> guard s'} * (1 - k) + k"
        using k by(intro add_mono mult_right_mono)(simp_all)
      also have "\<dots> = \<integral> s'. indicator {s'. \<not> guard s'} s' * (1 - k) +  k \<partial>?M s"
        using True by(simp add: ennreal_less_top_iff lossless lossless_weight_spmfD)
      also have "\<dots> = \<integral> s'. indicator {s'. \<not> guard s'} s' + indicator {s'. guard s'} s' * k \<partial>?M s"
        by(rule Bochner_Integration.integral_cong)(simp_all split: split_indicator)
      also have "\<dots> = \<integral> s'. indicator {s'. \<not> guard s'} s' + indicator {s'. guard s'} s' * \<integral> s''. k \<partial>?M s' \<partial>?M s"
        by(rule Bochner_Integration.integral_cong)(auto simp add: lossless lossless_weight_spmfD split: split_indicator)
      also have "\<dots> \<le> \<integral> s'. indicator {s'. \<not> guard s'} s' + indicator {s'. guard s'} s' * \<integral> s''. weight_spmf (while s'') \<partial>?M s' \<partial>?M s"
        using k bounded
        by(intro integral_mono integrable_add measure_spmf.integrable_const_bound[where B=1] add_mono mult_left_mono)
          (simp_all add: weight_spmf_nonneg weight_spmf_le_1 mult_le_one k_le split: split_indicator)
      also have "\<dots> = \<integral>s'. (if \<not> guard s' then 1 else \<integral> s''. weight_spmf (while s'') \<partial>?M s') \<partial>?M s"
        by(rule Bochner_Integration.integral_cong)(simp_all split: split_indicator)
      also have "\<dots> = \<integral> s'. weight_spmf (while s') \<partial>measure_spmf (body s)"
        by(rule Bochner_Integration.integral_cong; simp add: while.simps weight_bind_spmf o_def)
      also have "\<dots> = weight_spmf (while s)" using True
        by(simp add: while.simps weight_bind_spmf o_def)
      finally show ?thesis .
    qed

    define k where "k \<equiv> INF s. weight_spmf (while s)"
    define k' where "k' \<equiv> p * (1 - k) + k"
    from s have "weight_spmf (while s) < 1"
      using weight_spmf_le_1[of "while s"] by(simp add: lossless_spmf_def)
    then have "k < 1"
      unfolding k_def by(rewrite cINF_less_iff)(auto intro!: bdd_belowI2 weight_spmf_nonneg)

    have "0 \<le> k" unfolding k_def by(auto intro: cINF_greatest simp add: weight_spmf_nonneg)
    moreover from \<open>k < 1\<close> have "k \<le> 1" by simp
    moreover have "k \<le> weight_spmf (while s)" for s unfolding k_def
      by(rule cINF_lower)(auto intro!: bdd_belowI2 weight_spmf_nonneg)
    ultimately have "\<And>s. k' \<le> weight_spmf (while s)"
      unfolding k'_def by(rule new_bound)
    hence "k' \<le> k" unfolding k_def by(auto intro: cINF_greatest)
    also have "k < k'" using p_pos \<open>k < 1\<close> by(auto simp add: k'_def)
    finally show False by simp
  qed
  thus ?thesis by blast
qed

primrec iter :: "nat \<Rightarrow> 'a \<Rightarrow> 'a spmf"
where
  "iter 0 s = return_spmf s"
| "iter (Suc n) s = (if guard s then bind_spmf (body s) (iter n) else return_spmf s)"

lemma iter_unguarded [simp]: "\<not> guard s \<Longrightarrow> iter n s = return_spmf s"
  by(induction n) simp_all
  
lemma iter_bind_iter: "bind_spmf (iter m s) (iter n) = iter (m + n) s"
  by(induction m arbitrary: s) simp_all

lemma iter_Suc2: "iter (Suc n) s = bind_spmf (iter n s) (\<lambda>s. if guard s then body s else return_spmf s)"
  using iter_bind_iter[of n s 1, symmetric]
  by(simp del: iter.simps)(rule bind_spmf_cong; simp cong: bind_spmf_cong)

lemma lossless_iter: "(\<And>s. guard s \<Longrightarrow> lossless_spmf (body s)) \<Longrightarrow> lossless_spmf (iter n s)"
  by(induction n arbitrary: s) simp_all

lemma iter_mono_emeasure1:
  "emeasure (measure_spmf (iter n s)) {s. \<not> guard s} \<le> emeasure (measure_spmf (iter (Suc n) s)) {s. \<not> guard s}"
  (is "?lhs \<le> ?rhs")
proof(cases "guard s")
  case True
  have "?lhs = emeasure (measure_spmf (bind_spmf (iter n s) return_spmf)) {s. \<not> guard s}" by simp
  also have "\<dots> = \<integral>\<^sup>+ s'. emeasure (measure_spmf (return_spmf s')) {s. \<not> guard s} \<partial>measure_spmf (iter n s)"
    by(simp del: bind_return_spmf add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
  also have "\<dots> \<le> \<integral>\<^sup>+ s'. emeasure (measure_spmf (if guard s' then body s' else return_spmf s')) {s. \<not> guard s} \<partial>measure_spmf (iter n s)"
    by(rule nn_integral_mono)(simp add: measure_spmf_return_spmf)
  also have "\<dots> = ?rhs"
    by(simp add: iter_Suc2 measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra del: iter.simps)
  finally show ?thesis .
qed simp

lemma weight_while_conv_iter:
  "weight_spmf (while s) = (SUP n. measure (measure_spmf (iter n s)) {s. \<not> guard s})"
  (is "?lhs = ?rhs")
proof(rule antisym)
  have "emeasure (measure_spmf (while s)) UNIV \<le> (SUP n. emeasure (measure_spmf (iter n s)) {s. \<not> guard s})"
    (is "_ \<le> (SUP n. ?f n s)")
  proof(induction arbitrary: s rule: while_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step while')
    show ?case (is "?lhs' \<le> ?rhs'")
    proof(cases "guard s")
      case True
      have inc: "incseq ?f" by(rule incseq_SucI le_funI iter_mono_emeasure1)+

      from True have "?lhs' = \<integral>\<^sup>+ s'. emeasure (measure_spmf (while' s')) UNIV \<partial>measure_spmf (body s)"
        by(simp add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
      also have "\<dots> \<le> \<integral>\<^sup>+ s'. (SUP n. ?f n s') \<partial>measure_spmf (body s)"
        by(rule nn_integral_mono)(rule step.IH)
      also have "\<dots> = (SUP n. \<integral>\<^sup>+ s'. ?f n s' \<partial>measure_spmf (body s))" using inc
        by(subst nn_integral_monotone_convergence_SUP) simp_all
      also have "\<dots> = (SUP n. ?f (Suc n) s)" using True
        by(simp add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
      also have "\<dots> \<le> (SUP n. ?f n s)"
        by(rule SUP_mono)(auto intro: exI[where x="Suc _"])
      finally show ?thesis .
    next
      case False
      then have "?lhs' = emeasure (measure_spmf (iter 0 s)) {s. \<not> guard s}" 
        by(simp add: measure_spmf_return_spmf)
      also have \<open>\<dots> \<le> ?rhs'\<close> by(rule SUP_upper) simp
      finally show ?thesis .
    qed
  qed
  also have "\<dots> = ennreal (SUP n. measure (measure_spmf (iter n s)) {s. \<not> guard s})"
    by(subst ennreal_SUP)(fold measure_spmf.emeasure_eq_measure, auto simp add: not_less measure_spmf.subprob_emeasure_le_1 intro!: exI[where x="1"])
  also have "0 \<le> (SUP n. measure (measure_spmf (iter n s)) {s. \<not> guard s})"
    by(rule cSUP_upper2)(auto intro!: bdd_aboveI[where M=1] simp add: measure_spmf.subprob_measure_le_1)
  ultimately show "?lhs \<le> ?rhs" by(simp add: measure_spmf.emeasure_eq_measure space_measure_spmf)
  
  show "?rhs \<le> ?lhs"
  proof(rule cSUP_least)
    show "measure (measure_spmf (iter n s)) {s. \<not> guard s} \<le> weight_spmf (while s)" (is "?f n s \<le> _") for n
    proof(induction n arbitrary: s)
      case 0 show ?case
        by(simp add: measure_spmf_return_spmf measure_return while_simps split: split_indicator)
    next
      case (Suc n)
      show ?case
      proof(cases "guard s")
        case True
        have "?f (Suc n) s = \<integral>\<^sup>+ s'. ?f n s' \<partial>measure_spmf (body s)"
          using True unfolding measure_spmf.emeasure_eq_measure[symmetric]
          by(simp add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
        also have "\<dots> \<le> \<integral>\<^sup>+ s'. weight_spmf (while s') \<partial>measure_spmf (body s)"
          by(rule nn_integral_mono ennreal_leI Suc.IH)+
        also have "\<dots> = weight_spmf (while s)"
          using True unfolding measure_spmf.emeasure_eq_measure[symmetric] space_measure_spmf
          by(simp add: while_simps measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
        finally show ?thesis by(simp)
      next
        case False then show ?thesis
          by(simp add: measure_spmf_return_spmf measure_return while_simps split: split_indicator)
      qed
    qed
  qed simp
qed

lemma termination_0_1:
  assumes p: "\<And>s. guard s \<Longrightarrow> p \<le> weight_spmf (while s)"
    and p_pos: "0 < p"
    and lossless: "\<And>s. guard s \<Longrightarrow> lossless_spmf (body s)"
  shows "lossless_spmf (while s)"
  unfolding lossless_spmf_def
proof(rule antisym)
  let ?X = "{s. \<not> guard s}"
  show "weight_spmf (while s) \<le> 1" by(rule weight_spmf_le_1)
  
  define p' where "p' \<equiv> p / 2"
  have p'_pos: "p' > 0" and "p' < p" using p_pos by(simp_all add: p'_def)
  
  have "\<exists>n. p' < measure (measure_spmf (iter n s)) ?X" if "guard s" for s using p[OF that] \<open>p' < p\<close>
    unfolding weight_while_conv_iter
    by(subst (asm) le_cSUP_iff)(auto intro!: measure_spmf.subprob_measure_le_1)
  then obtain N where p': "p' \<le> measure (measure_spmf (iter (N s) s)) ?X" if "guard s" for s
    using p by atomize_elim(rule choice, force dest: order.strict_implies_order)

  interpret fuse: loop_spmf guard "\<lambda>s. iter (N s) s" .
  
  have "1 = weight_spmf (fuse.while s)"
    by(rule lossless_weight_spmfD[symmetric])
      (rule fuse.termination_0_1_immediate; auto simp add: spmf_map vimage_def intro: p' p'_pos lossless_iter lossless)
  also have "\<dots> \<le> (\<Squnion>n. measure (measure_spmf (iter n s)) ?X)"
    unfolding fuse.weight_while_conv_iter
  proof(rule cSUP_least)
    fix n
    have "emeasure (measure_spmf (fuse.iter n s)) ?X \<le> (SUP n. emeasure (measure_spmf (iter n s)) ?X)"
    proof(induction n arbitrary: s)
      case 0 show ?case by(auto intro!: SUP_upper2[where i=0])
    next
      case (Suc n)
      have inc: "incseq (\<lambda>n s'. emeasure (measure_spmf (iter n s')) ?X)"
        by(rule incseq_SucI le_funI iter_mono_emeasure1)+

      have "emeasure (measure_spmf (fuse.iter (Suc n) s)) ?X = emeasure (measure_spmf (iter (N s) s \<bind> fuse.iter n)) ?X"
        by simp
      also have "\<dots> = \<integral>\<^sup>+ s'. emeasure (measure_spmf (fuse.iter n s')) ?X \<partial>measure_spmf (iter (N s) s)"
        by(simp add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
      also have "\<dots> \<le> \<integral>\<^sup>+ s'. (SUP n. emeasure (measure_spmf (iter n s')) ?X) \<partial>measure_spmf (iter (N s) s)"
        by(rule nn_integral_mono Suc.IH)+
      also have "\<dots> = (SUP n. \<integral>\<^sup>+ s'. emeasure (measure_spmf (iter n s')) ?X \<partial>measure_spmf (iter (N s) s))"
        by(rule nn_integral_monotone_convergence_SUP[OF inc]) simp
      also have "\<dots> = (SUP n. emeasure (measure_spmf (bind_spmf (iter (N s) s) (iter n))) ?X)"
        by(simp add: measure_spmf_bind o_def emeasure_bind[where N="measure_spmf _"] space_measure_spmf Pi_def space_subprob_algebra)
      also have "\<dots> = (SUP n. emeasure (measure_spmf (iter (N s + n) s)) ?X)" by(simp add: iter_bind_iter)
      also have "\<dots> \<le> (SUP n. emeasure (measure_spmf (iter n s)) ?X)" by(rule SUP_mono) auto
      finally show ?case .
    qed
    also have "\<dots> = ennreal (SUP n. measure (measure_spmf (iter n s)) ?X)"
      by(subst ennreal_SUP)(fold measure_spmf.emeasure_eq_measure, auto simp add: not_less measure_spmf.subprob_emeasure_le_1 intro!: exI[where x="1"])
    also have "0 \<le> (SUP n. measure (measure_spmf (iter n s)) ?X)"
      by(rule cSUP_upper2)(auto intro!: bdd_aboveI[where M=1] simp add: measure_spmf.subprob_measure_le_1)
    ultimately show "measure (measure_spmf (fuse.iter n s)) ?X \<le> \<dots>"
      by(simp add: measure_spmf.emeasure_eq_measure)
  qed simp
  finally show  "1 \<le> weight_spmf (while s)" unfolding weight_while_conv_iter .
qed

end

lemma termination_0_1_immediate_invar:
  fixes I :: "'s \<Rightarrow> bool"
  assumes p: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> spmf (map_spmf guard (body s)) False \<ge> p"
  and p_pos: "0 < p"
  and lossless: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> lossless_spmf (body s)"
  and invar: "\<And>s s'. \<lbrakk> s' \<in> set_spmf (body s); I s; guard s \<rbrakk> \<Longrightarrow> I s'"
  and I: "I s"
  shows "lossless_spmf (loop_spmf.while guard body s)"
  including lifting_syntax
proof -
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr \<equiv> \<lambda>x y. x = Rep y"
    have [transfer_rule]: "bi_unique cr" "right_total cr" using td cr_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I" using type_definition_Domainp[OF td cr_def] by simp

    define guard' where "guard' \<equiv> (Rep ---> id) guard"
    have [transfer_rule]: "(cr ===> (=)) guard guard'" by(simp add: rel_fun_def cr_def guard'_def)
    define body1 where "body1 \<equiv> \<lambda>s. if guard s then body s else return_pmf None"
    define body1' where "body1' \<equiv> (Rep ---> map_spmf Abs) body1"
    have [transfer_rule]: "(cr ===> rel_spmf cr) body1 body1'"
      by(auto simp add: rel_fun_def body1'_def body1_def cr_def spmf_rel_map td.Rep[simplified] invar td.Abs_inverse intro!: rel_spmf_reflI)
    define s' where "s' \<equiv> Abs s"
    have [transfer_rule]: "cr s s'" by(simp add: s'_def cr_def I td.Abs_inverse)

    have "\<And>s. guard' s \<Longrightarrow> p \<le> spmf (map_spmf guard' (body1' s)) False"
      by(transfer fixing: p)(simp add: body1_def p)
    moreover note p_pos
    moreover have "\<And>s. guard' s \<Longrightarrow> lossless_spmf (body1' s)" by transfer(simp add: lossless body1_def)
    ultimately have "lossless_spmf (loop_spmf.while guard' body1' s')" by(rule loop_spmf.termination_0_1_immediate)
    hence "lossless_spmf (loop_spmf.while guard body1 s)" by transfer }
  from this[cancel_type_definition] I show ?thesis by(auto cong: loop_spmf_while_cong)
qed

lemma termination_0_1_invar:
  fixes I :: "'s \<Rightarrow> bool"
  assumes p: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> p \<le> weight_spmf (loop_spmf.while guard body s)"
    and p_pos: "0 < p"
    and lossless: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> lossless_spmf (body s)"
    and invar: "\<And>s s'. \<lbrakk> s' \<in> set_spmf (body s); I s; guard s \<rbrakk> \<Longrightarrow> I s'"
    and I: "I s"
  shows "lossless_spmf (loop_spmf.while guard body s)"
  including lifting_syntax
proof-
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr \<equiv> \<lambda>x y. x = Rep y"
    have [transfer_rule]: "bi_unique cr" "right_total cr" using td cr_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I" using type_definition_Domainp[OF td cr_def] by simp

    define guard' where "guard' \<equiv> (Rep ---> id) guard"
    have [transfer_rule]: "(cr ===> (=)) guard guard'" by(simp add: rel_fun_def cr_def guard'_def)
    define body1 where "body1 \<equiv> \<lambda>s. if guard s then body s else return_pmf None"
    define body1' where "body1' \<equiv> (Rep ---> map_spmf Abs) body1"
    have [transfer_rule]: "(cr ===> rel_spmf cr) body1 body1'"
      by(auto simp add: rel_fun_def body1'_def body1_def cr_def spmf_rel_map td.Rep[simplified] invar td.Abs_inverse intro!: rel_spmf_reflI)
    define s' where "s' \<equiv> Abs s"
    have [transfer_rule]: "cr s s'" by(simp add: s'_def cr_def I td.Abs_inverse)
    
    interpret loop_spmf guard' body1' .

    note UNIV_parametric_pred[transfer_rule]
    have "\<And>s. guard' s \<Longrightarrow> p \<le> weight_spmf (while s)"
      unfolding measure_measure_spmf_def[symmetric] space_measure_spmf
      by(transfer fixing: p)(simp add: body1_def p[simplified space_measure_spmf] cong: loop_spmf_while_cong)
    moreover note p_pos
    moreover have "\<And>s. guard' s \<Longrightarrow> lossless_spmf (body1' s)" by transfer(simp add: lossless body1_def)
    ultimately have "lossless_spmf (while s')" by(rule termination_0_1)
    hence "lossless_spmf (loop_spmf.while guard body1 s)" by transfer }
  from this[cancel_type_definition] I show ?thesis by(auto cong: loop_spmf_while_cong)
qed

subsection \<open>Variant rule\<close>

context loop_spmf begin

lemma termination_variant:
  fixes bound :: nat
  assumes bound: "\<And>s. guard s \<Longrightarrow> f s \<le> bound"
  and step: "\<And>s. guard s \<Longrightarrow> p \<le> spmf (map_spmf (\<lambda>s'. f s' < f s) (body s)) True"
  and p_pos: "0 < p"
  and lossless: "\<And>s. guard s \<Longrightarrow> lossless_spmf (body s)"
  shows "lossless_spmf (while s)"
proof -
  define p' and n where "p' \<equiv> min p 1" and "n \<equiv> bound + 1"
  have p'_pos: "0 < p'" and p'_le_1: "p' \<le> 1" 
    and step': "guard s \<Longrightarrow> p' \<le> measure (measure_spmf (body s)) {s'. f s' < f s}" for s
    using p_pos step[of s] by(simp_all add: p'_def spmf_map vimage_def)
  have "p' ^ n \<le> weight_spmf (while s)" if "f s < n" for s using that
  proof(induction n arbitrary: s)
    case 0 thus ?case by simp
  next
    case (Suc n)
    show ?case
    proof(cases "guard s")
      case False
      hence "weight_spmf (while s) = 1" by(simp add: while.simps)
      thus ?thesis using p'_le_1 p_pos 
        by simp(meson less_eq_real_def mult_le_one p'_pos power_le_one zero_le_power)
    next
      case True
      let ?M = "measure_spmf (body s)"
      have "p' ^ Suc n \<le> (\<integral> s'. indicator {s'. f s' < f s} s' \<partial>?M) * p' ^ n"
        using step'[OF True] p'_pos by(simp add: mult_right_mono)
      also have "\<dots> = (\<integral> s'. indicator {s'. f s' < f s} s' * p' ^ n \<partial>?M)" by simp
      also have "\<dots> \<le> (\<integral> s'. indicator {s'. f s' < f s} s' * weight_spmf (while s') \<partial>?M)"
        using Suc.prems p'_le_1 p'_pos
        by(intro integral_mono)(auto simp add: Suc.IH power_le_one weight_spmf_le_1 split: split_indicator intro!: measure_spmf.integrable_const_bound[where B=1])
      also have "\<dots> \<le> \<dots> + (\<integral> s'. indicator {s'. f s' \<ge> f s} s' * weight_spmf (while s') \<partial>?M)"
        by(simp add: integral_nonneg_AE weight_spmf_nonneg)
      also have "\<dots> = \<integral> s'. weight_spmf (while s') \<partial>?M"
        by(subst Bochner_Integration.integral_add[symmetric])
          (auto intro!: Bochner_Integration.integral_cong measure_spmf.integrable_const_bound[where B=1] weight_spmf_le_1 split: split_indicator)
      also have "\<dots> = weight_spmf (while s)"
        using True by(subst (1 2) while.simps)(simp add: weight_bind_spmf o_def)
      finally show ?thesis .
    qed
  qed
  moreover have "0 < p' ^ n" using p'_pos by simp
  ultimately show ?thesis using lossless
  proof(rule termination_0_1_invar)
    show "f s < n" if "guard s" "guard s \<longrightarrow> f s < n" for s using that by simp
    show "guard s \<longrightarrow> f s < n" using bound[of s] by(auto simp add: n_def)
    show "guard s' \<longrightarrow> f s' < n" for s' using bound[of s'] by(clarsimp simp add: n_def)
  qed
qed

end

lemma termination_variant_invar:
  fixes bound :: nat and I :: "'s \<Rightarrow> bool"
  assumes bound: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> f s \<le> bound"
  and step: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> p \<le> spmf (map_spmf (\<lambda>s'. f s' < f s) (body s)) True"
  and p_pos: "0 < p"
  and lossless: "\<And>s. \<lbrakk> guard s; I s \<rbrakk> \<Longrightarrow> lossless_spmf (body s)"
  and invar: "\<And>s s'. \<lbrakk> s' \<in> set_spmf (body s); I s; guard s \<rbrakk> \<Longrightarrow> I s'"
  and I: "I s"
  shows "lossless_spmf (loop_spmf.while guard body s)"
  including lifting_syntax
proof -
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr \<equiv> \<lambda>x y. x = Rep y"
    have [transfer_rule]: "bi_unique cr" "right_total cr" using td cr_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I" using type_definition_Domainp[OF td cr_def] by simp

    define guard' where "guard' \<equiv> (Rep ---> id) guard"
    have [transfer_rule]: "(cr ===> (=)) guard guard'" by(simp add: rel_fun_def cr_def guard'_def)
    define body1 where "body1 \<equiv> \<lambda>s. if guard s then body s else return_pmf None"
    define body1' where "body1' \<equiv> (Rep ---> map_spmf Abs) body1"
    have [transfer_rule]: "(cr ===> rel_spmf cr) body1 body1'"
      by(auto simp add: rel_fun_def body1'_def body1_def cr_def spmf_rel_map td.Rep[simplified] invar td.Abs_inverse intro!: rel_spmf_reflI)
    define s' where "s' \<equiv> Abs s"
    have [transfer_rule]: "cr s s'" by(simp add: s'_def cr_def I td.Abs_inverse)
    define f' where "f' \<equiv> (Rep ---> id) f"
    have [transfer_rule]: "(cr ===> (=)) f f'" by(simp add: rel_fun_def cr_def f'_def)

    have "\<And>s. guard' s \<Longrightarrow> f' s \<le> bound" by(transfer fixing: bound)(rule bound)
    moreover have "\<And>s. guard' s \<Longrightarrow> p \<le> spmf (map_spmf (\<lambda>s'. f' s' < f' s) (body1' s)) True"
      by(transfer fixing: p)(simp add: step body1_def)
    note this p_pos
    moreover have "\<And>s. guard' s \<Longrightarrow> lossless_spmf (body1' s)"
      by transfer(simp add: body1_def lossless)
    ultimately have "lossless_spmf (loop_spmf.while guard' body1' s')" by(rule loop_spmf.termination_variant)
    hence "lossless_spmf (loop_spmf.while guard body1 s)" by transfer }
  from this[cancel_type_definition] I show ?thesis by(auto cong: loop_spmf_while_cong)
qed

end
