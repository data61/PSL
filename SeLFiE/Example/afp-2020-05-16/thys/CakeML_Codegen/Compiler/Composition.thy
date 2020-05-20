section \<open>Composition of correctness results\<close>

theory Composition
imports "../Backend/CakeML_Correctness"
begin

hide_const (open) sem_env.v

text \<open>@{typ term} \<open>\<longrightarrow>\<close> @{typ nterm} \<open>\<longrightarrow>\<close> @{typ pterm} \<open>\<longrightarrow>\<close> @{typ sterm}\<close>

subsection \<open>Reflexive-transitive closure of @{thm [source=true] irules.compile_correct}.\<close>

lemma (in prules) prewrite_closed:
  assumes "rs \<turnstile>\<^sub>p t \<longrightarrow> t'" "closed t"
  shows "closed t'"
using assms proof induction
  case (step name rhs)
  thus ?case
    using all_rules by force
next
  case (beta c)
  obtain pat rhs where "c = (pat, rhs)" by (cases c) auto
  with beta have "closed_except rhs (frees pat)"
    by (auto simp: closed_except_simps)
  show ?case
    apply (rule rewrite_step_closed[OF _ beta(2)[unfolded \<open>c = _\<close>]])
    using \<open>closed_except rhs (frees pat)\<close> beta by (auto simp: closed_except_def)
qed (auto simp: closed_except_def)

corollary (in prules) prewrite_rt_closed:
  assumes "rs \<turnstile>\<^sub>p t \<longrightarrow>* t'" "closed t"
  shows "closed t'"
using assms
by induction (auto intro: prewrite_closed)

corollary (in irules) compile_correct_rt:
  assumes "Rewriting_Pterm.compile rs \<turnstile>\<^sub>p t \<longrightarrow>* t'" "finished rs"
  shows "rs \<turnstile>\<^sub>i t \<longrightarrow>* t'"
using assms proof (induction rule: rtranclp_induct)
  case step
  thus ?case
    by (meson compile_correct rtranclp.simps)
qed auto


subsection \<open>Reflexive-transitive closure of @{thm [source=true] prules.compile_correct}.\<close>

lemma (in prules) compile_correct_rt:
  assumes "Rewriting_Sterm.compile rs \<turnstile>\<^sub>s u \<longrightarrow>* u'"
  shows "rs \<turnstile>\<^sub>p sterm_to_pterm u \<longrightarrow>* sterm_to_pterm u'"
using assms proof induction
  case step
  thus ?case
    by (meson compile_correct rtranclp.simps)
qed auto

lemma srewrite_stepD:
  assumes "srewrite_step rs name t"
  shows "(name, t) \<in> set rs"
using assms by induct auto

lemma (in srules) srewrite_wellformed:
  assumes "rs \<turnstile>\<^sub>s t \<longrightarrow> t'" "wellformed t"
  shows "wellformed t'"
using assms proof induction
  case (step name rhs)
  hence "(name, rhs) \<in> set rs"
    by (auto dest: srewrite_stepD)
  thus ?case
    using all_rules by (auto simp: list_all_iff)
next
  case (beta cs t t')
  then obtain pat rhs env where "(pat, rhs) \<in> set cs" "match pat t = Some env" "t' = subst rhs env"
    by (elim rewrite_firstE)
  show ?case
    unfolding \<open>t' = _\<close>
    proof (rule subst_wellformed)
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> beta by (auto simp: list_all_iff)
    next
      show "wellformed_env env"
        using \<open>match pat t = Some env\<close> beta
        by (auto intro: wellformed.match)
    qed
qed auto

lemma (in srules) srewrite_wellformed_rt:
  assumes "rs \<turnstile>\<^sub>s t \<longrightarrow>* t'" "wellformed t"
  shows "wellformed t'"
using assms
by induction (auto intro: srewrite_wellformed)

lemma vno_abs_value_to_sterm: "no_abs (value_to_sterm v) \<longleftrightarrow> vno_abs v" for v
by (induction v) (auto simp: no_abs.list_comb list_all_iff)


subsection \<open>Reflexive-transitive closure of @{thm [source=true] rules.compile_correct}.\<close>

corollary (in rules) compile_correct_rt:
  assumes "compile \<turnstile>\<^sub>n u \<longrightarrow>* u'" "closed u"
  shows "rs \<turnstile> nterm_to_term' u \<longrightarrow>* nterm_to_term' u'"
using assms
proof induction
  case (step u' u'')
  hence "rs \<turnstile> nterm_to_term' u \<longrightarrow>* nterm_to_term' u'"
    by auto
  also have "rs \<turnstile> nterm_to_term' u' \<longrightarrow> nterm_to_term' u''"
    using step by (auto dest: rewrite_rt_closed intro!: compile_correct simp: closed_except_def)
  finally show ?case .
qed auto


subsection \<open>Reflexive-transitive closure of @{thm [source=true] irules.transform_correct}.\<close>

corollary (in irules) transform_correct_rt:
  assumes "transform_irule_set rs \<turnstile>\<^sub>i u \<longrightarrow>* u''" "t \<approx>\<^sub>p u" "closed t"
  obtains t'' where "rs \<turnstile>\<^sub>i t \<longrightarrow>* t''" "t'' \<approx>\<^sub>p u''"
using assms proof (induction arbitrary: thesis t)
  case (step u' u'')

  obtain t' where "rs \<turnstile>\<^sub>i t \<longrightarrow>* t'" "t' \<approx>\<^sub>p u'"
    using step by blast

  obtain t'' where "rs \<turnstile>\<^sub>i t' \<longrightarrow>* t''" "t'' \<approx>\<^sub>p u''"
    apply (rule transform_correct)
       apply (rule \<open>transform_irule_set rs \<turnstile>\<^sub>i u' \<longrightarrow> u''\<close>)
      apply (rule \<open>t' \<approx>\<^sub>p u'\<close>)
     apply (rule irewrite_rt_closed)
      apply (rule \<open>rs \<turnstile>\<^sub>i t \<longrightarrow>* t'\<close>)
     apply (rule \<open>closed t\<close>)
    apply blast
    done

  show ?case
    apply (rule step.prems)
     apply (rule rtranclp_trans)
      apply fact+
    done
qed blast

corollary (in irules) transform_correct_rt_no_abs:
  assumes "transform_irule_set rs \<turnstile>\<^sub>i t \<longrightarrow>* u" "closed t" "no_abs u"
  shows "rs \<turnstile>\<^sub>i t \<longrightarrow>* u"
proof -
  have "t \<approx>\<^sub>p t" by (rule prelated_refl)
  obtain t' where "rs \<turnstile>\<^sub>i t \<longrightarrow>* t'" "t' \<approx>\<^sub>p u"
    apply (rule transform_correct_rt)
       apply (rule assms)
      apply (rule \<open>t \<approx>\<^sub>p t\<close>)
     apply (rule assms)
    apply blast
    done
  thus ?thesis
    using assms by (metis prelated_no_abs_right)
qed

corollary transform_correct_rt_n_no_abs0:
  assumes "irules C rs" "(transform_irule_set ^^ n) rs \<turnstile>\<^sub>i t \<longrightarrow>* u" "closed t" "no_abs u"
  shows "rs \<turnstile>\<^sub>i t \<longrightarrow>* u"
using assms(1,2) proof (induction n arbitrary: rs)
  case (Suc n)
  interpret irules C rs by fact
  show ?case
    apply (rule transform_correct_rt_no_abs)
      apply (rule Suc.IH)
       apply (rule rules_transform)
    using Suc(3) apply (simp add: funpow_swap1)
     apply fact+
    done
qed auto

corollary (in irules) transform_correct_rt_n_no_abs:
  assumes "(transform_irule_set ^^ n) rs \<turnstile>\<^sub>i t \<longrightarrow>* u" "closed t" "no_abs u"
  shows "rs \<turnstile>\<^sub>i t \<longrightarrow>* u"
by (rule transform_correct_rt_n_no_abs0) (rule irules_axioms assms)+

hide_fact transform_correct_rt_n_no_abs0


subsection \<open>Iterated application of @{const transform_irule_set}.\<close>

definition max_arity :: "irule_set \<Rightarrow> nat" where
"max_arity rs = fMax ((arity \<circ> snd) |`| rs)"

lemma rules_transform_iter0:
  assumes "irules C_info rs"
  shows "irules C_info ((transform_irule_set ^^ n) rs)"
using assms
by (induction n) (auto intro: irules.rules_transform del: irulesI)

lemma (in irules) rules_transform_iter: "irules C_info ((transform_irule_set ^^ n) rs)"
by (rule rules_transform_iter0) (rule irules_axioms)

lemma transform_irule_set_n_heads: "fst |`| ((transform_irule_set ^^ n) rs) = fst |`| rs"
by (induction n) (auto simp: transform_irule_set_heads)

hide_fact rules_transform_iter0

definition transform_irule_set_iter :: "irule_set \<Rightarrow> irule_set" where
"transform_irule_set_iter rs = (transform_irule_set ^^ max_arity rs) rs"

lemma transform_irule_set_iter_heads: "fst |`| transform_irule_set_iter rs = fst |`| rs"
unfolding transform_irule_set_iter_def by (simp add: transform_irule_set_n_heads)

lemma (in irules) finished_alt_def: "finished rs \<longleftrightarrow> max_arity rs = 0"
proof
  assume "max_arity rs = 0"
  hence "\<not> fBex ((arity \<circ> snd) |`| rs) (\<lambda>x. 0 < x)"
    using nonempty
    unfolding max_arity_def
    by (metis fBex_fempty fmax_ex_gr not_less0)
  thus "finished rs"
    unfolding finished_def
    by force
next
  assume "finished rs"
  have "fMax ((arity \<circ> snd) |`| rs) \<le> 0"
    proof (rule fMax_le)
      show "fBall ((arity \<circ> snd) |`| rs) (\<lambda>x. x \<le> 0)"
        using \<open>finished rs\<close> unfolding finished_def by force
    next
      show "(arity \<circ> snd) |`| rs \<noteq> {||}"
        using nonempty by force
    qed
  thus "max_arity rs = 0"
    unfolding max_arity_def by simp
qed

lemma (in irules) transform_finished_id: "finished rs \<Longrightarrow> transform_irule_set rs = rs"
unfolding transform_irule_set_def finished_def transform_irules_def map_prod_def id_apply
by (rule fset_map_snd_id) (auto simp: fmember.rep_eq elim!: fBallE)

lemma (in irules) max_arity_decr: "max_arity (transform_irule_set rs) = max_arity rs - 1"
proof (cases "finished rs")
  case True
  thus ?thesis
    by (auto simp: transform_finished_id finished_alt_def)
next
  case False
  have "(arity \<circ> snd) |`| transform_irule_set rs = (\<lambda>x. x - 1) |`| (arity \<circ> snd) |`| rs"
    unfolding transform_irule_set_def fset.map_comp
    proof (rule fset.map_cong0, safe, unfold o_apply map_prod_simp id_apply snd_conv)
      fix name irs
      assume "(name, irs) \<in> fset rs"
      hence "(name, irs) |\<in>| rs"
        by (simp add: fmember.rep_eq)
      hence "arity_compatibles irs" "irs \<noteq> {||}"
        using nonempty inner by (blast dest: fpairwiseD)+
      thus "arity (transform_irules irs) = arity irs - 1"
        by (simp add: arity_transform_irules)
    qed
  hence "max_arity (transform_irule_set rs) = fMax ((\<lambda>x. x - 1) |`| (arity \<circ> snd) |`| rs)"
    unfolding max_arity_def by simp
  also have "\<dots> = fMax ((arity \<circ> snd) |`| rs) - 1"
    proof (rule fmax_decr)
      show "fBex ((arity \<circ> snd) |`| rs) ((\<le>) 1)"
        using False unfolding finished_def by force
    qed
  finally show ?thesis
    unfolding max_arity_def
    by simp
qed

lemma max_arity_decr'0:
  assumes "irules C rs"
  shows "max_arity ((transform_irule_set ^^ n) rs) = max_arity rs - n"
proof (induction n)
  case (Suc n)
  show ?case
    apply simp
    apply (subst irules.max_arity_decr)
    using Suc assms by (auto intro: irules.rules_transform_iter del: irulesI)
qed auto

lemma (in irules) max_arity_decr': "max_arity ((transform_irule_set ^^ n) rs) = max_arity rs - n"
by (rule max_arity_decr'0) (rule irules_axioms)

hide_fact max_arity_decr'0

lemma (in irules) transform_finished: "finished (transform_irule_set_iter rs)"
unfolding transform_irule_set_iter_def
by (subst irules.finished_alt_def)
   (auto simp: max_arity_decr' intro: rules_transform_iter del: Rewriting_Pterm_Elim.irulesI)

text \<open>Trick as described in \<open>\<section>7.1\<close> in the locale manual.\<close>
locale irules' = irules

sublocale irules' \<subseteq> irules'_as_irules: irules C_info "transform_irule_set_iter rs"
unfolding transform_irule_set_iter_def by (rule rules_transform_iter)

sublocale crules \<subseteq> crules_as_irules': irules' C_info "Rewriting_Pterm_Elim.compile rs"
unfolding irules'_def by (fact compile_rules)

sublocale irules' \<subseteq> irules'_as_prules: prules C_info "Rewriting_Pterm.compile (transform_irule_set_iter rs)"
by (rule irules'_as_irules.compile_rules) (rule transform_finished)


subsection \<open>Big-step semantics\<close>

context srules begin

definition global_css :: "(name, sclauses) fmap" where
"global_css = fmap_of_list (map (map_prod id clauses) rs)"

lemma fmdom_global_css: "fmdom global_css = fst |`| fset_of_list rs"
unfolding global_css_def by simp

definition as_vrules :: "vrule list" where
"as_vrules = map (\<lambda>(name, _). (name, Vrecabs global_css name fmempty)) rs"

lemma as_vrules_fst[simp]: "fst |`| fset_of_list as_vrules = fst |`| fset_of_list rs"
unfolding as_vrules_def
  apply simp
  apply (rule fset.map_cong)
  apply (rule refl)
  by auto

lemma as_vrules_fst'[simp]: "map fst as_vrules = map fst rs"
unfolding as_vrules_def
  by auto

lemma list_all_as_vrulesI:
  assumes "list_all (\<lambda>(_, t). P fmempty (clauses t)) rs"
  assumes "R (fst |`| fset_of_list rs)"
  shows "list_all (\<lambda>(_, t). value_pred.pred P Q R t) as_vrules"
proof (rule list_allI, safe)
  fix name rhs
  assume "(name, rhs) \<in> set as_vrules"
  hence "rhs = Vrecabs global_css name fmempty"
    unfolding as_vrules_def by auto

  moreover have "fmpred (\<lambda>_. P fmempty) global_css"
    unfolding global_css_def list.pred_map
    using assms by (auto simp: list_all_iff intro!: fmpred_of_list)

  moreover have "name |\<in>| fmdom global_css"
    unfolding global_css_def
    apply auto
    using \<open>(name, rhs) \<in> set as_vrules\<close> unfolding as_vrules_def
    including fset.lifting apply transfer'
    by force

  moreover have "R (fmdom global_css)"
    using assms unfolding global_css_def
    by auto

  ultimately show "value_pred.pred P Q R rhs"
    by (simp add: value_pred.pred_alt_def)
qed

lemma srules_as_vrules: "vrules C_info as_vrules"
proof (standard, unfold as_vrules_fst)
  have "list_all (\<lambda>(_, t). vwellformed t) as_vrules"
    unfolding vwellformed_def
    apply (rule list_all_as_vrulesI)
     apply (rule list.pred_mono_strong)
      apply (rule all_rules)
     apply (auto elim: clausesE)
    done

  moreover have "list_all (\<lambda>(_, t). vclosed t) as_vrules"
    unfolding vclosed_def
    apply (rule list_all_as_vrulesI)
     apply auto
    apply (rule list.pred_mono_strong)
     apply (rule all_rules)
    apply (auto elim: clausesE simp: Sterm.closed_except_simps)
    done

  moreover have "list_all (\<lambda>(_, t). \<not> is_Vconstr t) as_vrules"
    unfolding as_vrules_def
    by (auto simp: list_all_iff)

  ultimately show "list_all vrule as_vrules"
    unfolding list_all_iff by fastforce
next
  show "distinct (map fst as_vrules)"
    using distinct by auto
next
  show "fdisjnt (fst |`| fset_of_list rs) C"
    using disjnt by simp
next
  show "list_all (\<lambda>(_, rhs). not_shadows_vconsts rhs) as_vrules"
    unfolding not_shadows_vconsts_def
    apply (rule list_all_as_vrulesI)
     apply auto
    apply (rule list.pred_mono_strong)
     apply (rule not_shadows)
    by (auto simp: list_all_iff list_ex_iff all_consts_def elim!: clausesE)
next
  show "vconstructor_value_rs as_vrules"
    unfolding vconstructor_value_rs_def
    apply (rule conjI)
    unfolding vconstructor_value_def
     apply (rule list_all_as_vrulesI)
      apply (simp add: list_all_iff)
     apply simp
    apply simp
    using disjnt by simp
next
  show "list_all (\<lambda>(_, rhs). vwelldefined rhs) as_vrules"
    unfolding vwelldefined_def
    apply (rule list_all_as_vrulesI)
     apply auto
    apply (rule list.pred_mono_strong)
     apply (rule swelldefined_rs)
    apply auto
    apply (erule clausesE)
    apply hypsubst_thin
    apply (subst (asm) welldefined_sabs)
    by simp
next
  show "distinct all_constructors"
    by (fact distinct_ctr)
qed

sublocale srules_as_vrules: vrules C_info as_vrules
by (fact srules_as_vrules)

lemma rs'_rs_eq: "srules_as_vrules.rs' = rs"
unfolding srules_as_vrules.rs'_def
unfolding as_vrules_def
apply (subst map_prod_def)
apply simp
unfolding comp_def
apply (subst case_prod_twice)
apply (rule list_map_snd_id)
unfolding global_css_def
using all_rules map
apply (auto simp: list_all_iff map_of_is_map map_of_map map_prod_def fmap_of_list.rep_eq)
subgoal for a b
  by (erule ballE[where x = "(a, b)"], cases b, auto simp: is_abs_def term_cases_def)
done

lemma veval_correct:
  fixes v
  assumes "as_vrules, fmempty \<turnstile>\<^sub>v t \<down> v" "wellformed t" "closed t"
  shows "rs, fmempty \<turnstile>\<^sub>s t \<down> value_to_sterm v"
using assms
by (rule srules_as_vrules.veval_correct[unfolded rs'_rs_eq])

end


subsection \<open>ML-style semantics\<close>

context srules begin

lemma as_vrules_mk_rec_env: "fmap_of_list as_vrules = mk_rec_env global_css fmempty"
apply (subst global_css_def)
apply (subst as_vrules_def)
apply (subst mk_rec_env_def)
apply (rule fmap_ext)
apply (subst fmlookup_fmmap_keys)
apply (subst fmap_of_list.rep_eq)
apply (subst fmap_of_list.rep_eq)
apply (subst map_of_map_keyed)
apply (subst (2) map_prod_def)
apply (subst id_apply)
apply (subst map_of_map)
apply simp
apply (subst option.map_comp)
apply (rule option.map_cong)
 apply (rule refl)
apply simp
apply (subst global_css_def)
apply (rule refl)
done

abbreviation (input) "vrelated \<equiv> srules_as_vrules.vrelated"
notation srules_as_vrules.vrelated ("\<turnstile>\<^sub>v/ _ \<approx> _" [0, 50] 50)

lemma vrecabs_global_css_refl:
  assumes "name |\<in>| fmdom global_css"
  shows "\<turnstile>\<^sub>v Vrecabs global_css name fmempty \<approx> Vrecabs global_css name fmempty"
using assms
proof (coinduction arbitrary: name)
  case vrelated
  have "rel_option (\<lambda>v\<^sub>1 v\<^sub>2. (\<exists>name. v\<^sub>1 = Vrecabs global_css name fmempty \<and> v\<^sub>2 = Vrecabs global_css name fmempty \<and> name |\<in>| fmdom global_css) \<or> \<turnstile>\<^sub>v v\<^sub>1 \<approx> v\<^sub>2) (fmlookup (fmap_of_list as_vrules) y) (fmlookup (mk_rec_env global_css fmempty) y)" for y
    apply (subst as_vrules_mk_rec_env)
    apply (rule option.rel_refl_strong)
    apply (rule disjI1)
    apply (simp add: mk_rec_env_def)
    apply (elim conjE exE)
    apply (intro exI conjI)
    by (auto intro: fmdomI)
  with vrelated show ?case
    by fastforce
qed

lemma as_vrules_refl_rs: "fmrel_on_fset (fst |`| fset_of_list as_vrules) vrelated (fmap_of_list as_vrules) (fmap_of_list as_vrules)"
apply rule
apply (subst (2) as_vrules_def)
apply (subst (2) as_vrules_def)
apply (simp add: fmap_of_list.rep_eq)
apply (rule rel_option_reflI)
apply simp
apply (drule map_of_SomeD)
apply auto
apply (rule vrecabs_global_css_refl)
unfolding global_css_def
by (auto simp: fset_of_list_elem intro: rev_fimage_eqI)

lemma as_vrules_refl_C: "fmrel_on_fset C vrelated (fmap_of_list as_vrules) (fmap_of_list as_vrules)"
proof
  fix c
  assume "c |\<in>| C"
  hence "c |\<notin>| fset_of_list (map fst as_vrules)"
    using srules_as_vrules.vconstructor_value_rs
    unfolding vconstructor_value_rs_def fdisjnt_alt_def
    by auto
  hence "c |\<notin>| fmdom (fmap_of_list as_vrules)"
    by simp
  hence "fmlookup (fmap_of_list as_vrules) c = None"
    by (metis fmdom_notD)
  thus "rel_option vrelated (fmlookup (fmap_of_list as_vrules) c) (fmlookup (fmap_of_list as_vrules) c)"
    by simp
qed

lemma veval'_correct'':
  fixes t v
  assumes "fmap_of_list as_vrules \<turnstile>\<^sub>v t \<down> v"
  assumes "wellformed t"
  assumes "\<not> shadows_consts t"
  assumes "welldefined t"
  assumes "closed t"
  assumes "vno_abs v"
  shows "as_vrules, fmempty \<turnstile>\<^sub>v t \<down> v"
proof -
  obtain v\<^sub>1 where "as_vrules, fmempty \<turnstile>\<^sub>v t \<down> v\<^sub>1" "\<turnstile>\<^sub>v v\<^sub>1 \<approx> v"
    using \<open>fmap_of_list as_vrules \<turnstile>\<^sub>v t \<down> v\<close>
    proof (rule srules_as_vrules.veval'_correct', unfold as_vrules_fst)
      show "wellformed t" "\<not> shadows_consts t" "closed t" "consts t |\<subseteq>| all_consts"
        by fact+
    next
      show "wellformed_venv (fmap_of_list as_vrules)"
        apply rule
        using srules_as_vrules.all_rules
        apply (auto simp: list_all_iff)
        done
    next
      show "not_shadows_vconsts_env (fmap_of_list as_vrules) "
        apply rule
        using srules_as_vrules.not_shadows
        apply (auto simp: list_all_iff)
        done
    next
      have "fmrel_on_fset (fst |`| fset_of_list as_vrules |\<union>| C) vrelated (fmap_of_list as_vrules) (fmap_of_list as_vrules)"
        apply (rule fmrel_on_fset_unionI)
         apply (rule as_vrules_refl_rs)
        apply (rule as_vrules_refl_C)
        done

      show "fmrel_on_fset (consts t) vrelated (fmap_of_list as_vrules) (fmap_of_list as_vrules)"
        apply (rule fmrel_on_fsubset)
         apply fact+
        using assms by (auto simp: all_consts_def)
    qed

  thus ?thesis
    using assms by (metis srules_as_vrules.vrelated.eq_right)
qed

end

subsection \<open>CakeML\<close>

context srules begin

definition as_sem_env :: "v sem_env \<Rightarrow> v sem_env" where
"as_sem_env env = \<lparr> sem_env.v = build_rec_env (mk_letrec_body all_consts rs) env nsEmpty, sem_env.c = nsEmpty \<rparr>"

lemma compile_sem_env:
  "evaluate_dec ck mn env state (compile_group all_consts rs) (state, Rval (as_sem_env env))"
unfolding compile_group_def as_sem_env_def
apply (rule evaluate_dec.dletrec1)
unfolding mk_letrec_body_def Let_def
apply (simp add:comp_def case_prod_twice)
using name_as_string.fst_distinct[OF distinct]
by auto

lemma compile_sem_env':
  "fun_evaluate_decs mn state env [(compile_group all_consts rs)] = (state, Rval (as_sem_env env))"
unfolding compile_group_def as_sem_env_def mk_letrec_body_def Let_def
apply (simp add: comp_def case_prod_twice)
using name_as_string.fst_distinct[OF distinct]
by auto

lemma compile_prog[unfolded combine_dec_result.simps, simplified]:
  "evaluate_prog ck env state (compile rs) (state, combine_dec_result (as_sem_env env) (Rval \<lparr> sem_env.v = nsEmpty, sem_env.c = nsEmpty \<rparr>))"
unfolding compile_def
apply (rule evaluate_prog.cons1)
apply rule
apply (rule evaluate_top.tdec1)
apply (rule compile_sem_env)
apply (rule evaluate_prog.empty)
done

lemma compile_prog'[unfolded combine_dec_result.simps, simplified]:
  "fun_evaluate_prog state env (compile rs) = (state, combine_dec_result (as_sem_env env) (Rval \<lparr> sem_env.v = nsEmpty, sem_env.c = nsEmpty \<rparr>))"
unfolding compile_def fun_evaluate_prog_def no_dup_mods_def no_dup_top_types_def prog_to_mods_def prog_to_top_types_def decs_to_types_def
using compile_sem_env' compile_group_def by simp

definition sem_env :: "v sem_env" where
"sem_env \<equiv> extend_dec_env (as_sem_env empty_sem_env) empty_sem_env"

(* FIXME introduce lemma: is_cupcake_all_env extend_dec_env *)
(* FIXME introduce lemma: is_cupcake_all_env empty_sem_env *)
lemma cupcake_sem_env: "is_cupcake_all_env sem_env"
unfolding as_sem_env_def sem_env_def
apply (rule is_cupcake_all_envI)
apply (simp add: extend_dec_env_def empty_sem_env_def nsEmpty_def)
apply (rule cupcake_nsAppend_preserve)
apply (rule cupcake_build_rec_preserve)
  apply (simp add: empty_sem_env_def)
 apply (simp add: nsEmpty_def)
apply (rule mk_letrec_cupcake)
apply simp
apply (simp add: empty_sem_env_def)
done

lemma sem_env_refl: "fmrel related_v (fmap_of_list as_vrules) (fmap_of_ns (sem_env.v sem_env))"
proof
  fix name
  show "rel_option related_v (fmlookup (fmap_of_list as_vrules) name) (fmlookup (fmap_of_ns (sem_env.v sem_env)) name)"
    apply (simp add:
            as_sem_env_def build_rec_env_fmap cake_mk_rec_env_def sem_env_def
            fmap_of_list.rep_eq map_of_map_keyed option.rel_map
            as_vrules_def mk_letrec_body_def comp_def case_prod_twice)
    apply (rule option.rel_refl_strong)
    apply (rule related_v.rec_closure)
     apply auto[]
    apply (simp add:
            fmmap_of_list[symmetric, unfolded apsnd_def map_prod_def id_def] fmap.rel_map
            global_css_def Let_def map_prod_def comp_def case_prod_twice)
    apply (thin_tac "map_of rs name = _")
    apply (rule fmap.rel_refl_strong)
    apply simp
    subgoal premises prems for rhs
      proof -
        obtain name where "(name, rhs) \<in> set rs"
          using prems
          including fmap.lifting
          by transfer' (auto dest: map_of_SomeD)
        hence "is_abs rhs" "closed rhs" "welldefined rhs"
          using all_rules swelldefined_rs by (auto simp add: list_all_iff)
        then obtain cs where "clauses rhs = cs" "rhs = Sabs cs" "wellformed_clauses cs"
          using \<open>(name, rhs) \<in> set rs\<close> all_rules
          by (cases rhs) (auto simp: list_all_iff is_abs_def term_cases_def)
        show ?thesis
          unfolding related_fun_alt_def \<open>clauses rhs = cs\<close>
          proof (intro conjI)
            show "list_all2 (rel_prod related_pat related_exp) cs (map (\<lambda>(pat, t). (mk_ml_pat (mk_pat pat), mk_con (frees pat |\<union>| all_consts) t)) cs)"
              unfolding list.rel_map
              apply (rule list.rel_refl_strong)
              apply (rename_tac z, case_tac z, hypsubst_thin)
              apply simp
              subgoal premises prems for pat t
                proof (rule mk_exp_correctness)
                  have "\<not> shadows_consts rhs"
                    using \<open>(name, rhs) \<in> set rs\<close> not_shadows
                    by (auto simp: list_all_iff all_consts_def)
                  thus "\<not> shadows_consts t"
                    unfolding \<open>rhs = Sabs cs\<close> using prems
                    by (auto simp: list_all_iff list_ex_iff)
                next
                  have "frees t |\<subseteq>| frees pat"
                    using \<open>closed rhs\<close> prems unfolding \<open>rhs = _\<close>
                    apply (auto simp: list_all_iff Sterm.closed_except_simps)
                    apply (erule ballE[where x = "(pat, t)"])
                     apply (auto simp: closed_except_def)
                    done
                  moreover have "consts t |\<subseteq>| all_consts"
                    using \<open>welldefined rhs\<close> prems unfolding \<open>rhs = _\<close> welldefined_sabs
                    by (auto simp: list_all_iff all_consts_def)
                  ultimately show "ids t |\<subseteq>| frees pat |\<union>| all_consts"
                    unfolding ids_def by auto
                qed (auto simp: all_consts_def)
              done
          next
            have 1: "frees (Sabs cs) = {||}"
              using \<open>closed rhs\<close> unfolding \<open>rhs = Sabs cs\<close>
              by (auto simp: closed_except_def)

            have 2: "welldefined rhs"
              using swelldefined_rs \<open>(name, rhs) \<in> set rs\<close>
              by (auto simp: list_all_iff)

            show "fresh_fNext all_consts |\<notin>| ids (Sabs cs)"
              apply (rule fNext_not_member_subset)
              unfolding ids_def 1
              using 2 \<open>rhs = _\<close> by (simp add: all_consts_def del: consts_sterm.simps)
          next
            show "fresh_fNext all_consts |\<notin>| all_consts"
              by (rule fNext_not_member)
          qed
      qed
    done
qed

lemma semantic_correctness':
  assumes "cupcake_evaluate_single sem_env (mk_con all_consts t) (Rval ml_v)"
  assumes "welldefined t" "closed t" "\<not> shadows_consts t" "wellformed t"
  obtains v where "fmap_of_list as_vrules \<turnstile>\<^sub>v t \<down> v" "related_v v ml_v"
using assms(1) proof (rule semantic_correctness)
  show "is_cupcake_all_env sem_env"
    by (fact cupcake_sem_env)
next
  show "related_exp t (mk_con all_consts t)"
    apply (rule mk_exp_correctness)
    using assms
    unfolding ids_def closed_except_def by (auto simp: all_consts_def)
next
  show "wellformed t" "\<not> shadows_consts t" by fact+
next
  show "closed_except t (fmdom (fmap_of_list as_vrules))"
    using \<open>closed t\<close> by (auto simp: closed_except_def)
next
  show "closed_venv (fmap_of_list as_vrules)"
    apply (rule fmpred_of_list)
    using srules_as_vrules.all_rules
    by (auto simp: list_all_iff)

  show "wellformed_venv (fmap_of_list as_vrules)"
    apply (rule fmpred_of_list)
    using srules_as_vrules.all_rules
    by (auto simp: list_all_iff)
next
  have 1: "fmpred (\<lambda>_. list_all (\<lambda>(pat, t). consts t |\<subseteq>| C |\<union>| fmdom global_css)) global_css"
    apply (subst (2) global_css_def)
    apply (rule fmpred_of_list)
    apply (auto simp: map_prod_def)
    subgoal premises prems for pat t
      proof -
        from prems obtain cs where "t = Sabs cs"
          by (elim clausesE)
        have "welldefined t"
          using swelldefined_rs prems
          by (auto simp: list_all_iff fmdom_global_css)

        show ?thesis
          using \<open>welldefined t\<close>
          unfolding \<open>t = _\<close> welldefined_sabs
          by (auto simp: all_consts_def list_all_iff fmdom_global_css)
      qed
    done

  show "fmpred (\<lambda>_. vwelldefined') (fmap_of_list as_vrules)"
    apply (rule fmpred_of_list)
    unfolding as_vrules_def
    apply simp
    apply (erule imageE)
    apply (auto split: prod.splits)
      apply (subst fdisjnt_alt_def)
      apply simp
      apply (rule 1)
     apply (subst global_css_def)
     apply simp
    subgoal for x1 x2
      apply (rule fimage_eqI[where x = "(x1, x2)"])
      by (auto simp: fset_of_list_elem)
    subgoal
      using disjnt by (auto simp: fdisjnt_alt_def fmdom_global_css)
    done
next
  show "not_shadows_vconsts_env (fmap_of_list as_vrules)"
    apply (rule fmpred_of_list)
    using srules_as_vrules.not_shadows
    unfolding list_all_iff
    by auto
next
  show "fdisjnt C (fmdom (fmap_of_list as_vrules))"
    using disjnt by (auto simp: fdisjnt_alt_def)
next
  show "fmrel_on_fset (ids t) related_v (fmap_of_list as_vrules) (fmap_of_ns (sem_env.v sem_env))"
    unfolding fmrel_on_fset_fmrel_restrict
    apply (rule fmrel_restrict_fset)
    apply (rule sem_env_refl)
    done
next
  show "consts t |\<subseteq>| fmdom (fmap_of_list as_vrules) |\<union>| C"
    apply (subst fmdom_fmap_of_list)
    apply (subst as_vrules_fst')
    apply simp
    using assms by (auto simp: all_consts_def)
qed blast

end

fun cake_to_value :: "v \<Rightarrow> value" where
"cake_to_value (Conv (Some (name, _)) vs) = Vconstr (Name name) (map cake_to_value vs)"

context cakeml' begin

lemma cake_to_value_abs_free:
  assumes "is_cupcake_value v" "cake_no_abs v"
  shows "vno_abs (cake_to_value v)"
  using assms by (induction v) (auto elim: is_cupcake_value.elims simp: list_all_iff)

lemma cake_to_value_related:
  assumes "cake_no_abs v" "is_cupcake_value v"
  shows "related_v (cake_to_value v) v"
using assms proof (induction v)
  case (Conv c vs)
  then obtain name tid where "c = Some ((as_string name), TypeId (Short tid))"
    apply (elim is_cupcake_value.elims)
    subgoal
      by (metis name.sel v.simps(2))
    by auto
  show ?case
    unfolding \<open>c = _\<close>
    apply simp
    apply (rule related_v.conv)
    apply (simp add: list.rel_map)
    apply (rule list.rel_refl_strong)
    apply (rule Conv)
    using Conv unfolding \<open>c = _\<close>
    by (auto simp: list_all_iff)
qed auto

lemma related_v_abs_free_uniq:
  assumes "related_v v\<^sub>1 ml_v" "related_v v\<^sub>2 ml_v" "cake_no_abs ml_v"
  shows "v\<^sub>1 = v\<^sub>2"
using assms proof (induction arbitrary: v\<^sub>2)
  case (conv vs\<^sub>1 ml_vs name)
  then obtain vs\<^sub>2 where "v\<^sub>2 = Vconstr name vs\<^sub>2" "list_all2 related_v vs\<^sub>2 ml_vs"
    by (auto elim: related_v.cases simp: name.expand)
  moreover have "list_all cake_no_abs ml_vs"
    using conv by simp
  have "list_all2 (=) vs\<^sub>1 vs\<^sub>2"
    using \<open>list_all2 _ vs\<^sub>1 _\<close>  \<open>list_all2 _ vs\<^sub>2 _\<close> \<open>list_all cake_no_abs ml_vs\<close>
    by (induction arbitrary: vs\<^sub>2 rule: list.rel_induct) (auto simp: list_all2_Cons2)
  thus ?case
    unfolding \<open>v\<^sub>2 = _\<close>
    by (simp add: list.rel_eq)
qed auto

corollary related_v_abs_free_cake_to_value:
  assumes "related_v v ml_v" "cake_no_abs ml_v" "is_cupcake_value ml_v"
  shows "v = cake_to_value ml_v"
using assms by (metis cake_to_value_related related_v_abs_free_uniq)

end

context srules begin

lemma cupcake_sem_env_preserve:
  assumes "cupcake_evaluate_single sem_env (mk_con S t) (Rval ml_v)" "wellformed t"
  shows "is_cupcake_value ml_v"
apply (rule cupcake_single_preserve[OF assms(1)])
 apply (rule cupcake_sem_env)
apply (rule mk_exp_cupcake)
apply fact
done

lemma semantic_correctness'':
  assumes "cupcake_evaluate_single sem_env (mk_con all_consts t) (Rval ml_v)"
  assumes "welldefined t" "closed t" "\<not> shadows_consts t" "wellformed t"
  assumes "cake_no_abs ml_v"
  shows "fmap_of_list as_vrules \<turnstile>\<^sub>v t \<down> cake_to_value ml_v"
using assms
by (metis cupcake_sem_env_preserve semantic_correctness' related_v_abs_free_cake_to_value)

end


subsection \<open>Composition\<close>

context rules begin

abbreviation term_to_nterm where
"term_to_nterm t \<equiv> fresh_frun (Term_to_Nterm.term_to_nterm [] t) all_consts"

abbreviation sterm_to_cake where
"sterm_to_cake \<equiv> rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.mk_con all_consts"

abbreviation "term_to_cake t \<equiv> sterm_to_cake (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
abbreviation "cake_to_term t \<equiv> (convert_term (value_to_sterm (cake_to_value t)) :: term)"

abbreviation "cake_sem_env \<equiv> rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.sem_env"

definition "compiled \<equiv> rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.as_vrules"

lemma fmdom_compiled: "fmdom (fmap_of_list compiled) = heads_of rs"
unfolding compiled_def
by (simp add:
        rules_as_nrules.crules_as_irules'.irules'_as_prules.compile_heads
        Rewriting_Pterm.compile_heads transform_irule_set_iter_heads
        Rewriting_Pterm_Elim.compile_heads
        compile_heads consts_of_heads)

lemma cake_semantic_correctness:
  assumes "cupcake_evaluate_single cake_sem_env (sterm_to_cake t) (Rval ml_v)"
  assumes "welldefined t" "closed t" "\<not> shadows_consts t" "wellformed t"
  assumes "cake_no_abs ml_v"
  shows "fmap_of_list compiled \<turnstile>\<^sub>v t \<down> cake_to_value ml_v"
unfolding compiled_def
apply (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.semantic_correctness'')
using assms
by (simp_all add:
      rules_as_nrules.crules_as_irules'.irules'_as_prules.compile_heads
      Rewriting_Pterm.compile_heads transform_irule_set_iter_heads
      Rewriting_Pterm_Elim.compile_heads
      compile_heads consts_of_heads all_consts_def)


text \<open>Lo and behold, this is the final correctness theorem!\<close>

theorem compiled_correct:
  \<comment> \<open>If CakeML evaluation of a term succeeds ...\<close>
  assumes "\<exists>k. Evaluate_Single.evaluate cake_sem_env (s \<lparr> clock := k \<rparr>) (term_to_cake t) = (s', Rval ml_v)"
  \<comment> \<open>... producing a constructor term without closures ...\<close>
  assumes "cake_no_abs ml_v"
  \<comment> \<open>... and some syntactic properties of the involved terms hold ...\<close>
  assumes "closed t" "\<not> shadows_consts t" "welldefined t" "wellformed t"
  \<comment> \<open>... then this evaluation can be reproduced in the term-rewriting semantics\<close>
  shows "rs \<turnstile> t \<longrightarrow>* cake_to_term ml_v"
proof -
  let ?heads = "fst |`| fset_of_list rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.as_vrules"
  have "?heads = heads_of rs"
    using fmdom_compiled unfolding compiled_def by simp

  have "wellformed (nterm_to_pterm (term_to_nterm t))"
    by auto
  hence "wellformed (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
    by (auto intro: pterm_to_sterm_wellformed)

  have "is_cupcake_all_env cake_sem_env"
    by (rule rules_as_nrules.nrules_as_crules.crules_as_irules'.irules'_as_prules.prules_as_srules.cupcake_sem_env)
  have "is_cupcake_exp (term_to_cake t)"
    by (rule rules_as_nrules.nrules_as_crules.crules_as_irules'.irules'_as_prules.prules_as_srules.srules_as_cake.mk_exp_cupcake) fact
  obtain k where "Evaluate_Single.evaluate cake_sem_env (s \<lparr> clock := k \<rparr>) (term_to_cake t) = (s', Rval ml_v)"
    using assms by blast
  then have "Big_Step_Unclocked_Single.evaluate cake_sem_env (s \<lparr> clock := (clock s') \<rparr>) (term_to_cake t) (s', Rval ml_v)"
    using unclocked_single_fun_eq by fastforce
  have "cupcake_evaluate_single cake_sem_env (sterm_to_cake (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))) (Rval ml_v)"
    apply (rule cupcake_single_complete)
      apply fact+
    done
  hence "is_cupcake_value ml_v"
    apply (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.cupcake_sem_env_preserve)
    by (auto intro: pterm_to_sterm_wellformed)
  hence "vno_abs (cake_to_value ml_v)"
    using \<open>cake_no_abs _\<close>
    by (metis rules_as_nrules.nrules_as_crules.crules_as_irules'.irules'_as_prules.prules_as_srules.srules_as_cake.cake_to_value_abs_free)

  hence "no_abs (value_to_sterm (cake_to_value ml_v))"
    by (metis vno_abs_value_to_sterm)

  hence "no_abs (sterm_to_pterm (value_to_sterm (cake_to_value ml_v)))"
    by (metis sterm_to_pterm convert_term_no_abs)

  have "welldefined (term_to_nterm t)"
    unfolding term_to_nterm'_def
    apply (subst fresh_frun_def)
    apply (subst pred_stateD[OF term_to_nterm_consts])
     apply (subst surjective_pairing)
     apply (rule refl)
    apply fact
    done
  have "welldefined (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
    apply (subst pterm_to_sterm_consts)
     apply fact
    apply (subst consts_nterm_to_pterm)
    apply fact+
    done

  have "\<not> shadows_consts t"
    using assms unfolding shadows_consts_def fdisjnt_alt_def
    by auto
  hence "\<not> shadows_consts (term_to_nterm t)"
    unfolding shadows_consts_def shadows_consts_def
    apply auto
    using term_to_nterm_all_vars[folded wellformed_term_def]
    by (metis assms(6) fdisjnt_swap sup_idem)

  have "\<not> shadows_consts (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
    apply (subst pterm_to_sterm_shadows[symmetric])
     apply fact
    apply (subst shadows_nterm_to_pterm)
    unfolding shadows_consts_def
    apply simp
    apply (rule term_to_nterm_all_vars[where T = "fempty", simplified, THEN fdisjnt_swap])
     apply (fold wellformed_term_def)
     apply fact
    using \<open>closed t\<close> unfolding closed_except_def by (auto simp: fdisjnt_alt_def)

  have "closed (term_to_nterm t)"
    using assms unfolding closed_except_def
    using term_to_nterm_vars unfolding wellformed_term_def by blast
  hence "closed (nterm_to_pterm (term_to_nterm t))"
    using closed_nterm_to_pterm unfolding closed_except_def
    by auto
  have "closed (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
    unfolding closed_except_def
    apply (subst pterm_to_sterm_frees)
     apply fact
    using \<open>closed (term_to_nterm t)\<close> closed_nterm_to_pterm unfolding closed_except_def
    by auto

  have "fmap_of_list compiled \<turnstile>\<^sub>v pterm_to_sterm (nterm_to_pterm (term_to_nterm t)) \<down> cake_to_value ml_v"
    by (rule cake_semantic_correctness) fact+
  hence "fmap_of_list rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.as_vrules \<turnstile>\<^sub>v pterm_to_sterm (nterm_to_pterm (term_to_nterm t)) \<down> cake_to_value ml_v"
    using assms unfolding compiled_def by simp
  hence "rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.as_vrules, fmempty \<turnstile>\<^sub>v pterm_to_sterm (nterm_to_pterm (term_to_nterm t)) \<down> cake_to_value ml_v"
    proof (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.veval'_correct'')
      show "\<not> rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.shadows_consts (pterm_to_sterm (nterm_to_pterm (term_to_nterm t)))"
        using \<open>\<not> shadows_consts (_::sterm)\<close> \<open>?heads = heads_of rs\<close> by auto
    next
      show "consts (pterm_to_sterm (nterm_to_pterm (term_to_nterm t))) |\<subseteq>| rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.all_consts"
        using \<open>welldefined (pterm_to_sterm _)\<close> \<open>?heads = _\<close> by auto
    qed fact+
  hence "Rewriting_Sterm.compile (Rewriting_Pterm.compile (transform_irule_set_iter (Rewriting_Pterm_Elim.compile (consts_of compile)))), fmempty \<turnstile>\<^sub>s pterm_to_sterm (nterm_to_pterm (term_to_nterm t)) \<down> value_to_sterm (cake_to_value ml_v)"
    by (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.veval_correct) fact+
  hence "Rewriting_Sterm.compile (Rewriting_Pterm.compile (transform_irule_set_iter (Rewriting_Pterm_Elim.compile (consts_of compile)))) \<turnstile>\<^sub>s pterm_to_sterm (nterm_to_pterm (term_to_nterm t)) \<longrightarrow>* value_to_sterm (cake_to_value ml_v)"
    by (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.prules_as_srules.seval_correct) fact
  hence "Rewriting_Pterm.compile (transform_irule_set_iter (Rewriting_Pterm_Elim.compile (consts_of compile))) \<turnstile>\<^sub>p sterm_to_pterm (pterm_to_sterm (nterm_to_pterm (term_to_nterm t))) \<longrightarrow>* sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    by (rule rules_as_nrules.crules_as_irules'.irules'_as_prules.compile_correct_rt)
  hence "Rewriting_Pterm.compile (transform_irule_set_iter (Rewriting_Pterm_Elim.compile (consts_of compile))) \<turnstile>\<^sub>p nterm_to_pterm (term_to_nterm t) \<longrightarrow>* sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    by (subst (asm) pterm_to_sterm_sterm_to_pterm) fact
  hence "transform_irule_set_iter (Rewriting_Pterm_Elim.compile (consts_of compile)) \<turnstile>\<^sub>i nterm_to_pterm (term_to_nterm t) \<longrightarrow>* sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    by (rule rules_as_nrules.crules_as_irules'.irules'_as_irules.compile_correct_rt)
       (rule rules_as_nrules.crules_as_irules.transform_finished)
  have "Rewriting_Pterm_Elim.compile (consts_of compile) \<turnstile>\<^sub>i nterm_to_pterm (term_to_nterm t) \<longrightarrow>* sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    apply (rule rules_as_nrules.crules_as_irules.transform_correct_rt_n_no_abs)
    using \<open>transform_irule_set_iter _ \<turnstile>\<^sub>i _ \<longrightarrow>* _\<close> unfolding transform_irule_set_iter_def
      apply simp
     apply fact+
    done

  then obtain t' where "compile \<turnstile>\<^sub>n term_to_nterm t \<longrightarrow>* t'" "t' \<approx>\<^sub>i sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    using \<open>closed (term_to_nterm t)\<close>
    by (metis rules_as_nrules.compile_correct_rt)
  hence "no_abs t'"
    using \<open>no_abs (sterm_to_pterm _)\<close>
    by (metis irelated_no_abs)

  have "rs \<turnstile> nterm_to_term' (term_to_nterm t) \<longrightarrow>* nterm_to_term' t'"
    by (rule compile_correct_rt) fact+
  hence "rs \<turnstile> t \<longrightarrow>* nterm_to_term' t'"
    apply (subst (asm) fresh_frun_def)
    apply (subst (asm) term_to_nterm_nterm_to_term[where S = "fempty" and t = t, simplified])
      apply (fold wellformed_term_def)
      apply fact
    using assms unfolding closed_except_def by auto

  have "nterm_to_pterm t' = sterm_to_pterm (value_to_sterm (cake_to_value ml_v))"
    using \<open>t' \<approx>\<^sub>i _\<close>
    by auto
  hence "(convert_term t' :: pterm) = convert_term (value_to_sterm (cake_to_value ml_v))"
    apply (subst (asm) nterm_to_pterm)
     apply fact
    apply (subst (asm) sterm_to_pterm)
     apply fact
    apply assumption
    done
  hence "nterm_to_term' t' = convert_term (value_to_sterm (cake_to_value ml_v))"
    apply (subst nterm_to_term')
     apply (rule \<open>no_abs t'\<close>)
    apply (rule convert_term_inj)
    subgoal premises
      apply (rule convert_term_no_abs)
      apply fact
      done
    subgoal premises
      apply (rule convert_term_no_abs)
      apply fact
      done
    apply (subst convert_term_idem)
     apply (rule \<open>no_abs t'\<close>)
    apply (subst convert_term_idem)
     apply (rule \<open>no_abs (value_to_sterm (cake_to_value ml_v))\<close>)
    apply assumption
    done

  thus ?thesis
    using \<open>rs \<turnstile> t \<longrightarrow>* nterm_to_term' t'\<close> by simp
qed

end

end