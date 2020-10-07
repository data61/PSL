section \<open>Sequential pattern matching\<close>

theory Rewriting_Sterm
imports Rewriting_Pterm
begin

type_synonym srule = "name \<times> sterm"

abbreviation closed_srules :: "srule list \<Rightarrow> bool" where
"closed_srules \<equiv> list_all (closed \<circ> snd)"

primrec srule :: "srule \<Rightarrow> bool" where
"srule (_, rhs) \<longleftrightarrow> wellformed rhs \<and> closed rhs \<and> is_abs rhs"

lemma sruleI[intro!]: "wellformed rhs \<Longrightarrow> closed rhs \<Longrightarrow> is_abs rhs \<Longrightarrow> srule (name, rhs)"
by simp

locale srules = constants C_info "fst |`| fset_of_list rs" for C_info and rs :: "srule list" +
  assumes all_rules: "list_all srule rs"
  assumes distinct: "distinct (map fst rs)"
  assumes not_shadows: "list_all (\<lambda>(_, rhs). \<not> shadows_consts rhs) rs"
  assumes swelldefined_rs: "list_all (\<lambda>(_, rhs). welldefined rhs) rs"
begin

lemma map: "is_map (set rs)"
using distinct by (rule distinct_is_map)

lemma clausesE:
  assumes "(name, rhs) \<in> set rs"
  obtains cs where "rhs = Sabs cs"
proof -
  from assms have "is_abs rhs"
    using all_rules unfolding list_all_iff by auto
  then obtain cs where "rhs = Sabs cs"
    by (cases rhs) (auto simp: is_abs_def term_cases_def)
  with that show thesis .
qed

end

subsubsection \<open>Rewriting\<close>

inductive srewrite_step where
cons_match: "srewrite_step ((name, rhs) # rest) name rhs" |
cons_nomatch: "name \<noteq> name' \<Longrightarrow> srewrite_step rs name rhs \<Longrightarrow> srewrite_step ((name', rhs') # rs) name rhs"

lemma srewrite_stepI0:
  assumes "(name, rhs) \<in> set rs" "is_map (set rs)"
  shows "srewrite_step rs name rhs"
using assms proof (induction rs)
  case (Cons r rs)
  then obtain name' rhs' where "r = (name', rhs')" by force
  show ?case
    proof (cases "name = name'")
      case False
      show ?thesis
        unfolding \<open>r = _\<close>
        apply (rule srewrite_step.cons_nomatch)
        subgoal by fact
        apply (rule Cons)
        using False Cons(2) \<open>r = _\<close> apply force
        using Cons(3) unfolding is_map_def by auto
    next
      case True
      have "rhs = rhs'"
        apply (rule is_mapD)
          apply fact
        unfolding \<open>r = _\<close>
        using Cons(2) \<open>r = _\<close> apply simp
        using True apply simp
        done
      show ?thesis
        unfolding \<open>r = _\<close> \<open>name = _\<close> \<open>rhs = _\<close>
        by (rule srewrite_step.cons_match)
    qed
qed auto

lemma (in srules) srewrite_stepI: "(name, rhs) \<in> set rs \<Longrightarrow> srewrite_step rs name rhs"
using map
by (metis srewrite_stepI0)

hide_fact srewrite_stepI0

inductive srewrite :: "srule list \<Rightarrow> sterm \<Rightarrow> sterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>s/ _ \<longrightarrow>/ _" [50,0,50] 50) for rs where
step: "srewrite_step rs name rhs \<Longrightarrow> rs \<turnstile>\<^sub>s Sconst name \<longrightarrow> rhs" |
beta: "rewrite_first cs t t' \<Longrightarrow> rs \<turnstile>\<^sub>s Sabs cs $\<^sub>s t \<longrightarrow> t'" |
"fun": "rs \<turnstile>\<^sub>s t \<longrightarrow> t' \<Longrightarrow> rs \<turnstile>\<^sub>s t $\<^sub>s u \<longrightarrow> t' $\<^sub>s u" |
arg: "rs \<turnstile>\<^sub>s u \<longrightarrow> u' \<Longrightarrow> rs \<turnstile>\<^sub>s t $\<^sub>s u \<longrightarrow> t $\<^sub>s u'"

code_pred srewrite .

abbreviation srewrite_rt :: "srule list \<Rightarrow> sterm \<Rightarrow> sterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>s/ _ \<longrightarrow>*/ _" [50,0,50] 50) where
"srewrite_rt rs \<equiv> (srewrite rs)\<^sup>*\<^sup>*"

global_interpretation srewrite: rewriting "srewrite rs" for rs
by standard (auto intro: srewrite.intros simp: app_sterm_def)+

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) srewrite_step .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) srewrite .

subsubsection \<open>Translation from @{typ pterm} to @{typ sterm}\<close>

text \<open>
  In principle, any function of type @{typ \<open>('a \<times> 'b) fset \<Rightarrow> ('a \<times> 'b) list\<close>} that orders
  by keys would do here. However, For simplicity's sake, we choose a fixed one
  (@{const ordered_fmap}) here.
\<close>

primrec pterm_to_sterm :: "pterm \<Rightarrow> sterm" where
"pterm_to_sterm (Pconst name) = Sconst name" |
"pterm_to_sterm (Pvar name) = Svar name" |
"pterm_to_sterm (t $\<^sub>p u) = pterm_to_sterm t $\<^sub>s pterm_to_sterm u" |
"pterm_to_sterm (Pabs cs) = Sabs (ordered_fmap (map_prod id pterm_to_sterm |`| cs))"

lemma pterm_to_sterm:
  assumes "no_abs t"
  shows "pterm_to_sterm t = convert_term t"
using assms proof induction
  case (free name)
  show ?case
    apply simp
    apply (simp add: free_sterm_def free_pterm_def)
    done
next
  case (const name)
  show ?case
    apply simp
    apply (simp add: const_sterm_def const_pterm_def)
    done
next
  case (app t\<^sub>1 t\<^sub>2)
  then show ?case
    apply simp
    apply (simp add: app_sterm_def app_pterm_def)
    done
qed

text \<open>
  @{const sterm_to_pterm} has to be defined, for technical reasons, in
  @{theory CakeML_Codegen.Pterm}.
\<close>

lemma pterm_to_sterm_wellformed:
  assumes "wellformed t"
  shows "wellformed (pterm_to_sterm t)"
using assms proof (induction t rule: pterm_induct)
  case (Pabs cs)
  show ?case
    apply simp
    unfolding map_prod_def id_apply
    apply (intro conjI)
    subgoal
      apply (subst list_all_iff_fset)
      apply (subst ordered_fmap_set_eq)
       apply (rule is_fmap_image)
      using Pabs apply simp
      apply (rule fBallI)
      apply (erule fimageE)
      apply auto[]
      using Pabs(2) apply auto[]
      apply (rule Pabs)
      using Pabs(2) by auto
    subgoal
      apply (rule ordered_fmap_distinct)
      apply (rule is_fmap_image)
      using Pabs(2) by simp
    subgoal
      apply (subgoal_tac "cs \<noteq> {||}")
      including fset.lifting apply transfer
      unfolding ordered_map_def
      using Pabs(2) by auto
    done
qed auto

lemma pterm_to_sterm_sterm_to_pterm:
  assumes "wellformed t"
  shows "sterm_to_pterm (pterm_to_sterm t) = t"
using assms proof (induction t)
  case (Pabs cs)
  note fset_of_list_map[simp del]
  show ?case
    apply simp
    unfolding map_prod_def id_apply
    apply (subst ordered_fmap_image)
    subgoal
      apply (rule is_fmap_image)
      using Pabs by simp
    apply (subst ordered_fmap_set_eq)
    subgoal
      apply (rule is_fmap_image)
      apply (rule is_fmap_image)
      using Pabs by simp
    subgoal
      apply (subst fset.map_comp)
      apply (subst map_prod_def[symmetric])+
      unfolding o_def
      apply (subst prod.map_comp)
      apply (subst id_def[symmetric])+
      apply simp
      apply (subst map_prod_def)
      unfolding id_def
      apply (rule fset_map_snd_id)
      apply simp
      apply (rule Pabs)
      using Pabs(2) by (auto simp: fmember.rep_eq snds.simps)
    done
qed auto

corollary pterm_to_sterm_frees: "wellformed t \<Longrightarrow> frees (pterm_to_sterm t) = frees t"
by (metis pterm_to_sterm_sterm_to_pterm sterm_to_pterm_frees)

corollary pterm_to_sterm_closed:
  "closed_except t S \<Longrightarrow> wellformed t \<Longrightarrow> closed_except (pterm_to_sterm t) S"
unfolding closed_except_def
by (simp add: pterm_to_sterm_frees)

corollary pterm_to_sterm_consts: "wellformed t \<Longrightarrow> consts (pterm_to_sterm t) = consts t"
by (metis pterm_to_sterm_sterm_to_pterm sterm_to_pterm_consts)

corollary (in constants) pterm_to_sterm_shadows:
  "wellformed t \<Longrightarrow> shadows_consts t \<longleftrightarrow> shadows_consts (pterm_to_sterm t)"
unfolding shadows_consts_def
by (metis pterm_to_sterm_sterm_to_pterm sterm_to_pterm_all_frees)

definition compile :: "prule fset \<Rightarrow> srule list" where
"compile rs = ordered_fmap (map_prod id pterm_to_sterm |`| rs)"

subsubsection \<open>Correctness of translation\<close>

context prules begin

lemma compile_heads: "fst |`| fset_of_list (compile rs) = fst |`| rs"
  unfolding compile_def
  apply (subst ordered_fmap_set_eq)
   apply (subst map_prod_def, subst id_apply)
   apply (rule is_fmap_image)
   apply (rule fmap)
  apply simp
  done

lemma compile_rules: "srules C_info (compile rs)"
proof
  show "list_all srule (compile rs)"
    using fmap all_rules
    unfolding compile_def list_all_iff
    including fset.lifting
    apply transfer
    apply (subst ordered_map_set_eq)
    subgoal by simp
    subgoal
      unfolding map_prod_def id_def
      by (erule is_map_image)
    subgoal
      apply (rule ballI)
      apply safe
      subgoal
        apply (rule pterm_to_sterm_wellformed)
        apply fastforce
        done
      subgoal
        apply (rule pterm_to_sterm_closed)
         apply fastforce
        apply fastforce
        done
      subgoal for _ _ a b
        apply (erule ballE[where x = "(a, b)"])
         apply (cases b; auto)
            apply (auto simp: is_abs_def term_cases_def)
        done
      done
    done
next
  show "distinct (map fst (compile rs))"
    unfolding compile_def
    apply (rule ordered_fmap_distinct)
    unfolding map_prod_def id_def
    apply (rule is_fmap_image)
    apply (rule fmap)
    done
next
  have "list_all (\<lambda>(_, rhs). welldefined rhs) (compile rs)"
    unfolding compile_def
    apply (subst ordered_fmap_list_all)
    subgoal
      apply (subst map_prod_def)
      apply (subst id_apply)
      apply (rule is_fmap_image)
      by (fact fmap)
    apply simp
    apply (rule fBallI)
    subgoal for x
      apply (cases x, simp)
      apply (subst pterm_to_sterm_consts)
      using all_rules apply force
      using welldefined_rs by force
    done
  thus "list_all (\<lambda>(_, rhs). consts rhs |\<subseteq>| pre_constants.all_consts C_info (fst |`| fset_of_list (compile rs))) (compile rs)"
    by (simp add: compile_heads)
next
  interpret c: constants _ "fset_of_list (map fst (compile rs))"
    by (simp add: constants_axioms compile_heads)
  have all_consts: "c.all_consts = all_consts"
    by (simp add: compile_heads)

  note fset_of_list_map[simp del]
  have "list_all (\<lambda>(_, rhs). \<not> shadows_consts rhs) (compile rs)"
    unfolding compile_def
    apply (subst list_all_iff_fset)
    apply (subst ordered_fmap_set_eq)
     apply (subst map_prod_def)
    unfolding id_apply
     apply (rule is_fmap_image)
     apply (fact fmap)
    apply simp
    apply (rule fBall_pred_weaken[where P = "\<lambda>(_, rhs). \<not> shadows_consts rhs"])
    subgoal for x
      apply (cases x, simp)
      apply (subst (asm) pterm_to_sterm_shadows)
      using all_rules apply force
      by simp
    subgoal
      using not_shadows by force
    done
  thus "list_all (\<lambda>(_, rhs). \<not> pre_constants.shadows_consts C_info (fst |`| fset_of_list (compile rs)) rhs) (compile rs)"
    unfolding compile_heads all_consts .
next
  show "fdisjnt (fst |`| fset_of_list (compile rs)) C"
    unfolding compile_def
    apply (subst fset_of_list_map[symmetric])
    apply (subst ordered_fmap_keys)
     apply (subst map_prod_def)
     apply (subst id_apply)
     apply (rule is_fmap_image)
    using fmap disjnt by auto
next
  show "distinct all_constructors"
    by (fact distinct_ctr)
qed

sublocale prules_as_srules: srules C_info "compile rs"
by (fact compile_rules)

end

global_interpretation srelated: term_struct_rel_strong "(\<lambda>p s. p = sterm_to_pterm s)"
proof (standard, goal_cases)
  case (5 name t)
  then show ?case by (cases t) (auto simp: const_sterm_def const_pterm_def split: option.splits)
next
  case (6 u\<^sub>1 u\<^sub>2 t)
  then show ?case by (cases t) (auto simp: app_sterm_def app_pterm_def split: option.splits)
qed (auto simp: const_sterm_def const_pterm_def app_sterm_def app_pterm_def)

lemma srelated_subst:
  assumes "srelated.P_env penv senv"
  shows "subst (sterm_to_pterm t) penv = sterm_to_pterm (subst t senv)"
using assms
proof (induction t arbitrary: penv senv)
  case (Svar name)
  thus ?case
    by (cases rule: fmrel_cases[where x = name]) auto
next
  case (Sabs cs)
  show ?case
    apply simp
    including fset.lifting
    apply (transfer' fixing: cs penv senv)
    unfolding set_map image_comp
    apply (rule image_cong[OF refl])
    unfolding comp_apply
    apply (case_tac x)
    apply hypsubst_thin
    apply simp
    apply (rule Sabs)
      apply assumption
     apply (simp add: snds.simps)
    apply rule
    apply (rule Sabs)
    done
qed auto

context begin

private lemma srewrite_step_non_empty: "srewrite_step rs' name rhs \<Longrightarrow> rs' \<noteq> []"
by (induct rule: srewrite_step.induct) auto

private lemma compile_consE:
  assumes "(name, rhs') # rest = compile rs" "is_fmap rs"
  obtains rhs where "rhs' = pterm_to_sterm rhs" "(name, rhs) |\<in>| rs" "rest = compile (rs - {| (name, rhs) |})"
proof -
  from assms have "ordered_fmap (map_prod id pterm_to_sterm |`| rs) = (name, rhs') # rest"
    unfolding compile_def
    by simp
  hence "(name, rhs') \<in> set (ordered_fmap (map_prod id pterm_to_sterm |`| rs))"
    by simp

  have "(name, rhs') |\<in>| map_prod id pterm_to_sterm |`| rs"
    apply (rule ordered_fmap_sound)
    subgoal
      unfolding map_prod_def id_apply
      apply (rule is_fmap_image)
      apply fact
      done
    subgoal by fact
    done
  then obtain rhs where "rhs' = pterm_to_sterm rhs" "(name, rhs) |\<in>| rs"
    by auto

  have "rest = compile (rs - {| (name, rhs) |})"
    unfolding compile_def
    apply (subst inj_on_fimage_set_diff[where C = rs])
    subgoal
      apply (rule inj_onI)
      apply safe
       apply auto
      apply (subst (asm) fmember.rep_eq[symmetric])+
      using \<open>is_fmap rs\<close> by (blast dest: is_fmapD)
    subgoal by simp
    subgoal using \<open>(name, rhs) |\<in>| rs\<close> by simp
    subgoal
      apply simp
      apply (subst ordered_fmap_remove)
        apply (subst map_prod_def)
      unfolding id_apply
        apply (rule is_fmap_image)
        apply fact
      using \<open>(name, rhs) |\<in>| rs\<close> apply force
      apply (subst \<open>rhs' = pterm_to_sterm rhs\<close>[symmetric])
      apply (subst \<open>ordered_fmap _ = _\<close>[unfolded id_def])
      by simp
    done

  show thesis
    by (rule that) fact+
qed

private lemma compile_correct_step:
  assumes "srewrite_step (compile rs) name rhs" "is_fmap rs" "fBall rs prule"
  shows "(name, sterm_to_pterm rhs) |\<in>| rs"
using assms proof (induction "compile rs" name rhs arbitrary: rs)
  case (cons_match name rhs' rest)
  then obtain rhs where "rhs' = pterm_to_sterm rhs" "(name, rhs) |\<in>| rs"
    by (auto elim: compile_consE)

  show ?case
    unfolding \<open>rhs' = _\<close>
    apply (subst pterm_to_sterm_sterm_to_pterm)
    using fbspec[OF \<open>fBall rs prule\<close> \<open>(name, rhs) |\<in>| rs\<close>] apply force
    by fact
next
  case (cons_nomatch name name\<^sub>1 rest rhs rhs\<^sub>1')
  then obtain rhs\<^sub>1 where "rhs\<^sub>1' = pterm_to_sterm rhs\<^sub>1" "(name\<^sub>1, rhs\<^sub>1) |\<in>| rs" "rest = compile (rs - {| (name\<^sub>1, rhs\<^sub>1) |})"
    by (auto elim: compile_consE)

  let ?rs' = "rs - {| (name\<^sub>1, rhs\<^sub>1) |}"
  have "(name, sterm_to_pterm rhs) |\<in>| ?rs'"
    proof (intro cons_nomatch)
      show "rest = compile ?rs'"
        by fact

      show "is_fmap (rs |-| {|(name\<^sub>1, rhs\<^sub>1)|})"
        using \<open>is_fmap rs\<close>
        by (rule is_fmap_subset) auto

      show "fBall ?rs' prule"
        using cons_nomatch by blast
    qed
  thus ?case
    by simp
qed

lemma compile_correct0:
  assumes "compile rs \<turnstile>\<^sub>s u \<longrightarrow> u'" "prules C rs"
  shows "rs \<turnstile>\<^sub>p sterm_to_pterm u \<longrightarrow> sterm_to_pterm u'"
using assms proof induction
  case (beta cs t t')
  then obtain pat rhs env where "(pat, rhs) \<in> set cs" "match pat t = Some env" "t' = subst rhs env"
    by (auto elim: rewrite_firstE)

  then obtain env' where "match pat (sterm_to_pterm t) = Some env'" "srelated.P_env env' env"
    by (metis option.distinct(1) option.inject option.rel_cases srelated.match_rel)
  hence "subst (sterm_to_pterm rhs) env' = sterm_to_pterm (subst rhs env)"
    by (simp add: srelated_subst)

  let ?rhs' = "sterm_to_pterm rhs"

  have "(pat, ?rhs') |\<in>| fset_of_list (map (map_prod id sterm_to_pterm) cs)"
    using \<open>(pat, rhs) \<in> set cs\<close>
    including fset.lifting
    by transfer' force

  note fset_of_list_map[simp del]
  show ?case
    apply simp
    apply (rule prewrite.intros)
     apply fact
    unfolding rewrite_step.simps
    apply (subst map_option_eq_Some)
    apply (intro exI conjI)
     apply fact
    unfolding \<open>t' = _\<close>
    by fact
next
  case (step name rhs)
  hence "(name, sterm_to_pterm rhs) |\<in>| rs"
    unfolding prules_def prules_axioms_def
    by (metis compile_correct_step)
  thus ?case
    by (auto intro: prewrite.intros)
qed (auto intro: prewrite.intros)

end

lemma (in prules) compile_correct:
  assumes "compile rs \<turnstile>\<^sub>s u \<longrightarrow> u'"
  shows "rs \<turnstile>\<^sub>p sterm_to_pterm u \<longrightarrow> sterm_to_pterm u'"
by (rule compile_correct0) (fact | standard)+

hide_fact compile_correct0

subsubsection \<open>Completeness of translation\<close>

global_interpretation srelated': term_struct_rel_strong "(\<lambda>p s. pterm_to_sterm p = s)"
proof (standard, goal_cases)
  case (1 t name)
  then show ?case by (cases t) (auto simp: const_sterm_def const_pterm_def split: option.splits)
next
  case (3 t u\<^sub>1 u\<^sub>2)
  then show ?case by (cases t) (auto simp: app_sterm_def app_pterm_def split: option.splits)
qed (auto simp: const_sterm_def const_pterm_def app_sterm_def app_pterm_def)

corollary srelated_env_unique:
  "srelated'.P_env penv senv \<Longrightarrow> srelated'.P_env penv senv' \<Longrightarrow> senv = senv'"
apply (subst (asm) fmrel_iff)+
apply (subst (asm) option.rel_sel)+
apply (rule fmap_ext)
by (metis option.exhaust_sel)

lemma srelated_subst':
  assumes "srelated'.P_env penv senv" "wellformed t"
  shows "pterm_to_sterm (subst t penv) = subst (pterm_to_sterm t) senv"
using assms proof (induction t arbitrary: penv senv)
  case (Pvar name)
  thus ?case
    by (cases rule: fmrel_cases[where x = name]) auto
next
  case (Pabs cs)
  hence "is_fmap cs"
    by force

  show ?case
    apply simp
    unfolding map_prod_def id_apply
    apply (subst ordered_fmap_image[symmetric])
     apply fact
    apply (subst fset.map_comp[symmetric])
    apply (subst ordered_fmap_image[symmetric])
    subgoal by (rule is_fmap_image) fact
    apply (subst ordered_fmap_image[symmetric])
     apply fact
    apply auto
    apply (drule ordered_fmap_sound[OF \<open>is_fmap cs\<close>])
    subgoal for pat rhs
      apply (rule Pabs)
         apply (subst (asm) fmember.rep_eq)
         apply assumption
        apply auto
      using Pabs by force+
    done
qed auto

lemma srelated_find_match:
  assumes "find_match cs t = Some (penv, pat, rhs)" "srelated'.P_env penv senv"
  shows "find_match (map (map_prod id pterm_to_sterm) cs) (pterm_to_sterm t) = Some (senv, pat, pterm_to_sterm rhs)"
proof -
  let ?cs' = "map (map_prod id pterm_to_sterm) cs"
  let ?t' = "pterm_to_sterm t"
  have *: "list_all2 (rel_prod (=) (\<lambda>p s. pterm_to_sterm p = s)) cs ?cs'"
    unfolding list.rel_map
    by (auto intro: list.rel_refl)

  obtain senv0
    where "find_match ?cs' ?t' = Some (senv0, pat, pterm_to_sterm rhs)" "srelated'.P_env penv senv0"
    using srelated'.find_match_rel[OF * refl, where t = t, unfolded assms]
    unfolding option_rel_Some1 rel_prod_conv
    by auto
  with assms have "senv = senv0"
    by (metis srelated_env_unique)
  show ?thesis
    unfolding \<open>senv = _\<close> by fact
qed

lemma (in prules) compile_complete:
  assumes "rs \<turnstile>\<^sub>p t \<longrightarrow> t'" "wellformed t"
  shows "compile rs \<turnstile>\<^sub>s pterm_to_sterm t \<longrightarrow> pterm_to_sterm t'"
using assms proof induction
  case (step name rhs)
  then show ?case
    apply simp
    apply rule
    apply (rule prules_as_srules.srewrite_stepI)
    unfolding compile_def
    apply (subst fset_of_list_elem[symmetric])
    apply (subst ordered_fmap_set_eq)
     apply (insert fmap)
     apply (rule is_fmapI)
     apply (force dest: is_fmapD)
    by (simp add: rev_fimage_eqI)
next
  case (beta c cs t t')
  from beta obtain pat rhs penv where "c = (pat, rhs)" "match pat t = Some penv" "subst rhs penv = t'"
    by (metis (no_types, lifting) map_option_eq_Some rewrite_step.simps surj_pair)
  then obtain senv where "match pat (pterm_to_sterm t) = Some senv" "srelated'.P_env penv senv"
    by (metis option_rel_Some1 srelated'.match_rel)
  have "wellformed rhs"
    using beta \<open>c = _\<close> prules.all_rules prule.simps
    by force
  then have "subst (pterm_to_sterm rhs) senv = pterm_to_sterm t'"
    using srelated_subst' \<open>_ = t'\<close> \<open>srelated'.P_env _ _\<close>
    by metis
  have "(pat, pterm_to_sterm rhs) |\<in>| map_prod id pterm_to_sterm |`| cs"
    using beta \<open>c = _\<close>
    by (metis fimage_eqI id_def map_prod_simp)
  have "is_fmap cs"
    using beta
    by auto
  have "find_match (ordered_fmap cs) t = Some (penv, pat, rhs)"
    apply (rule compatible_find_match)
    subgoal
      apply (subst ordered_fmap_set_eq[OF \<open>is_fmap cs\<close>])+
      using beta by simp
    subgoal
      unfolding list_all_iff
      apply rule
      apply (rename_tac x, case_tac x)
      apply simp
      apply (drule ordered_fmap_sound[OF \<open>is_fmap cs\<close>])
      using beta by auto
    subgoal
      apply (subst ordered_fmap_set_eq)
      by fact
    subgoal
      by fact
    subgoal
      using beta(1) \<open>c = _\<close> \<open>is_fmap cs\<close>
      using fset_of_list_elem ordered_fmap_set_eq by fast
    done

  show ?case
    apply simp
    apply rule
    apply (subst \<open>_ = pterm_to_sterm t'\<close>[symmetric])
    apply (rule find_match_rewrite_first)
    unfolding map_prod_def id_apply
    apply (subst ordered_fmap_image[symmetric])
     apply fact
    apply (subst map_prod_def[symmetric])
    apply (subst id_def[symmetric])
    apply (rule srelated_find_match)
    by fact+
qed (auto intro: srewrite.intros)

subsubsection \<open>Computability\<close>

export_code compile
  checking Scala

end