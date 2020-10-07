section \<open>Terms with explicit pattern matching\<close>

theory Pterm
imports
  "../Utils/Compiler_Utils"
  Consts
  Sterm \<comment> \<open>Inclusion of this theory might seem a bit strange. Indeed, it is only for technical
    reasons: to allow for a \<^theory_text>\<open>quickcheck\<close> setup.\<close>
begin

datatype pterm =
  Pconst name |
  Pvar name |
  Pabs "(term \<times> pterm) fset" |
  Papp pterm pterm (infixl "$\<^sub>p" 70)

primrec sterm_to_pterm :: "sterm \<Rightarrow> pterm" where
"sterm_to_pterm (Sconst name) = Pconst name" |
"sterm_to_pterm (Svar name) = Pvar name" |
"sterm_to_pterm (t $\<^sub>s u) = sterm_to_pterm t $\<^sub>p sterm_to_pterm u" |
"sterm_to_pterm (Sabs cs) = Pabs (fset_of_list (map (map_prod id sterm_to_pterm) cs))"

quickcheck_generator pterm
  \<comment> \<open>will print some fishy ``constructor'' names, but at least it works\<close>
  constructors: sterm_to_pterm

lemma sterm_to_pterm_total:
  obtains t' where "t = sterm_to_pterm t'"
proof (induction t arbitrary: thesis)
  case (Pconst x)
  then show ?case
    by (metis sterm_to_pterm.simps)
next
  case (Pvar x)
  then show ?case
    by (metis sterm_to_pterm.simps)
next
  case (Pabs cs)
  from Pabs.IH obtain cs' where "cs = fset_of_list (map (map_prod id sterm_to_pterm) cs')"
    apply atomize_elim
    proof (induction cs)
      case empty
      show ?case
        apply (rule exI[where x = "[]"])
        by simp
    next
      case (insert c cs)
      obtain pat rhs where "c = (pat, rhs)" by (cases c) auto

      have "\<exists>cs'. cs = fset_of_list (map (map_prod id sterm_to_pterm) cs')"
        apply (rule insert)
        using insert.prems unfolding finsert.rep_eq
        by blast
      then obtain cs' where "cs = fset_of_list (map (map_prod id sterm_to_pterm) cs')"
        by blast

      obtain rhs' where "rhs = sterm_to_pterm rhs'"
        apply (rule insert.prems[of "(pat, rhs)" rhs])
        unfolding \<open>c = _\<close> by simp+

      show ?case
        apply (rule exI[where x = "(pat, rhs') # cs'"])
        unfolding \<open>c = _\<close> \<open>cs = _\<close> \<open>rhs = _\<close>
        by (simp add: id_def)
    qed
  hence "Pabs cs = sterm_to_pterm (Sabs cs')"
    by simp
  then show ?case
    using Pabs by metis
next
  case (Papp t1 t2)
  then obtain t1' t2' where "t1 = sterm_to_pterm t1'" "t2 = sterm_to_pterm t2'"
    by metis
  then have "t1 $\<^sub>p t2 = sterm_to_pterm (t1' $\<^sub>s t2')"
    by simp
  with Papp show ?case
    by metis
qed

lemma pterm_induct[case_names Pconst Pvar Pabs Papp]:
  assumes "\<And>x. P (Pconst x)"
  assumes "\<And>x. P (Pvar x)"
  assumes "\<And>cs. (\<And>pat t. (pat, t) |\<in>| cs \<Longrightarrow> P t) \<Longrightarrow> P (Pabs cs)"
  assumes "\<And>t u. P t \<Longrightarrow> P u \<Longrightarrow> P (t $\<^sub>p u)"
  shows "P t"
proof (rule pterm.induct, goal_cases)
  case (3 cs)
  show ?case
    apply (rule assms)
    using 3
    apply (subst (asm) fmember.rep_eq[symmetric])
    by auto
qed fact+

instantiation pterm :: pre_term begin

definition app_pterm where
"app_pterm t u = t $\<^sub>p u"

fun unapp_pterm where
"unapp_pterm (t $\<^sub>p u) = Some (t, u)" |
"unapp_pterm _ = None"

definition const_pterm where
"const_pterm = Pconst"

fun unconst_pterm where
"unconst_pterm (Pconst name) = Some name" |
"unconst_pterm _ = None"

definition free_pterm where
"free_pterm = Pvar"

fun unfree_pterm where
"unfree_pterm (Pvar name) = Some name" |
"unfree_pterm _ = None"

function (sequential) subst_pterm where
"subst_pterm (Pvar s) env = (case fmlookup env s of Some t \<Rightarrow> t | None \<Rightarrow> Pvar s)" |
"subst_pterm (t\<^sub>1 $\<^sub>p t\<^sub>2) env = subst_pterm t\<^sub>1 env $\<^sub>p subst_pterm t\<^sub>2 env" |
"subst_pterm (Pabs cs) env = Pabs ((\<lambda>(pat, rhs). (pat, subst_pterm rhs (fmdrop_fset (frees pat) env))) |`| cs)" |
"subst_pterm t _ = t"
by pat_completeness auto

termination
proof (relation "measure (size \<circ> fst)", goal_cases)
  case 4
  then show ?case
    apply auto
    including fset.lifting apply transfer
    apply (rule le_imp_less_Suc)
    apply (rule sum_nat_le_single[where y = "(a, (b, size b))" for a b])
    by auto
qed auto

primrec consts_pterm :: "pterm \<Rightarrow> name fset" where
"consts_pterm (Pconst x) = {|x|}" |
"consts_pterm (t\<^sub>1 $\<^sub>p t\<^sub>2) = consts_pterm t\<^sub>1 |\<union>| consts_pterm t\<^sub>2" |
"consts_pterm (Pabs cs) = ffUnion (snd |`| map_prod id consts_pterm |`| cs)" |
"consts_pterm (Pvar _) = {||}"

primrec frees_pterm :: "pterm \<Rightarrow> name fset" where
"frees_pterm (Pvar x) = {|x|}" |
"frees_pterm (t\<^sub>1 $\<^sub>p t\<^sub>2) = frees_pterm t\<^sub>1 |\<union>| frees_pterm t\<^sub>2" |
"frees_pterm (Pabs cs) = ffUnion ((\<lambda>(pv, tv). tv - frees pv) |`| map_prod id frees_pterm |`| cs)" |
"frees_pterm (Pconst _) = {||}"

instance
by standard
   (auto
      simp: app_pterm_def const_pterm_def free_pterm_def
      elim: unapp_pterm.elims unconst_pterm.elims unfree_pterm.elims
      split: option.splits)

end

corollary subst_pabs_id:
  assumes "\<And>pat rhs. (pat, rhs) |\<in>| cs \<Longrightarrow> subst rhs (fmdrop_fset (frees pat) env) = rhs"
  shows "subst (Pabs cs) env = Pabs cs"
apply (subst subst_pterm.simps)
apply (rule arg_cong[where f = Pabs])
apply (rule fset_map_snd_id)
apply (rule assms)
apply (subst (asm) fmember.rep_eq[symmetric])
apply assumption
done

corollary frees_pabs_alt_def:
  "frees (Pabs cs) = ffUnion ((\<lambda>(pat, rhs). frees rhs - frees pat) |`| cs)"
apply simp
apply (rule arg_cong[where f = ffUnion])
apply (rule fset.map_cong[OF refl])
by auto

lemma sterm_to_pterm_frees[simp]: "frees (sterm_to_pterm t) = frees t"
proof (induction t)
  case (Sabs cs)
  show ?case
    apply simp
    apply (rule arg_cong[where f = ffUnion])
    apply (rule fimage_cong[OF refl])
    apply clarsimp
    apply (subst Sabs)
    by (auto simp: fset_of_list_elem snds.simps)
qed auto

lemma sterm_to_pterm_consts[simp]: "consts (sterm_to_pterm t) = consts t"
proof (induction t)
  case (Sabs cs)
  show ?case
    apply simp
    apply (rule arg_cong[where f = ffUnion])
    apply (rule fimage_cong[OF refl])
    apply clarsimp
    apply (subst Sabs)
    by (auto simp: fset_of_list_elem snds.simps)
qed auto

lemma subst_sterm_to_pterm:
  "subst (sterm_to_pterm t) (fmmap sterm_to_pterm env) = sterm_to_pterm (subst t env)"
proof (induction t arbitrary: env rule: sterm_induct)
  case (Sabs cs)
  show ?case
    apply simp
    apply (rule fset.map_cong0)
    apply (auto split: prod.splits)
    apply (rule Sabs)
    by (auto simp: fset_of_list.rep_eq)
qed (auto split: option.splits)

instantiation pterm :: "term" begin

definition abs_pred_pterm :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm \<Rightarrow> bool" where
[code del]: "abs_pred P t \<longleftrightarrow> (\<forall>cs. t = Pabs cs \<longrightarrow> (\<forall>pat t. (pat, t) |\<in>| cs \<longrightarrow> P t) \<longrightarrow> P t)"

context begin

private lemma abs_pred_trivI0: "P t \<Longrightarrow> abs_pred P (t::pterm)"
unfolding abs_pred_pterm_def by auto

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    by (induction t rule: pterm_induct)
       (auto simp: const_pterm_def free_pterm_def app_pterm_def abs_pred_pterm_def)
next
  (* FIXME proving 2, 3 and 4 via sterm probably requires lifting setup *)
  (* lifting setup requires a consistent ordering without assumptions! *)
  (* but: other parts (in Eq_Logic_PM_Seq) require a key-ordering that only works with assumptions *)
  (* solution: don't try to abstract over the ordering *)

  case (2 t)
  show ?case
    unfolding abs_pred_pterm_def
    apply clarify
    apply (rule subst_pabs_id)
    by blast
next
  case (3 x t)
  show ?case
    unfolding abs_pred_pterm_def
    apply clarsimp
    apply (rule fset.map_cong0)
    apply (rename_tac c)
    apply (case_tac c; hypsubst_thin)
    apply simp
    subgoal for cs env pat rhs
      apply (cases "x |\<in>| frees pat")
      subgoal
        apply (rule arg_cong[where f = "subst rhs"])
        by (auto intro: fmap_ext)
      subgoal premises prems[rule_format]
        apply (subst (2) prems(1)[symmetric, where pat = pat])
        subgoal
          by (subst fmember.rep_eq) fact
        subgoal
          using prems unfolding ffUnion_alt_def
          by (auto simp: fmember.rep_eq fset_of_list.rep_eq elim!: fBallE)
        subgoal
          apply (rule arg_cong[where f = "subst rhs"])
          by (auto intro: fmap_ext)
        done
      done
    done
next
  case (4 t)
  show ?case
    unfolding abs_pred_pterm_def
    apply clarsimp
    apply (rule fset.map_cong0)
    apply clarsimp
    subgoal premises prems[rule_format] for cs env\<^sub>1 env\<^sub>2 a b
      apply (rule prems(2)[unfolded fmember.rep_eq, OF prems(5)])
      using prems unfolding fdisjnt_alt_def by auto
    done
next
  case 5
  show ?case
    proof (rule abs_pred_trivI0, clarify)
      fix t :: pterm
      fix env :: "(name, pterm) fmap"

      obtain t' where "t = sterm_to_pterm t'"
        by (rule sterm_to_pterm_total)
      obtain env' where "env = fmmap sterm_to_pterm env'"
        by (metis fmmap_total sterm_to_pterm_total)

      show "frees (subst t env) = frees t - fmdom env" if "fmpred (\<lambda>_. closed) env"
        unfolding \<open>t = _\<close> \<open>env = _\<close>
        apply simp
        apply (subst subst_sterm_to_pterm)
        apply simp
        apply (rule subst_frees)
        using that unfolding \<open>env = _\<close>
        apply simp
        apply (rule fmpred_mono_strong; assumption?)
        unfolding closed_except_def by simp
    qed
next
  case 6
  show ?case
    proof (rule abs_pred_trivI0, clarify)
      fix t :: pterm
      fix env :: "(name, pterm) fmap"

      obtain t' where "t = sterm_to_pterm t'"
        by (rule sterm_to_pterm_total)
      obtain env' where "env = fmmap sterm_to_pterm env'"
        by (metis fmmap_total sterm_to_pterm_total)

      show "consts (subst t env) = consts t |\<union>| ffUnion (consts |`| fmimage env (frees t))"
        unfolding \<open>t = _\<close> \<open>env = _\<close>
        apply simp
        apply (subst comp_def)
        apply simp
        apply (subst subst_sterm_to_pterm)
        apply simp
        apply (rule subst_consts')
        done
    qed
qed (rule abs_pred_trivI0)

end

end

lemma no_abs_abs[simp]: "\<not> no_abs (Pabs cs)"
by (subst no_abs.simps) (auto simp: term_cases_def)

lemma sterm_to_pterm:
  assumes "no_abs t"
  shows "sterm_to_pterm t = convert_term t"
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

abbreviation Pabs_single ("\<Lambda>\<^sub>p _. _" [0, 50] 50) where
"Pabs_single x rhs \<equiv> Pabs {| (Free x, rhs) |}"

lemma closed_except_simps:
  "closed_except (Pvar x) S \<longleftrightarrow> x |\<in>| S"
  "closed_except (t\<^sub>1 $\<^sub>p t\<^sub>2) S \<longleftrightarrow> closed_except t\<^sub>1 S \<and> closed_except t\<^sub>2 S"
  "closed_except (Pabs cs) S \<longleftrightarrow> fBall cs (\<lambda>(pat, t). closed_except t (S |\<union>| frees pat))"
  "closed_except (Pconst name) S \<longleftrightarrow> True"
proof goal_cases
  case 3
  show ?case
    proof (standard, goal_cases)
      case 1
      then show ?case
        apply (auto simp: ffUnion_alt_def closed_except_def)
        apply (drule ffUnion_least_rev)
        apply auto
        by (smt case_prod_conv fBall_alt_def fminus_iff fset_rev_mp id_apply map_prod_simp)
    next
      case 2
      then show ?case
        by (fastforce simp: ffUnion_alt_def closed_except_def)
    qed
qed (auto simp: ffUnion_alt_def closed_except_def)

instantiation pterm :: pre_strong_term  begin

function (sequential) wellformed_pterm :: "pterm \<Rightarrow> bool" where
"wellformed_pterm (t\<^sub>1 $\<^sub>p t\<^sub>2) \<longleftrightarrow> wellformed_pterm t\<^sub>1 \<and> wellformed_pterm t\<^sub>2" |
"wellformed_pterm (Pabs cs) \<longleftrightarrow> fBall cs (\<lambda>(pat, t). linear pat \<and> wellformed_pterm t) \<and> is_fmap cs \<and> pattern_compatibles cs \<and> cs \<noteq> {||}" |
"wellformed_pterm _ \<longleftrightarrow> True"
by pat_completeness auto

termination
proof (relation "measure size", goal_cases)
  case 4
  then show ?case
    apply auto
    including fset.lifting apply transfer
    apply (rule le_imp_less_Suc)
    apply (rule sum_nat_le_single[where y = "(a, (b, size b))" for a b])
    by auto
qed auto

primrec all_frees_pterm :: "pterm \<Rightarrow> name fset" where
"all_frees_pterm (Pvar x) = {|x|}" |
"all_frees_pterm (t\<^sub>1 $\<^sub>p t\<^sub>2) = all_frees_pterm t\<^sub>1 |\<union>| all_frees_pterm t\<^sub>2" |
"all_frees_pterm (Pabs cs) = ffUnion ((\<lambda>(P, T). P |\<union>| T) |`| map_prod frees all_frees_pterm |`| cs)" |
"all_frees_pterm (Pconst _) = {||}"

instance
by standard (auto simp: const_pterm_def free_pterm_def app_pterm_def)

end

lemma sterm_to_pterm_all_frees[simp]: "all_frees (sterm_to_pterm t) = all_frees t"
proof (induction t)
  case (Sabs cs)
  show ?case
    apply simp
    apply (rule arg_cong[where f = ffUnion])
    apply (rule fimage_cong[OF refl])
    apply clarsimp
    apply (subst Sabs)
    by (auto simp: fset_of_list_elem snds.simps)
qed auto

instance pterm :: strong_term proof (standard, goal_cases)
  case (1 t)
  obtain t' where "t = sterm_to_pterm t'"
    by (metis sterm_to_pterm_total)
  show ?case
    apply (rule abs_pred_trivI)
    unfolding \<open>t = _\<close> sterm_to_pterm_all_frees sterm_to_pterm_frees
    by (rule frees_all_frees)
next
  case (2 t)
  show ?case
    unfolding abs_pred_pterm_def
    apply (intro allI impI)
    apply (simp add: case_prod_twice, intro conjI)
    subgoal by blast
    subgoal by (auto intro: is_fmap_image)
    subgoal
      unfolding fpairwise_image fpairwise_alt_def
      by (auto elim!: fBallE)
    done
qed

lemma wellformed_PabsI:
  assumes "is_fmap cs" "pattern_compatibles cs" "cs \<noteq> {||}"
  assumes "\<And>pat t. (pat, t) |\<in>| cs \<Longrightarrow> linear pat"
  assumes "\<And>pat t. (pat, t) |\<in>| cs \<Longrightarrow> wellformed t"
  shows "wellformed (Pabs cs)"
using assms by auto

corollary subst_closed_pabs:
  assumes "(pat, rhs) |\<in>| cs" "closed (Pabs cs)"
  shows "subst rhs (fmdrop_fset (frees pat) env) = rhs"
using assms by (subst subst_closed_except_id) (auto simp: fdisjnt_alt_def closed_except_simps)

lemma (in constants) shadows_consts_pterm_simps[simp]:
  "shadows_consts (t\<^sub>1 $\<^sub>p t\<^sub>2) \<longleftrightarrow> shadows_consts t\<^sub>1 \<or> shadows_consts t\<^sub>2"
  "shadows_consts (Pvar name) \<longleftrightarrow> name |\<in>| all_consts"
  "shadows_consts (Pabs cs) \<longleftrightarrow> fBex cs (\<lambda>(pat, t). shadows_consts pat \<or> shadows_consts t)"
  "shadows_consts (Pconst name) \<longleftrightarrow> False"
proof goal_cases
  case 3

  (* FIXME duplicated from Sterm *)
  show ?case
    unfolding shadows_consts_def
    apply rule
    subgoal
      by (force simp: ffUnion_alt_def fset_of_list_elem fdisjnt_alt_def elim!: ballE)
    subgoal
      apply (auto simp: fset_of_list_elem fdisjnt_alt_def)
      by (auto simp: fset_eq_empty_iff ffUnion_alt_def fset_of_list_elem elim!: allE fBallE)
    done
qed (auto simp: shadows_consts_def fdisjnt_alt_def)

end