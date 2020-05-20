section \<open>Terms with sequential pattern matching\<close>

theory Sterm
imports Strong_Term
begin

datatype sterm =
  Sconst name |
  Svar name |
  Sabs (clauses: "(term \<times> sterm) list") |
  Sapp sterm sterm (infixl "$\<^sub>s" 70)

datatype_compat sterm

derive linorder sterm

abbreviation Sabs_single ("\<Lambda>\<^sub>s _. _" [0, 50] 50) where
"Sabs_single x rhs \<equiv> Sabs [(Free x, rhs)]"

type_synonym sclauses = "(term \<times> sterm) list"

lemma sterm_induct[case_names Sconst Svar Sabs Sapp]:
  assumes "\<And>x. P (Sconst x)"
  assumes "\<And>x. P (Svar x)"
  assumes "\<And>cs. (\<And>pat t. (pat, t) \<in> set cs \<Longrightarrow> P t) \<Longrightarrow> P (Sabs cs)"
  assumes "\<And>t u. P t \<Longrightarrow> P u \<Longrightarrow> P (t $\<^sub>s u)"
  shows "P t"
using assms
  apply induction_schema
    apply pat_completeness
   apply lexicographic_order
  done

instantiation sterm :: pre_term begin

definition app_sterm where
"app_sterm t u = t $\<^sub>s u"

fun unapp_sterm where
"unapp_sterm (t $\<^sub>s u) = Some (t, u)" |
"unapp_sterm _ = None"

definition const_sterm where
"const_sterm = Sconst"

fun unconst_sterm where
"unconst_sterm (Sconst name) = Some name" |
"unconst_sterm _ = None"

fun unfree_sterm where
"unfree_sterm (Svar name) = Some name" |
"unfree_sterm _ = None"

definition free_sterm where
"free_sterm = Svar"

fun frees_sterm where
"frees_sterm (Svar name) = {|name|}" |
"frees_sterm (Sconst _) = {||}" |
"frees_sterm (Sabs cs) = ffUnion (fset_of_list (map (\<lambda>(pat, rhs). frees_sterm rhs - frees pat) cs))" |
"frees_sterm (t $\<^sub>s u) = frees_sterm t |\<union>| frees_sterm u"

fun subst_sterm where
"subst_sterm (Svar s) env = (case fmlookup env s of Some t \<Rightarrow> t | None \<Rightarrow> Svar s)" |
"subst_sterm (t\<^sub>1 $\<^sub>s t\<^sub>2) env = subst_sterm t\<^sub>1 env $\<^sub>s subst_sterm t\<^sub>2 env" |
"subst_sterm (Sabs cs) env = Sabs (map (\<lambda>(pat, rhs). (pat, subst_sterm rhs (fmdrop_fset (frees pat) env))) cs)" |
"subst_sterm t env = t"

fun consts_sterm :: "sterm \<Rightarrow> name fset" where
"consts_sterm (Svar _) = {||}" |
"consts_sterm (Sconst name) = {|name|}" |
"consts_sterm (Sabs cs) = ffUnion (fset_of_list (map (\<lambda>(_, rhs). consts_sterm rhs) cs))" |
"consts_sterm (t $\<^sub>s u) = consts_sterm t |\<union>| consts_sterm u"

instance
by standard
   (auto
      simp: app_sterm_def const_sterm_def free_sterm_def
      elim: unapp_sterm.elims unconst_sterm.elims unfree_sterm.elims
      split: option.splits)

end

instantiation sterm :: "term" begin

definition abs_pred_sterm :: "(sterm \<Rightarrow> bool) \<Rightarrow> sterm \<Rightarrow> bool" where
[code del]: "abs_pred P t \<longleftrightarrow> (\<forall>cs. t = Sabs cs \<longrightarrow> (\<forall>pat t. (pat, t) \<in> set cs \<longrightarrow> P t) \<longrightarrow> P t)"

lemma abs_pred_stermI[intro]:
  assumes "\<And>cs. (\<And>pat t. (pat, t) \<in> set cs \<Longrightarrow> P t) \<Longrightarrow> P (Sabs cs)"
  shows "abs_pred P t"
using assms unfolding abs_pred_sterm_def by auto

instance proof (standard, goal_cases)
  case (1 P t)
  then show ?case
    by (induction t) (auto simp: const_sterm_def free_sterm_def app_sterm_def abs_pred_sterm_def)
next
  case (2 t)
  show ?case
    apply rule
    apply auto
    apply (subst (3) list.map_id[symmetric])
    apply (rule list.map_cong0)
    apply auto
    by blast
next
  case (3 x t)
  show ?case
    apply rule
    apply clarsimp
    subgoal for cs env pat rhs
      apply (cases "x |\<in>| frees pat")
      subgoal
        apply (rule arg_cong[where f = "subst rhs"])
        by (auto intro: fmap_ext)
      subgoal premises prems[rule_format]
        apply (subst (2) prems(1)[symmetric, where pat = pat])
        subgoal by fact
        subgoal
          using prems
          unfolding ffUnion_alt_def
          by (auto simp add: fmember.rep_eq fset_of_list.rep_eq elim!: fBallE)
        subgoal
          apply (rule arg_cong[where f = "subst rhs"])
          by (auto intro: fmap_ext)
        done
      done
    done
next
  case (4 t)
  show ?case
    apply rule
    apply clarsimp
    subgoal premises prems[rule_format]
      apply (rule prems(1)[OF prems(4)])
      subgoal using prems by auto
      subgoal using prems unfolding fdisjnt_alt_def by auto
      done
    done
next
  case 5
  show ?case
    proof (intro abs_pred_stermI allI impI, goal_cases)
      case (1 cs env)
      show ?case
        proof safe
          fix name
          assume "name |\<in>| frees (subst (Sabs cs) env)"
          then obtain pat rhs
            where "(pat, rhs) \<in> set cs"
              and "name |\<in>| frees (subst rhs (fmdrop_fset (frees pat) env))"
              and "name |\<notin>| frees pat"
            by (auto simp: fset_of_list_elem case_prod_twice comp_def ffUnion_alt_def)

          hence "name |\<in>| frees rhs |-| fmdom (fmdrop_fset (frees pat) env)"
            using 1 by (simp add: fmpred_drop_fset)

          hence "name |\<in>| frees rhs |-| frees pat"
            using \<open>name |\<notin>| frees pat\<close> by blast

          show "name |\<in>| frees (Sabs cs)"
            apply (simp add: ffUnion_alt_def)
            apply (rule fBexI[where x = "(pat, rhs)"])
            unfolding prod.case
             apply (fact \<open>name |\<in>| frees rhs |-| frees pat\<close>)
            unfolding fset_of_list_elem
            by fact

          assume "name |\<in>| fmdom env"
          thus False
            using \<open>name |\<in>| frees rhs |-| fmdom (fmdrop_fset (frees pat) env)\<close> \<open>name |\<notin>| frees pat\<close>
            by fastforce
        next
          fix name
          assume "name |\<in>| frees (Sabs cs)" "name |\<notin>| fmdom env"

          then obtain pat rhs
            where "(pat, rhs) \<in> set cs" "name |\<in>| frees rhs" "name |\<notin>| frees pat"
            by (auto simp: fset_of_list_elem ffUnion_alt_def)

          moreover hence "name |\<in>| frees rhs |-| fmdom (fmdrop_fset (frees pat) env) |-| frees pat"
            using \<open>name |\<notin>| fmdom env\<close> by fastforce

          ultimately have "name |\<in>| frees (subst rhs (fmdrop_fset (frees pat) env)) |-| frees pat"
            using 1 by (simp add: fmpred_drop_fset)

          show "name |\<in>| frees (subst (Sabs cs) env)"
            apply (simp add: case_prod_twice comp_def)
            unfolding ffUnion_alt_def
            apply (rule fBexI)
             apply (fact \<open>name |\<in>| frees (subst rhs (fmdrop_fset (frees pat) env)) |-| frees pat\<close>)
            apply (subst fimage_iff)
            apply (rule fBexI[where x = "(pat, rhs)"])
             apply simp
            using \<open>(pat, rhs) \<in> set cs\<close>
            by (auto simp: fset_of_list_elem)
        qed
    qed
next
  case 6
  show ?case
    proof (intro abs_pred_stermI allI impI, goal_cases)
      case (1 cs env)

      \<comment> \<open>some property on various operations that is only useful in here\<close>
      have *: "fbind (fmimage m (fbind A g)) f = fbind A (\<lambda>x. fbind (fmimage m (g x)) f)"
        for m A f g
        including fset.lifting fmap.lifting
        by transfer' force

      have "consts (subst (Sabs cs) env) = fbind (fset_of_list cs) (\<lambda>(pat, rhs). consts rhs |\<union>| ffUnion (consts |`| fmimage (fmdrop_fset (frees pat) env) (frees rhs)))"
        apply (simp add: funion_image_bind_eq)
        apply (rule fbind_cong[OF refl])
        apply (clarsimp split: prod.splits)
        apply (subst 1)
         apply (subst (asm) fset_of_list_elem, assumption)
        apply simp
        by (simp add: funion_image_bind_eq)
      also have "\<dots> = fbind (fset_of_list cs) (consts \<circ> snd) |\<union>| fbind (fset_of_list cs) (\<lambda>(pat, rhs). ffUnion (consts |`| fmimage (fmdrop_fset (frees pat) env) (frees rhs)))"
        apply (subst fbind_fun_funion[symmetric])
        apply (rule fbind_cong[OF refl])
        by auto
      also have "\<dots> = consts (Sabs cs) |\<union>| fbind (fset_of_list cs) (\<lambda>(pat, rhs). ffUnion (consts |`| fmimage (fmdrop_fset (frees pat) env) (frees rhs)))"
        apply (rule cong[OF cong, OF refl _ refl, where f1 = "funion"])
        apply (subst funion_image_bind_eq[symmetric])
        unfolding consts_sterm.simps
        apply (rule arg_cong[where f = ffUnion])
        apply (subst fset_of_list_map)
        apply (rule fset.map_cong[OF refl])
        by auto
      also have "\<dots> = consts (Sabs cs) |\<union>| fbind (fmimage env (fbind (fset_of_list cs) (\<lambda>(pat, rhs). frees rhs |-| frees pat))) consts"
        apply (subst funion_image_bind_eq)
        apply (subst fmimage_drop_fset)
        apply (rule cong[OF cong, OF refl refl, where f1 = "funion"])
        apply (subst *)
        apply (rule fbind_cong[OF refl])
        by auto
      also have "\<dots> = consts (Sabs cs) |\<union>| ffUnion (consts |`| fmimage env (frees (Sabs cs)))"
        by (simp only: frees_sterm.simps fset_of_list_map  fmimage_Union funion_image_bind_eq)

      finally show ?case .
    qed
qed (auto simp: abs_pred_sterm_def)

end

lemma no_abs_abs[simp]: "\<not> no_abs (Sabs cs)"
by (subst no_abs.simps) (auto simp: term_cases_def)

lemma closed_except_simps:
  "closed_except (Svar x) S \<longleftrightarrow> x |\<in>| S"
  "closed_except (t\<^sub>1 $\<^sub>s t\<^sub>2) S \<longleftrightarrow> closed_except t\<^sub>1 S \<and> closed_except t\<^sub>2 S"
  "closed_except (Sabs cs) S \<longleftrightarrow> list_all (\<lambda>(pat, t). closed_except t (S |\<union>| frees pat)) cs"
  "closed_except (Sconst name) S \<longleftrightarrow> True"
proof goal_cases
  case 3
  show ?case
    proof (standard, goal_cases)
      case 1
      then show ?case
        apply (auto simp: list_all_iff ffUnion_alt_def fset_of_list_elem closed_except_def)
        apply (drule ffUnion_least_rev)
        apply auto
        by (smt case_prod_conv fbspec fimageI fminusI fset_of_list_elem fset_rev_mp)
    next
      case 2
      then show ?case
        by (fastforce simp: list_all_iff ffUnion_alt_def fset_of_list_elem closed_except_def)
    qed
qed (auto simp: ffUnion_alt_def closed_except_def)

lemma closed_except_sabs:
  assumes "closed (Sabs cs)" "(pat, rhs) \<in> set cs"
  shows "closed_except rhs (frees pat)"
using assms unfolding closed_except_def
apply auto
by (metis bot.extremum_uniqueI fempty_iff ffUnion_subset_elem fimageI fminusI fset_of_list_elem old.prod.case)

instantiation sterm :: strong_term  begin

fun wellformed_sterm :: "sterm \<Rightarrow> bool" where
"wellformed_sterm (t\<^sub>1 $\<^sub>s t\<^sub>2) \<longleftrightarrow> wellformed_sterm t\<^sub>1 \<and> wellformed_sterm t\<^sub>2" |
"wellformed_sterm (Sabs cs) \<longleftrightarrow> list_all (\<lambda>(pat, t). linear pat \<and> wellformed_sterm t) cs \<and> distinct (map fst cs) \<and> cs \<noteq> []" |
"wellformed_sterm _ \<longleftrightarrow> True"

primrec all_frees_sterm :: "sterm \<Rightarrow> name fset" where
"all_frees_sterm (Svar x) = {|x|}" |
"all_frees_sterm (t\<^sub>1 $\<^sub>s t\<^sub>2) = all_frees_sterm t\<^sub>1 |\<union>| all_frees_sterm t\<^sub>2" |
"all_frees_sterm (Sabs cs) = ffUnion (fset_of_list (map (\<lambda>(P, T). P |\<union>| T) (map (map_prod frees all_frees_sterm) cs)))" |
"all_frees_sterm (Sconst _) = {||}"

instance proof (standard, goal_cases)
  case (7 t)
  show ?case
    apply (intro abs_pred_stermI allI impI)
    apply simp
    apply (rule ffUnion_least)
    apply (rule fBallI)
    apply auto
    apply (subst ffUnion_alt_def)
    apply simp
    apply (rule_tac x = "(a, b)" in fBexI)
    by (auto simp: fset_of_list_elem)
next
  case (8 t)
  show ?case
    apply (intro abs_pred_stermI allI impI)
    apply (simp add: list.pred_map comp_def case_prod_twice, safe)
    subgoal
      apply (subst list_all_iff)
      apply (rule ballI)
      apply safe[1]
       apply (fastforce simp: list_all_iff)
      subgoal premises prems[rule_format]
        apply (rule prems)
          apply (fact prems)
        using prems apply (fastforce simp: list_all_iff)
        using prems by force
      done
    subgoal
      apply (subst map_cong[OF refl])
      by auto
    done
qed (auto simp: const_sterm_def free_sterm_def app_sterm_def)

end

lemma match_sabs[simp]: "\<not> is_free t \<Longrightarrow> match t (Sabs cs) = None"
by (cases t) auto

context pre_constants begin

lemma welldefined_sabs: "welldefined (Sabs cs) \<longleftrightarrow> list_all (\<lambda>(_, t). welldefined t) cs"
apply (auto simp: list_all_iff ffUnion_alt_def dest!: ffUnion_least_rev)
 apply (subst (asm) list_all_iff_fset[symmetric])
 apply (auto simp: list_all_iff fset_of_list_elem)
done

lemma shadows_consts_sterm_simps[simp]:
  "shadows_consts (t\<^sub>1 $\<^sub>s t\<^sub>2) \<longleftrightarrow> shadows_consts t\<^sub>1 \<or> shadows_consts t\<^sub>2"
  "shadows_consts (Svar name) \<longleftrightarrow> name |\<in>| all_consts"
  "shadows_consts (Sabs cs) \<longleftrightarrow> list_ex (\<lambda>(pat, t). \<not> fdisjnt all_consts (frees pat) \<or> shadows_consts t) cs"
  "shadows_consts (Sconst name) \<longleftrightarrow> False"
proof (goal_cases)
  case 3
  show ?case
    unfolding shadows_consts_def list_ex_iff
    apply rule
    subgoal
      by (force simp: ffUnion_alt_def fset_of_list_elem fdisjnt_alt_def elim!: ballE)
    subgoal
      apply (auto simp: fset_of_list_elem fdisjnt_alt_def)
      by (auto simp: fset_eq_empty_iff ffUnion_alt_def fset_of_list_elem elim!: allE fBallE)
    done
qed (auto simp: shadows_consts_def fdisjnt_alt_def)

(* FIXME derive from axioms? *)
lemma subst_shadows:
  assumes "\<not> shadows_consts (t::sterm)" "not_shadows_consts_env \<Gamma>"
  shows "\<not> shadows_consts (subst t \<Gamma>)"
using assms proof (induction t arbitrary: \<Gamma> rule: sterm_induct)
  case (Sabs cs)
  show ?case
    apply (simp add: list_ex_iff case_prod_twice)
    apply (rule ballI)
    subgoal for c
      apply (cases c, hypsubst_thin, simp)
      apply (rule conjI)
      subgoal using Sabs(2) by (fastforce simp: list_ex_iff)
      apply (rule Sabs(1))
        apply assumption
      subgoal using Sabs(2) by (fastforce simp: list_ex_iff)
      subgoal using Sabs(3) by force
      done
    done
qed (auto split: option.splits)

end

end