theory Refine_Monadic_Extensions
imports
  "../Libs/Refine_Monadic/Refine_Monadic"
  "Nondeterminism"
begin

  lemmas nres_monad_simps = nres_monad1 nres_monad2 nres_monad3

  lemma refine_IdI: "A \<le> B \<Longrightarrow> A \<le> \<Down> Id B" by simp
  lemma refine_Id_eq: "A \<le> \<Down> Id B \<longleftrightarrow> A \<le> B" by simp

  lemma FOREACH_sound[intro]:
    assumes "finite S"
    assumes "\<And> S' a\<^sub>1 x. S' \<subseteq> S \<Longrightarrow> foreach f S' a\<^sub>0 a\<^sub>1 \<Longrightarrow> x \<in> S - S' \<Longrightarrow> F x a\<^sub>1 \<le> SPEC (f x a\<^sub>1)"
    shows "FOREACH S F a\<^sub>0 \<le> SPEC (foreach f S a\<^sub>0)"
  proof (intro refine_vcg FOREACH_rule[where ?I = "\<lambda> S'. foreach f (S - S') a\<^sub>0"])
    case (goal1)
    show ?case using assms(1) by this
  next
    case (goal2)
    show ?case by auto
  next
    case (goal3 x S' a\<^sub>1)
    have 0: "S - (S' - {x}) = insert x (S - S')" using goal3(1-2) by auto
    show ?case
    unfolding 0
    proof (intro refine_vcg order_trans[OF assms(2)])
      show "S - S' \<subseteq> S" by auto
      show "foreach f (S - S') a\<^sub>0 a\<^sub>1" using goal3(3) by this
      show "x \<in> S - (S - S')" using goal3(1-2) by auto
      show "\<And> a\<^sub>2. f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> foreach f (insert x (S - S')) a\<^sub>0 a\<^sub>2" using goal3(1) goal3(3) by auto
    qed
  next
    case (goal4 a\<^sub>1)
    show ?case using goal4 by simp
  qed

  lemma FOREACHc_sound[intro]:
    assumes "finite S"
    assumes "\<And> S' a\<^sub>1 x. S' \<subseteq> S \<Longrightarrow> foreach\<^sub>C c f S' a\<^sub>0 a\<^sub>1 \<Longrightarrow> c a\<^sub>1 \<Longrightarrow> x \<in> S - S' \<Longrightarrow>
      F x a\<^sub>1 \<le> SPEC (f x a\<^sub>1)"
    shows "FOREACH\<^sub>C S c F a\<^sub>0 \<le> SPEC (foreach\<^sub>C c f S a\<^sub>0)"
  proof (intro refine_vcg FOREACHc_rule[where ?I = "\<lambda> S'. foreach\<^sub>C c f (S - S') a\<^sub>0"])
    case (goal1)
    show ?case using assms(1) by this
  next
    case (goal2)
    show ?case by auto
  next
    case (goal3 x S' a\<^sub>1)
    have 0: "S - (S' - {x}) = insert x (S - S')" using goal3(1-2) by auto
    show ?case
    unfolding 0
    proof (intro refine_vcg order_trans[OF assms(2)])
      show "S - S' \<subseteq> S" by auto
      show "foreach\<^sub>C c f (S - S') a\<^sub>0 a\<^sub>1" using goal3(3) by this
      show "c a\<^sub>1" using goal3(4) by this
      show "x \<in> S - (S - S')" using goal3(1-2) by auto
    next
      case (goal5 a\<^sub>2)
      show ?case
      proof (rule insert)
        show "foreach\<^sub>C c f (S - S') a\<^sub>0 a\<^sub>1" using goal3(3) by this
        show "c a\<^sub>1" using goal3(4) by this
        show "x \<notin> S - S'" using goal3(1) by auto
        show "f x a\<^sub>1 a\<^sub>2" using goal5 by this
      qed
    qed
  next
    case (goal4 a\<^sub>1)
    show ?case using goal4 by simp
  next
    case (goal5 S' a\<^sub>1)
    show ?case
    proof (rule abort)
      show "foreach\<^sub>C c f (S - S') a\<^sub>0 a\<^sub>1" using goal5(3) by this
      show "\<not> c a\<^sub>1" using goal5(4) by this
      show "S - S' \<subseteq> S" by auto
    qed
  qed

  definition FIND :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a option nres"
    where "FIND A P \<equiv> FOREACH\<^sub>C A (op = None) (\<lambda> a _. RETURN (if P a then Some a else None)) None"

  lemma FIND_sound[intro]:
    assumes "finite A"
    shows "FIND A P \<le> SPEC (find A P)"
  proof -
    have "FIND A P = FOREACH\<^sub>C A (op = None) (\<lambda> a _. RETURN (if P a then Some a else None)) None"
      unfolding FIND_def by rule
    also have "\<dots> \<le> SPEC (foreach\<^sub>C (op = None) (\<lambda> a _. op = (if P a then Some a else None)) A None)"
      using assms by auto
    also have "\<dots> \<le> SPEC (find A P)"
    proof (rule SPEC_rule)
      fix r'
      assume 1: "foreach\<^sub>C (op = None) (\<lambda> a _. op = (if P a then Some a else None)) A None r'"
      def r \<equiv> "None :: 'a option"
      have 2: "foreach\<^sub>C (op = None) (\<lambda> a _. op = (if P a then Some a else None)) A r r'"
        using 1 unfolding r_def by this
      show "find A P r'"
      using 2 r_def
      proof induct
        case empty
        show ?case by auto
      next
        case (insert S a\<^sub>1 x a\<^sub>2)
        show ?case using insert by auto
      next
        case (abort S a\<^sub>1 S')
        show ?case using abort by (cases a\<^sub>1, auto)
      qed
    qed
    finally show ?thesis by this
  qed

end