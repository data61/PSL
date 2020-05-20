section \<open>Chain-Complete Partial Orders\<close>

theory CCPO_Extensions
imports
  "HOL-Library.Complete_Partial_Order2"
  ENat_Extensions
  Set_Extensions
begin

  lemma chain_split[dest]:
    assumes "Complete_Partial_Order.chain ord C" "x \<in> C"
    shows "C = {y \<in> C. ord x y} \<union> {y \<in> C. ord y x}"
  proof -
    have 1: "\<And> y. y \<in> C \<Longrightarrow> ord x y \<or> ord y x" using chainD assms by this
    show ?thesis using 1 by blast
  qed

  lemma infinite_chain_below[dest]:
    assumes "Complete_Partial_Order.chain ord C" "infinite C" "x \<in> C"
    assumes "finite {y \<in> C. ord x y}"
    shows "infinite {y \<in> C. ord y x}"
  proof -
    have 1: "C = {y \<in> C. ord x y} \<union> {y \<in> C. ord y x}" using assms(1, 3) by rule
    show ?thesis using finite_Un assms(2, 4) 1 by (metis (poly_guards_query))
  qed
  lemma infinite_chain_above[dest]:
    assumes "Complete_Partial_Order.chain ord C" "infinite C" "x \<in> C"
    assumes "finite {y \<in> C. ord y x}"
    shows "infinite {y \<in> C. ord x y}"
  proof -
    have 1: "C = {y \<in> C. ord x y} \<union> {y \<in> C. ord y x}" using assms(1, 3) by rule
    show ?thesis using finite_Un assms(2, 4) 1 by (metis (poly_guards_query))
  qed

  lemma (in ccpo) ccpo_Sup_upper_inv:
    assumes "Complete_Partial_Order.chain less_eq C" "x > \<Squnion> C"
    shows "x \<notin> C"
    using assms ccpo_Sup_upper by fastforce
  lemma (in ccpo) ccpo_Sup_least_inv:
    assumes "Complete_Partial_Order.chain less_eq C" "\<Squnion> C > x"
    obtains y
    where "y \<in> C" "\<not> y \<le> x"
    using assms ccpo_Sup_least that by fastforce

  lemma ccpo_Sup_least_inv':
    fixes C :: "'a :: {ccpo, linorder} set"
    assumes "Complete_Partial_Order.chain less_eq C" "\<Squnion> C > x"
    obtains y
    where "y \<in> C" "y > x"
  proof -
    obtain y where 1: "y \<in> C" "\<not> y \<le> x" using ccpo_Sup_least_inv assms by this
    show ?thesis using that 1 by simp
  qed

  lemma mcont2mcont_lessThan[THEN lfp.mcont2mcont, simp, cont_intro]:
    shows mcont_lessThan: "mcont Sup less_eq Sup less_eq
      (lessThan :: 'a :: {ccpo, linorder} \<Rightarrow> 'a set)"
  proof
    show "monotone less_eq less_eq (lessThan :: 'a \<Rightarrow> 'a set)" by (rule, auto)
    show "cont Sup less_eq Sup less_eq (lessThan :: 'a \<Rightarrow> 'a set)"
    proof
      fix C :: "'a set"
      assume 1: "Complete_Partial_Order.chain less_eq C"
      show "{..< \<Squnion> C} = \<Union> (lessThan ` C)"
      proof (intro equalityI subsetI)
        fix A
        assume 2: "A \<in> {..< \<Squnion> C}"
        obtain B where 3: "B \<in> C" "B > A" using ccpo_Sup_least_inv' 1 2 by blast
        show "A \<in> \<Union> (lessThan ` C)" using 3 by auto
      next
        fix A
        assume 2: "A \<in> \<Union> (lessThan ` C)"
        show "A \<in> {..< \<Squnion> C}" using ccpo_Sup_upper 2 by force
      qed
    qed
  qed

  class esize =
    fixes esize :: "'a \<Rightarrow> enat"

  class esize_order = esize + order +
    assumes esize_finite[dest]: "esize x \<noteq> \<infinity> \<Longrightarrow> finite {y. y \<le> x}"
    assumes esize_mono[intro]: "x \<le> y \<Longrightarrow> esize x \<le> esize y"
    assumes esize_strict_mono[intro]: "esize x \<noteq> \<infinity> \<Longrightarrow> x < y \<Longrightarrow> esize x < esize y"
  begin

    lemma infinite_chain_eSuc_esize[dest]:
      assumes "Complete_Partial_Order.chain less_eq C" "infinite C" "x \<in> C"
      obtains y
      where "y \<in> C" "esize y \<ge> eSuc (esize x)"
    proof (cases "esize x")
      case (enat k)
      have 1: "finite {y \<in> C. y \<le> x}" using esize_finite enat by simp
      have 2: "infinite {y \<in> C. y \<ge> x}" using assms 1 by rule
      have 3: "{y \<in> C. y > x} = {y \<in> C. y \<ge> x} - {x}" by auto
      have 4: "infinite {y \<in> C. y > x}" using 2 unfolding 3 by simp
      obtain y where 5: "y \<in> C" "y > x" using 4 by auto
      have 6: "esize y > esize x" using esize_strict_mono enat 5(2) by blast
      show ?thesis using that 5(1) 6 ileI1 by simp
    next
      case (infinity)
      show ?thesis using that infinity assms(3) by simp
    qed

    lemma infinite_chain_arbitrary_esize[dest]:
      assumes "Complete_Partial_Order.chain less_eq C" "infinite C"
      obtains x
      where "x \<in> C" "esize x \<ge> enat n"
    proof (induct n arbitrary: thesis)
      case 0
      show ?case using assms(2) 0 by force
    next
      case (Suc n)
      obtain x where 1: "x \<in> C" "esize x \<ge> enat n" using Suc(1) by blast
      obtain y where 2: "y \<in> C" "esize y \<ge> eSuc (esize x)" using assms 1(1) by rule
      show ?case using gfp.leq_trans Suc(2) 1(2) 2 by fastforce
    qed

  end

  class esize_ccpo = esize_order + ccpo
  begin

    lemma esize_cont[dest]:
      assumes "Complete_Partial_Order.chain less_eq C" "C \<noteq> {}"
      shows "esize (\<Squnion> C) = \<Squnion> (esize ` C)"
    proof (cases "finite C")
      case False
      have 1: "esize (\<Squnion> C) = \<infinity>"
      proof
        fix n
        obtain A where 1: "A \<in> C" "esize A \<ge> enat n" using assms(1) False by rule
        have 2: "A \<le> \<Squnion> C" using ccpo_Sup_upper assms(1) 1(1) by this
        have "enat n \<le> esize A" using 1(2) by this
        also have "\<dots> \<le> esize (\<Squnion> C)" using 2 by rule
        finally show "enat n \<le> esize (\<Squnion> C)" by this
      qed
      have 2: "(\<Squnion> A \<in> C. esize A) = \<infinity>"
      proof
        fix n
        obtain A where 1: "A \<in> C" "esize A \<ge> enat n" using assms(1) False by rule
        show "enat n \<le> (\<Squnion> A \<in> C. esize A)" using SUP_upper2 1 by this
      qed
      show ?thesis using 1 2 by simp
    next
      case True
      have 1: "esize (\<Squnion> C) = (\<Squnion> x \<in> C. esize x)"
      proof (intro order_class.antisym SUP_upper SUP_least esize_mono)
        show "\<Squnion> C \<in> C" using in_chain_finite assms(1) True assms(2) by this
        show "\<And> x. x \<in> C \<Longrightarrow> x \<le> \<Squnion> C" using ccpo_Sup_upper assms(1) by this
      qed
      show ?thesis using 1 by simp
    qed

    lemma esize_mcont: "mcont Sup less_eq Sup less_eq esize"
      by (blast intro: mcontI monotoneI contI)
  
    lemmas mcont2mcont_esize = esize_mcont[THEN lfp.mcont2mcont, simp, cont_intro]

  end

end
