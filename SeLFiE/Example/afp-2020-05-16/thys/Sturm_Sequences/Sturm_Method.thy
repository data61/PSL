section \<open>The ``sturm'' proof method\<close>

(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Sturm_Method
imports Sturm_Theorem
begin

subsection \<open>Preliminary lemmas\<close>

text \<open>
  In this subsection, we prove lemmas that reduce root counting and
  related statements to simple, computable expressions using the 
  @{term "count_roots"} function family.
\<close>

lemma poly_card_roots_less_leq:
  "card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = count_roots_between p a b"
  by (simp add: count_roots_between_correct)

lemma poly_card_roots_leq_leq:
  "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
       ( count_roots_between p a b + 
      (if (a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0) then 1 else 0))"
proof (cases "(a \<le> b \<and> poly p a = 0 \<and> p \<noteq> 0) \<or> (a = b \<and> p = 0)")
  case False
    note False' = this
    thus ?thesis
    proof (cases "p = 0")
      case False
        with False' have "poly p a \<noteq> 0 \<or> a > b" by auto
        hence "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = 
               {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
        by (auto simp: less_eq_real_def)
        thus ?thesis using poly_card_roots_less_leq False' 
            by (auto split: if_split_asm)
    next
      case True
        have "{x. a \<le> x \<and> x \<le> b} = {a..b}"
             "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a \<le> x \<and> x \<le> b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ioc infinite_Icc)
        with True False show ?thesis
            using count_roots_between_correct by (simp add: )
    qed
next
  case True
    note True' = this
    have fin: "finite {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0}" 
    proof (cases "p = 0")
      case True
        with True' have "a = b" by simp
        hence "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} = {b}" using True by auto
        thus ?thesis by simp
    next
      case False
        from poly_roots_finite[OF this] show ?thesis by fast
    qed
    with True have "{x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} =
        insert a {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by auto
    hence "card {x. a \<le> x \<and> x \<le> b \<and> poly p x = 0} =
           Suc (card {x. a < x \<and> x \<le> b \<and> poly p x = 0})" using fin by force
    thus ?thesis using True count_roots_between_correct by simp
qed

lemma poly_card_roots_less_less:
  "card {x. a < x \<and> x < b \<and> poly p x = 0} = 
      ( count_roots_between p a b -
              (if poly p b = 0 \<and> a < b \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p b = 0 \<and> a < b \<and> p \<noteq> 0")
  case False
    note False' = this
    show ?thesis
    proof (cases "p = 0")
      case True
        have [simp]: "{x. a < x \<and> x < b} = {a<..<b}"
                     "{x. a < x \<and> x \<le> b} = {a<..b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a < x \<and> x < b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ioo infinite_Ioc)
        with True False' show ?thesis 
            by (auto simp: count_roots_between_correct)
    next
      case False
        with False' have "{x. a < x \<and> x < b \<and> poly p x = 0} = 
                          {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
          by (auto simp: less_eq_real_def)
      thus ?thesis using poly_card_roots_less_leq False by auto
  qed
next
  case True
    with poly_roots_finite
        have fin: "finite {x. a < x \<and> x < b \<and> poly p x = 0}" by fast
    from True have "{x. a < x \<and> x \<le> b \<and> poly p x = 0} =
        insert b {x. a < x \<and> x < b \<and> poly p x = 0}" by auto
    hence "Suc (card {x. a < x \<and> x < b \<and> poly p x = 0}) =
           card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" using fin by force
    also note count_roots_between_correct[symmetric]
    finally show ?thesis using True by simp
qed

lemma poly_card_roots_leq_less:
  "card {x::real. a \<le> x \<and> x < b \<and> poly p x = 0} =
      ( count_roots_between p a b +
      (if p \<noteq> 0 \<and> a < b \<and> poly p a = 0 then 1 else 0) -
      (if p \<noteq> 0 \<and> a < b \<and> poly p b = 0 then 1 else 0))"
proof (cases "p = 0 \<or> a \<ge> b")
  case True
    note True' = this
    show ?thesis
    proof (cases "a \<ge> b")
      case False
        hence "{x. a < x \<and> x \<le> b} = {a<..b}"
              "{x. a \<le> x \<and> x < b} = {a..<b}" by auto
        with True False have "card {x. a < x \<and> x \<le> b} = 0" "card {x. a \<le> x \<and> x < b} = 0"
          by (auto simp add: card_eq_0_iff infinite_Ico infinite_Ioc)
        with False True' show ?thesis 
            by (simp add: count_roots_between_correct)
    next
      case True
        with True' have "{x. a \<le> x \<and> x < b \<and> poly p x = 0} = 
                          {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
          by (auto simp: less_eq_real_def)
      thus ?thesis using poly_card_roots_less_leq True by simp
  qed
next
  case False
    let ?A = "{x. a \<le> x \<and> x < b \<and> poly p x = 0}"
    let ?B = "{x. a < x \<and> x \<le> b \<and> poly p x = 0}"
    let ?C = "{x. x = b \<and> poly p x = 0}"
    let ?D = "{x. x = a \<and> poly p a = 0}"
    have CD_if: "?C = (if poly p b = 0 then {b} else {})"
                "?D = (if poly p a = 0 then {a} else {})" by auto
    from False poly_roots_finite 
        have [simp]: "finite ?A" "finite ?B" "finite ?C" "finite ?D"
            by (fast, fast, simp_all)
    
    from False have "?A = (?B \<union> ?D) - ?C" by (auto simp: less_eq_real_def)
    with False have "card ?A = card ?B + (if poly p a = 0 then 1 else 0) -
                       (if poly p b = 0 then 1 else 0)" by (auto simp: CD_if)
    also note count_roots_between_correct[symmetric]
    finally show ?thesis using False by simp
qed

lemma poly_card_roots:
  "card {x::real. poly p x = 0} = count_roots p"
  using count_roots_correct by simp

lemma poly_no_roots:
  "(\<forall>x. poly p x \<noteq> 0) \<longleftrightarrow> ( p \<noteq> 0 \<and> count_roots p = 0)"
    by (auto simp: count_roots_correct dest: poly_roots_finite)

lemma poly_pos:
  "(\<forall>x. poly p x > 0) \<longleftrightarrow> ( 
        p \<noteq> 0 \<and> poly_inf p = 1 \<and> count_roots p = 0)"
  by (simp only: Let_def poly_pos poly_no_roots, blast)


lemma poly_card_roots_greater:
  "card {x::real. x > a \<and> poly p x = 0} = count_roots_above p a"
  using count_roots_above_correct by simp

lemma poly_card_roots_leq:
  "card {x::real. x \<le> a \<and> poly p x = 0} = count_roots_below p a"
  using count_roots_below_correct by simp

lemma poly_card_roots_geq:
  "card {x::real. x \<ge> a \<and> poly p x = 0} = (
      count_roots_above p a + (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x \<ge> a \<and> poly p x = 0} = card {x. x > a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a<..<a+1}"
        by (metis infinite_Ioo less_add_one) 
      moreover have "{a<..<a+1} \<subseteq> {x. x \<ge> a \<and> poly p x = 0}"
                    "{a<..<a+1} \<subseteq> {x. x > a \<and> poly p x = 0}" 
          using \<open>p = 0\<close> by auto
      ultimately have "\<not>finite {x. x \<ge> a \<and> poly p x = 0}" 
                      "\<not>finite {x. x > a \<and> poly p x = 0}" 
        by (auto dest!: finite_subset[of "{a<..<a+1}"] simp: infinite_Ioo)
      thus ?thesis by simp
    next
      assume "poly p a \<noteq> 0"
      hence "{x. x \<ge> a \<and> poly p x = 0} = {x. x > a \<and> poly p x = 0}" 
          by (auto simp: less_eq_real_def)
      thus ?thesis by simp
    qed auto
    thus ?thesis using False 
        by (auto intro: poly_card_roots_greater)
next
  case True
    hence "finite {x. x > a \<and> poly p x = 0}" using poly_roots_finite by force
    moreover have "{x. x \<ge> a \<and> poly p x = 0} = 
                       insert a {x. x > a \<and> poly p x = 0}" using True by auto
    ultimately have "card {x. x \<ge> a \<and> poly p x = 0} = 
                         Suc (card {x. x > a \<and> poly p x = 0})"
        using card_insert_disjoint by auto
    thus ?thesis using True by (auto intro: poly_card_roots_greater)
qed

lemma poly_card_roots_less:
  "card {x::real. x < a \<and> poly p x = 0} =
       (count_roots_below p a - (if poly p a = 0 \<and> p \<noteq> 0 then 1 else 0))"
proof (cases "poly p a = 0 \<and> p \<noteq> 0")
  case False
    hence "card {x. x < a \<and> poly p x = 0} = card {x. x \<le> a \<and> poly p x = 0}"
    proof (cases rule: disjE)
      assume "p = 0"
      have "\<not>finite {a - 1<..<a}" 
        by (metis infinite_Ioo diff_add_cancel less_add_one) 
      moreover have "{a - 1<..<a} \<subseteq> {x. x \<le> a \<and> poly p x = 0}"
                    "{a - 1<..<a} \<subseteq> {x. x < a \<and> poly p x = 0}" 
          using \<open>p = 0\<close> by auto
      ultimately have "\<not>finite {x. x \<le> a \<and> poly p x = 0}" 
                     "\<not>finite {x. x < a \<and> poly p x = 0}" 
          by (auto dest: finite_subset[of "{a - 1<..<a}"] simp: infinite_Ioo)
      thus ?thesis by simp
    next
      assume "poly p a \<noteq> 0"
      hence "{x. x < a \<and> poly p x = 0} = {x. x \<le> a \<and> poly p x = 0}" 
          by (auto simp: less_eq_real_def)
      thus ?thesis by simp
    qed auto
    thus ?thesis using False 
        by (auto intro: poly_card_roots_leq)
next
  case True
    hence "finite {x. x < a \<and> poly p x = 0}" using poly_roots_finite by force
    moreover have "{x. x \<le> a \<and> poly p x = 0} = 
                       insert a {x. x < a \<and> poly p x = 0}" using True by auto
    ultimately have "Suc (card {x. x < a \<and> poly p x = 0}) =
                     (card {x. x \<le> a \<and> poly p x = 0})"
        using card_insert_disjoint by auto
    also note count_roots_below_correct[symmetric]
    finally show ?thesis using True by simp
qed


lemma poly_no_roots_less_leq:
  "(\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> count_roots_between p a b = 0)))"
  by (auto simp: count_roots_between_correct card_eq_0_iff not_le 
           dest: poly_roots_finite)

lemma poly_pos_between_less_leq:
  "(\<forall>x. a < x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p b > 0 \<and> count_roots_between p a b = 0)))"
  by (simp only: poly_pos_between_less_leq Let_def 
                 poly_no_roots_less_leq, blast)


lemma poly_no_roots_leq_leq:
  "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a > b \<or> (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 0)))"
apply (intro iffI)
apply (force simp add: count_roots_between_correct card_eq_0_iff)
apply (elim conjE disjE, simp, intro allI)
apply (rename_tac x, case_tac "x = a")
apply (auto simp add: count_roots_between_correct card_eq_0_iff
            dest: poly_roots_finite)
done

lemma poly_pos_between_leq_leq:
  "(\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ((a > b \<or> (p \<noteq> 0 \<and> poly p a > 0 \<and> 
                count_roots_between p a b = 0)))"
by (simp only: poly_pos_between_leq_leq Let_def poly_no_roots_leq_leq, force)



lemma poly_no_roots_less_less:
  "(\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> 
   ((a \<ge> b \<or> p \<noteq> 0 \<and> count_roots_between p a b = 
       (if poly p b = 0 then 1 else 0)))"
proof (standard, goal_cases)
  case A: 1
    show ?case
    proof (cases "a \<ge> b")
      case True
      with A show ?thesis by simp
    next
      case False
      with A have [simp]: "p \<noteq> 0" using dense[of a b] by auto
      have B: "{x. a < x \<and> x \<le> b \<and> poly p x = 0} =
                {x. a < x \<and> x < b \<and> poly p x = 0} \<union>
                (if poly p b = 0 then {b} else {})" using A False by auto
      have "count_roots_between p a b =
                 card {x. a < x \<and> x < b \<and> poly p x = 0} +
                (if poly p b = 0 then 1 else 0)"
         by (subst count_roots_between_correct, subst B, subst card_Un_disjoint, 
             rule finite_subset[OF _ poly_roots_finite], blast, simp_all)
      also from A have "{x. a < x \<and> x < b \<and> poly p x = 0} = {}" by simp
      finally show ?thesis by auto
    qed
next
  case prems: 2
    hence "card {x. a < x \<and> x < b \<and> poly p x = 0} = 0"
        by (subst poly_card_roots_less_less, auto simp: count_roots_between_def)
    thus ?case using prems
        by (cases "p = 0", simp, subst (asm) card_eq_0_iff, 
            auto dest: poly_roots_finite)
qed

lemma poly_pos_between_less_less:
  "(\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p ((a+b)/2) > 0 \<and> 
       count_roots_between p a b = (if poly p b = 0 then 1 else 0))))"
  by (simp only: poly_pos_between_less_less Let_def 
                 poly_no_roots_less_less, blast)

lemma poly_no_roots_leq_less:
  "(\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
   ((a \<ge> b \<or> p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_between p a b = 
       (if a < b \<and> poly p b = 0 then 1 else 0)))"
proof (standard, goal_cases)
  case prems: 1
    hence "\<forall>x. a < x \<and> x < b \<longrightarrow> poly p x \<noteq> 0" by simp
    thus ?case using prems by (subst (asm) poly_no_roots_less_less, auto)
next
  case prems: 2
    hence "(b \<le> a \<or> p \<noteq> 0 \<and> count_roots_between p a b = 
               (if poly p b = 0 then 1 else 0))" by auto
    thus ?case using prems unfolding Let_def
        by (subst (asm) poly_no_roots_less_less[symmetric, unfolded Let_def], 
        auto split: if_split_asm simp: less_eq_real_def) 
qed

lemma poly_pos_between_leq_less:
  "(\<forall>x. a \<le> x \<and> x < b \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ((a \<ge> b \<or> (p \<noteq> 0 \<and> poly p a > 0 \<and> count_roots_between p a b = 
        (if a < b \<and> poly p b = 0 then 1 else 0))))"
 by (simp only: poly_pos_between_leq_less Let_def 
                poly_no_roots_leq_less, force)


lemma poly_no_roots_greater:
  "(\<forall>x. x > a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ((p \<noteq> 0 \<and> count_roots_above p a = 0))"
proof-
  have "\<forall>x. \<not> a < x \<Longrightarrow> False" by (metis gt_ex)
  thus ?thesis by (auto simp: count_roots_above_correct card_eq_0_iff
                        intro: poly_roots_finite )
qed

lemma poly_pos_greater:
  "(\<forall>x. x > a \<longrightarrow> poly p x > 0) \<longleftrightarrow> (
       p \<noteq> 0 \<and> poly_inf p = 1 \<and> count_roots_above p a = 0)"
  unfolding Let_def
  by (subst poly_pos_greater, subst poly_no_roots_greater, force)

lemma poly_no_roots_leq:
  "(\<forall>x. x \<le> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow> 
       ( (p \<noteq> 0 \<and> count_roots_below p a = 0))"
    by (auto simp: Let_def count_roots_below_correct card_eq_0_iff
             intro: poly_roots_finite)

lemma poly_pos_leq:
  "(\<forall>x. x \<le> a \<longrightarrow> poly p x > 0) \<longleftrightarrow> 
   ( p \<noteq> 0 \<and> poly_neg_inf p = 1 \<and> count_roots_below p a = 0)"
  by (simp only: poly_pos_leq Let_def poly_no_roots_leq, blast)



lemma poly_no_roots_geq:
  "(\<forall>x. x \<ge> a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ( (p \<noteq> 0 \<and> poly p a \<noteq> 0 \<and> count_roots_above p a = 0))"
proof (standard, goal_cases)
  case prems: 1
  hence "\<forall>x>a. poly p x \<noteq> 0" by simp
  thus ?case using prems by (subst (asm) poly_no_roots_greater, auto)
next
  case prems: 2
  hence "(p \<noteq> 0 \<and> count_roots_above p a = 0)" by simp
  thus ?case using prems 
      by (subst (asm) poly_no_roots_greater[symmetric, unfolded Let_def], 
          auto simp: less_eq_real_def)
qed

lemma poly_pos_geq:
  "(\<forall>x. x \<ge> a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   (p \<noteq> 0 \<and> poly_inf p = 1 \<and> poly p a \<noteq> 0 \<and> count_roots_above p a = 0)"
  by (simp only: poly_pos_geq Let_def poly_no_roots_geq, blast)

lemma poly_no_roots_less:
  "(\<forall>x. x < a \<longrightarrow> poly p x \<noteq> 0) \<longleftrightarrow>
       ((p \<noteq> 0 \<and> count_roots_below p a = (if poly p a = 0 then 1 else 0)))"
proof (standard, goal_cases)
  case prems: 1
  hence "{x. x \<le> a \<and> poly p x = 0} = (if poly p a = 0 then {a} else {})"
      by (auto simp: less_eq_real_def)
  moreover have "\<forall>x. \<not> x < a \<Longrightarrow> False" by (metis lt_ex)
  ultimately show ?case using prems by (auto simp: count_roots_below_correct)
next
  case prems: 2
  have A: "{x. x \<le> a \<and> poly p x = 0} = {x. x < a \<and> poly p x = 0} \<union> 
            (if poly p a = 0 then {a} else {})" by (auto simp: less_eq_real_def)
  have "count_roots_below p a = card {x. x < a \<and> poly p x = 0} +
            (if poly p a = 0 then 1 else 0)" using prems
      by (subst count_roots_below_correct, subst A, subst card_Un_disjoint,
          auto intro: poly_roots_finite)
  with prems have "card {x. x < a \<and> poly p x = 0} = 0" by simp
  thus ?case using prems
      by (subst (asm) card_eq_0_iff, auto intro: poly_roots_finite)
qed

lemma poly_pos_less:
  "(\<forall>x. x < a \<longrightarrow> poly p x > 0) \<longleftrightarrow>
   (p \<noteq> 0 \<and> poly_neg_inf p = 1 \<and> count_roots_below p a = 
       (if poly p a = 0 then 1 else 0))"
  by (simp only: poly_pos_less Let_def poly_no_roots_less, blast)


lemmas sturm_card_substs = poly_card_roots poly_card_roots_less_leq 
    poly_card_roots_leq_less poly_card_roots_less_less poly_card_roots_leq_leq
    poly_card_roots_less poly_card_roots_leq poly_card_roots_greater
    poly_card_roots_geq 

lemmas sturm_prop_substs = poly_no_roots poly_no_roots_less_leq 
    poly_no_roots_leq_leq poly_no_roots_less_less poly_no_roots_leq_less
    poly_no_roots_leq poly_no_roots_less poly_no_roots_geq 
    poly_no_roots_greater
    poly_pos poly_pos_greater poly_pos_geq poly_pos_less poly_pos_leq
    poly_pos_between_leq_less poly_pos_between_less_leq
    poly_pos_between_leq_leq poly_pos_between_less_less


subsection \<open>Reification\<close>

text \<open>
  This subsection defines a number of equations to automatically convert 
  statements about roots of polynomials into a canonical form so that they 
  can be proven using the above substitutions.
\<close>

definition "PR_TAG x \<equiv> x"

lemma sturm_id_PR_prio0:
  "{x::real. P x} = {x::real. (PR_TAG P) x}"
  "(\<forall>x::real. f x < g x) = (\<forall>x::real. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. P x) = (\<forall>x::real. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  by (simp_all add: PR_TAG_def)

lemma sturm_id_PR_prio1:
  "{x::real. x < a \<and> P x} = {x::real. x < a \<and> (PR_TAG P) x}"
  "{x::real. x \<le> a \<and> P x} = {x::real. x \<le> a \<and> (PR_TAG P) x}"
  "{x::real. x \<ge> b \<and> P x} = {x::real. x \<ge> b \<and> (PR_TAG P) x}"
  "{x::real. x > b \<and> P x} = {x::real. x > b \<and> (PR_TAG P) x}"
  "(\<forall>x::real < a. f x < g x) = (\<forall>x::real < a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real \<le> a. f x < g x) = (\<forall>x::real \<le> a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real > a. f x < g x) = (\<forall>x::real > a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real \<ge> a. f x < g x) = (\<forall>x::real \<ge> a. PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real < a. P x) = (\<forall>x::real < a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real > a. P x) = (\<forall>x::real > a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real \<le> a. P x) = (\<forall>x::real \<le> a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real \<ge> a. P x) = (\<forall>x::real \<ge> a. \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  by (simp_all add: PR_TAG_def)

lemma sturm_id_PR_prio2:
  "{x::real. x > a \<and> x \<le> b \<and> P x} = 
       {x::real. x > a \<and> x \<le> b \<and> PR_TAG P x}"
  "{x::real. x \<ge> a \<and> x \<le> b \<and> P x} = 
       {x::real. x \<ge> a \<and> x \<le> b \<and> PR_TAG P x}"
  "{x::real. x \<ge> a \<and> x < b \<and> P x} = 
       {x::real. x \<ge> a \<and> x < b \<and> PR_TAG P x}"
  "{x::real. x > a \<and> x < b \<and> P x} = 
       {x::real. x > a \<and> x < b \<and> PR_TAG P x}"
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a < x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> f x < g x) = 
       (\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> PR_TAG (\<lambda>x. f x < g x) x)"
  "(\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> P x) = 
       (\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> P x) = 
       (\<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> P x) = 
       (\<forall>x::real. a \<le> x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  "(\<forall>x::real. a < x \<and> x < b \<longrightarrow> P x) = 
       (\<forall>x::real. a < x \<and> x < b \<longrightarrow> \<not>(PR_TAG (\<lambda>x. \<not>P x)) x)"
  by (simp_all add: PR_TAG_def)



lemma PR_TAG_intro_prio0:
  fixes P :: "real \<Rightarrow> bool" and f :: "real \<Rightarrow> real"
  shows
  "PR_TAG P = P' \<Longrightarrow> PR_TAG (\<lambda>x. \<not>(\<not>P x)) = P'"
  "\<lbrakk>PR_TAG P = (\<lambda>x. poly p x = 0); PR_TAG Q = (\<lambda>x. poly q x = 0)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. P x \<and> Q x) = (\<lambda>x. poly (gcd p q) x = 0)" and
 " \<lbrakk>PR_TAG P = (\<lambda>x. poly p x = 0); PR_TAG Q = (\<lambda>x. poly q x = 0)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. P x \<or> Q x) = (\<lambda>x. poly (p*q) x = 0)" and

  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x = g x) = (\<lambda>x. poly (p-q) x = 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x \<noteq> g x) = (\<lambda>x. poly (p-q) x \<noteq> 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x < g x) = (\<lambda>x. poly (q-p) x > 0)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x \<le> g x) = (\<lambda>x. poly (q-p) x \<ge> 0)"

  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. -f x) = (\<lambda>x. poly (-p) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x + g x) = (\<lambda>x. poly (p+q) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x - g x) = (\<lambda>x. poly (p-q) x)"
  "\<lbrakk>PR_TAG f = (\<lambda>x. poly p x); PR_TAG g = (\<lambda>x. poly q x)\<rbrakk>
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * g x) = (\<lambda>x. poly (p*q) x)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^n) = (\<lambda>x. poly (p^n) x)"
  "PR_TAG (\<lambda>x. poly p x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. x::real) = (\<lambda>x. poly [:0,1:] x)"
  "PR_TAG (\<lambda>x. a::real) = (\<lambda>x. poly [:a:] x)"
  by (simp_all add: PR_TAG_def poly_eq_0_iff_dvd field_simps)


lemma PR_TAG_intro_prio1:
  fixes f :: "real \<Rightarrow> real"
  shows
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x = 0) = (\<lambda>x. poly p x = 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<noteq> 0) = (\<lambda>x. poly p x \<noteq> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. 0 = f x) = (\<lambda>x. poly p x = 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. 0 \<noteq> f x) = (\<lambda>x. poly p x \<noteq> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<ge> 0) = (\<lambda>x. poly p x \<ge> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x > 0) = (\<lambda>x. poly p x > 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x \<le> 0) = (\<lambda>x. poly (-p) x \<ge> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> PR_TAG (\<lambda>x. f x < 0) = (\<lambda>x. poly (-p) x > 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> 
       PR_TAG (\<lambda>x. 0 \<le> f x) = (\<lambda>x. poly (-p) x \<le> 0)"
  "PR_TAG f = (\<lambda>x. poly p x) \<Longrightarrow> 
       PR_TAG (\<lambda>x. 0 < f x) = (\<lambda>x. poly (-p) x < 0)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. a * f x) = (\<lambda>x. poly (smult a p) x)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * a) = (\<lambda>x. poly (smult a p) x)"
  "PR_TAG f = (\<lambda>x. poly p x) 
       \<Longrightarrow> PR_TAG (\<lambda>x. f x / a) = (\<lambda>x. poly (smult (inverse a) p) x)"
  "PR_TAG (\<lambda>x. x^n :: real) = (\<lambda>x. poly (monom 1 n) x)"
by (simp_all add: PR_TAG_def field_simps poly_monom)

lemma PR_TAG_intro_prio2:
  "PR_TAG (\<lambda>x. 1 / b) = (\<lambda>x. inverse b)"
  "PR_TAG (\<lambda>x. a / b) = (\<lambda>x. a / b)"
  "PR_TAG (\<lambda>x. a / b * x^n :: real) = (\<lambda>x. poly (monom (a/b) n) x)"
  "PR_TAG (\<lambda>x. x^n * a / b :: real) = (\<lambda>x. poly (monom (a/b) n) x)"
  "PR_TAG (\<lambda>x. a * x^n :: real) = (\<lambda>x. poly (monom a n) x)"
  "PR_TAG (\<lambda>x. x^n * a :: real) = (\<lambda>x. poly (monom a n) x)"
  "PR_TAG (\<lambda>x. x^n / a :: real) = (\<lambda>x. poly (monom (inverse a) n) x)"
(* TODO: can this be done more efficiently? I should think so. *)
  "PR_TAG (\<lambda>x. f x^(Suc (Suc 0)) :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * f x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^Suc n :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^n * f x :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^Suc n :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. f x * (f x)^n :: real) = (\<lambda>x. poly p x)"
  "PR_TAG (\<lambda>x. (f x)^(m+n) :: real) = (\<lambda>x. poly p x)
       \<Longrightarrow> PR_TAG (\<lambda>x. (f x)^m * (f x)^n :: real) = (\<lambda>x. poly p x)"
by (simp_all add: PR_TAG_def field_simps poly_monom power_add)

lemma sturm_meta_spec: "(\<And>x::real. P x) \<Longrightarrow> P x" by simp
lemma sturm_imp_conv: 
  "(a < x \<longrightarrow> x < b \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x < b \<longrightarrow> c)"
  "(a \<le> x \<longrightarrow> x < b \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x < b \<longrightarrow> c)"
  "(a < x \<longrightarrow> x \<le> b \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x \<le> b \<longrightarrow> c)"
  "(a \<le> x \<longrightarrow> x \<le> b \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x \<le> b \<longrightarrow> c)"
  "(x < b \<longrightarrow> a < x \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x < b \<longrightarrow> c)"
  "(x < b \<longrightarrow> a \<le> x \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x < b \<longrightarrow> c)"
  "(x \<le> b \<longrightarrow> a < x \<longrightarrow> c) \<longleftrightarrow> (a < x \<and> x \<le> b \<longrightarrow> c)"
  "(x \<le> b \<longrightarrow> a \<le> x \<longrightarrow> c) \<longleftrightarrow> (a \<le> x \<and> x \<le> b \<longrightarrow> c)"
  by auto


subsection \<open>Setup for the ``sturm'' method\<close>

ML_file \<open>sturm.ML\<close>

method_setup sturm = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Sturm.sturm_tac ctxt true))
\<close>

end
