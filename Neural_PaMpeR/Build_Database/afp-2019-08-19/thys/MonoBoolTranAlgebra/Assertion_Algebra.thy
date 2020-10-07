section \<open>Boolean Algebra of Assertions\<close>

theory  Assertion_Algebra
imports Mono_Bool_Tran_Algebra
begin

text\<open>
This section introduces the boolean algebra of assertions. The 
type $\mathsf{Assertion}$ and the boolean operation are instroduced 
based on the set $\mathsf{assertion}$ and the operations on the monotonic 
boolean transformers algebra. The type $\mathsf{Assertion}$ over
a complete monotonic boolean transformers algebra is a complete boolean 
algebra.
\<close>

typedef (overloaded) ('a::mbt_algebra) Assertion = "assertion::'a set"
  apply (rule_tac x = "\<bottom>" in exI)
  by (unfold assertion_def, simp)

definition
  assert :: "'a::mbt_algebra Assertion \<Rightarrow> 'a"  ("{\<cdot> _ }" [0] 1000) where
  "{\<cdot>p} =  Rep_Assertion p"

definition 
  "abs_wpt x = Abs_Assertion (wpt x)"

lemma [simp]: "{\<cdot>p} \<in> assertion"
  by (unfold assert_def, cut_tac x = p in Rep_Assertion, simp)

lemma [simp]: "abs_wpt ({\<cdot>p}) = p"
  apply (simp add: abs_wpt_def)
  by (simp add: assert_def Rep_Assertion_inverse)


lemma [simp]: "x \<in> assertion \<Longrightarrow> {\<cdot>Abs_Assertion x} = x"
  apply (simp add: assert_def)
  by (rule Abs_Assertion_inverse, simp)

  
lemma [simp]: "x \<in> assertion \<Longrightarrow> {\<cdot>abs_wpt x} = x"
  apply (simp add: abs_wpt_def assert_def)
  by (rule Abs_Assertion_inverse, simp)

lemma assert_injective: "{\<cdot>p} = {\<cdot>q} \<Longrightarrow> p = q"
  proof -
    assume A: "{\<cdot> p } = {\<cdot> q } "
    have "p = abs_wpt ({\<cdot>p})" by simp
    also have "... = q" by (subst A, simp)
    finally show ?thesis .
  qed

instantiation Assertion :: (mbt_algebra) boolean_algebra
begin
  definition
    uminus_Assertion_def: "- p = abs_wpt(neg_assert {\<cdot>p})"

  definition
    bot_Assertion_def: "\<bottom> = abs_wpt \<bottom>"

  definition
    top_Assertion_def: "\<top> = abs_wpt 1"

  definition
    inf_Assertion_def: "p \<sqinter> q = abs_wpt ({\<cdot>p} \<sqinter> {\<cdot>q})"
  
  definition
    sup_Assertion_def: "p \<squnion> q = abs_wpt ({\<cdot>p} \<squnion> {\<cdot>q})"

  definition 
    less_eq_Assertion_def: "(p \<le> q) = ({\<cdot>p} \<le>  {\<cdot>q})"

  definition 
    less_Assertion_def: "(p < q) = ({\<cdot>p} < {\<cdot>q})"

  definition 
    minus_Assertion_def: "(p::'a Assertion) - q = p \<sqinter> - q"

instance
  proof
    fix x y :: "'a Assertion" show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (simp add: less_Assertion_def less_eq_Assertion_def less_le_not_le)
  next
    fix x ::"'a Assertion" show "x \<le> x" by (simp add: less_eq_Assertion_def)
  next
    fix x y z :: "'a Assertion" assume A: "x \<le> y" assume B: "y \<le> z" from A and B show "x \<le> z"
      by (simp add: less_eq_Assertion_def)
  next
    fix x y :: "'a Assertion" assume A: "x \<le> y" assume B: "y \<le> x" from A and B show "x = y"
      apply (cut_tac p = x and q = y in assert_injective)
      by (rule antisym, simp_all add: less_eq_Assertion_def)
  next
    fix x y :: "'a Assertion" show "x \<sqinter> y \<le> x"
      by (simp add: less_eq_Assertion_def inf_Assertion_def)
    fix x y :: "'a Assertion" show "x \<sqinter> y \<le> y"
      by (simp add: less_eq_Assertion_def inf_Assertion_def)
  next
    fix x y z :: "'a Assertion" assume A: "x \<le> y" assume B: "x \<le> z" from A and B show "x \<le> y \<sqinter> z"
      by (simp add: less_eq_Assertion_def inf_Assertion_def)
  next
    fix x y :: "'a Assertion" show "x \<le> x \<squnion> y"
      by (simp add: less_eq_Assertion_def sup_Assertion_def)
    fix x y :: "'a Assertion" show "y \<le> x \<squnion> y"
      by (simp add: less_eq_Assertion_def sup_Assertion_def)
  next
    fix x y z :: "'a Assertion" assume A: "y \<le> x" assume B: "z \<le> x" from A and B show "y \<squnion> z \<le> x"
      by (simp add: less_eq_Assertion_def sup_Assertion_def)
  next
    fix x :: "'a Assertion" show "\<bottom> \<le> x"
      by (simp add: less_eq_Assertion_def bot_Assertion_def)
  next
    fix x :: "'a Assertion" show "x \<le> \<top>"
      by (simp add: less_eq_Assertion_def top_Assertion_def)
  next
    fix x y z :: "'a Assertion" show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
      by (simp add: less_eq_Assertion_def sup_Assertion_def inf_Assertion_def sup_inf_distrib)
  next
    fix x :: "'a Assertion" show "x \<sqinter> - x = \<bottom>"
      by (simp add: inf_Assertion_def uminus_Assertion_def bot_Assertion_def)
  next
    fix x :: "'a Assertion" show "x \<squnion> - x = \<top>"
      by (simp add: sup_Assertion_def uminus_Assertion_def top_Assertion_def)
  next
    fix x y :: "'a Assertion" show "x - y = x \<sqinter> - y"
      by (simp add: minus_Assertion_def)
  qed

end


lemma assert_image [simp]: "assert ` A \<subseteq> assertion"
  by auto

instantiation Assertion :: (complete_mbt_algebra) complete_lattice
begin
  definition
    Sup_Assertion_def: "Sup A = abs_wpt (Sup (assert ` A))"

  definition
    Inf_Assertion_def: "Inf (A::('a Assertion) set) = - (Sup (uminus ` A))"

lemma Sup1: "(x::'a Assertion) \<in> A \<Longrightarrow> x \<le> Sup A"
    apply (simp add: Sup_Assertion_def less_eq_Assertion_def Abs_Assertion_inverse)
    by (rule Sup_upper, simp)

lemma Sup2: "(\<And>x::'a Assertion . x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z"
    apply (simp add: Sup_Assertion_def less_eq_Assertion_def Abs_Assertion_inverse)
    apply (rule Sup_least)
    by blast

instance
proof
  fix x :: "'a Assertion" fix A assume A: "x \<in> A" from A show "Inf A \<le> x"
    apply (simp add: Inf_Assertion_def)
    apply (subst compl_le_compl_iff [THEN sym], simp)
    by (rule Sup1, simp)
next
  fix z :: "'a Assertion" fix A assume A: "\<And>x . x \<in> A \<Longrightarrow> z \<le> x" from A show "z \<le> Inf A"
    apply (simp add: Inf_Assertion_def)
    apply (subst compl_le_compl_iff [THEN sym], simp)
    apply (rule Sup2)
    apply safe
    by simp
next
  fix x :: "'a Assertion" fix A assume A: "x \<in> A" from A show "x \<le> Sup A"
    by (rule Sup1)
next
  fix z :: "'a Assertion" fix A assume A: "\<And>x . x \<in> A \<Longrightarrow> x \<le> z" from A show "Sup A \<le> z"
    by (rule Sup2)
next
  show "Inf {} = (\<top>::'a Assertion)"
    by (auto simp: Inf_Assertion_def Sup_Assertion_def compl_bot_eq [symmetric] bot_Assertion_def)
next
  show "Sup {} = (\<bottom>::'a Assertion)"
    by (auto simp: Sup_Assertion_def bot_Assertion_def)
qed
end

lemma assert_top [simp]: "{\<cdot>\<top>} = 1"
  by (simp add: top_Assertion_def)

lemma assert_Sup: "{\<cdot>Sup A} = Sup (assert ` A)"
  by (simp add: Sup_Assertion_def Abs_Assertion_inverse)

 
lemma assert_Inf: "{\<cdot>Inf A} = (Inf (assert ` A)) \<sqinter> 1"
proof (cases "A = {}")
  case True then show ?thesis by simp
next
  note image_cong_simp [cong del]
  case False then show ?thesis
  apply (simp add: Inf_Assertion_def uminus_Assertion_def)
  apply (simp add: neg_assert_def assert_Sup dual_Sup Inf_comp inf_commute inf_Inf comp_def)
  apply (rule_tac f = Inf in arg_cong)
  apply safe
  apply simp
  apply (subst inf_commute)
  apply (simp add: image_def uminus_Assertion_def)
  apply (simp add: neg_assert_def dual_comp dual_inf sup_comp assertion_prop)
  apply auto [1]
  apply (simp)
  apply (subst image_def, simp)
  apply (simp add: uminus_Assertion_def)
  apply (subst inf_commute)
  apply (simp add: neg_assert_def dual_comp dual_inf sup_comp assertion_prop)
  apply auto
  done
qed

lemma assert_Inf_ne: "A \<noteq> {} \<Longrightarrow> {\<cdot>Inf A} = Inf (assert ` A)"
  apply (unfold assert_Inf)
  apply (rule antisym)
  apply simp_all
  apply safe
  apply (erule notE)
  apply (rule_tac y = "{\<cdot>x}" in order_trans)
  by (simp_all add: INF_lower)
 
  
lemma assert_Sup_range: "{\<cdot>Sup (range p)} = Sup (range (assert o p))"
  apply (subst assert_Sup)
  by (rule_tac f = "Sup" in arg_cong, auto)

lemma assert_Sup_less: "{\<cdot> Sup_less p w } = Sup_less (assert o p) w"
  apply (simp add: Sup_less_def)
  apply (subst assert_Sup)
  by (rule_tac f = "Sup" in arg_cong, auto)

end
