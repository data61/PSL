section \<open>Algebra of Monotonic Boolean Transformers\<close>

theory  Mono_Bool_Tran_Algebra
imports Mono_Bool_Tran
begin

text\<open>
In this section we introduce the {\em algebra of monotonic boolean transformers}.
This is a bounded distributive lattice with a monoid operation, a
dual operator and an iteration operator. The standard model for this
algebra is the set of monotonic boolean transformers introduced
in the previous section. 
\<close>

class dual = 
  fixes dual::"'a \<Rightarrow> 'a" ("_ ^ o" [81] 80)

class omega = 
  fixes omega::"'a \<Rightarrow> 'a" ("_ ^ \<omega>" [81] 80)

class star = 
  fixes star::"'a \<Rightarrow> 'a" ("(_ ^ *)" [81] 80)

class dual_star = 
  fixes dual_star::"'a \<Rightarrow> 'a" ("(_ ^ \<otimes>)" [81] 80)

class mbt_algebra = monoid_mult + dual + omega + distrib_lattice + order_top + order_bot + star + dual_star +
  assumes
      dual_le: "(x \<le> y) = (y ^ o \<le> x ^ o)"
  and dual_dual [simp]: "(x ^ o) ^ o = x"
  and dual_comp: "(x * y) ^ o = x ^ o * y ^ o"
  and dual_one [simp]: "1 ^ o = 1"
  and top_comp [simp]: "\<top> * x = \<top>"
  and inf_comp: "(x \<sqinter> y) * z = (x * z) \<sqinter> (y * z)"
  and le_comp: "x \<le> y \<Longrightarrow> z * x \<le> z * y"
  and dual_neg: "(x * \<top>) \<sqinter> (x ^ o * \<bottom>) = \<bottom>"
  and omega_fix: "x ^ \<omega> = (x * (x ^ \<omega>)) \<sqinter> 1"
  and omega_least: "(x * z) \<sqinter> y \<le> z \<Longrightarrow> (x ^ \<omega>) * y \<le> z"
  and star_fix: "x ^ * = (x * (x ^ *)) \<sqinter> 1"
  and star_greatest: "z \<le> (x * z) \<sqinter> y \<Longrightarrow> z \<le> (x ^ *) * y"
  and dual_star_def: "(x ^ \<otimes>) = (((x ^ o) ^ *) ^ o)"
begin

lemma le_comp_right: "x \<le> y \<Longrightarrow> x * z \<le> y * z"
  apply (cut_tac x = x and y = y and z = z in inf_comp)
  apply (simp add: inf_absorb1)
  apply (subgoal_tac "x * z \<sqinter> (y * z) \<le> y * z")
  apply simp
  by (rule inf_le2)

subclass bounded_lattice
  proof qed

end

instantiation MonoTran :: (complete_boolean_algebra) mbt_algebra
begin

lift_definition dual_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran"
  is dual_fun
  by (fact mono_dual_fun)

lift_definition omega_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran"
  is omega_fun
  by (fact mono_omega_fun)

lift_definition star_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran"
  is star_fun
  by (fact mono_star_fun)

definition dual_star_MonoTran :: "'a MonoTran \<Rightarrow> 'a MonoTran"
where
  "(x::('a MonoTran)) ^ \<otimes> = ((x ^ o) ^ *) ^ o"
  
instance proof
  fix x y :: "'a MonoTran" show "(x \<le> y) = (y ^ o \<le> x ^ o)"
    apply transfer
    apply (auto simp add: fun_eq_iff le_fun_def)
    apply (drule_tac x = "-xa" in spec)
    apply simp
    done
next
  fix x :: "'a MonoTran" show "(x ^ o) ^ o = x"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  fix x y :: "'a MonoTran" show "(x * y) ^ o = x ^ o * y ^ o"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  show "(1::'a MonoTran) ^ o = 1"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  fix x :: "'a MonoTran" show "\<top> * x = \<top>"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  fix x y z :: "'a MonoTran" show "(x \<sqinter> y) * z = (x * z) \<sqinter> (y * z)"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  fix x y z :: "'a MonoTran" assume A: "x \<le> y" from A show " z * x \<le> z * y"
    apply transfer
    apply (auto simp add: le_fun_def elim: monoE)
    done
next
  fix x :: "'a MonoTran" show "x * \<top> \<sqinter> (x ^ o * \<bottom>) = \<bottom>"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
next
  fix x :: "'a MonoTran" show "x ^ \<omega> = x * x ^ \<omega> \<sqinter> 1"
    apply transfer
    apply (simp add: fun_eq_iff)
    apply (simp add: omega_fun_def Omega_fun_def)
    apply (subst lfp_unfold, simp_all add: ac_simps)
    apply (auto intro!: mono_comp mono_comp_fun)
    done
next
  fix x y z :: "'a MonoTran" assume A: "x * z \<sqinter> y \<le> z" from A show "x ^ \<omega> * y \<le> z"
    apply transfer
    apply (auto simp add: lfp_omega lfp_def)
    apply (rule Inf_lower)
    apply (auto simp add: Omega_fun_def ac_simps)
    done
next
  fix x :: "'a MonoTran" show "x ^ * = x * x ^ * \<sqinter> 1"
    apply transfer
    apply (auto simp add: star_fun_def Omega_fun_def)
    apply (subst gfp_unfold, simp_all add: ac_simps)
    apply (auto intro!: mono_comp mono_comp_fun)
    done
next
  fix x y z :: "'a MonoTran" assume A: "z \<le> x * z \<sqinter> y" from A show "z \<le> x ^ * * y"
    apply transfer
    apply (auto simp add: gfp_star gfp_def)
    apply (rule Sup_upper)
    apply (auto simp add: Omega_fun_def)
    done
next
  fix x :: "'a MonoTran" show "x ^ \<otimes> = ((x ^ o) ^ *) ^ o"
    by (simp add: dual_star_MonoTran_def) 
qed

end

context mbt_algebra begin

lemma dual_top [simp]: "\<top> ^ o = \<bottom>"
  apply (rule antisym, simp_all)
  by (subst dual_le, simp)

lemma dual_bot [simp]: "\<bottom> ^ o = \<top>"
  apply (rule antisym, simp_all)
  by (subst dual_le, simp)

lemma dual_inf: "(x \<sqinter> y) ^ o = (x ^ o) \<squnion> (y ^ o)"
  apply (rule antisym, simp_all, safe)
  apply (subst dual_le, simp, safe)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  by (subst dual_le, simp)

lemma dual_sup: "(x \<squnion> y) ^ o = (x ^ o) \<sqinter> (y ^ o)"
  apply (rule antisym, simp_all, safe)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp)
  apply (subst dual_le, simp, safe)
  apply (subst dual_le, simp)
  by (subst dual_le, simp)

lemma sup_comp: "(x \<squnion> y) * z = (x * z) \<squnion> (y * z)"
  apply (subgoal_tac "((x ^ o \<sqinter> y ^ o) * z ^ o) ^ o = ((x ^ o * z ^ o) \<sqinter> (y ^ o * z ^ o)) ^ o")
  apply (simp add: dual_inf dual_comp)
  by (simp add: inf_comp)


lemma dual_eq: "x ^ o = y ^ o \<Longrightarrow> x = y"
  apply (subgoal_tac "(x ^ o) ^ o = (y ^ o) ^ o")
  apply (subst (asm) dual_dual)
  apply (subst (asm) dual_dual)
  by simp_all

lemma dual_neg_top [simp]: "(x ^ o * \<bottom>) \<squnion> (x * \<top>) = \<top>"
  apply (rule dual_eq)
  by(simp add: dual_sup dual_comp dual_neg)

 lemma bot_comp [simp]: "\<bottom> * x = \<bottom>"
   by (rule dual_eq, simp add: dual_comp)

lemma [simp]: "(x * \<top>) * y = x * \<top>" 
  by (simp add: mult.assoc)

lemma [simp]: "(x * \<bottom>) * y = x * \<bottom>" 
  by (simp add: mult.assoc)


lemma gt_one_comp: "1 \<le> x \<Longrightarrow> y \<le> x * y"
  by (cut_tac x = 1 and y = x and z = y in le_comp_right, simp_all)


  theorem omega_comp_fix: "x ^ \<omega> * y = (x * (x ^ \<omega>) * y) \<sqinter> y"
  apply (subst omega_fix)
  by (simp add: inf_comp)

  theorem dual_star_fix: "x^\<otimes> = (x * (x^\<otimes>)) \<squnion> 1"
    by (metis dual_comp dual_dual dual_inf dual_one dual_star_def star_fix)

  theorem star_comp_fix: "x ^ * * y = (x * (x ^ *) * y) \<sqinter> y"
  apply (subst star_fix)
  by (simp add: inf_comp)

  theorem dual_star_comp_fix: "x^\<otimes> * y = (x * (x^\<otimes>) * y) \<squnion> y"
  apply (subst dual_star_fix)
  by (simp add: sup_comp)

  theorem dual_star_least: "(x * z) \<squnion> y \<le> z \<Longrightarrow> (x^\<otimes>) * y \<le> z"
    apply (subst dual_le)
    apply (simp add: dual_star_def dual_comp)
    apply (rule star_greatest)
    apply (subst dual_le)
    by (simp add: dual_inf dual_comp)

  lemma omega_one [simp]: "1 ^ \<omega> = \<bottom>"
    apply (rule antisym, simp_all)
    by (cut_tac x = "1::'a" and y = 1 and z = \<bottom> in omega_least, simp_all)

  lemma omega_mono: "x \<le> y \<Longrightarrow> x ^ \<omega> \<le> y ^ \<omega>"
    apply (cut_tac x = x and y = 1 and z = "y ^ \<omega>" in omega_least, simp_all)
    apply (subst (2) omega_fix, simp_all)
    apply (rule_tac y = "x * y ^ \<omega>" in order_trans, simp)
    by (rule le_comp_right, simp)
end

sublocale mbt_algebra < conjunctive "inf" "inf" "times"
done
sublocale mbt_algebra < disjunctive "sup" "sup" "times"
done

context mbt_algebra begin
lemma dual_conjunctive: "x \<in> conjunctive \<Longrightarrow> x ^ o \<in> disjunctive"
  apply (simp add: conjunctive_def disjunctive_def)
  apply safe
  apply (rule dual_eq)
  by (simp add: dual_comp dual_sup)

lemma dual_disjunctive: "x \<in> disjunctive \<Longrightarrow> x ^ o \<in> conjunctive"
  apply (simp add: conjunctive_def disjunctive_def)
  apply safe
  apply (rule dual_eq)
  by (simp add: dual_comp dual_inf)

lemma comp_pres_conj: "x \<in> conjunctive \<Longrightarrow> y \<in> conjunctive \<Longrightarrow> x * y \<in> conjunctive"
  apply (subst conjunctive_def, safe)
  by (simp add: mult.assoc conjunctiveD)

lemma comp_pres_disj: "x \<in> disjunctive \<Longrightarrow> y \<in> disjunctive \<Longrightarrow> x * y \<in> disjunctive"
  apply (subst disjunctive_def, safe)
  by (simp add: mult.assoc disjunctiveD)

lemma start_pres_conj: "x \<in> conjunctive \<Longrightarrow> (x ^ *) \<in> conjunctive"
  apply (subst conjunctive_def, safe)
  apply (rule antisym, simp_all)
  apply (metis inf_le1 inf_le2 le_comp)
  apply (rule star_greatest)
  apply (subst conjunctiveD, simp)
  apply (subst star_comp_fix)
  apply (subst star_comp_fix)
  by (metis inf.assoc inf_left_commute mult.assoc order_refl)

lemma dual_star_pres_disj: "x \<in> disjunctive \<Longrightarrow> x^\<otimes> \<in> disjunctive"
  apply (simp add: dual_star_def)
  apply (rule dual_conjunctive)
  apply (rule start_pres_conj)
  by (rule dual_disjunctive, simp)

subsection\<open>Assertions\<close>

text\<open>
Usually, in Kleene algebra with tests or in other progrm algebras, tests or assertions
or assumptions are defined using an existential quantifier. An element of the algebra
is a test if it has a complement with respect to $\bot$ and $1$. In this formalization
assertions can be defined much simpler using the dual operator.
\<close>

definition
   "assertion = {x . x \<le> 1 \<and> (x * \<top>) \<sqinter> (x ^ o) = x}"

lemma assertion_prop: "x \<in> assertion \<Longrightarrow> (x * \<top>) \<sqinter> 1 = x"
  apply (simp add: assertion_def)
  apply safe
  apply (rule antisym)
  apply simp_all
  proof -
    assume [simp]: "x \<le> 1"
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    have "x * \<top> \<sqinter> 1 \<le> x * \<top> \<sqinter> x ^ o"
      apply simp
      apply (rule_tac y = 1 in order_trans)
      apply simp
      apply (subst dual_le)
      by simp
    also have "\<dots> = x" by (cut_tac A, simp)
    finally show "x * \<top> \<sqinter> 1 \<le> x" .
  next
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    have "x = x * \<top> \<sqinter> x ^ o" by (simp add: A)
    also have "\<dots> \<le> x * \<top>" by simp
    finally show "x \<le> x * \<top>" .
  qed

lemma dual_assertion_prop: "x \<in> assertion \<Longrightarrow> ((x ^ o) * \<bottom>) \<squnion> 1 = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_sup dual_comp assertion_prop)

lemma assertion_disjunctive: "x \<in> assertion \<Longrightarrow> x \<in> disjunctive"
  apply (simp add: disjunctive_def, safe)
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    fix y z::"'a"
    have "x * (y \<squnion> z) = (x * \<top> \<sqinter> 1) * (y \<squnion> z)" by (cut_tac  A, simp)
    also have "\<dots> = (x * \<top>) \<sqinter> (y \<squnion> z)" by (simp add: inf_comp)
    also have "\<dots> = ((x * \<top>) \<sqinter> y) \<squnion> ((x * \<top>) \<sqinter> z)" by (simp add: inf_sup_distrib)
    also have "\<dots> = (((x * \<top>) \<sqinter> 1) * y) \<squnion> (((x * \<top>) \<sqinter> 1) * z)" by (simp add: inf_comp)
    also have "\<dots> = x * y \<squnion> x * z" by (cut_tac  A, simp)
    finally show "x * (y \<squnion> z) = x * y \<squnion> x * z" .
  qed

lemma Abs_MonoTran_injective: "mono x \<Longrightarrow> mono y \<Longrightarrow> Abs_MonoTran x = Abs_MonoTran y \<Longrightarrow> x = y"
  apply (subgoal_tac "Rep_MonoTran (Abs_MonoTran x) = Rep_MonoTran (Abs_MonoTran y)")
  apply (subst (asm) Abs_MonoTran_inverse, simp)
  by (subst (asm) Abs_MonoTran_inverse, simp_all)
end

lemma mbta_MonoTran_disjunctive: "Rep_MonoTran ` disjunctive = Apply.disjunctive"
  apply (simp add: disjunctive_def Apply.disjunctive_def)
  apply transfer
  apply auto
  proof -
    fix f :: "'a \<Rightarrow> 'a" and a b
    assume prem: "\<forall>y. mono y \<longrightarrow> (\<forall>z. mono z \<longrightarrow> f \<circ> y \<squnion> z = (f \<circ> y) \<squnion> (f \<circ> z))"
    { fix g h :: "'b \<Rightarrow> 'a"
      assume "mono g" and "mono h"
      then have "f \<circ> g \<squnion> h = (f \<circ> g) \<squnion> (f \<circ> h)"
        using prem by blast
    } note * = this
    assume "mono f"
    show "f (a \<squnion> b) = f a \<squnion> f b" (is "?P = ?Q")
    proof (rule order_antisym)
      show "?P \<le> ?Q"
        using * [of "\<lambda>_. a" "\<lambda>_. b"] by (simp add: comp_def fun_eq_iff)
    next
      from \<open>mono f\<close> show "?Q \<le> ?P" by (rule Lattices.semilattice_sup_class.mono_sup)
    qed
  next
    fix f :: "'a \<Rightarrow> 'a"
    assume "\<forall>y z. f (y \<squnion> z) = f y \<squnion> f z"
    then have *: "\<And>y z. f (y \<squnion> z) = f y \<squnion> f z" by blast
    show "mono f"
    proof
      fix a b :: 'a
      assume "a \<le> b"
      then show "f a \<le> f b"
        unfolding sup.order_iff * [symmetric] by simp
    qed
  qed

lemma assertion_MonoTran: "assertion = Abs_MonoTran ` assertion_fun"
    apply (safe)
    apply (subst assertion_fun_disj_less_one)
    apply (simp add: image_def)
    apply (rule_tac x = "Rep_MonoTran x" in bexI)
    apply (simp add: Rep_MonoTran_inverse)
    apply safe
    apply (drule assertion_disjunctive)
    apply (unfold mbta_MonoTran_disjunctive [THEN sym], simp)
    apply (simp add: assertion_def less_eq_MonoTran_def one_MonoTran_def Abs_MonoTran_inverse)
    apply (simp add: assertion_def)
    by (simp_all add: inf_MonoTran_def less_eq_MonoTran_def 
      times_MonoTran_def dual_MonoTran_def top_MonoTran_def Abs_MonoTran_inverse one_MonoTran_def assertion_fun_dual)

context mbt_algebra begin
lemma assertion_conjunctive: "x \<in> assertion \<Longrightarrow> x \<in> conjunctive"
  apply (simp add: conjunctive_def, safe)
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    fix y z::"'a"
    have "x * (y \<sqinter> z) = (x * \<top> \<sqinter> 1) * (y \<sqinter> z)" by (cut_tac  A, simp)
    also have "\<dots> = (x * \<top>) \<sqinter> (y \<sqinter> z)" by (simp add: inf_comp)
    also have "\<dots> = ((x * \<top>) \<sqinter> y) \<sqinter> ((x * \<top>) \<sqinter> z)"
      apply (rule antisym, simp_all, safe)
      apply (rule_tac y = "y \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule_tac y = "y \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      apply simp_all
      apply (simp add: inf_assoc)
      apply (rule_tac y = " x * \<top> \<sqinter> y" in order_trans)
      apply (rule inf_le1)
      apply simp
      apply (rule_tac y = " x * \<top> \<sqinter> z" in order_trans)
      apply (rule inf_le2)
      by simp
    also have "\<dots> = (((x * \<top>) \<sqinter> 1) * y) \<sqinter> (((x * \<top>) \<sqinter> 1) * z)" by (simp add: inf_comp)
    also have "\<dots> = (x * y) \<sqinter> (x * z)" by (cut_tac  A, simp)
    finally show "x * (y \<sqinter> z) = (x * y) \<sqinter> (x * z)" .
  qed

lemma dual_assertion_conjunctive: "x \<in> assertion \<Longrightarrow> x ^ o \<in> conjunctive"
  apply (drule assertion_disjunctive)
  by (rule dual_disjunctive, simp)

lemma dual_assertion_disjunct: "x \<in> assertion \<Longrightarrow> x ^ o \<in> disjunctive"
  apply (drule assertion_conjunctive)
  by (rule dual_conjunctive, simp)


lemma [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y \<le> x * y"
  apply (simp add: assertion_def, safe)
  proof -
  assume A: "x \<le> 1"
  assume B: "x * \<top> \<sqinter> x ^ o = x"
  assume C: "y \<le> 1"
  assume D: "y * \<top> \<sqinter> y ^ o = y"
  have "x \<sqinter> y = (x * \<top> \<sqinter> x ^ o) \<sqinter> (y * \<top> \<sqinter> y ^ o)" by (cut_tac B D, simp)
  also have "\<dots> \<le> (x * \<top>) \<sqinter> (((x^o) * (y * \<top>)) \<sqinter> ((x^o) * (y^o)))"
    apply (simp, safe)
      apply (rule_tac y = "x * \<top> \<sqinter> x ^ o" in order_trans)
      apply (rule inf_le1)
      apply simp
      apply (rule_tac y = "y * \<top>" in order_trans)
      apply (rule_tac y = "y * \<top> \<sqinter> y ^ o" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule gt_one_comp)
      apply (subst dual_le, simp add: A)
      apply (rule_tac y = "y ^ o" in order_trans)
      apply (rule_tac y = "y * \<top> \<sqinter> y ^ o" in order_trans)
      apply (rule inf_le2)
      apply simp
      apply (rule gt_one_comp)
      by (subst dual_le, simp add: A)
    also have "... = ((x * \<top>) \<sqinter> (x ^ o)) * ((y * \<top>) \<sqinter> (y ^ o))"
      apply (cut_tac x = x in dual_assertion_conjunctive)
      apply (cut_tac A, cut_tac B, simp add: assertion_def)
      by (simp add: inf_comp conjunctiveD)
    also have "... = x * y"
      by (cut_tac B, cut_tac D, simp)
    finally show "x \<sqinter> y \<le> x * y" .
  qed
    
lemma [simp]: "x \<in> assertion \<Longrightarrow> x * y \<le> y"
  by (unfold assertion_def, cut_tac x = x and y = 1 and z = y in le_comp_right, simp_all)


lemma [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x * y \<le> x"
  apply (subgoal_tac "x * y \<le> (x * \<top>) \<sqinter> (x ^ o)")
  apply (simp add: assertion_def) 
  apply (simp, safe)
  apply (rule le_comp, simp)
  apply (rule_tac y = 1 in order_trans)
  apply (rule_tac y = y in order_trans)
  apply simp
  apply (simp add: assertion_def)
  by (subst dual_le, simp add: assertion_def)

lemma assertion_inf_comp_eq: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y = x * y"
  by (rule antisym, simp_all)

lemma one_right_assertion [simp]: "x \<in> assertion \<Longrightarrow> x * 1 = x"
  apply (drule assertion_prop)
  proof -
    assume A: "x * \<top> \<sqinter> 1 = x"
    have "x * 1 = (x * \<top> \<sqinter> 1) * 1" by (simp add: A)
    also have "\<dots> = x * \<top> \<sqinter> 1" by (simp add: inf_comp)
    also have "\<dots> = x" by (simp add: A)
    finally show ?thesis .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<squnion> 1 = 1"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> 1 \<squnion> x = 1"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<sqinter> 1 = x"
  by (rule antisym, simp_all add: assertion_def)
  
lemma [simp]: "x \<in> assertion \<Longrightarrow> 1 \<sqinter> x = x"
  by (rule antisym, simp_all add: assertion_def)

lemma [simp]:  "x \<in> assertion \<Longrightarrow> x \<le> x * \<top>"
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma [simp]: "x \<in> assertion \<Longrightarrow> x \<le> 1"
  by (simp add: assertion_def)

definition
  "neg_assert (x::'a) = (x ^ o * \<bottom>) \<sqinter> 1"
  

lemma sup_uminus[simp]: "x \<in> assertion \<Longrightarrow> x \<squnion> neg_assert x = 1"
  apply (simp add: neg_assert_def)
  apply (simp add: sup_inf_distrib)
  apply (rule antisym, simp_all)
  apply (unfold assertion_def)
  apply safe
  apply (subst dual_le)
  apply (simp add: dual_sup dual_comp)
  apply (subst inf_commute)
  by simp

lemma inf_uminus[simp]: "x \<in> assertion \<Longrightarrow> x \<sqinter> neg_assert x = \<bottom>"
  apply (simp add: neg_assert_def)
  apply (rule antisym, simp_all)
  apply (rule_tac y = "x \<sqinter> (x ^ o * \<bottom>)" in order_trans)
  apply simp
  apply (rule_tac y = "x ^ o * \<bottom> \<sqinter> 1" in order_trans)
  apply (rule inf_le2)
  apply simp
  apply (rule_tac y = "(x * \<top>)  \<sqinter> (x ^ o * \<bottom>)" in order_trans)
  apply simp
  apply (rule_tac y = x in order_trans)
  apply simp_all
  by (simp add: dual_neg)


lemma uminus_assertion[simp]: "x \<in> assertion \<Longrightarrow> neg_assert x \<in> assertion"
  apply (subst assertion_def)
  apply (simp add: neg_assert_def)
  apply (simp add: inf_comp dual_inf dual_comp inf_sup_distrib)
  apply (subst inf_commute)
  by (simp add: dual_neg)

lemma uminus_uminus [simp]: "x \<in> assertion \<Longrightarrow> neg_assert (neg_assert x) = x"
  apply (simp add: neg_assert_def)
  by (simp add: dual_inf dual_comp sup_comp assertion_prop)

lemma dual_comp_neg [simp]: "x ^ o * y \<squnion> (neg_assert x) * \<top> = x ^ o * y"
  apply (simp add: neg_assert_def inf_comp)
  apply (rule antisym, simp_all)
  by (rule le_comp, simp)


lemma [simp]: "(neg_assert x) ^ o * y \<squnion> x * \<top> = (neg_assert x) ^ o * y"
  apply (simp add: neg_assert_def inf_comp dual_inf dual_comp sup_comp)
  by (rule antisym, simp_all)

lemma [simp]: " x * \<top> \<squnion> (neg_assert x) ^ o * y= (neg_assert x) ^ o * y"
  by (simp add: neg_assert_def inf_comp dual_inf dual_comp sup_comp)

lemma inf_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<sqinter> y \<in> assertion"
  apply (subst assertion_def)
  apply safe
  apply (rule_tac y = x in order_trans)
  apply simp_all
  apply (simp add: assertion_inf_comp_eq)
  proof -
    assume A: "x \<in> assertion"
    assume B: "y \<in> assertion"
    have C: "(x * \<top>) \<sqinter> (x ^ o) = x"
      by (cut_tac A, unfold assertion_def, simp) 
    have D: "(y * \<top>) \<sqinter> (y ^ o) = y"
      by (cut_tac B, unfold assertion_def, simp)
    have "x * y = ((x * \<top>) \<sqinter> (x ^ o)) * ((y * \<top>) \<sqinter> (y ^ o))" by (simp add: C D)
    also have "\<dots> = x * \<top> \<sqinter> ((x ^ o) * ((y * \<top>) \<sqinter> (y ^ o)))" by (simp add: inf_comp)
    also have "\<dots> =  x * \<top> \<sqinter> ((x ^ o) * (y * \<top>)) \<sqinter> ((x ^ o) *(y ^ o))" 
      by (cut_tac A, cut_tac x = x in dual_assertion_conjunctive, simp_all add: conjunctiveD inf_assoc)
    also have "\<dots> = (((x * \<top>) \<sqinter> (x ^ o)) * (y * \<top>)) \<sqinter> ((x ^ o) *(y ^ o))"
      by (simp add: inf_comp)
    also have "\<dots> = (x * y * \<top>)  \<sqinter> ((x * y) ^ o)" by (simp add: C mult.assoc dual_comp)
    finally show "(x * y * \<top>)  \<sqinter> ((x * y) ^ o) = x * y" by simp
  qed

lemma comp_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x * y \<in> assertion"
  by (subst assertion_inf_comp_eq [THEN sym], simp_all)


lemma sup_assertion [simp]: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> x \<squnion> y \<in> assertion"
  apply (subst assertion_def)
  apply safe
  apply (unfold assertion_def)
  apply simp
  apply safe
  proof -
    assume [simp]: "x \<le> 1"
    assume [simp]: "y \<le> 1"
    assume A: "x * \<top> \<sqinter> x ^ o = x"
    assume B: "y * \<top> \<sqinter> y ^ o = y"
    have "(y * \<top>) \<sqinter> (x ^ o) \<sqinter> (y ^ o) = (x ^ o) \<sqinter> (y * \<top>) \<sqinter> (y ^ o)" by (simp add: inf_commute)
    also have "\<dots> = (x ^ o) \<sqinter> ((y * \<top>) \<sqinter> (y ^ o))" by (simp add: inf_assoc)
    also have "\<dots> = (x ^ o) \<sqinter> y" by (simp add: B)
    also have "\<dots> = y"
      apply (rule antisym, simp_all)
      apply (rule_tac y = 1 in order_trans)
      apply simp
      by (subst dual_le, simp)
    finally have [simp]: "(y * \<top>) \<sqinter> (x ^ o) \<sqinter> (y ^ o) = y" .
    have "x * \<top> \<sqinter> (x ^ o) \<sqinter> (y ^ o) = x \<sqinter> (y ^ o)"  by (simp add: A)
    also have "\<dots> = x"
      apply (rule antisym, simp_all)
      apply (rule_tac y = 1 in order_trans)
      apply simp
      by (subst dual_le, simp)
    finally have [simp]: "x * \<top> \<sqinter> (x ^ o) \<sqinter> (y ^ o) = x" .
    have "(x \<squnion> y) * \<top> \<sqinter> (x \<squnion> y) ^ o = (x * \<top> \<squnion> y * \<top>) \<sqinter> ((x ^ o) \<sqinter> (y ^ o))" by (simp add: sup_comp dual_sup)
    also have "\<dots> = x \<squnion> y" by (simp add: inf_sup_distrib inf_assoc [THEN sym])
    finally show "(x \<squnion> y) * \<top> \<sqinter> (x \<squnion> y) ^ o = x \<squnion> y" .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> x * x = x"
  by (simp add: assertion_inf_comp_eq [THEN sym])

lemma [simp]: "x \<in> assertion \<Longrightarrow> (x ^ o) * (x ^ o) = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_comp assertion_inf_comp_eq [THEN sym])

lemma [simp]: "x \<in> assertion \<Longrightarrow> x * (x ^ o) = x"
  proof -
    assume A: "x \<in> assertion"
    have B: "x * \<top> \<sqinter> (x ^ o) = x" by (cut_tac A, unfold assertion_def, simp)
    have "x * x ^ o = (x * \<top> \<sqinter> (x ^ o)) * x ^ o" by (simp add: B)
    also have "\<dots> = x * \<top> \<sqinter> (x ^ o)" by (cut_tac A, simp add: inf_comp)
    also have "\<dots> = x" by (simp add: B)
    finally show ?thesis .
  qed

lemma [simp]: "x \<in> assertion \<Longrightarrow> (x ^ o) * x = x ^ o"
  apply (rule dual_eq)
  by (simp add: dual_comp)


lemma [simp]: "\<bottom> \<in> assertion"
  by (unfold assertion_def, simp)

lemma [simp]: "1 \<in> assertion"
  by (unfold assertion_def, simp)


subsection \<open>Weakest precondition of true\<close>

definition
  "wpt x = (x * \<top>) \<sqinter> 1"

lemma wpt_is_assertion [simp]: "wpt x \<in> assertion"
  apply (unfold wpt_def assertion_def, safe)
  apply simp
  apply (simp add: inf_comp dual_inf dual_comp inf_sup_distrib)
  apply (rule antisym)
  by (simp_all add: dual_neg)

lemma wpt_comp: "(wpt x) * x = x"
  apply (simp add: wpt_def inf_comp)
  apply (rule antisym, simp_all)
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma wpt_comp_2: "wpt (x * y) = wpt (x * (wpt y))"
  by (simp add: wpt_def inf_comp mult.assoc)

lemma wpt_assertion [simp]: "x \<in> assertion \<Longrightarrow> wpt x = x"
  by (simp add: wpt_def assertion_prop)

lemma wpt_le_assertion: "x \<in> assertion \<Longrightarrow> x * y = y \<Longrightarrow> wpt y \<le> x"
  apply (simp add: wpt_def)
  proof -
    assume A: "x \<in> assertion"
    assume B: "x * y = y"
    have "y * \<top> \<sqinter> 1 = x * (y * \<top>) \<sqinter> 1" by (simp add: B mult.assoc [THEN sym])
    also have "\<dots> \<le> x * \<top> \<sqinter> 1" 
      apply simp
      apply (rule_tac y = "x * (y * \<top>)" in order_trans)
      apply simp_all
      by (rule le_comp, simp)
    also have "\<dots> = x" by (cut_tac A, simp add: assertion_prop)
    finally show "y * \<top> \<sqinter> 1 \<le> x" .
  qed

lemma wpt_choice: "wpt (x \<sqinter> y) = wpt x \<sqinter> wpt y"
  apply (simp add: wpt_def inf_comp)
  proof -
    have "x * \<top> \<sqinter> 1 \<sqinter> (y * \<top> \<sqinter> 1) = x * \<top> \<sqinter> ((y * \<top> \<sqinter> 1) \<sqinter> 1)" apply (subst inf_assoc) by (simp add: inf_commute)
    also have "... = x * \<top> \<sqinter> (y * \<top> \<sqinter> 1)" by (subst inf_assoc, simp)
    also have "... = (x * \<top>) \<sqinter> (y * \<top>) \<sqinter> 1" by (subst inf_assoc, simp)
    finally show "x * \<top> \<sqinter> (y * \<top>) \<sqinter> 1 = x * \<top> \<sqinter> 1 \<sqinter> (y * \<top> \<sqinter> 1)" by simp
  qed
end 

context lattice begin
lemma [simp]: "x \<le> y \<Longrightarrow> x \<sqinter> y = x"
  by (simp add: inf_absorb1)
end


context mbt_algebra begin

lemma wpt_dual_assertion_comp: "x \<in> assertion \<Longrightarrow> y \<in> assertion \<Longrightarrow> wpt ((x ^ o) * y) = (neg_assert x) \<squnion> y"
  apply (simp add: wpt_def neg_assert_def)
  proof -
    assume A: "x \<in> assertion"
    assume B: "y \<in> assertion"
    have C: "((x ^ o) * \<bottom>) \<squnion> 1 = x ^ o"
      by (rule dual_assertion_prop, rule A)
    have "x ^ o * y * \<top> \<sqinter> 1 = (((x ^ o) * \<bottom>) \<squnion> 1) * y * \<top> \<sqinter> 1" by (simp add: C)
    also have "\<dots> = ((x ^ o) * \<bottom> \<squnion> (y * \<top>)) \<sqinter> 1" by (simp add: sup_comp)
    also have "\<dots> = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> ((y * \<top>) \<sqinter> 1)" by (simp add: inf_sup_distrib2)
    also have "\<dots> = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> y" by (cut_tac B, drule assertion_prop, simp)
    finally show "x ^ o * y * \<top> \<sqinter> 1 = (((x ^ o) * \<bottom>) \<sqinter> 1) \<squnion> y" .
  qed

lemma le_comp_left_right: "x \<le> y \<Longrightarrow> u \<le> v \<Longrightarrow> x * u \<le> y * v"
  apply (rule_tac y = "x * v" in order_trans)
  apply (rule le_comp, simp)
  by (rule le_comp_right, simp)

lemma wpt_dual_assertion: "x \<in> assertion \<Longrightarrow> wpt (x ^ o) = 1"
  apply (simp add: wpt_def)
  apply (rule antisym)
  apply simp_all
  apply (cut_tac x = 1 and y = "x ^ o" and u = 1 and v = \<top> in le_comp_left_right)
  apply simp_all
  apply (subst dual_le)
  by simp

lemma assertion_commute: "x \<in> assertion \<Longrightarrow> y \<in> conjunctive \<Longrightarrow> y * x = wpt(y * x) * y"
  apply (simp add: wpt_def)
  apply (simp add: inf_comp)
  apply (drule_tac x = y and y = "x * \<top>" and z = 1 in conjunctiveD)
  by (simp add: mult.assoc [THEN sym] assertion_prop)


lemma wpt_mono: "x \<le> y \<Longrightarrow> wpt x \<le> wpt y"
  apply (simp add: wpt_def)
  apply (rule_tac y = "x * \<top>" in order_trans, simp_all)
  by (rule le_comp_right, simp)

lemma "a \<in> conjunctive \<Longrightarrow> x * a \<le> a * y \<Longrightarrow> (x ^ \<omega>) * a \<le> a * (y ^ \<omega>)"
  apply (rule omega_least)
  apply (simp add: mult.assoc [THEN sym])
  apply (rule_tac y = "a * y * y ^ \<omega> \<sqinter> a" in order_trans)
  apply (simp)
  apply (rule_tac y = "x * a * y ^ \<omega>" in order_trans, simp_all)
  apply (rule le_comp_right, simp)
  apply (simp add: mult.assoc)
  apply (subst (2) omega_fix)
  by (simp add: conjunctiveD)

lemma [simp]: "x \<le> 1 \<Longrightarrow> y * x \<le> y"
  by (cut_tac x = x and y = 1 and z = y in le_comp, simp_all)

lemma [simp]: "x \<le> x * \<top>"
  by (cut_tac x = 1 and y = \<top> and z = x in le_comp, simp_all)

lemma [simp]: "x * \<bottom> \<le> x"
  by (cut_tac x = \<bottom> and y = 1 and z = x in le_comp, simp_all)

end

subsection\<open>Monotonic Boolean trasformers algebra with post condition statement\<close>

definition
  "post_fun (p::'a::order) q = (if p \<le> q then (\<top>::'b::{order_bot,order_top}) else \<bottom>)"

lemma mono_post_fun [simp]: "mono (post_fun (p::_::{order_bot,order_top}))"
  apply (simp add: post_fun_def mono_def, safe)
  apply (subgoal_tac "p \<le> y", simp)
  apply (rule_tac y = x in order_trans)
  apply simp_all
  done

lemma post_top [simp]: "post_fun p p = \<top>"
  by (simp add: post_fun_def)

lemma post_refin [simp]: "mono S \<Longrightarrow> ((S p)::'a::bounded_lattice) \<sqinter> (post_fun p) x \<le> S x"
  apply (simp add: le_fun_def assert_fun_def post_fun_def, safe)
  by (rule_tac f = S in monoD, simp_all)

class post_mbt_algebra = mbt_algebra +
  fixes post :: "'a \<Rightarrow> 'a"
  assumes post_1: "(post x) * x * \<top> = \<top>"
  and post_2: "y * x * \<top> \<sqinter> (post x) \<le> y"

instantiation MonoTran :: (complete_boolean_algebra) post_mbt_algebra
begin

lift_definition post_MonoTran :: "'a::complete_boolean_algebra MonoTran \<Rightarrow> 'a::complete_boolean_algebra MonoTran"
  is "\<lambda>x. post_fun (x \<top>)"
  by (rule mono_post_fun)

instance proof
  fix x :: "'a MonoTran" show "post x * x * \<top> = \<top>"
    apply transfer
    apply (simp add: fun_eq_iff)
    done
  fix x y :: "'a MonoTran" show "y * x * \<top> \<sqinter> post x \<le> y"
    apply transfer
    apply (simp add: le_fun_def)
    done
qed
   
end

subsection\<open>Complete monotonic Boolean transformers algebra\<close>

class complete_mbt_algebra = post_mbt_algebra + complete_distrib_lattice +
  assumes Inf_comp: "(Inf X) * z = (INF x \<in> X . (x * z))"

instance MonoTran :: (complete_boolean_algebra) complete_mbt_algebra
  apply intro_classes
  apply transfer
  apply (simp add: Inf_comp_fun)
  done

context complete_mbt_algebra begin
lemma dual_Inf: "(Inf X) ^ o = (SUP x\<in> X . x ^ o)"
  apply (rule antisym)
  apply (subst dual_le, simp)
  apply (rule Inf_greatest)
  apply (subst dual_le, simp)
  apply (rule SUP_upper, simp)
  apply (rule SUP_least)
  apply (subst dual_le, simp)
  by (rule Inf_lower, simp)

lemma dual_Sup: "(Sup X) ^ o = (INF x\<in> X . x ^ o)"
  apply (rule antisym)
  apply (rule INF_greatest)
  apply (subst dual_le, simp)
  apply (rule Sup_upper, simp)
  apply (subst dual_le, simp)
  apply (rule Sup_least)
  apply (subst dual_le, simp)
  by (rule INF_lower, simp)

lemma INF_comp: "(\<Sqinter>(f ` A)) * z = (INF a \<in> A . (f a) * z)"
  unfolding Inf_comp
  apply (subgoal_tac "((\<lambda>x::'a. x * z) ` f ` A) = ((\<lambda>a::'b. f a * z) ` A)")
  by auto

lemma dual_INF: "(\<Sqinter>(f ` A)) ^ o = (SUP a \<in> A . (f a) ^ o)"
  unfolding Inf_comp dual_Inf
  apply (subgoal_tac "(dual ` f ` A) = ((\<lambda>a::'b. f a ^ o) ` A)")
  by auto

lemma dual_SUP: "(\<Squnion>(f ` A)) ^ o = (INF a \<in> A . (f a) ^ o)"
  unfolding dual_Sup
  apply (subgoal_tac "(dual ` f ` A) = ((\<lambda>a::'b. f a ^ o) ` A)")
  by auto

lemma Sup_comp: "(Sup X) * z = (SUP x \<in> X . (x * z))"
  apply (rule dual_eq)
  by (simp add: dual_comp dual_Sup dual_SUP INF_comp image_comp)

lemma SUP_comp: "(\<Squnion>(f ` A)) * z = (SUP a \<in> A . (f a) * z)"
  unfolding Sup_comp
  apply (subgoal_tac "((\<lambda>x::'a. x * z) ` f ` A) = ((\<lambda>a::'b. f a * z) ` A)")
  by auto


lemma Sup_assertion [simp]: "X \<subseteq> assertion \<Longrightarrow> Sup X \<in> assertion"
  apply (unfold assertion_def)
  apply safe
  apply (rule Sup_least)
  apply blast
  apply (simp add: Sup_comp dual_Sup Sup_inf)
  apply (subgoal_tac "((\<lambda>y . y \<sqinter> \<Sqinter>(dual ` X)) ` (\<lambda>x . x * \<top>) ` X) = X")
  apply simp
  proof -
    assume A: "X \<subseteq> {x. x \<le> 1 \<and> x * \<top> \<sqinter> x ^ o = x}"
    have B [simp]: "!! x . x \<in> X \<Longrightarrow>  x * \<top> \<sqinter> (\<Sqinter>(dual ` X)) = x"
    proof -
      fix x
      assume C: "x \<in> X"
      have "x * \<top> \<sqinter> \<Sqinter>(dual ` X) = x * \<top> \<sqinter> (x ^ o \<sqinter> \<Sqinter>(dual ` X))"
        apply (subgoal_tac "\<Sqinter>(dual ` X) = (x ^ o \<sqinter> \<Sqinter>(dual ` X))", simp)
        apply (rule antisym, simp_all)
        apply (rule Inf_lower, cut_tac C, simp)
        done
      also have "\<dots> = x \<sqinter> \<Sqinter>(dual ` X)" by (unfold  inf_assoc [THEN sym], cut_tac A, cut_tac C, auto)
      also have "\<dots> = x"
        apply (rule antisym, simp_all)
        apply (rule INF_greatest)
        apply (cut_tac A C)
        apply (rule_tac y = 1 in order_trans)
        apply auto[1]
        apply (subst dual_le, auto)
        done
      finally show "x * \<top> \<sqinter> \<Sqinter>(dual ` X) = x" .
      qed
      show "(\<lambda>y. y \<sqinter> \<Sqinter>(dual ` X)) ` (\<lambda>x . x * \<top>) ` X = X"
        by (simp add: image_comp)
    qed

lemma Sup_range_assertion [simp]: "(!!w . p w \<in> assertion) \<Longrightarrow> Sup (range p) \<in> assertion"
  by (rule Sup_assertion, auto)

lemma Sup_less_assertion [simp]: "(!!w . p w \<in> assertion) \<Longrightarrow> Sup_less p w \<in> assertion"
  by (unfold Sup_less_def, rule Sup_assertion, auto)

theorem omega_lfp: 
  "x ^ \<omega> * y = lfp (\<lambda> z . (x * z) \<sqinter> y)"
  apply (rule antisym)
  apply (rule lfp_greatest)
  apply (drule omega_least, simp)
  apply (rule lfp_lowerbound)
  apply (subst (2) omega_fix)
  by (simp add: inf_comp mult.assoc)
end

lemma [simp]: "mono (\<lambda> (t::'a::mbt_algebra) . x * t \<sqinter> y)"
  apply (simp add: mono_def, safe)
  apply (rule_tac y = "x * xa" in order_trans, simp)
  by (rule le_comp, simp)


class mbt_algebra_fusion = mbt_algebra +
  assumes fusion: "(\<forall> t . x * t \<sqinter> y \<sqinter> z \<le> u * (t \<sqinter> z) \<sqinter> v)
          \<Longrightarrow> (x ^ \<omega>) * y \<sqinter> z \<le> (u ^ \<omega>) * v "

lemma 
    "class.mbt_algebra_fusion (1::'a::complete_mbt_algebra) ((*)) (\<sqinter>) (\<le>) (<) (\<squnion>) dual dual_star omega star \<bottom> \<top>"
    apply unfold_locales
    apply (cut_tac h = "\<lambda> t . t \<sqinter> z" and f = "\<lambda> t . x * t \<sqinter> y" and g = "\<lambda> t . u * t \<sqinter> v" in weak_fusion)
    apply (rule inf_Disj)
    apply simp_all
    apply (simp add: le_fun_def)
    by  (simp add: omega_lfp)

context mbt_algebra_fusion
begin

lemma omega_star: "x \<in> conjunctive \<Longrightarrow> x ^ \<omega> = wpt (x ^ \<omega>) * (x ^ *)"
  apply (simp add: wpt_def inf_comp)
  apply (rule antisym)
  apply (cut_tac x = x and y = 1 and z = "x ^ \<omega> * \<top> \<sqinter> x ^ *" in omega_least)
  apply (simp_all add: conjunctiveD,safe)
  apply  (subst (2) omega_fix)
  apply (simp add: inf_comp inf_assoc mult.assoc)
  apply (metis inf.commute inf_assoc inf_le1 star_fix)
  apply (cut_tac x = x and y = \<top> and z = "x ^ *" and u = x and v = 1 in fusion)
  apply (simp add: conjunctiveD)
  apply (metis inf_commute inf_le1 le_infE star_fix)
  by (metis mult.right_neutral)

lemma omega_pres_conj: "x \<in> conjunctive \<Longrightarrow> x ^ \<omega> \<in> conjunctive"
  apply (subst omega_star, simp)
  apply (rule comp_pres_conj)
  apply (rule assertion_conjunctive, simp)
  by (rule start_pres_conj, simp)
end

end
