section\<open>Left Complemented Monoid\<close>

theory LeftComplementedMonoid
  imports Operations LatticeProperties.Lattice_Prop
begin

class right_pordered_monoid_mult = order + monoid_mult +
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> a * c \<le> b * c"

class one_greatest = one + ord +
  assumes one_greatest [simp]: "a \<le> 1"

class integral_right_pordered_monoid_mult = right_pordered_monoid_mult + one_greatest

class left_residuated = ord + times + left_imp +
  assumes left_residual: "(x * a \<le> b) = (x \<le> a l\<rightarrow> b)"

class left_residuated_pordered_monoid = integral_right_pordered_monoid_mult + left_residuated

class left_inf = inf + times + left_imp +
  assumes inf_l_def: "(a \<sqinter> b)  = (a l\<rightarrow> b) * a"

class left_complemented_monoid = left_residuated_pordered_monoid + left_inf +
  assumes right_divisibility: "(a \<le> b) = (\<exists> c . a = c * b)"
begin
lemma lcm_D: "a l\<rightarrow> a = 1"
  apply (rule antisym, simp)
  by (unfold left_residual [THEN sym], simp)

subclass semilattice_inf
    apply unfold_locales
    apply (metis inf_l_def right_divisibility)
    apply (metis inf_l_def left_residual order_refl)    
    by (metis inf_l_def left_residual mult_right_mono right_divisibility)

  lemma left_one_inf [simp]: "1 \<sqinter> a = a" 
    by (rule antisym, simp_all)

  lemma left_one_impl [simp]: "1 l\<rightarrow> a = a"
    (*by (metis inf_l_def left_one_inf mult.right_neutral)*)
    proof -
      have "1 l\<rightarrow> a = 1 \<sqinter> a" by (unfold inf_l_def, simp)
      also have "1 \<sqinter> a = a" by simp
      finally show ?thesis .
    qed

  lemma lcm_A: "(a l\<rightarrow> b) * a = (b l\<rightarrow> a) * b"
    apply (unfold inf_l_def [THEN sym])
    by (simp add: inf_commute)

  lemma lcm_B: "((a * b) l\<rightarrow> c) = (a l\<rightarrow> (b l\<rightarrow> c))" 
    apply (rule antisym)
    apply (simp add: left_residual [THEN sym] mult.assoc)
    apply (simp add: left_residual)

    apply (simp add: left_residual [THEN sym])
    apply (rule_tac y="(b l\<rightarrow> c) * b" in order_trans)
    apply (simp add: mult.assoc [THEN sym]) 
    apply (rule mult_right_mono)
    by (simp_all add: left_residual)
  
  lemma lcm_C: "(a \<le> b) = ((a l\<rightarrow> b) = 1)"
    (*by (metis eq_iff left_residual mult.left_neutral one_greatest)*)
    proof -
      have "(a \<le> b) = (1 * a \<le> b)" by simp
      also have "\<dots> = (1 \<le> a l\<rightarrow> b)" by (unfold left_residual, simp)
      also have "\<dots> = (a l\<rightarrow> b = 1)" apply safe by(rule antisym, simp_all)
      finally show ?thesis .
    qed

  end

class less_def = ord +
  assumes less_def: "(a < b) = ((a \<le> b) \<and> \<not> (b \<le> a))"

class one_times = one + times +
  assumes one_left [simp]: "1 * a = a" 
  and one_right [simp]: "a * 1 = a"

class left_complemented_monoid_algebra = left_imp + one_times + left_inf + less_def +
  assumes left_impl_one [simp]: "a l\<rightarrow> a = 1"
  and left_impl_times: "(a l\<rightarrow> b) * a = (b l\<rightarrow> a) * b"
  and left_impl_ded: "((a * b) l\<rightarrow> c) = (a l\<rightarrow> (b l\<rightarrow> c))"
  and left_lesseq: "(a \<le> b) = ((a l\<rightarrow> b) = 1)"
begin
  lemma A: "(1 l\<rightarrow> a) l\<rightarrow> 1 = 1"
    proof -
      have "(1 l\<rightarrow> a) l\<rightarrow> 1 = (1 l\<rightarrow> a) * 1 l\<rightarrow> 1" by simp
      also have "... = (a l\<rightarrow> 1) * a l\<rightarrow> 1" by (subst left_impl_times, simp)
      also have "... = 1" by (simp add: left_impl_ded)
      finally show ?thesis .
    qed

  subclass order
    proof
      fix x y show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (unfold less_def, simp)
    next
      fix x show "x \<le> x" by (unfold left_lesseq, simp)
    next
      fix x y z assume a: "x \<le> y" assume b: "y \<le> z"
      have "x l\<rightarrow> z = 1 * x l\<rightarrow> z" by simp 
      also have "... = (x l\<rightarrow> y) * x l\<rightarrow> z" by (cut_tac a, simp add: left_lesseq)
      also have "... = (y l\<rightarrow> x) * y l\<rightarrow> z" by (simp add: left_impl_times)
      also have "... = (y l\<rightarrow> x) l\<rightarrow> (y l\<rightarrow> z)" by (simp add: left_impl_ded)
      also have "... = (y l\<rightarrow> x) l\<rightarrow> 1" by (cut_tac b, simp add: left_lesseq)
      also have "... = (1 * y l\<rightarrow> x) l\<rightarrow> 1" by simp
      also have "... = (1 l\<rightarrow> (y l\<rightarrow> x)) l\<rightarrow> 1" by (subst left_impl_ded, simp)
      also have "... = 1" by (simp add: A)
      finally show "x \<le> z"  by (simp add: left_lesseq)
    next
      fix x y z assume a: "x \<le> y" assume b: "y \<le> x"
      have "x = (x l\<rightarrow> y) * x" by (cut_tac a, simp add: left_lesseq)
      also have "... = (y l\<rightarrow> x) * y" by (simp add: left_impl_times)
      also have "... = y" by (cut_tac b, simp add: left_lesseq)
      finally show "x = y" .
    qed


  lemma B: "(1 l\<rightarrow> a) \<le> 1"
    apply (unfold left_lesseq)
    by (rule A)

  lemma C: "a \<le> (1 l\<rightarrow> a)"
    by (simp add: left_lesseq left_impl_ded [THEN sym])

  lemma D: "a \<le> 1"
    apply (rule_tac y = "1 l\<rightarrow> a" in order_trans)
    by (simp_all add: C B)

  lemma less_eq: "(a \<le> b) = (\<exists> c . a = (c * b))"
    (*by (metis left_impl_ded left_impl_one left_impl_times left_lesseq one_left)*)
    apply safe
    apply (unfold left_lesseq)
    apply (rule_tac x = "b l\<rightarrow> a" in exI)
    apply (simp add: left_impl_times)
    apply (simp add: left_impl_ded)
    apply (case_tac "c \<le> 1")
    apply (simp add: left_lesseq)
    by (simp add: D)


  lemma F: "(a * b) * c l\<rightarrow> z = a * (b * c) l\<rightarrow> z"
    by (simp add: left_impl_ded)

  lemma associativity: "(a * b) * c = a * (b * c)"
    (*by (metis F left_impl_one left_impl_times one_left)*)
    apply (rule antisym)
    apply (unfold left_lesseq)
    apply (simp add: F)
    by (simp add: F [THEN sym])

  lemma H: "a * b \<le> b"
    apply (simp add: less_eq)
    by auto

  lemma I: "a * b l\<rightarrow> b = 1"
    apply (case_tac "a * b \<le> b")
    apply (simp add: left_lesseq)
    by (simp add: H)

  lemma K: "a \<le> b \<Longrightarrow> a * c \<le> b * c"
    apply (unfold less_eq)
    apply clarify
    apply (rule_tac x = "ca" in exI)
    by (simp add: associativity) 

  lemma L: "(x * a \<le> b) = (x \<le> a l\<rightarrow> b)"
    by (simp add: left_lesseq left_impl_ded)

  subclass left_complemented_monoid 
    apply unfold_locales 
    apply (simp_all add:  less_def D associativity K)
    apply (simp add: L)
    by (simp add: less_eq)
  end



lemma (in left_complemented_monoid) left_complemented_monoid: 
    "class.left_complemented_monoid_algebra (*) inf (l\<rightarrow>) (\<le>) (<) 1"
  by (unfold_locales, simp_all add: less_le_not_le lcm_A lcm_B lcm_C lcm_D)

end
