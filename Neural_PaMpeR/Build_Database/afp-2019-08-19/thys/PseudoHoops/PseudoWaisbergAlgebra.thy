section\<open>Pseudo Waisberg Algebra\<close>

theory PseudoWaisbergAlgebra
imports Operations
begin

class impl_lr_algebra = one + left_imp + right_imp + 
  assumes W1a [simp]: "1 l\<rightarrow> a = a"
  and W1b [simp]: "1 r\<rightarrow> a = a"

  and W2a: "(a l\<rightarrow> b) r\<rightarrow> b = (b l\<rightarrow> a) r\<rightarrow> a"
  and W2b: "(b l\<rightarrow> a) r\<rightarrow> a = (b r\<rightarrow> a) l\<rightarrow> a"
  and W2c: "(b r\<rightarrow> a) l\<rightarrow> a = (a r\<rightarrow> b) l\<rightarrow> b"

  and W3a: "(a l\<rightarrow> b) l\<rightarrow> ((b l\<rightarrow> c) r\<rightarrow> (a l\<rightarrow> c)) = 1"
  and W3b: "(a r\<rightarrow> b) r\<rightarrow> ((b r\<rightarrow> c) l\<rightarrow> (a r\<rightarrow> c)) = 1"

begin

lemma P1_a [simp]: "x l\<rightarrow> x = 1"
  apply (cut_tac a = 1 and b = 1 and c = x in W3b)
  by simp

lemma P1_b [simp]: "x r\<rightarrow> x = 1"
  apply (cut_tac a = 1 and b = 1 and c = x in W3a)
  by simp

lemma P2_a: "x l\<rightarrow> y = 1 \<Longrightarrow> y l\<rightarrow> x = 1 \<Longrightarrow> x = y"
  apply (subgoal_tac "(y l\<rightarrow> x) r\<rightarrow> x = y")
  apply simp
  apply (subgoal_tac "(x l\<rightarrow> y) r\<rightarrow> y = y")
  apply (unfold W2a)
  by simp_all

lemma P2_b: "x r\<rightarrow> y = 1 \<Longrightarrow> y r\<rightarrow> x = 1 \<Longrightarrow> x = y"
  apply (subgoal_tac "(y r\<rightarrow> x) l\<rightarrow> x = y")
  apply simp
  apply (subgoal_tac "(x r\<rightarrow> y) l\<rightarrow> y = y")
  apply (unfold W2c)
  by simp_all

lemma P2_c: "x l\<rightarrow> y = 1 \<Longrightarrow> y r\<rightarrow> x = 1 \<Longrightarrow> x = y"
  apply (subgoal_tac "(y r\<rightarrow> x) l\<rightarrow> x = y")
  apply simp
  apply (subgoal_tac "(x l\<rightarrow> y) r\<rightarrow> y = y")
  apply (unfold W2b) [1]
  apply (unfold W2c) [1]
  by simp_all

lemma P3_a: "(x l\<rightarrow> 1) r\<rightarrow> 1 = 1"
  apply (unfold W2a)
  by simp

lemma P3_b: "(x r\<rightarrow> 1) l\<rightarrow> 1 = 1"
  apply (unfold W2c)
  by simp

lemma P4_a [simp]: "x l\<rightarrow> 1 = 1"
  apply (subgoal_tac "x l\<rightarrow> ((x l\<rightarrow> 1) r\<rightarrow> 1) = 1")
  apply (simp add: P3_a)
  apply (cut_tac a = 1 and b = x and c = 1 in W3a)
  by simp

lemma P4_b [simp]: "x r\<rightarrow> 1 = 1"
  apply (subgoal_tac "x r\<rightarrow> ((x r\<rightarrow> 1) l\<rightarrow> 1) = 1")
  apply (simp add: P3_b)
  apply (cut_tac a = 1 and b = x and c = 1 in W3b)
  by simp

lemma P5_a: "x l\<rightarrow> y = 1 \<Longrightarrow> y l\<rightarrow> z = 1 \<Longrightarrow> x l\<rightarrow> z = 1"
  apply (cut_tac a = x and b = y and c = z in W3a)
  by simp

lemma P5_b: "x r\<rightarrow> y = 1 \<Longrightarrow> y r\<rightarrow> z = 1 \<Longrightarrow> x r\<rightarrow> z = 1"
  apply (cut_tac a = x and b = y and c = z in W3b)
  by simp

lemma P6_a: "x l\<rightarrow> (y r\<rightarrow> x) = 1"
  apply (cut_tac a = y and b = 1 and c = x in W3b)
  by simp

lemma P6_b: "x r\<rightarrow> (y l\<rightarrow> x) = 1"
  apply (cut_tac a = y and b = 1 and c = x in W3a)
  by simp

lemma P7: "(x l\<rightarrow> (y r\<rightarrow> z) = 1) = (y r\<rightarrow> (x l\<rightarrow> z) = 1)"
  proof
    fix x y z assume A: "x l\<rightarrow> y r\<rightarrow> z = 1" show "y r\<rightarrow> x l\<rightarrow> z = 1"
      apply (rule_tac y = "(z r\<rightarrow> y) l\<rightarrow> y" in P5_b)
      apply (simp add: P6_b)
      apply (unfold W2c)
      apply (subgoal_tac "(x l\<rightarrow> (y r\<rightarrow> z)) l\<rightarrow> (((y r\<rightarrow> z) l\<rightarrow> z) r\<rightarrow> x l\<rightarrow> z) = 1")
      apply (unfold A) [1]
      apply simp
      by (simp add: W3a)
    next
    fix x y z assume A: "y r\<rightarrow> x l\<rightarrow> z = 1" show "x l\<rightarrow> y r\<rightarrow> z = 1"
      apply (rule_tac y = "(z l\<rightarrow> x) r\<rightarrow> x" in P5_a)
      apply (simp add: P6_a)
      apply (unfold W2a)
      apply (subgoal_tac "(y r\<rightarrow> x l\<rightarrow> z) r\<rightarrow> (((x l\<rightarrow> z) r\<rightarrow> z) l\<rightarrow> y r\<rightarrow> z) = 1")
      apply (unfold A) [1]
      apply simp
      by (simp add: W3b)
    qed

lemma P8_a: "(x l\<rightarrow> y) r\<rightarrow> ((z l\<rightarrow> x) l\<rightarrow> (z l\<rightarrow> y)) = 1"
  by (simp add: W3a P7 [THEN sym])


lemma P8_b: "(x r\<rightarrow> y) l\<rightarrow> ((z r\<rightarrow> x) r\<rightarrow> (z r\<rightarrow> y)) = 1"
  by (simp add: W3b P7)

lemma P9: "x l\<rightarrow> (y r\<rightarrow> z) = y r\<rightarrow> (x l\<rightarrow> z)"
  apply (rule P2_c)
  apply (subst P7)
  apply (rule_tac y = "(z r\<rightarrow> y) l\<rightarrow> y" in P5_b)
  apply (simp add: P6_b)
  apply (subst W2c)
  apply (rule P8_a)
  apply (subst P7 [THEN sym])
  apply (rule_tac y = "(z l\<rightarrow> x) r\<rightarrow> x" in P5_a)
  apply (simp add: P6_a)
  apply (subst W2a)
  by (simp add: P8_b)

definition
  "lesseq_a a b = (a l\<rightarrow> b = 1)"

definition
  "less_a a b = (lesseq_a a b \<and> \<not> lesseq_a b a)"

definition
  "lesseq_b a b = (a r\<rightarrow> b = 1)"

definition
  "less_b a b = (lesseq_b a b \<and> \<not> lesseq_b b a)"

definition
  "sup_a a b = (a l\<rightarrow> b) r\<rightarrow> b"

end

sublocale impl_lr_algebra < order_a:order lesseq_a less_a
  apply unfold_locales
  apply (simp add: less_a_def)
  apply (simp_all add: lesseq_a_def)
  apply (rule P5_a)
  apply simp_all
  apply (rule P2_a)
  by simp_all

sublocale impl_lr_algebra < order_b:order lesseq_b less_b
  apply unfold_locales
  apply (simp add: less_b_def)
  apply (simp_all add: lesseq_b_def)
  apply (rule P5_b)
  apply simp_all
  apply (rule P2_b)
  by simp_all

sublocale impl_lr_algebra < slattice_a:semilattice_sup sup_a lesseq_a less_a
  apply unfold_locales
  apply (simp_all add: lesseq_a_def sup_a_def)
  apply (simp add: P9)
  apply (simp add: P9)
  apply (subst W2a)
  apply (subgoal_tac "((z l\<rightarrow> y) r\<rightarrow> y) l\<rightarrow> ((y l\<rightarrow> x) r\<rightarrow> x) = 1")
  apply simp
  apply (subgoal_tac "((z l\<rightarrow> y) r\<rightarrow> y) l\<rightarrow> ((x l\<rightarrow> y) r\<rightarrow> y) = 1")
  apply (simp add: W2a)
  apply (subgoal_tac "((z l\<rightarrow> y) r\<rightarrow> y) l\<rightarrow> (x l\<rightarrow> y) r\<rightarrow> y = ((x l\<rightarrow> y) r\<rightarrow> (z l\<rightarrow> y)) r\<rightarrow> (((z l\<rightarrow> y) r\<rightarrow> y) l\<rightarrow> (x l\<rightarrow> y) r\<rightarrow> y)")
  apply (simp add: W3b)
  apply (subgoal_tac "(x l\<rightarrow> y) r\<rightarrow> z l\<rightarrow> y = 1")
  apply simp
  apply (cut_tac a = z and b = x and c = y in W3a)
  by simp

sublocale impl_lr_algebra < slattice_b:semilattice_sup sup_a lesseq_b less_b
  apply unfold_locales
  apply (simp_all add: lesseq_b_def sup_a_def)
  apply (simp_all add: W2b)
  apply (simp add: P9 [THEN sym])
  apply (simp add: P9 [THEN sym])
  apply (subst W2c)
  apply (subgoal_tac "((z r\<rightarrow> y) l\<rightarrow> y) r\<rightarrow> ((y r\<rightarrow> x) l\<rightarrow> x) = 1")
  apply simp
  apply (subgoal_tac "((z r\<rightarrow> y) l\<rightarrow> y) r\<rightarrow> ((x r\<rightarrow> y) l\<rightarrow> y) = 1")
  apply (simp add: W2c)
  apply (subgoal_tac "((z r\<rightarrow> y) l\<rightarrow> y) r\<rightarrow> (x r\<rightarrow> y) l\<rightarrow> y = ((x r\<rightarrow> y) l\<rightarrow> (z r\<rightarrow> y)) l\<rightarrow> (((z r\<rightarrow> y) l\<rightarrow> y) r\<rightarrow> (x r\<rightarrow> y) l\<rightarrow> y)")
  apply (simp add: W3a)
  apply (subgoal_tac "(x r\<rightarrow> y) l\<rightarrow> z r\<rightarrow> y = 1")
  apply simp
  apply (cut_tac a = z and b = x and c = y in W3b)
  by simp


context impl_lr_algebra
begin
lemma lesseq_a_b: "lesseq_b = lesseq_a"
  apply (simp add: fun_eq_iff)
  apply clarify
  apply (cut_tac x = x and y = xa in slattice_a.le_iff_sup)
  apply (cut_tac x = x and y = xa in slattice_b.le_iff_sup)
  by simp

lemma P10: "(a l\<rightarrow> b = 1) = (a r\<rightarrow> b = 1)"
  apply (cut_tac lesseq_a_b)
  by (simp add: fun_eq_iff lesseq_a_def lesseq_b_def)
end

class one_ord = one + ord

class impl_lr_ord_algebra = impl_lr_algebra + one_ord +
  assumes
     order: "a \<le> b = (a l\<rightarrow> b = 1)"
  and
     strict: "a < b = (a \<le> b \<and> \<not> b \<le> a)"
begin
lemma order_l: "(a \<le> b) = (a l\<rightarrow> b = 1)"
  by (simp add: order)

lemma order_r: "(a \<le> b) = (a r\<rightarrow> b = 1)"
  by (simp add: order P10)

lemma P11_a: "a \<le> b l\<rightarrow> a"
  by (simp add: order_r P6_b)

lemma P11_b: "a \<le> b r\<rightarrow> a"
  by (simp add: order_l P6_a)

lemma P12: "(a \<le> b l\<rightarrow> c) = (b \<le> a r\<rightarrow> c)" 
  apply (subst order_r)
  apply (subst order_l)
  by (simp add: P7)

lemma P13_a: "a \<le> b \<Longrightarrow> b l\<rightarrow> c \<le> a l\<rightarrow> c"
  apply (subst order_r)
  apply (simp add: order_l)
  apply (cut_tac a = a and b = b and c = c in W3a)
  by simp

lemma P13_b: "a \<le> b \<Longrightarrow> b r\<rightarrow> c \<le> a r\<rightarrow> c"
  apply (subst order_l)
  apply (simp add: order_r)
  apply (cut_tac a = a and b = b and c = c in W3b)
  by simp

lemma P14_a: "a \<le> b \<Longrightarrow> c l\<rightarrow> a \<le> c l\<rightarrow> b"
  apply (simp add: order_l)
  apply (cut_tac x = a and y = b and z = c in P8_a)
  by simp
  
lemma P14_b: "a \<le> b \<Longrightarrow> c r\<rightarrow> a \<le> c r\<rightarrow> b"
  apply (simp add: order_r)
  apply (cut_tac x = a and y = b and z = c in P8_b)
  by simp

subclass order
  apply (subgoal_tac "(\<le>) = lesseq_a \<and> (<) = less_a")
  apply simp
  apply unfold_locales
  apply safe
  by (simp_all add: fun_eq_iff lesseq_a_def less_a_def order_l strict)

end

class one_zero_uminus = one + zero + left_uminus + right_uminus

class impl_neg_lr_algebra = impl_lr_ord_algebra + one_zero_uminus +
  assumes
      W4: "-l 1 = -r 1"
  and W5a: "(-l a r\<rightarrow> -l b) l\<rightarrow> (b l\<rightarrow> a) = 1"
  and W5b: "(-r a l\<rightarrow> -r b) l\<rightarrow> (b r\<rightarrow> a) = 1"
  and zero_def: "0 = -l 1"
begin

lemma zero_r_def: "0 = -r 1"
  by (simp add: zero_def W4)

lemma C1_a [simp]: "(-l x r\<rightarrow> 0) l\<rightarrow> x = 1"
  apply (unfold zero_def)
  apply (cut_tac a = x and b = 1 in W5a)
  by simp

lemma C1_b [simp]: "(-r x l\<rightarrow> 0) r\<rightarrow> x = 1"
  apply (unfold zero_r_def)
  apply (cut_tac a = x and b = 1 in W5b)
  by (simp add: P10)

lemma C2_b [simp]: "0 r\<rightarrow> x = 1"
  apply (cut_tac x= "-r x l\<rightarrow> 0" and y = x and z = 0 in P8_b) 
  by (simp add: P6_b)
  
lemma C2_a [simp]: "0 l\<rightarrow> x = 1"
  by (simp add: P10)

lemma C3_a: "x l\<rightarrow> 0 = -l x"
  proof -
    have A: "-l x l\<rightarrow> (x l\<rightarrow> 0) = 1"
      apply (cut_tac x = "-l x" and y = "-l (-r 1)" in P6_a)
      apply (cut_tac a = "-r 1" and b = "x" in W5a)
      apply (unfold zero_r_def)
      apply (rule_tac y = " -l (-r (1::'a)) r\<rightarrow> -l x" in P5_a)
      by simp_all
    have B: "(x l\<rightarrow> 0) r\<rightarrow> -l x = 1"
      apply (cut_tac a = "-l x r\<rightarrow> 0" and b = x and c = 0 in W3a)
      apply simp
      apply (cut_tac b = "-l x" and a = 0 in W2c)
      by simp
    show "x l\<rightarrow> 0 = -l x"
      apply (rule antisym)
      apply (simp add: order_r B) 
      by (simp add: order_l A)
    qed

lemma C3_b: "x r\<rightarrow> 0 = -r x"
  apply (rule antisym)
  apply (simp add: order_l)
  apply (cut_tac x = x in C1_b)
  apply (cut_tac a = "-r x l\<rightarrow> 0" and b = x and c = 0 in W3b)
  apply simp
  apply (cut_tac b = "-r x" and a = 0 in W2a)
  apply simp
  apply (cut_tac x = "-r x" and y = "-r (-l 1)" in P6_b)
  apply (cut_tac a = "-l 1" and b = "x" in W5b)
  apply (unfold zero_def order_r)
  apply (rule_tac y = " -r (-l (1::'a)) l\<rightarrow> -r x" in P5_b)
  by (simp_all add: P10)

lemma C4_a [simp]: "-r (-l x) = x" 
  apply (unfold C3_b [THEN sym] C3_a [THEN sym])
  apply (subst W2a)
  by simp
 
lemma C4_b [simp]: "-l (-r x) = x" 
  apply (unfold C3_b [THEN sym] C3_a [THEN sym])
  apply (subst W2c)
  by simp

lemma C5_a: "-r x l\<rightarrow> -r y = y r\<rightarrow> x"
  apply (rule antisym)
  apply (simp add: order_l W5b)
  apply (cut_tac a = "-r y" and b = "-r x" in W5a)
  by (simp add: order_l)
  
  
lemma C5_b: "-l x r\<rightarrow> -l y = y l\<rightarrow> x"
  apply (rule antisym)
  apply (simp add: order_l W5a)
  apply (cut_tac a = "-l y" and b = "-l x" in W5b)
  by (simp add: order_l)

lemma C6: "-r x l\<rightarrow> y = -l y r\<rightarrow> x"
  apply (cut_tac x = x and y = "-l y" in C5_a)
  by simp

lemma C7_a: "(x \<le> y) = (-l y \<le> -l x)"
  apply (subst order_l)
  apply (subst order_r)
  by (simp add: C5_b)
 
lemma C7_b: "(x \<le> y) = (-r y \<le> -r x)"
  apply (subst order_r)
  apply (subst order_l)
  by (simp add: C5_a)

end

class pseudo_wajsberg_algebra = impl_neg_lr_algebra +
  assumes 
  W6: "-r (a l\<rightarrow> -l b) = -l (b r\<rightarrow> -r a)"
begin
definition
  "mult a b = -r (a l\<rightarrow> -l b)"

definition
  "inf_a a b = -l (a r\<rightarrow> -r (a l\<rightarrow> b))"

definition
  "inf_b a b = -r (b l\<rightarrow> -l (b r\<rightarrow> a))"

end

sublocale pseudo_wajsberg_algebra < slattice_inf_a:semilattice_inf inf_a "(\<le>)" "(<)"
  apply unfold_locales
  apply (simp_all add: inf_a_def)
  apply (subst C7_b) 
  apply (simp add: order_l P9 C5_a P10 [THEN sym] P6_a)
  apply (subst C7_b) 
  apply (simp add: order_l P9 C5_a P10 [THEN sym] P6_a)
  apply (subst W6 [THEN sym])
  apply (subst C7_a)
  apply simp
  proof -
    fix x y z
    assume A: "x \<le> y"
    assume B: "x \<le> z"
    have C: "x l\<rightarrow> y = 1" by (simp add: order_l [THEN sym] A)
    have E: "((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> -l x = ((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((x l\<rightarrow> y) l\<rightarrow> -l x)"
      by (simp add: C)
    have F: "((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((x l\<rightarrow> y) l\<rightarrow> -l x) =  ((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((-l y r\<rightarrow> -l x) l\<rightarrow> -l x)"
      by (simp add: C5_b)
    have G: "((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((-l y r\<rightarrow> -l x) l\<rightarrow> -l x) = ((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((-l x r\<rightarrow> -l y) l\<rightarrow> -l y)"
      by (simp add: W2c)
    have H: "((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((-l x r\<rightarrow> -l y) l\<rightarrow> -l y) = ((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((y l\<rightarrow> x) l\<rightarrow> -l y)"
      by (simp add: C5_b)
    have I: "((y l\<rightarrow> z) l\<rightarrow> -l y) l\<rightarrow> ((y l\<rightarrow> x) l\<rightarrow> -l y) = 1"
      apply (simp add: order_l [THEN sym] P14_a)
      apply (rule P13_a)
      apply (rule P14_a)
      by (simp add: B)
    show "(y l\<rightarrow> z) l\<rightarrow> -l y \<le> -l x"
      by (simp add: order_l E F G H I)
    next
    qed
      

sublocale pseudo_wajsberg_algebra < slattice_inf_b:semilattice_inf inf_b "(\<le>)" "(<)"
  apply unfold_locales
  apply (simp_all add: inf_b_def)
  apply (subst C7_a)
  apply (simp add: order_r P9 [THEN sym] C5_b P10 P6_b)
  apply (subst C7_a) 
  apply (simp add: order_r P9 [THEN sym] C5_b P10 P6_b)
  apply (subst W6)
  apply (subst C7_b)
  apply simp
  proof -
    fix x y z
    assume A: "x \<le> y"
    assume B: "x \<le> z"
    have C: "x r\<rightarrow> z = 1" by (simp add: order_r [THEN sym] B)
    have E: "((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> -r x = ((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((x r\<rightarrow> z) r\<rightarrow> -r x)"
      by (simp add: C)
    have F: "((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((x r\<rightarrow> z) r\<rightarrow> -r x) =  ((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((-r z l\<rightarrow> -r x) r\<rightarrow> -r x)"
      by (simp add: C5_a)
    have G: "((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((-r z l\<rightarrow> -r x) r\<rightarrow> -r x) = ((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((-r x l\<rightarrow> -r z) r\<rightarrow> -r z)"
      by (simp add: W2a)
    have H: "((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((-r x l\<rightarrow> -r z) r\<rightarrow> -r z) = ((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((z r\<rightarrow> x) r\<rightarrow> -r z)"
      by (simp add: C5_a)
    have I: "((z r\<rightarrow> y) r\<rightarrow> -r z) r\<rightarrow> ((z r\<rightarrow> x) r\<rightarrow> -r z) = 1"
      apply (simp add: order_r [THEN sym])
      apply (rule P13_b)
      apply (rule P14_b)
      by (simp add: A)
    show "(z r\<rightarrow> y) r\<rightarrow> -r z \<le> -r x"
      by (simp add: order_r E F G H I)
    next
    qed

context pseudo_wajsberg_algebra
begin
lemma inf_a_b: "inf_a = inf_b"
  apply (simp add: fun_eq_iff)
  apply clarify
  apply (rule antisym)
  by simp_all



end
end
