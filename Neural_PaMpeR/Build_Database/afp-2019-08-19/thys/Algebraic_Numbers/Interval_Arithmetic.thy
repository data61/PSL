(*  
    Author:      Sebastiaan Joosten 
                 René Thiemann
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Interval Arithmetic\<close>

text \<open>We provide basic interval arithmetic operations for real and complex intervals.
  As application we prove that complex polynomial evaluation is continuous w.r.t.
  interval arithmetic. To be more precise, if an interval sequence converges to some 
  element $x$, then the interval polynomial evaluation of $f$ tends to $f(x)$.\<close>
  
theory Interval_Arithmetic
imports
  Algebraic_Numbers_Prelim (* for ipoly *)
begin

text \<open>Intervals\<close>

datatype ('a) interval = Interval (lower: 'a) (upper: 'a)

hide_const(open) lower upper

definition to_interval where "to_interval a \<equiv> Interval a a"

abbreviation of_int_interval :: "int \<Rightarrow> 'a :: ring_1 interval" where
  "of_int_interval x \<equiv> to_interval (of_int x)" 


subsection \<open>Syntactic Class Instantiations\<close>

instantiation interval :: ("zero") zero begin
  definition zero_interval where "0 \<equiv> Interval 0 0"
  instance..
end

instantiation interval :: (one) one begin
  definition "1 = Interval 1 1"
  instance..
end

instantiation interval :: (plus) plus begin
  fun plus_interval where "Interval lx ux + Interval ly uy = Interval (lx + ly) (ux + uy)"
  instance..
end

instantiation interval :: (uminus) uminus begin
  fun uminus_interval where "- Interval l u = Interval (-u) (-l)"
  instance..
end

instantiation interval :: (minus) minus begin
  fun minus_interval where "Interval lx ux - Interval ly uy = Interval (lx - uy) (ux - ly)"
  instance..
end

instantiation interval :: ("{ord,times}") times begin
  fun times_interval where
  "Interval lx ux * Interval ly uy =
     (let x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy
      in Interval (min x1 (min x2 (min x3 x4))) (max x1 (max x2 (max x3 x4))))"
  instance..
end

instantiation interval :: ("{ord,times,inverse}") "inverse" begin
  fun inverse_interval where
    "inverse (Interval l u) = Interval (inverse u) (inverse l)"
  definition divide_interval :: "'a interval \<Rightarrow> _" where
    "divide_interval X Y = X  * (inverse Y)"
  instance..
end

subsection \<open>Class Instantiations\<close>

instance interval :: (semigroup_add) semigroup_add
proof
  fix a b c :: "'a interval"
  show "a + b + c = a + (b + c)" by (cases a, cases b, cases c, auto simp: ac_simps)
qed

instance interval :: (monoid_add) monoid_add
proof
  fix a :: "'a interval"
  show "0 + a = a" by (cases a, auto simp: zero_interval_def)
  show "a + 0 = a" by (cases a, auto simp: zero_interval_def)
qed

instance interval :: (ab_semigroup_add) ab_semigroup_add
proof
  fix a b :: "'a interval"
  show "a + b = b + a" by (cases a, cases b, auto simp: ac_simps)
qed

instance interval :: (comm_monoid_add) comm_monoid_add by (intro_classes, auto)

text \<open>Intervals do not form an additive group, but satisfy some properties.\<close>

lemma interval_uminus_zero[simp]:
  shows "-(0 :: 'a :: group_add interval) = 0"
  by (simp add: zero_interval_def)

lemma interval_diff_zero[simp]:
  fixes a :: "'a :: cancel_comm_monoid_add interval"
  shows "a - 0 = a" by (cases a, simp add: zero_interval_def)

text \<open>Without type invariant, intervals do not form a multiplicative monoid,
 but satisfy some properties.\<close>

instance interval :: ("{linorder,mult_zero}") mult_zero
proof
  fix a :: "'a interval"
  show "a * 0 = 0" "0 * a = 0" by (atomize(full), cases a, auto simp: zero_interval_def)
qed

subsection \<open>Membership\<close>

fun in_interval :: "'a :: order \<Rightarrow> 'a interval \<Rightarrow> bool" ("(_/ \<in>\<^sub>i _)" [51, 51] 50) where
  "y \<in>\<^sub>i Interval lx ux = (lx \<le> y \<and> y \<le> ux)" 

lemma in_interval_to_interval[intro!]: "a \<in>\<^sub>i to_interval a"
  by (auto simp: to_interval_def)

lemma plus_in_interval:
  fixes x y :: "'a :: ordered_comm_monoid_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> y \<in>\<^sub>i Y \<Longrightarrow> x + y \<in>\<^sub>i X + Y"
  by (cases X, cases Y, auto dest:add_mono)

lemma uminus_in_interval:
  fixes x :: "'a :: ordered_ab_group_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> -x \<in>\<^sub>i -X"
  by (cases X, auto)

lemma minus_in_interval:
  fixes x y :: "'a :: ordered_ab_group_add"
  shows "x \<in>\<^sub>i X \<Longrightarrow> y \<in>\<^sub>i Y \<Longrightarrow> x - y \<in>\<^sub>i X - Y"
  by (cases X, cases Y, auto dest:diff_mono)

lemma times_in_interval:
  fixes x y :: "'a :: linordered_ring"
  assumes "x \<in>\<^sub>i X" "y \<in>\<^sub>i Y"
  shows "x * y \<in>\<^sub>i X * Y"
proof -
  obtain X1 X2 where X:"Interval X1 X2 = X" by (cases X,auto)
  obtain Y1 Y2 where Y:"Interval Y1 Y2 = Y" by (cases Y,auto)
  from assms X Y have assms: "X1 \<le> x" "x \<le> X2" "Y1 \<le> y" "y \<le> Y2" by auto
  have "(X1 * Y1 \<le> x * y \<or> X1 * Y2 \<le> x * y \<or> X2 * Y1 \<le> x * y \<or> X2 * Y2 \<le> x * y) \<and>
        (X1 * Y1 \<ge> x * y \<or> X1 * Y2 \<ge> x * y \<or> X2 * Y1 \<ge> x * y \<or> X2 * Y2 \<ge> x * y)"
  proof (cases x "0::'a" rule: linorder_cases)
    case x0: less
    show ?thesis
    proof (cases "y < 0")
      case y0: True
      from y0 x0 assms have "x * y \<le> X1 * y" by (intro mult_right_mono_neg, auto)
      also from x0 y0 assms have "X1 * y \<le> X1 * Y1" by (intro mult_left_mono_neg, auto)
      finally have 1: "x * y \<le> X1 * Y1".
      show ?thesis proof(cases "X2 \<le> 0")
        case True
        with assms have "X2 * Y2 \<le> X2 * y" by (auto intro: mult_left_mono_neg)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono_neg)
        finally have "X2 * Y2 \<le> x * y".
        with 1 show ?thesis by auto
      next
        case False
        with assms have "X2 * Y1 \<le> X2 * y" by (auto intro: mult_left_mono)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono_neg)
        finally have "X2 * Y1 \<le> x * y".
        with 1 show ?thesis by auto
      qed
    next
      case False
      then have y0: "y \<ge> 0" by auto
      from x0 y0 assms have "X1 * Y2 \<le> x * Y2" by (intro mult_right_mono, auto)
      also from y0 x0 assms have "... \<le> x * y" by (intro mult_left_mono_neg, auto)
      finally have 1: "X1 * Y2 \<le> x * y".
      show ?thesis
      proof(cases "X2 \<le> 0")
        case X2: True
        from assms y0 have "x * y \<le> X2 * y" by (intro mult_right_mono)
        also from assms X2 have "... \<le> X2 * Y1" by (auto intro: mult_left_mono_neg)
        finally have "x * y \<le> X2 * Y1".
        with 1 show ?thesis by auto
      next
        case X2: False
        from assms y0 have "x * y \<le> X2 * y" by (intro mult_right_mono)
        also from assms X2 have "... \<le> X2 * Y2" by (auto intro: mult_left_mono)
        finally have "x * y \<le> X2 * Y2".
        with 1 show ?thesis by auto
      qed
    qed
  next
    case [simp]: equal
    with assms show ?thesis by (cases "Y2 \<le> 0", auto intro:mult_sign_intros)
  next
    case x0: greater
    show ?thesis
    proof (cases "y < 0")
      case y0: True
      from x0 y0 assms have "X2 * Y1 \<le> X2 * y" by (intro mult_left_mono, auto)
      also from y0 x0 assms have "X2 * y \<le> x * y" by (intro mult_right_mono_neg, auto)
      finally have 1: "X2 * Y1 \<le> x * y".
      show ?thesis
      proof(cases "Y2 \<le> 0")
        case Y2: True
        from x0 assms have "x * y \<le> x * Y2" by (auto intro: mult_left_mono)
        also from assms Y2 have "... \<le> X1 * Y2" by (auto intro: mult_right_mono_neg)
        finally have "x * y \<le> X1 * Y2".
        with 1 show ?thesis by auto
      next
        case Y2: False
        from x0 assms have "x * y \<le> x * Y2" by (auto intro: mult_left_mono)
        also from assms Y2 have "... \<le> X2 * Y2" by (auto intro: mult_right_mono)
        finally have "x * y \<le> X2 * Y2".
        with 1 show ?thesis by auto
      qed
    next
      case y0: False
      from x0 y0 assms have "x * y \<le> X2 * y" by (intro mult_right_mono, auto)
      also from y0 x0 assms have "... \<le> X2 * Y2" by (intro mult_left_mono, auto)
      finally have 1: "x * y \<le> X2 * Y2".
      show ?thesis
      proof(cases "X1 \<le> 0")
        case True
        with assms have "X1 * Y2 \<le> X1 * y" by (auto intro: mult_left_mono_neg)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono)
        finally have "X1 * Y2 \<le> x * y".
        with 1 show ?thesis by auto
      next
        case False
        with assms have "X1 * Y1 \<le> X1 * y" by (auto intro: mult_left_mono)
        also from assms y0 have "... \<le> x * y" by (auto intro: mult_right_mono)
        finally have "X1 * Y1 \<le> x * y".
        with 1 show ?thesis by auto
      qed
    qed
  qed
  hence min:"min (X1 * Y1) (min (X1 * Y2) (min (X2 * Y1) (X2 * Y2))) \<le> x * y"
    and max:"x * y \<le> max (X1 * Y1) (max (X1 * Y2) (max (X2 * Y1) (X2 * Y2)))"
    by (auto simp:min_le_iff_disj le_max_iff_disj)
  show ?thesis using min max X Y by (auto simp: Let_def)
qed

subsection \<open>Convergence\<close>

definition interval_tendsto :: "(nat \<Rightarrow> 'a :: topological_space interval) \<Rightarrow> 'a \<Rightarrow> bool"
  (infixr "\<longlonglongrightarrow>\<^sub>i" 55) where
  "(X \<longlonglongrightarrow>\<^sub>i x) \<equiv> ((interval.upper \<circ> X) \<longlonglongrightarrow> x) \<and> ((interval.lower \<circ> X) \<longlonglongrightarrow> x)"

lemma interval_tendstoI[intro]:
  assumes "(interval.upper \<circ> X) \<longlonglongrightarrow> x" and "(interval.lower \<circ> X) \<longlonglongrightarrow> x"
  shows "X \<longlonglongrightarrow>\<^sub>i x"
  using assms by (auto simp:interval_tendsto_def)

lemma const_interval_tendsto: "(\<lambda>i. to_interval a) \<longlonglongrightarrow>\<^sub>i a"
  by (auto simp: o_def to_interval_def)

lemma interval_tendsto_0: "(\<lambda>i. 0) \<longlonglongrightarrow>\<^sub>i 0"
  by (auto simp: o_def zero_interval_def)

lemma plus_interval_tendsto:
  fixes x y :: "'a :: topological_monoid_add"
  assumes "X \<longlonglongrightarrow>\<^sub>i x" "Y \<longlonglongrightarrow>\<^sub>i y"
  shows "(\<lambda> i. X i + Y i) \<longlonglongrightarrow>\<^sub>i x + y"
proof -
  have *: "X i + Y i = Interval (interval.lower (X i) + interval.lower (Y i)) (interval.upper (X i) + interval.upper (Y i))" for i
     by (cases "X i"; cases "Y i", auto)
  from assms show ?thesis unfolding * interval_tendsto_def o_def by (auto intro: tendsto_intros)
qed

lemma uminus_interval_tendsto:
  fixes x :: "'a :: topological_group_add"
  assumes "X \<longlonglongrightarrow>\<^sub>i x"
  shows "(\<lambda>i. - X i) \<longlonglongrightarrow>\<^sub>i -x"
proof-
  have *: "- X i = Interval (- interval.upper (X i)) (- interval.lower (X i))" for i
    by (cases "X i", auto)
  from assms show ?thesis unfolding o_def * interval_tendsto_def by (auto intro: tendsto_intros)
qed

lemma minus_interval_tendsto:
  fixes x y :: "'a :: topological_group_add"
  assumes "X \<longlonglongrightarrow>\<^sub>i x" "Y \<longlonglongrightarrow>\<^sub>i y"
  shows "(\<lambda> i. X i - Y i) \<longlonglongrightarrow>\<^sub>i x - y"
proof -
  have *: "X i - Y i = Interval (interval.lower (X i) - interval.upper (Y i)) (interval.upper (X i) - interval.lower (Y i))" for i
    by (cases "X i"; cases "Y i", auto)
  from assms show ?thesis unfolding o_def * interval_tendsto_def by (auto intro: tendsto_intros)
qed

lemma times_interval_tendsto:
  fixes x y :: "'a :: {linorder_topology, real_normed_algebra}"
  assumes "X \<longlonglongrightarrow>\<^sub>i x" "Y \<longlonglongrightarrow>\<^sub>i y"
  shows "(\<lambda> i. X i * Y i) \<longlonglongrightarrow>\<^sub>i x * y"
proof -
  have *: "(interval.lower (X i * Y i)) = (
    let lx = (interval.lower (X i)); ux = (interval.upper (X i));
        ly = (interval.lower (Y i)); uy = (interval.upper (Y i)); 
        x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy in 
      (min x1 (min x2 (min x3 x4))))" "(interval.upper (X i * Y i)) = (
    let lx = (interval.lower (X i)); ux = (interval.upper (X i));
        ly = (interval.lower (Y i)); uy = (interval.upper (Y i)); 
      x1 = lx * ly; x2 = lx * uy; x3 = ux * ly; x4 = ux * uy in 
      (max x1 (max x2 (max x3 x4))))" for i
    by (cases "X i"; cases "Y i", auto simp: Let_def)+
  have "(\<lambda>i. (interval.lower (X i * Y i))) \<longlonglongrightarrow> min (x * y) (min (x * y) (min (x * y) (x *y)))" 
    using assms unfolding interval_tendsto_def * Let_def o_def
    by (intro tendsto_min tendsto_intros, auto)
  moreover 
  have "(\<lambda>i. (interval.upper (X i * Y i))) \<longlonglongrightarrow> max (x * y) (max (x * y) (max (x * y) (x *y)))" 
    using assms unfolding interval_tendsto_def * Let_def o_def
    by (intro tendsto_max tendsto_intros, auto)
  ultimately show ?thesis unfolding interval_tendsto_def o_def by auto
qed

lemma interval_tendsto_neq:
  fixes a b :: "real"
  assumes "(\<lambda> i. f i) \<longlonglongrightarrow>\<^sub>i a" and "a \<noteq> b" 
  shows "\<exists> n. \<not> b \<in>\<^sub>i f n" 
proof -
  let ?d = "norm (b - a) / 2" 
  from assms have d: "?d > 0" by auto
  from assms(1)[unfolded interval_tendsto_def] 
  have cvg: "(interval.lower o f) \<longlonglongrightarrow> a" "(interval.upper o f) \<longlonglongrightarrow> a" by auto
  from LIMSEQ_D[OF cvg(1) d] obtain n1 where 
    n1: "\<And> n. n \<ge> n1 \<Longrightarrow> norm ((interval.lower \<circ> f) n - a) < ?d " by auto
  from LIMSEQ_D[OF cvg(2) d] obtain n2 where
    n2: "\<And> n. n \<ge> n2 \<Longrightarrow> norm ((interval.upper \<circ> f) n - a) < ?d " by auto
  define n where "n = max n1 n2"  
  from n1[of n] n2[of n] have bnd: 
    "norm ((interval.lower \<circ> f) n - a) < ?d" 
    "norm ((interval.upper \<circ> f) n - a) < ?d" 
    unfolding n_def by auto
  show ?thesis by (rule exI[of _ n], insert bnd, cases "f n", auto,argo)
qed

subsection \<open>Complex Intervals\<close>

datatype complex_interval = Complex_Interval (Re_interval: "real interval") (Im_interval: "real interval")

definition in_complex_interval :: "complex \<Rightarrow> complex_interval \<Rightarrow> bool" ("(_/ \<in>\<^sub>c _)" [51, 51] 50) where
  "y \<in>\<^sub>c x \<equiv> (case x of Complex_Interval r i \<Rightarrow> Re y \<in>\<^sub>i r \<and> Im y \<in>\<^sub>i i)" 
      
instantiation complex_interval :: comm_monoid_add begin

  definition "0 \<equiv> Complex_Interval 0 0"

  fun plus_complex_interval :: "complex_interval \<Rightarrow> complex_interval \<Rightarrow> complex_interval" where
    "Complex_Interval rx ix + Complex_Interval ry iy = Complex_Interval (rx + ry) (ix + iy)" 

  instance
  proof
    fix a b c :: complex_interval
    show "a + b + c = a + (b + c)" by (cases a, cases b, cases c, simp add: ac_simps)
    show "a + b = b + a" by (cases a, cases b, simp add: ac_simps)
    show "0 + a = a" by (cases a, simp add: ac_simps zero_complex_interval_def)
  qed
end

lemma plus_complex_interval: "x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> x + y \<in>\<^sub>c X + Y"
  unfolding in_complex_interval_def using plus_in_interval by (cases X, cases Y, auto)

definition of_int_complex_interval :: "int \<Rightarrow> complex_interval" where
  "of_int_complex_interval x = Complex_Interval (of_int_interval x) 0" 

lemma of_int_complex_interval_0[simp]: "of_int_complex_interval 0 = 0"
  by (simp add: of_int_complex_interval_def zero_complex_interval_def to_interval_def zero_interval_def)

lemma of_int_complex_interval: "of_int i \<in>\<^sub>c of_int_complex_interval i" 
  unfolding in_complex_interval_def of_int_complex_interval_def
  by (auto simp: zero_complex_interval_def zero_interval_def)

instantiation complex_interval :: mult_zero begin

  fun times_complex_interval where
    "Complex_Interval rx ix * Complex_Interval ry iy =
     Complex_Interval (rx * ry - ix * iy) (rx * iy + ix * ry)"

  instance
  proof
    fix a :: complex_interval
    show "0 * a = 0" "a * 0 = 0" by (atomize(full), cases a, auto simp: zero_complex_interval_def)
  qed
end

instantiation complex_interval :: minus begin

  fun minus_complex_interval where
    "Complex_Interval R I - Complex_Interval R' I' = Complex_Interval (R-R') (I-I')"

  instance..

end

lemma times_complex_interval: "x \<in>\<^sub>c X \<Longrightarrow> y \<in>\<^sub>c Y \<Longrightarrow> x * y \<in>\<^sub>c X * Y"
  unfolding in_complex_interval_def
  by (cases X, cases Y, auto intro: times_in_interval minus_in_interval plus_in_interval)

definition ipoly_complex_interval :: "int poly \<Rightarrow> complex_interval \<Rightarrow> complex_interval" where
  "ipoly_complex_interval p x = fold_coeffs (\<lambda>a b. of_int_complex_interval a + x * b) p 0" 

lemma ipoly_complex_interval_0[simp]:
  "ipoly_complex_interval 0 x = 0"
  by (auto simp: ipoly_complex_interval_def)

lemma ipoly_complex_interval_pCons[simp]:
  "ipoly_complex_interval (pCons a p) x = of_int_complex_interval a + x * (ipoly_complex_interval p x)"
  by (cases "p = 0"; cases "a = 0", auto simp: ipoly_complex_interval_def)

lemma ipoly_complex_interval: assumes x: "x \<in>\<^sub>c X" 
  shows "ipoly p x \<in>\<^sub>c ipoly_complex_interval p X" 
proof -
  define xs where "xs = coeffs p"
  have 0: "in_complex_interval 0 0" (is "in_complex_interval ?Z ?z")
    unfolding in_complex_interval_def zero_complex_interval_def zero_interval_def by auto
  define Z where "Z = ?Z" 
  define z where "z = ?z" 
  from 0 have 0: "in_complex_interval Z z" unfolding Z_def z_def by auto
  note x = times_complex_interval[OF x]
  show ?thesis 
    unfolding poly_map_poly_code ipoly_complex_interval_def fold_coeffs_def 
      xs_def[symmetric] Z_def[symmetric] z_def[symmetric] using 0
    by (induct xs arbitrary: Z z, auto intro!: plus_complex_interval of_int_complex_interval x)
qed
  
definition complex_interval_tendsto (infix "\<longlonglongrightarrow>\<^sub>c" 55) where
  "C \<longlonglongrightarrow>\<^sub>c c \<equiv> ((Re_interval \<circ> C) \<longlonglongrightarrow>\<^sub>i Re c) \<and> ((Im_interval \<circ> C) \<longlonglongrightarrow>\<^sub>i Im c)"

lemma complex_interval_tendstoI[intro!]:
  "(Re_interval \<circ> C) \<longlonglongrightarrow>\<^sub>i Re c \<Longrightarrow> (Im_interval \<circ> C) \<longlonglongrightarrow>\<^sub>i Im c \<Longrightarrow> C \<longlonglongrightarrow>\<^sub>c c"
  by (simp add: complex_interval_tendsto_def)

lemma of_int_complex_interval_tendsto: "(\<lambda>i. of_int_complex_interval n) \<longlonglongrightarrow>\<^sub>c of_int n"
  by (auto simp: o_def of_int_complex_interval_def intro!:const_interval_tendsto interval_tendsto_0)

lemma Im_interval_plus: "Im_interval (A + B) = Im_interval A + Im_interval B" 
  by (cases A; cases B, auto)

lemma Re_interval_plus: "Re_interval (A + B) = Re_interval A + Re_interval B" 
  by (cases A; cases B, auto)

lemma Im_interval_minus: "Im_interval (A - B) = Im_interval A - Im_interval B" 
  by (cases A; cases B, auto)

lemma Re_interval_minus: "Re_interval (A - B) = Re_interval A - Re_interval B" 
  by (cases A; cases B, auto)
    
lemma Re_interval_times: "Re_interval (A * B) = Re_interval A * Re_interval B - Im_interval A * Im_interval B" 
  by (cases A; cases B, auto)

lemma Im_interval_times: "Im_interval (A * B) = Re_interval A * Im_interval B + Im_interval A * Re_interval B" 
  by (cases A; cases B, auto)

lemma plus_complex_interval_tendsto:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i + B i) \<longlonglongrightarrow>\<^sub>c a + b" 
  unfolding complex_interval_tendsto_def
  by (auto intro!: plus_interval_tendsto simp: o_def Re_interval_plus Im_interval_plus)

lemma minus_complex_interval_tendsto:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i - B i) \<longlonglongrightarrow>\<^sub>c a - b" 
  unfolding complex_interval_tendsto_def
  by (auto intro!: minus_interval_tendsto simp: o_def Re_interval_minus Im_interval_minus)

lemma times_complex_interval_tendsto:
  "A \<longlonglongrightarrow>\<^sub>c a \<Longrightarrow> B \<longlonglongrightarrow>\<^sub>c b \<Longrightarrow> (\<lambda>i. A i * B i) \<longlonglongrightarrow>\<^sub>c a * b"
  unfolding complex_interval_tendsto_def
  by (auto intro!: minus_interval_tendsto times_interval_tendsto plus_interval_tendsto 
    simp: o_def Re_interval_times Im_interval_times)

lemma ipoly_complex_interval_tendsto:
  assumes "C \<longlonglongrightarrow>\<^sub>c c"
  shows "(\<lambda>i. ipoly_complex_interval p (C i)) \<longlonglongrightarrow>\<^sub>c ipoly p c"
proof(induct p)
  case 0
  show ?case by (auto simp: o_def zero_complex_interval_def zero_interval_def complex_interval_tendsto_def)
next
  case (pCons a p)
  show ?case
    apply (unfold ipoly_complex_interval_pCons of_int_hom.map_poly_pCons_hom poly_pCons)
    apply (intro plus_complex_interval_tendsto times_complex_interval_tendsto assms pCons of_int_complex_interval_tendsto)
    done
qed

lemma complex_interval_tendsto_neq: assumes "(\<lambda> i. f i) \<longlonglongrightarrow>\<^sub>c a" 
  and "a \<noteq> b" 
shows "\<exists> n. \<not> b \<in>\<^sub>c f n" 
proof -
  from assms(1)[unfolded complex_interval_tendsto_def o_def]
  have cvg: "(\<lambda>x. Re_interval (f x)) \<longlonglongrightarrow>\<^sub>i Re a" "(\<lambda>x. Im_interval (f x)) \<longlonglongrightarrow>\<^sub>i Im a" by auto
  from assms(2) have "Re a \<noteq> Re b \<or> Im a \<noteq> Im b"
    using complex.expand by blast
  thus ?thesis
  proof
    assume "Re a \<noteq> Re b" 
    from interval_tendsto_neq[OF cvg(1) this] show ?thesis
      unfolding in_complex_interval_def by (metis (no_types, lifting) complex_interval.case_eq_if)
  next
    assume "Im a \<noteq> Im b" 
    from interval_tendsto_neq[OF cvg(2) this] show ?thesis
      unfolding in_complex_interval_def by (metis (no_types, lifting) complex_interval.case_eq_if)
  qed
qed
  
end
