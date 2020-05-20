theory Taylor_Models
  imports
    "Horner_Eval"
    "Polynomial_Expression_Additional"
    "Taylor_Models_Misc"
    "HOL-Decision_Procs.Approximation"
    "HOL-Library.Function_Algebras"
    "HOL-Library.Set_Algebras"
    "Affine_Arithmetic.Straight_Line_Program"
    "Affine_Arithmetic.Affine_Approximation"
begin

text \<open>TODO: get rid of float poly/float inteval and use real poly/real interval
  and data refinement?\<close>

section \<open>Multivariate Taylor Models\<close>

subsection \<open>Computing interval bounds on arithmetic expressions\<close>

text \<open>This is a wrapper around the "approx" function.
  It computes range bounds on floatarith expressions.\<close>
fun compute_bound_fa :: "nat \<Rightarrow> floatarith \<Rightarrow> float interval list \<Rightarrow> float interval option"
  where "compute_bound_fa prec f I = approx prec f (map Some I)"

lemma compute_bound_fa_correct:
  "interpret_floatarith f i \<in>\<^sub>r ivl"
  if "compute_bound_fa prec f I = Some ivl"
    "i all_in I"
  for i::"real list"
proof-
  have bounded: "bounded_by i (map Some I)"
    using that(2)
    unfolding bounded_by_def
    by (auto simp: bounds_of_interval_eq_lower_upper set_of_eq)
  from that have Some: "approx prec f (map Some I) = Some ivl"
    by (auto simp: lower_Interval upper_Interval min_def split: option.splits if_splits)
  from approx[OF bounded Some]
  show ?thesis by (auto simp: set_of_eq)
qed


subsection \<open>Definition of Taylor models and notion of rangeity\<close>

text \<open>Taylor models are a pair of a polynomial and an absolute error bound.\<close>
datatype taylor_model = TaylorModel (tm_poly: "float poly") (tm_bound: "float interval")

text \<open>Taylor model for a real valuation of variables\<close>

primrec insertion :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a poly \<Rightarrow> 'a::{plus,zero,minus,uminus,times,one,power}"
where
  "insertion bs (C c) = c"
| "insertion bs (poly.Bound n) = bs n"
| "insertion bs (Neg a) = - insertion bs a"
| "insertion bs (poly.Add a b) = insertion bs a + insertion bs b"
| "insertion bs (Sub a b) = insertion bs a - insertion bs b"
| "insertion bs (Mul a b) = insertion bs a * insertion bs b"
| "insertion bs (Pw t n) = insertion bs t ^ n"
| "insertion bs (CN c n p) = insertion bs c + (bs n) * insertion bs p"

definition range_tm :: "(nat \<Rightarrow> real) \<Rightarrow> taylor_model \<Rightarrow> real interval" where
"range_tm e tm = interval_of (insertion e (tm_poly tm)) + real_interval (tm_bound tm)"

lemma Ipoly_num_params_cong: "Ipoly xs p = Ipoly ys p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs ! i = ys ! i"
  using that
  by (induction p; auto)

lemma insertion_num_params_cong: "insertion e p = insertion f p"
  if "\<And>i. i < num_params p \<Longrightarrow> e i = f i"
  using that
  by (induction p; auto)

lemma insertion_eq_IpolyI: "insertion xs p = Ipoly ys p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs i = ys ! i"
  using that
  by (induction p; auto)

lemma Ipoly_eq_insertionI: "Ipoly ys p = insertion xs p"
  if "\<And>i. i < num_params p \<Longrightarrow> xs i = ys ! i"
  using that
  by (induction p; auto)

lemma range_tmI:
  "x \<in>\<^sub>i range_tm e tm"
  if x: "x \<in>\<^sub>i interval_of (insertion e ((tm_poly tm))) + real_interval (tm_bound tm)"
  for e::"nat\<Rightarrow>real"
  by (auto simp: range_tm_def x)

lemma range_tmD:
  "x \<in>\<^sub>i interval_of (insertion e (tm_poly tm)) + real_interval (tm_bound tm)"
  if "x \<in>\<^sub>i range_tm e tm"
  for e::"nat\<Rightarrow>real"
  using that
  by (auto simp: range_tm_def)


subsection \<open>Interval bounds for Taylor models\<close>

text \<open>Bound a polynomial by simply approximating it with interval arguments.\<close>
fun compute_bound_poly :: "nat \<Rightarrow> float interval poly \<Rightarrow> (float interval list) \<Rightarrow> (float interval list) \<Rightarrow> float interval" where
  "compute_bound_poly prec (poly.C f) I a = f"
| "compute_bound_poly prec (poly.Bound n) I a = round_interval prec (I ! n - (a ! n))"
| "compute_bound_poly prec (poly.Add p q) I a =
    round_interval prec (compute_bound_poly prec p I a + compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Sub p q) I a =
    round_interval prec (compute_bound_poly prec p I a - compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Mul p q) I a =
    mult_float_interval prec (compute_bound_poly prec p I a) (compute_bound_poly prec q I a)"
| "compute_bound_poly prec (poly.Neg p) I a = -compute_bound_poly prec p I a"
| "compute_bound_poly prec (poly.Pw p n) I a = power_float_interval prec n (compute_bound_poly prec p I a)"
| "compute_bound_poly prec (poly.CN p n q) I a =
    round_interval prec (compute_bound_poly prec p I a +
      mult_float_interval prec (round_interval prec (I ! n - (a ! n))) (compute_bound_poly prec q I a))"

text \<open>Bounds on Taylor models are simply a bound on its polynomial, widened by the approximation error.\<close>
fun compute_bound_tm :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> float interval"
  where "compute_bound_tm prec I a (TaylorModel p e) = compute_bound_poly prec p I a + e"

lemma compute_bound_tm_def:
  "compute_bound_tm prec I a tm = compute_bound_poly prec (tm_poly tm) I a + (tm_bound tm)"
  by (cases tm) auto

lemma real_of_float_in_real_interval_of[intro, simp]: "real_of_float x \<in>\<^sub>r X" if "x \<in>\<^sub>i X"
  using that
  by (auto simp: set_of_eq)

lemma in_set_of_round_interval[intro, simp]:
  "x \<in>\<^sub>r round_interval prec X" if "x \<in>\<^sub>r X"
  using round_ivl_correct[of X prec] that
  by (auto simp: set_of_eq)

lemma in_set_real_minus_interval[intro, simp]:
  "x - y \<in>\<^sub>r X - Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  using that
  by (auto simp: set_of_eq)

lemma real_interval_plus: "real_interval (a + b) = real_interval a + real_interval b"
  by (simp add: interval_eqI)

lemma real_interval_uminus: "real_interval (- b) = - real_interval b"
  by (simp add: interval_eqI)

lemma real_interval_of: "real_interval (interval_of b) = interval_of b"
  by (simp add: interval_eqI)

lemma real_interval_minus: "real_interval (a - b) = real_interval a - real_interval b"
  using real_interval_plus[of a "-b"] real_interval_uminus[of b]
  by (auto simp: interval_eq_iff)

lemma in_set_real_plus_interval[intro, simp]:
  "x + y \<in>\<^sub>r X + Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  using that
  by (auto simp: set_of_eq)

lemma in_set_neg_plus_interval[intro, simp]:
  "- y \<in>\<^sub>r - Y" if "y \<in>\<^sub>r Y"
  using that
  by (auto simp: set_of_eq)

lemma in_set_real_times_interval[intro, simp]:
  "x * y \<in>\<^sub>r X * Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  using that
  by (auto simp: real_interval_times intro!: times_in_intervalI)

lemma real_interval_one: "real_interval 1 = 1"
  by (simp add: interval_eqI)

lemma real_interval_zero: "real_interval 0 = 0"
  by (simp add: interval_eqI)

lemma real_interval_power: "real_interval (a ^ b) = real_interval a ^ b"
  by (induction b arbitrary: a)
    (auto simp: real_interval_times real_interval_one)

lemma in_set_real_power_interval[intro, simp]:
  "x ^ n \<in>\<^sub>r X ^ n" if "x \<in>\<^sub>r X"
  using that
  by (auto simp: real_interval_power intro!: set_of_power_mono)

lemma power_float_interval_real_interval[intro, simp]:
  "x ^ n \<in>\<^sub>r power_float_interval prec n X" if "x \<in>\<^sub>r X"
  by (auto simp: real_interval_power that intro!: power_float_intervalI)

lemma in_set_mult_float_interval[intro, simp]:
  "x * y \<in>\<^sub>r mult_float_interval prec X Y" if "x \<in>\<^sub>r X" "y \<in>\<^sub>r Y"
  using mult_float_interval[of X Y] in_set_real_times_interval[OF that] that(1) that(2)
  by blast

lemma in_set_real_minus_swapI: "e i \<in>\<^sub>r I ! i - a ! i"
  if "x - e i \<in>\<^sub>r a ! i" "x \<in>\<^sub>r I ! i"
  using that
  by (auto simp: set_of_eq)

definition develops_at_within::"(nat \<Rightarrow> real) \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> bool"
  where "develops_at_within e a I \<longleftrightarrow> (a all_subset I) \<and> (\<forall>i < length I. e i \<in>\<^sub>r I ! i - a ! i)"

lemma develops_at_withinI:
  assumes all_in: "a all_subset I"
  assumes e: "\<And>i. i < length I \<Longrightarrow> e i \<in>\<^sub>r I ! i - a ! i"
  shows "develops_at_within e a I"
  using assms by (auto simp: develops_at_within_def)

lemma develops_at_withinD:
  assumes "develops_at_within e a I"
  shows "a all_subset I"
    "\<And>i. i < length I \<Longrightarrow> e i \<in>\<^sub>r I ! i - a ! i"
  using assms by (auto simp: develops_at_within_def)

lemma compute_bound_poly_correct:
  fixes p::"float poly"
  assumes "num_params p \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "insertion e (p::real poly) \<in>\<^sub>r compute_bound_poly prec (map_poly interval_of p) I a"
  using assms(1)
proof (induction p)
  case (C x)
  then show ?case by auto
next
  case (Bound i)
  then show ?case
    using dev
    by (auto simp: develops_at_within_def)
next
  case (Add p1 p2)
  then show ?case by force
next
  case (Sub p1 p2)
  then show ?case by force
next
  case (Mul p1 p2)
  then show ?case by force
next
  case (Neg p)
  then show ?case by force
next
  case (Pw p x2a)
  then show ?case by force
next
  case (CN p1 i p2)
  then show ?case
    using dev
    by (auto simp: develops_at_within_def)
qed

lemma compute_bound_tm_correct:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes n: "num_params (tm_poly t) \<le> length I"
  assumes dev: "develops_at_within e a I"
  assumes x0: "x0 \<in>\<^sub>i range_tm e t"
  shows "x0 \<in>\<^sub>r compute_bound_tm prec I a t"
proof -
  let ?I = "insertion e (tm_poly t)"
  have "x0 = ?I + (x0 - ?I)" by simp
  also have "\<dots> \<in>\<^sub>r compute_bound_tm prec I a t"
    unfolding compute_bound_tm_def
    apply (rule in_set_real_plus_interval)
     apply (rule compute_bound_poly_correct)
        apply (rule assms)
       apply (rule dev)
    using range_tmD[OF x0]
    by (auto simp: set_of_eq)
  finally show "x0 \<in>\<^sub>r compute_bound_tm prec I a t" .
qed

lemma compute_bound_tm_correct_subset:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes n: "num_params (tm_poly t) \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "set_of (range_tm e t) \<subseteq> set_of (real_interval (compute_bound_tm prec I a t))"
  using assms
  by (auto intro!: compute_bound_tm_correct)

lemma compute_bound_poly_mono:
  assumes "num_params p \<le> length I"
  assumes mem: "I all_subset J" "a all_subset I"
  shows "set_of (compute_bound_poly prec p I a) \<subseteq> set_of (compute_bound_poly prec p J a)"
  using assms(1)
proof (induction p arbitrary: a)
  case (C x)
  then show ?case by auto
next
  case (Bound x)
  then show ?case using mem
    by (simp add: round_interval_mono set_of_sub_inc)
next
  case (Add p1 p2)
  then show ?case using mem
    by (simp add: round_interval_mono set_of_add_inc)
next
  case (Sub p1 p2)
  then show ?case using mem
    by (simp add: round_interval_mono set_of_sub_inc)
next
  case (Mul p1 p2)
  then show ?case using mem
    by (simp add: round_interval_mono mult_float_interval_mono)
next
  case (Neg p)
  then show ?case using mem
    by (simp add: round_interval_mono set_of_neg_inc)
next
  case (Pw p x2a)
  then show ?case using mem
    by (simp add: power_float_interval_mono)
next
  case (CN p1 x2a p2)
  then show ?case using mem
    by (simp add: round_interval_mono mult_float_interval_mono
        set_of_add_inc set_of_sub_inc)
qed

lemma compute_bound_tm_mono:
  fixes I :: "float interval list" and f :: "real list \<Rightarrow> real"
  assumes "num_params (tm_poly t) \<le> length I"
  assumes "I all_subset J"
  assumes "a all_subset I"
  shows "set_of (compute_bound_tm prec I a t) \<subseteq> set_of (compute_bound_tm prec J a t)"
  apply (simp add: compute_bound_tm_def)
  apply (rule set_of_add_inc_left)
  apply (rule compute_bound_poly_mono)
  using assms
  by (auto simp: set_of_eq)


subsection \<open>Computing taylor models for basic, univariate functions\<close>

definition tm_const :: "float \<Rightarrow> taylor_model"
  where "tm_const c = TaylorModel (poly.C c) 0"

context includes floatarith_notation begin

definition tm_pi :: "nat \<Rightarrow> taylor_model"
  where "tm_pi prec = (
  let pi_ivl = the (compute_bound_fa prec Pi [])
  in TaylorModel (poly.C (mid pi_ivl)) (centered pi_ivl)
)"

lemma zero_real_interval[intro,simp]: "0 \<in>\<^sub>r 0"
  by (auto simp: set_of_eq)

lemma range_TM_tm_const[simp]: "range_tm e (tm_const c) = interval_of c"
  by (auto simp: range_tm_def real_interval_zero tm_const_def)

lemma num_params_tm_const[simp]: "num_params (tm_poly (tm_const c)) = 0"
  by (auto simp: tm_const_def)

lemma num_params_tm_pi[simp]: "num_params (tm_poly (tm_pi prec)) = 0"
  by (auto simp: tm_pi_def Let_def)

lemma range_tm_tm_pi: "pi \<in>\<^sub>i range_tm e (tm_pi prec)"
proof-
  have "\<And>prec. real_of_float (lb_pi prec) \<le> real_of_float (ub_pi prec)"
    using iffD1[OF atLeastAtMost_iff, OF pi_boundaries]
    using order_trans by auto
  then obtain ivl_pi where ivl_pi_def: "compute_bound_fa prec Pi [] = Some ivl_pi"
    by (simp add: approx.simps)
  show ?thesis
    unfolding range_tm_def Let_def
    using compute_bound_fa_correct[OF ivl_pi_def, of "[]"]
    by (auto simp: set_of_eq Let_def centered_def ivl_pi_def tm_pi_def
        simp del: compute_bound_fa.simps)
qed


subsubsection \<open>Derivations of floatarith expressions\<close>

text \<open>Compute the nth derivative of a floatarith expression\<close>
fun deriv :: "nat \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
  where "deriv v f 0 = f"
  | "deriv v f (Suc n) = DERIV_floatarith v (deriv v f n)"

lemma isDERIV_DERIV_floatarith:
  assumes "isDERIV v f vs"
  shows "isDERIV v (DERIV_floatarith v f) vs"
  using assms
proof(induction f)
  case (Power f m)
  then show ?case
    by (cases m) (auto simp: isDERIV_Power)
qed (simp_all add: numeral_eq_Suc add_nonneg_eq_0_iff )

lemma isDERIV_is_analytic:
  "isDERIV i (Taylor_Models.deriv i f n) xs"
  if "isDERIV i f xs"
  using isDERIV_DERIV_floatarith that
  by(induction n) auto

lemma deriv_correct:
  assumes "isDERIV i f (xs[i:=t])" "i < length xs"
  shows "((\<lambda>x. interpret_floatarith (deriv i f n) (xs[i:=x])) has_real_derivative interpret_floatarith (deriv i f (Suc n)) (xs[i:=t]))
    (at t within S)"
  apply(simp)
  apply (rule has_field_derivative_at_within)
  apply(rule DERIV_floatarith)
   apply fact
  apply (rule isDERIV_is_analytic)
  apply fact
  done

text \<open>Faster derivation for univariate functions, producing smaller terms and thus less over-approximation.\<close>
text \<open>TODO: Extend to Arctan, Log!\<close>
fun deriv_rec :: "floatarith \<Rightarrow> nat \<Rightarrow> floatarith"
  where "deriv_rec (Exp (Var 0)) _ = Exp (Var 0)"
  | "deriv_rec (Cos (Var 0)) n = (case n mod 4
         of 0 \<Rightarrow> Cos (Var 0)
         | Suc 0 \<Rightarrow> Minus (Sin (Var 0))
         | Suc (Suc 0) \<Rightarrow> Minus (Cos (Var 0))
         | Suc (Suc (Suc 0)) \<Rightarrow> Sin (Var 0))"
  | "deriv_rec (Inverse (Var 0)) n = (if n = 0 then Inverse (Var 0) else Mult (Num (fact n * (if n mod 2 = 0 then 1 else -1))) (Inverse (Power (Var 0) (Suc n))))"
  | "deriv_rec f n = deriv 0 f n"

lemma deriv_rec_correct:
  assumes "isDERIV 0 f (xs[0:=t])" "0 < length xs"
  shows "((\<lambda>x. interpret_floatarith (deriv_rec f n) (xs[0:=x])) has_real_derivative interpret_floatarith (deriv_rec f (Suc n)) (xs[0:=t])) (at t within S)"
  apply(cases "(f, n)" rule: deriv_rec.cases)
                      apply(safe)
  using assms deriv_correct[OF assms]
proof-
  assume "f = Cos (Var 0)"

  have n_mod_4_cases: "n mod 4 = 0 | n mod 4 = 1 | n mod 4 = 2 | n mod 4 = 3"
    by auto
  have Sin_sin: "(\<lambda>xs. interpret_floatarith (Sin (Var 0)) xs) = (\<lambda>xs. sin (xs!0))"
    by (simp add: )
  show "((\<lambda>x. interpret_floatarith (deriv_rec (Cos (Var 0)) n) (xs[0:=x])) has_real_derivative
         interpret_floatarith (deriv_rec (Cos (Var 0)) (Suc n)) (xs[0:=t]))
         (at t within S)"
    using n_mod_4_cases assms
    by (auto simp add: mod_Suc Sin_sin field_differentiable_minus
        intro!: derivative_eq_intros)
next
  assume f_def: "f = Inverse (Var 0)" and "isDERIV 0 f (xs[0:=t])"
  hence "t \<noteq> 0" using assms
    by simp
  {
    fix n::nat and x::real
    assume "x \<noteq> 0"
    moreover have "(n mod 2 = 0 \<and> Suc n mod 2 = 1) \<or> (n mod 2 = 1 \<and> Suc n mod 2 = 0)"
      by (cases n rule: parity_cases) auto
    ultimately have "interpret_floatarith (deriv_rec f n) (xs[0:=x]) = fact n * (-1::real)^n / (x^Suc n)"
      using assms by (auto simp add: f_def field_simps fact_real_float_equiv)
  }
  note closed_formula = this

  have "((\<lambda>x. inverse (x ^ Suc n)) has_real_derivative -real (Suc n) * inverse (t ^ Suc (Suc n))) (at t)"
    using DERIV_inverse_fun[OF DERIV_pow[where n="Suc n"], where s=UNIV]
    apply(rule iffD1[OF DERIV_cong_ev[OF refl], rotated 2])
    using \<open>t \<noteq> 0\<close>
    by (simp_all add: divide_simps)
  hence "((\<lambda>x. fact n * (-1::real)^n * inverse (x ^ Suc n)) has_real_derivative fact (Suc n) * (- 1) ^ Suc n / t ^ Suc (Suc n)) (at t)"
    apply(rule iffD1[OF DERIV_cong_ev, OF refl _ _ DERIV_cmult[where c="fact n * (-1::real)^n"], rotated 2])
    using \<open>t \<noteq> 0\<close>
    by (simp_all add: field_simps distrib_left)
  then show "((\<lambda>x. interpret_floatarith (deriv_rec (Inverse (Var 0)) n) (xs[0:=x])) has_real_derivative
         interpret_floatarith (deriv_rec (Inverse (Var 0)) (Suc n)) (xs[0:=t]))
         (at t within S)"
    apply -
    apply (rule has_field_derivative_at_within)
    apply(rule iffD1[OF DERIV_cong_ev[OF refl _ closed_formula[OF \<open>t \<noteq> 0\<close>, symmetric]], unfolded f_def, rotated 1])
     apply simp
    using assms
    by (simp, safe, simp_all add: fact_real_float_equiv inverse_eq_divide even_iff_mod_2_eq_zero)
qed (use assms in \<open>simp_all add: has_field_derivative_subset[OF DERIV_exp subset_UNIV]\<close>)

lemma deriv_rec_0_idem[simp]:
  shows "deriv_rec f 0 = f"
  by (cases "(f, 0::nat)" rule: deriv_rec.cases, simp_all)


subsubsection \<open>Computing Taylor models for arbitrary univariate expressions\<close> 

fun tmf_c :: "nat \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> nat \<Rightarrow> float interval option"
  where "tmf_c prec I f i = compute_bound_fa prec (Mult (deriv_rec f i) (Inverse (Num (fact i)))) I"
    \<comment> \<open>The interval coefficients of the Taylor polynomial,
   i.e. the real coefficients approximated by a float interval.\<close>

fun tmf_ivl_cs :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> float interval list option"
  where "tmf_ivl_cs prec ord I a f = those (map (tmf_c prec a f) [0..<ord] @ [tmf_c prec I f ord])"
    \<comment> \<open>Make a list of bounds on the n+1 coefficients, with the n+1-th coefficient bounding
   the remainder term of the Taylor-Lagrange formula.\<close>

fun tmf_polys :: "float interval list \<Rightarrow> float poly \<times> float interval poly"
  where "tmf_polys [] = (poly.C 0, poly.C 0)"
  | "tmf_polys (c # cs) = (
         let (pf, pi) = tmf_polys cs
         in (poly.CN (poly.C (mid c)) 0 pf, poly.CN (poly.C (centered c)) 0 pi)
       )"

fun tm_floatarith :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float list \<Rightarrow> floatarith \<Rightarrow> taylor_model option"
  where "tm_floatarith prec ord I a f = (
  map_option (\<lambda>cs. 
    let (pf, pi) = tmf_polys cs;
        _ = compute_bound_tm prec (List.map2 (-) I a);
        e = round_interval prec (Ipoly (List.map2 (-) I a) pi) \<comment> \<open>TODO: use \<open>compute_bound_tm\<close> here?!\<close>
    in TaylorModel pf e
  ) (tmf_ivl_cs prec ord I a f)
)" \<comment> \<open>Compute a Taylor model from an arbitrary, univariate floatarith expression, if possible.
   This is used to compute Taylor models for elemental functions like sin, cos, exp, etc.\<close>

term compute_bound_poly
lemma tmf_c_correct:
  fixes A::"float interval list" and I::"float interval" and f::floatarith and a::"real list"
  assumes "a all_in A"
  assumes "tmf_c prec A f i = Some I"
  shows "interpret_floatarith (deriv_rec f i) a / fact i \<in>\<^sub>r I"
  using compute_bound_fa_correct[OF assms(2)[unfolded tmf_c.simps], where i="a"] assms(1)
  by (simp add: divide_real_def fact_real_float_equiv)

lemma tmf_ivl_cs_length:
  assumes "tmf_ivl_cs prec n A a f = Some cs"
  shows "length cs = n + 1"
  by (simp add: Some_those_length[OF assms[unfolded tmf_ivl_cs.simps]])

lemma tmf_ivl_cs_correct:
  fixes A::"float interval list" and f::floatarith
  assumes "a all_in I"
  assumes "tmf_ivl_cs prec ord I a f = Some cs"
  shows "\<And>i. i < ord \<Longrightarrow> tmf_c prec (map interval_of a) f i = Some (cs!i)"
    and "tmf_c prec I f ord = Some (cs!ord)"
    and "length cs = Suc ord"
proof-
  from tmf_ivl_cs_length[OF assms(2)]
  show "tmf_c prec I f ord = Some (cs!ord)"
    by (metis Some_those_nth assms(2) diff_zero length_map length_upt less_add_one
        nth_append_length tmf_ivl_cs.simps)
next
  fix i assume "i < ord"
  have "Some (cs!i) = (map (tmf_c prec a f) [0..<ord] @ [tmf_c prec I f ord]) ! i"
    apply(rule Some_those_nth)
    using assms(2) tmf_ivl_cs_length \<open>i < ord\<close>
    by simp_all
  then show "tmf_c prec a f i = Some (cs!i)" 
    using \<open>i < ord\<close>
    by (simp add: nth_append)
next
  show "length cs = Suc ord"
    using assms
    by (auto simp: split_beta' those_eq_Some_iff list_eq_iff_nth_eq)
qed 

lemma Ipoly_fst_tmf_polys:
  "Ipoly xs (fst (tmf_polys z)) = (\<Sum>i<length z. xs ! 0 ^ i * (mid (z ! i)))"
  for xs::"real list"
proof (induction z)
  case (Cons z zs)
  show ?case
    unfolding list.size add_Suc_right sum.lessThan_Suc_shift
    by (auto simp: split_beta' Let_def nth_Cons Cons sum_distrib_left ac_simps)
qed simp

lemma insertion_fst_tmf_polys:
  "insertion e (fst (tmf_polys z)) = (\<Sum>i<length z. e 0 ^ i * (mid (z ! i)))"
  for e::"nat \<Rightarrow> real"
proof (induction z)
  case (Cons z zs)
  show ?case
    unfolding list.size add_Suc_right sum.lessThan_Suc_shift
    by (auto simp: split_beta' Let_def nth_Cons Cons sum_distrib_left ac_simps)
qed simp

lemma Ipoly_snd_tmf_polys:
  "set_of (horner_eval (real_interval o centered o nth z) x (length z)) \<subseteq> set_of (Ipoly [x] (map_poly real_interval (snd (tmf_polys z))))"
proof (induction z)
  case (Cons z zs)
  show ?case
    using Cons[THEN set_of_mul_inc_right]
    unfolding list.size add_Suc_right sum.lessThan_Suc_shift
    by (auto simp: split_beta' Let_def nth_Cons sum_distrib_left ac_simps
        elim!: plus_in_intervalE intro!: plus_in_intervalI)
qed (auto simp: real_interval_zero)

lemma zero_interval[intro,simp]: "0 \<in>\<^sub>i 0"
  by (simp add: set_of_eq)

lemma sum_in_intervalI: "sum f X \<in>\<^sub>i sum g X" if "\<And>x. x \<in> X \<Longrightarrow> f x \<in>\<^sub>i g x"
  for f :: "_ \<Rightarrow> 'a :: ordered_comm_monoid_add"
  using that
proof (induction X rule: infinite_finite_induct)
  case (insert x F)
  then show ?case
    by (auto intro!: plus_in_intervalI)
qed simp_all

lemma set_of_sum_subset: "set_of (sum f X) \<subseteq> set_of (sum g X)"
  if "\<And>x. x \<in> X \<Longrightarrow> set_of (f x) \<subseteq> set_of (g x)"
  for f :: "_\<Rightarrow>'a::linordered_ab_group_add interval"
  using that
  by (induction X rule: infinite_finite_induct) (simp_all add: set_of_add_inc)

lemma interval_of_plus: "interval_of (a + b) = interval_of a + interval_of b"
  by (simp add: interval_eqI)

lemma interval_of_uminus: "interval_of (- a) = - interval_of a"
  by (simp add: interval_eqI)

lemma interval_of_zero: "interval_of 0 = 0"
  by (simp add: interval_eqI)

lemma interval_of_sum: "interval_of (sum f X) = sum (\<lambda>x. interval_of (f x)) X"
  by (induction X rule: infinite_finite_induct) (auto simp: interval_of_plus interval_of_zero)

lemma interval_of_prod: "interval_of (a * b) = interval_of a * interval_of b"
  by (simp add: lower_times upper_times interval_eqI)

lemma in_set_of_interval_of[simp]: "x \<in>\<^sub>i (interval_of y) \<longleftrightarrow> x = y" for x y::"'a::order"
  by (auto simp: set_of_eq)

lemma real_interval_Ipoly: "real_interval (Ipoly xs p) = Ipoly (map real_interval xs) (map_poly real_interval p)"
  if "num_params p \<le> length xs"
  using that
  by (induction p)
    (auto simp: real_interval_plus real_interval_minus real_interval_times
      real_interval_uminus real_interval_power)

lemma num_params_tmf_polys1: "num_params (fst (tmf_polys z)) \<le> Suc 0"
  by (induction z) (auto simp: split_beta' Let_def)

lemma num_params_tmf_polys2: "num_params (snd (tmf_polys z)) \<le> Suc 0"
  by (induction z) (auto simp: split_beta' Let_def)

lemma set_of_real_interval_subset: "set_of (real_interval x) \<subseteq> set_of (real_interval y)"
  if "set_of x \<subseteq> set_of y"
  using that
  by (auto simp: set_of_eq)

theorem tm_floatarith:
  assumes t: "tm_floatarith prec ord I xs f = Some t"
  assumes a: "xs all_in I" and x: "x \<in>\<^sub>r I ! 0"
  assumes xs_ne: "xs \<noteq> []"
  assumes deriv: "\<And>x. x \<in>\<^sub>r I ! 0 \<Longrightarrow> isDERIV 0 f (xs[0 := x])"
  assumes "\<And>i. 0 < i \<Longrightarrow> i < length xs \<Longrightarrow> e i = real_of_float (xs ! i)"
  assumes diff_e: "(x - real_of_float (xs ! 0)) = e 0"
  shows "interpret_floatarith f (xs[0:=x]) \<in>\<^sub>i range_tm e t"
proof -
  from xs_ne a have I_ne[simp]: "I \<noteq> []" by auto
  have xs'_in: "xs[0 := x] all_in I"
    using a
    by (auto simp: nth_list_update x)
  from t obtain z where z: "tmf_ivl_cs prec ord I xs f = Some z"
    and tz: "tm_poly t = fst (tmf_polys z)"
    and tb: "tm_bound t = round_interval prec (Ipoly (List.map2 (-) I xs) (snd (tmf_polys z)))"
    using assms(1)
    by (cases t) (auto simp: those_eq_Some_iff split_beta' Let_def simp del: tmf_ivl_cs.simps)
  from tmf_ivl_cs_correct[OF a z(1)]
  have z_less: "i < ord \<Longrightarrow> tmf_c prec (map interval_of xs) f i = Some (z ! i)"
    and lz: "length z = Suc ord" "length z - 1 = ord"
    and z_ord: "tmf_c prec I f ord = Some (z ! ord)" for i
    by auto
  have rewr: "{..ord} = insert ord {..<ord}" by auto
  let ?diff = "\<lambda>(i::nat) (x::real). interpret_floatarith (deriv_rec f i) (xs[0:=x])"
  let ?c = "real_of_float (xs ! 0)"
  let ?n = "ord"
  let ?a = "real_of_float (lower (I!0))"
  let ?b = "real_of_float (upper (I!0))"
  let ?x = "x::real"
  let ?f = "\<lambda>x::real. interpret_floatarith f (xs[0 := x])"
  have 2: "?diff 0 = ?f" using \<open>xs \<noteq> []\<close>
    by (simp add: map_update)
  have 3: "\<forall>m t. m < ?n \<and> ?a \<le> t \<and> t \<le> ?b \<longrightarrow> (?diff m has_real_derivative ?diff (Suc m) t) (at t)"
    by (auto intro!: derivative_eq_intros deriv_rec_correct deriv simp: set_of_eq xs_ne)
  have 4: "?a \<le> ?c" "?c \<le> ?b"  "?a \<le> ?x" "?x \<le> ?b"
    using a xs_ne x
    by (force simp: set_of_eq)+

  define cr where "cr \<equiv> \<lambda>s m. if m < ord then ?diff m ?c / fact m - mid (z ! m)
                           else ?diff m s / fact ord - mid (z ! ord)"
  define ci where "ci \<equiv> \<lambda>i. real_interval (z ! i) - interval_of (real_of_float (mid (z ! i)))"

  have cr_ord: "cr x ord \<in>\<^sub>i ci ord"
    using tmf_c_correct[OF xs'_in z_ord]
    by (auto simp: ci_def set_of_eq cr_def)

  have enclosure: "(\<Sum>m<ord. cr s m * (x - (xs ! 0)) ^ m) + cr s ord * (x - (xs ! 0)) ^ ord
      \<in>\<^sub>r round_interval prec (Ipoly (List.map2 (-) I (map interval_of xs)) (snd (tmf_polys z)))"
    if cr_ord: "cr s ord \<in>\<^sub>i ci ord" for s
  proof -
    have "(\<Sum>m<ord. cr s m  * (x - xs!0) ^ m) + cr s ord * (x - xs!0) ^ ord =
        horner_eval (cr s) (x - xs!0) (Suc ord)"
      by (simp add: horner_eval_eq_setsum)
    also have "\<dots> \<in>\<^sub>i horner_eval ci (real_interval (I ! 0 - xs ! 0)) (Suc ord)"
    proof (rule horner_eval_interval)
      fix i assume "i < Suc ord"
      then consider "i < ord" | "i = ord" by arith
      then show "cr s i \<in>\<^sub>i ci i"
      proof cases
        case 1
        then show ?thesis 
          by (auto simp: cr_def ci_def not_less less_Suc_eq_le
              intro!: minus_in_intervalI tmf_c_correct[OF _ z_less])
            (metis in_set_of_interval_of list_update_id map_update nth_map real_interval_of)
      qed (simp add: cr_ord)
    qed (auto intro!: minus_in_intervalI simp: real_interval_minus x)
    also have "\<dots> = set_of (horner_eval (real_interval o centered \<circ> (!) z)
      (real_interval (I ! 0 - xs ! 0)) (length z))"
      by (auto simp: ci_def centered_def real_interval_minus real_interval_of lz)
    also have "\<dots> \<subseteq> set_of (Ipoly [real_interval (I ! 0 - xs ! 0)]
        (map_poly real_interval (snd (tmf_polys z))))"
      (is "_ \<subseteq> set_of ?x")
      by (rule Ipoly_snd_tmf_polys)
    also have "\<dots> = set_of (real_interval (Ipoly [(I ! 0 - xs ! 0)] (snd (tmf_polys z))))"
      by (auto simp: real_interval_Ipoly num_params_tmf_polys2)
    also have "\<dots> \<subseteq> set_of (real_interval (round_interval prec (Ipoly [(I ! 0 - xs ! 0)] (snd (tmf_polys z)))))"
      by (rule set_of_real_interval_subset) (rule round_ivl_correct)
    also
    have "Ipoly [I ! 0 - interval_of (xs ! 0)] (snd (tmf_polys z)) = Ipoly (List.map2 (-) I (map interval_of xs)) (snd (tmf_polys z))"
      using  a
      apply (auto intro!: Ipoly_num_params_cong nth_equalityI
          simp: nth_Cons  simp del:length_greater_0_conv split: nat.splits dest!: less_le_trans[OF _ num_params_tmf_polys2[of z]])
      apply (subst map2_nth)
      by simp_all
    finally show ?thesis .
  qed
  consider "0 < ord" "x \<noteq> xs ! 0" | "0 < ord" "x = xs ! 0" | "ord = 0" by arith
  then show ?thesis
  proof cases
    case hyps: 1
    then have 1: "0 < ord" and 5: "x \<noteq> xs ! 0" by simp_all
    from Taylor[OF 1 2 3 4 5] obtain s where s: "(if ?x < ?c then ?x < s \<and> s < ?c else ?c < s \<and> s < ?x)"
      and tse: "?f ?x = (\<Sum>m<?n. ?diff m ?c / fact m * (?x - ?c) ^ m) + ?diff ?n s / fact ?n * (?x - ?c) ^ ?n"
      by blast

    have "interpret_floatarith f ((map real_of_float xs)[0 := x]) -
    Ipoly (List.map2 (-) [x] [xs!0]) (fst (tmf_polys z)) =
    (\<Sum>m<?n. ?diff m ?c / fact m * (?x - ?c) ^ m) + ?diff ?n s / fact ?n * (?x - ?c) ^ ?n -
    (\<Sum>m\<le>?n. (x - xs!0) ^ m * mid (z ! m))"
      unfolding tse
      by (simp add: Ipoly_fst_tmf_polys rewr lz)
    also have "\<dots> = (\<Sum>m<ord. cr s m  * (x - xs!0) ^ m) + cr s ord * (x - xs!0) ^ ord"
      unfolding rewr
      by (simp add: algebra_simps cr_def sum.distrib sum_subtractf)
    also have "cr s ord \<in>\<^sub>i ci ord"
      using a
      apply (auto simp: cr_def ci_def intro!: minus_in_intervalI
          tmf_c_correct[OF _ z_ord])
      by (smt "4"(1) "4"(2) "4"(3) "4"(4) a all_in_def in_real_intervalI length_greater_0_conv nth_list_update s xs_ne)
    note enclosure[OF this]
    also have "Ipoly (List.map2 (-) [x] (map real_of_float [xs ! 0])) (map_poly real_of_float (fst (tmf_polys z))) =
        insertion e (map_poly real_of_float (fst (tmf_polys z)))"
      using diff_e
      by (auto intro!: Ipoly_eq_insertionI simp: nth_Cons split: nat.splits dest: less_le_trans[OF _ num_params_tmf_polys1[of z]])
    finally
    show ?thesis
      by (simp add: tz tb range_tm_def set_of_eq)
  next
    case 3
    with 3 have "length z = Suc 0" by (simp add: lz)
    then have "fst (tmf_polys z) = fst (tmf_polys [z ! 0])"
      by (cases z) auto
    also have "\<dots> = CN (mid (z ! 0))\<^sub>p 0 0\<^sub>p"
      by simp
    finally have "fst (tmf_polys z) = CN (mid (z ! 0))\<^sub>p 0 0\<^sub>p" .
    with enclosure[OF cr_ord]
    show ?thesis
      by (simp add: cr_def 3 range_tm_def tz tb set_of_eq)
  next
    case 2
    have rewr: "{..<length z} = insert 0 {1..<length z}"
      by (auto simp: lz)
    from 2 enclosure[OF cr_ord]
    show ?thesis
      by (auto simp: zero_power 2 cr_def range_tm_def tz tb insertion_fst_tmf_polys
          diff_e[symmetric] rewr set_of_eq)
  qed
qed


subsection \<open>Operations on Taylor models\<close>

fun tm_norm_poly :: "taylor_model \<Rightarrow> taylor_model"
  where "tm_norm_poly (TaylorModel p e) = TaylorModel (polynate p) e"
\<comment> \<open>Normalizes the Taylor model by transforming its polynomial into horner form.\<close>

fun tm_lower_order tm_lower_order_of_normed :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_lower_order prec ord I a t = tm_lower_order_of_normed prec ord I a (tm_norm_poly t)"
  |  "tm_lower_order_of_normed prec ord I a (TaylorModel p e) = (
         let (l, r) = split_by_degree ord p
         in TaylorModel l (round_interval prec (e + compute_bound_poly prec r I a))
       )"
\<comment> \<open>Reduces the degree of a Taylor model's polynomial to n and keeps it range by increasing the error bound.\<close>

fun tm_round_floats tm_round_floats_of_normed :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_round_floats prec I a t = tm_round_floats_of_normed prec I a (tm_norm_poly t)"
  | "tm_round_floats_of_normed prec I a (TaylorModel p e) = (
         let (l, r) = split_by_prec prec p
         in TaylorModel l (round_interval prec (e + compute_bound_poly prec r I a))
       )"
\<comment> \<open>Rounding of Taylor models. Rounds both the coefficients of the polynomial and the floats in the error bound.\<close>

fun tm_norm tm_norm' :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_norm prec ord I a t = tm_norm' prec ord I a (tm_norm_poly t)"
  | "tm_norm' prec ord I a t = tm_round_floats_of_normed prec I a (tm_lower_order_of_normed prec ord I a t)" 
\<comment> \<open>Normalization of taylor models. Performs order lowering and rounding on tayor models,
   also converts the polynomial into horner form.\<close>

fun tm_neg :: "taylor_model \<Rightarrow> taylor_model"
  where "tm_neg (TaylorModel p e) = TaylorModel (~\<^sub>p p) (-e)"

fun tm_add :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_add (TaylorModel p1 e1) (TaylorModel p2 e2) = TaylorModel (p1 +\<^sub>p p2) (e1 + e2)"

fun tm_sub :: "taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_sub t1 t2 = tm_add t1 (tm_neg t2)"

fun tm_mul :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_mul prec ord I a (TaylorModel p1 e1) (TaylorModel p2 e2) = (
         let d1 = compute_bound_poly prec p1 I a;
             d2 = compute_bound_poly prec p2 I a;
             p = p1 *\<^sub>p p2;
             e = e1*d2 + d1*e2 + e1*e2
         in tm_norm' prec ord I a (TaylorModel p e)
       )"
lemmas [simp del] = tm_norm'.simps

fun tm_pow :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> nat \<Rightarrow> taylor_model"
  where "tm_pow prec ord I a t 0 = tm_const 1"
  | "tm_pow prec ord I a t (Suc n) = (
         if odd (Suc n)
         then tm_mul prec ord I a t (tm_pow prec ord I a t n)
         else let t' = tm_pow prec ord I a t ((Suc n) div 2)
              in tm_mul prec ord I a t' t'
       )"

text \<open>Evaluates a float polynomial, using a Taylor model as the parameter. This is used to compose Taylor models.\<close>
fun eval_poly_at_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> float poly \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "eval_poly_at_tm prec ord I a (poly.C c) t = tm_const c"
  | "eval_poly_at_tm prec ord I a (poly.Bound n) t = t"
  | "eval_poly_at_tm prec ord I a (poly.Add p1 p2) t
         = tm_add (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Sub p1 p2) t
         = tm_sub (eval_poly_at_tm prec ord I a p1 t)
                  (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Mul p1 p2) t
         = tm_mul prec ord I a (eval_poly_at_tm prec ord I a  p1 t)
                               (eval_poly_at_tm prec ord I a p2 t)"
  | "eval_poly_at_tm prec ord I a (poly.Neg p) t
         = tm_neg (eval_poly_at_tm prec ord I a p t)"
  | "eval_poly_at_tm prec ord I a (poly.Pw p n) t
         = tm_pow prec ord I a (eval_poly_at_tm prec ord I a p t) n"
  | "eval_poly_at_tm prec ord I a (poly.CN c n p) t = (
         let pt = eval_poly_at_tm prec ord I a p t;
             t_mul_pt = tm_mul prec ord I a t pt 
         in tm_add (eval_poly_at_tm prec ord I a c t) t_mul_pt
       )"

fun tm_inc_err :: "float interval \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_inc_err i (TaylorModel p e) = TaylorModel p (e + i)"

fun tm_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> float \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_comp prec ord I a ta (TaylorModel p e) t = (
         let t_sub_ta = tm_sub t (tm_const ta);
             pt = eval_poly_at_tm prec ord I a p t_sub_ta
         in tm_inc_err e pt
       )"

text \<open>\<open>tm_max\<close>, \<open>tm_min\<close> and \<open>tm_abs\<close> are implemented extremely naively, because I don't expect them to be very useful.
   But the implementation is fairly modular, i.e. \<open>tm_{abs,min,max}\<close> all can easily be swapped out,
   as long as the corresponding correctness lemmas \<open>tm_{abs,min,max}_range\<close> are updated as well.\<close>
fun tm_abs :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_abs prec I a t = (
  let bound = compute_bound_tm prec I a t; abs_bound=Ivl (0::float) (max (abs (lower bound)) (abs (upper bound)))
  in TaylorModel (poly.C (mid abs_bound)) (centered abs_bound))"

fun tm_union :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_union prec I a t1 t2 = (
  let b1 = compute_bound_tm prec I a t1; b2 = compute_bound_tm prec I a t2;
      b_combined = sup b1 b2
  in TaylorModel (poly.C (mid b_combined)) (centered b_combined))"

fun tm_min :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_min prec I a t1 t2 = tm_union prec I a t1 t2"

fun tm_max :: "nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> taylor_model \<Rightarrow> taylor_model \<Rightarrow> taylor_model"
  where "tm_max  prec I a t1 t2 = tm_union prec I a t1 t2"

text \<open>Rangeity of is preserved by our operations on Taylor models.\<close>

lemma insertion_polyadd[simp]: "insertion e (a +\<^sub>p b) = insertion e a + insertion e b"
  for a b::"'a::ring_1 poly"
  apply (induction a b rule: polyadd.induct)
  apply (auto simp: algebra_simps Let_def)
  by (metis (no_types) mult_zero_right ring_class.ring_distribs(1))


lemma insertion_polyneg[simp]: "insertion e (~\<^sub>p b) =  - insertion e b"
  for b::"'a::ring_1 poly"
  by (induction b rule: polyneg.induct) (auto simp: algebra_simps Let_def)

lemma insertion_polysub[simp]: "insertion e (a -\<^sub>p b) = insertion e a - insertion e b"
  for a b::"'a::ring_1 poly"
  by (simp add: polysub_def)

lemma insertion_polymul[simp]: "insertion e (a *\<^sub>p b) = insertion e a * insertion e b"
  for a b::"'a::comm_ring_1 poly"
  by (induction a b rule: polymul.induct)
    (auto simp: algebra_simps Let_def)

lemma insertion_polypow[simp]: "insertion e (a ^\<^sub>p b) = insertion e a ^ b"
  for a::"'a::comm_ring_1 poly"
proof (induction b rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof (cases n)
    case (Suc nat)
    then show ?thesis
      apply (auto simp: )
      apply (auto simp: Let_def div2_less_self 1 simp del: polypow.simps)
      apply (metis even_Suc even_two_times_div_two odd_Suc_div_two semiring_normalization_rules(27) semiring_normalization_rules(36))
      apply (metis even_two_times_div_two semiring_normalization_rules(36))
      done
  qed simp
qed

lemma insertion_polynate [simp]:
  "insertion bs (polynate p) = (insertion bs p :: 'a::comm_ring_1)"
  by (induct p rule: polynate.induct) (auto simp: )

lemma tm_norm_poly_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  shows "x \<in>\<^sub>i range_tm e (tm_norm_poly t)"
  using assms
  by (cases t) (simp add: range_tm_def)

lemma split_by_degree_correct_insertion:
  fixes x :: "nat \<Rightarrow> real" and p :: "float poly"
  assumes "split_by_degree ord p = (l, r)"
  shows "maxdegree l \<le> ord" (is ?P1)
    and   "insertion x p = insertion x l + insertion x r" (is ?P2)
    and   "num_params l \<le> num_params p" (is ?P3)
    and   "num_params r \<le> num_params p" (is ?P4)
proof -
  define xs where "xs = map x [0..<num_params p]"
  have xs: "i < num_params p \<Longrightarrow> x i = xs ! i" for i
    by (auto simp: xs_def)
  have "insertion x p = Ipoly xs p"
    by (auto intro!: insertion_eq_IpolyI xs)
  also
  from split_by_degree_correct[OF assms(1)[symmetric]]
  have "maxdegree l \<le> ord"
    and p: "Ipoly xs (map_poly real_of_float p) =
    Ipoly xs (map_poly real_of_float l) + Ipoly xs (map_poly real_of_float r)"
   and l: "num_params l \<le> num_params p"
   and r: "num_params r \<le> num_params p"
    by auto
  show ?P1 ?P3 ?P4 by fact+
  note p
  also have "Ipoly xs (map_poly real_of_float l) = insertion x l"
    using l
    by (auto intro!: xs Ipoly_eq_insertionI)
  also have "Ipoly xs (map_poly real_of_float r) = insertion x r"
    using r
    by (auto intro!: xs Ipoly_eq_insertionI)
  finally show ?P2 .
qed

lemma split_by_prec_correct_insertion:
  fixes x :: "nat \<Rightarrow> real" and p :: "float poly"
  assumes "split_by_prec ord p = (l, r)"
  shows "insertion x p = insertion x l + insertion x r" (is ?P1)
    and "num_params l \<le> num_params p" (is ?P2)
    and "num_params r \<le> num_params p" (is ?P3)
proof -
  define xs where "xs = map x [0..<num_params p]"
  have xs: "i < num_params p \<Longrightarrow> x i = xs ! i" for i
    by (auto simp: xs_def)
  have "insertion x p = Ipoly xs p"
    by (auto intro!: insertion_eq_IpolyI xs)
  also
  from split_by_prec_correct[OF assms(1)[symmetric]]
  have p: "Ipoly xs (map_poly real_of_float p) =
    Ipoly xs (map_poly real_of_float l) + Ipoly xs (map_poly real_of_float r)"
   and l: "num_params l \<le> num_params p"
   and r: "num_params r \<le> num_params p"
    by auto
  show ?P2 ?P3 by fact+
  note p
  also have "Ipoly xs (map_poly real_of_float l) = insertion x l"
    using l
    by (auto intro!: xs Ipoly_eq_insertionI)
  also have "Ipoly xs (map_poly real_of_float r) = insertion x r"
    using r
    by (auto intro!: xs Ipoly_eq_insertionI)
  finally show ?P1 .
qed

lemma tm_lower_order_of_normed_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_lower_order_of_normed prec ord I a t)"
proof-
  obtain p err where t_decomp: "t = TaylorModel p err"
    by (cases t) simp
  obtain pl pr where p_split: "split_by_degree ord p = (pl, pr)"
    by (cases "split_by_degree ord p", simp)

  from split_by_degree_correct_insertion[OF p_split]
  have params: "maxdegree pl \<le> ord" "num_params pl \<le> num_params p" "num_params pr \<le> num_params p"
    and ins: "insertion e (map_poly real_of_float p) =
      insertion e (map_poly real_of_float pl) + insertion e (map_poly real_of_float pr)"
    by auto
  from assms params have params_pr: "num_params pr \<le> length I" by (auto simp: t_decomp)

  have "range_tm e t =
    interval_of (insertion e (map_poly real_of_float pl)) +
    (interval_of (insertion e (map_poly real_of_float pr)) + real_interval err)"
    by (auto simp: t_decomp range_tm_def ins ac_simps interval_of_plus) term round_interval
  also have "set_of \<dots> \<subseteq> set_of (interval_of (insertion e pl)) +
    set_of (real_interval (round_interval prec (err + compute_bound_poly prec pr I a)))"
    unfolding set_of_plus real_interval_plus add.commute[of err]
    apply (rule set_plus_mono2[OF order_refl])
    apply (rule order_trans) prefer 2
     apply (rule set_of_real_interval_subset)
     apply (rule round_ivl_correct)
    unfolding set_of_plus real_interval_plus
    apply (rule set_plus_mono2[OF _ order_refl])
    apply (rule subsetI)
    apply simp
    apply (rule compute_bound_poly_correct)
      apply (rule params_pr)
    by (rule assms)
  also have "\<dots> = set_of (range_tm e (tm_lower_order_of_normed prec ord I a t))"
    by (simp add: t_decomp split_beta' Let_def p_split range_tm_def set_of_plus)
  finally show ?thesis using assms by auto
qed

lemma num_params_tm_norm_poly_le: "num_params (tm_poly (tm_norm_poly t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  using that
  by (cases t) (auto simp: intro!: num_params_polynate[THEN order_trans])

lemma tm_lower_order_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_lower_order prec ord I a t)"
  by (auto simp add: intro!: tm_lower_order_of_normed_range tm_norm_poly_range assms
      num_params_tm_norm_poly_le)

lemma tm_round_floats_of_normed_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  assumes dev: "develops_at_within e a I"
  assumes "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_round_floats_of_normed prec I a t)"
    \<comment> \<open>TODO: this is a clone of @{thm tm_lower_order_of_normed_range} -> general sweeping method!\<close>
proof-
  obtain p err where t_decomp: "t = TaylorModel p err"
    by (cases t) simp
  obtain pl pr where p_prec: "split_by_prec prec p = (pl, pr)"
    by (cases "split_by_prec prec p", simp)

  from split_by_prec_correct_insertion[OF p_prec]
  have params: "num_params pl \<le> num_params p" "num_params pr \<le> num_params p"
    and ins: "insertion e (map_poly real_of_float p) =
      insertion e (map_poly real_of_float pl) + insertion e (map_poly real_of_float pr)"
    by auto
  from assms params have params_pr: "num_params pr \<le> length I"
    by (auto simp: t_decomp)

  have "range_tm e t =
    interval_of (insertion e (map_poly real_of_float pl)) +
    (interval_of (insertion e (map_poly real_of_float pr)) + real_interval err)"
    by (auto simp: t_decomp range_tm_def ins ac_simps interval_of_plus)
  also have "set_of \<dots> \<subseteq> set_of (interval_of (insertion e pl)) +
    set_of (real_interval (round_interval prec (err + compute_bound_poly prec pr I a)))"
    unfolding set_of_plus real_interval_plus add.commute[of err]
    apply (rule set_plus_mono2[OF order_refl])
    apply (rule order_trans) prefer 2
     apply (rule set_of_real_interval_subset)
     apply (rule round_ivl_correct)
    unfolding set_of_plus real_interval_plus
    apply (rule set_plus_mono2[OF _ order_refl])
    apply (rule subsetI)
    apply simp
    apply (rule compute_bound_poly_correct)
     apply (rule params_pr)
    by (rule assms)
  also have "\<dots> = set_of (range_tm e (tm_round_floats_of_normed prec I a t))"
    by (simp add: t_decomp split_beta' Let_def p_prec range_tm_def set_of_plus)
  finally show ?thesis using assms by auto
qed

lemma num_params_split_by_degree_le: "num_params (fst (split_by_degree ord x)) \<le> K"
  "num_params (snd (split_by_degree ord x)) \<le> K"
  if "num_params x \<le> K" for x::"float poly"
  using split_by_degree_correct_insertion(3,4)[of ord x, OF surjective_pairing] that
  by auto

lemma num_params_split_by_prec_le: "num_params (fst (split_by_prec ord x)) \<le> K"
  "num_params (snd (split_by_prec ord x)) \<le> K"
  if "num_params x \<le> K" for x::"float poly"
  using split_by_prec_correct_insertion(2,3)[of ord x, OF surjective_pairing] that
  by auto

lemma num_params_tm_norm'_le:
  "num_params (tm_poly (tm_round_floats_of_normed prec I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  using that
  by (cases t) (auto simp: tm_norm'.simps split_beta' Let_def intro!: num_params_split_by_prec_le)

lemma tm_round_floats_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_round_floats prec I a t)"
  by (auto intro!: tm_round_floats_of_normed_range assms tm_norm_poly_range num_params_tm_norm_poly_le)

lemma num_params_tm_lower_order_of_normed_le: "num_params (tm_poly (tm_lower_order_of_normed prec ord I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  using that
  apply (cases t)
  apply (auto simp: split_beta' Let_def intro!: num_params_polynate[THEN order_trans])
  apply (rule order_trans[OF split_by_degree_correct(3)])
  by (auto simp: prod_eq_iff)


lemma tm_norm'_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_norm' prec ord I a t)"
  by (auto intro!: tm_round_floats_of_normed_range tm_lower_order_of_normed_range assms
      num_params_tm_norm_poly_le num_params_tm_lower_order_of_normed_le
      simp: tm_norm'.simps)

lemma num_params_tm_norm':
  "num_params (tm_poly (tm_norm' prec ord I a t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  using that
  by (cases t) (auto simp: tm_norm'.simps split_beta' Let_def
      intro!: num_params_tm_norm'_le num_params_split_by_prec_le num_params_split_by_degree_le)

lemma tm_norm_range:
  assumes "x \<in>\<^sub>i range_tm e t" "develops_at_within e a I" "num_params (tm_poly t) \<le> length I"
  shows "x \<in>\<^sub>i range_tm e (tm_norm prec ord I a t)"
  by (auto intro!: assms tm_norm'_range tm_norm_poly_range num_params_tm_norm_poly_le)
lemmas [simp del] = tm_norm.simps

lemma tm_neg_range:
  assumes "x \<in>\<^sub>i range_tm e t"
  shows "- x \<in>\<^sub>i range_tm e (tm_neg t)"
  using assms
  by (cases t)
    (auto simp: set_of_eq range_tm_def interval_of_plus interval_of_uminus map_poly_homo_polyneg)
lemmas [simp del] = tm_neg.simps


lemma tm_bound_tm_add[simp]: "tm_bound (tm_add t1 t2) = tm_bound t1 + tm_bound t2"
  by (cases t1; cases t2) (auto simp: )

lemma interval_of_add: "interval_of (a + b) = interval_of a + interval_of b"
  by (auto intro!: interval_eqI)

lemma tm_add_range:
  "x + y \<in>\<^sub>i range_tm e (tm_add t1 t2)"
  if "x \<in>\<^sub>i range_tm e t1"
    "y \<in>\<^sub>i range_tm e t2"
proof -
  from range_tmD[OF that(1)] range_tmD[OF that(2)]
  show ?thesis
    apply (cases t1; cases t2)
    apply (rule range_tmI)
    by (auto simp: map_poly_homo_polyadd real_interval_plus ac_simps interval_of_add
        num_params_polyadd insertion_polyadd set_of_eq
        dest: less_le_trans[OF _ num_params_polyadd])
qed
lemmas [simp del] = tm_add.simps

lemma tm_sub_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
  shows "x - y \<in>\<^sub>i range_tm e (tm_sub t1 t2)"
  using tm_add_range[OF assms(1) tm_neg_range[OF assms(2)]]
  by simp
lemmas [simp del] = tm_sub.simps

lemma set_of_intervalI: "set_of (interval_of y) \<subseteq> set_of Y" if "y \<in>\<^sub>i Y" for y::"'a::order"
  using that by (auto simp: set_of_eq)

lemma set_of_real_intervalI: "set_of (interval_of y) \<subseteq> set_of (real_interval Y)" if "y \<in>\<^sub>r Y"
  using that by (auto simp: set_of_eq)

lemma tm_mul_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
  assumes dev: "develops_at_within e a I"
  assumes params: "num_params (tm_poly t1) \<le> length I" "num_params (tm_poly t2) \<le> length I"
  shows "x * y \<in>\<^sub>i range_tm e (tm_mul prec ord I a t1 t2)"
proof -
  define p1 where "p1 = tm_poly t1"
  define p2 where "p2 = tm_poly t2"
  define e1 where "e1 = tm_bound t1"
  define e2 where "e2 = tm_bound t2"
  have t1_def: "t1 = TaylorModel p1 e1" and t2_def: "t2 = TaylorModel p2 e2"
    by (auto simp: p1_def e1_def p2_def e2_def)
  from params have params: "num_params p1 \<le> length I" "num_params p2 \<le> length I"
    by (auto simp: p1_def p2_def)
  from range_tmD[OF assms(1)]
  obtain xe where x: "x = insertion e p1 + xe"
    (is "_ = ?x' + _")
    and xe: "xe \<in>\<^sub>r e1"
    by (auto simp: p1_def e1_def elim!: plus_in_intervalE)
  from range_tmD[OF assms(2)]
  obtain ye where y: "y = insertion e p2 + ye"
    (is "_ = ?y' + _")
    and ye: "ye \<in>\<^sub>r e2"
    by (auto simp: p2_def e2_def elim!: plus_in_intervalE)
  have "x * y = insertion e (p1 *\<^sub>p p2) + (xe * ?y' + ?x' * ye + xe * ye)"
    by (simp add: algebra_simps x y map_poly_homo_polymul)
  also have "\<dots> \<in>\<^sub>i range_tm e (tm_mul prec ord I a t1 t2)"
    by (auto intro!: tm_round_floats_of_normed_range assms tm_norm'_range
        simp: split_beta' Let_def t1_def t2_def)
     (auto simp: range_tm_def real_interval_plus real_interval_times intro!: plus_in_intervalI
        times_in_intervalI xe ye params compute_bound_poly_correct dev
        num_params_polymul[THEN order_trans])
  finally show ?thesis .
qed

lemma num_params_tm_mul_le:
  "num_params (tm_poly (tm_mul prec ord I a t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  using that
  by (cases t1; cases t2)
     (auto simp: intro!: num_params_tm_norm' num_params_polymul[THEN order_trans])

lemmas [simp del] = tm_pow.simps\<comment> \<open>TODO: make a systematic decision\<close>

lemma
  shows tm_pow_range: "num_params (tm_poly t) \<le> length I \<Longrightarrow>
      develops_at_within e a I \<Longrightarrow>
      x \<in>\<^sub>i range_tm e t \<Longrightarrow>
      x ^ n \<in>\<^sub>i range_tm e (tm_pow prec ord I a t n)"
    and num_params_tm_pow_le[THEN order_trans]:
      "num_params (tm_poly (tm_pow prec ord I a t n)) \<le> num_params (tm_poly t)"
  unfolding atomize_conj atomize_imp
proof(induction n arbitrary: x t rule: nat_less_induct)
  case (1 n)
  note IH1 = 1(1)[rule_format, THEN conjunct1, rule_format]
  note IH2 = 1(1)[rule_format, THEN conjunct2, THEN order_trans]
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by (auto simp: tm_const_def range_tm_def set_of_eq tm_pow.simps)
  next
    case (Suc nat)
    have eq: "odd nat \<Longrightarrow> x * x ^ nat = x ^ ((Suc nat) div 2) * x ^ ((Suc nat) div 2)"
      apply (subst power_add[symmetric])
      unfolding div2_plus_div2
      by simp
    show ?thesis
      unfolding tm_pow.simps Suc
      using Suc
      apply (auto )
      subgoal
        apply (rule tm_mul_range) apply (assumption)
           apply (rule IH1) apply force
             apply assumption+
        apply (rule IH2) apply force
        apply assumption
        done
      subgoal
        apply (rule num_params_tm_mul_le) apply force
        apply (rule IH2) apply force 
        apply force
        done
      subgoal
        apply (auto simp: Let_def)
        unfolding eq odd_Suc_div_two
        apply (rule tm_mul_range)
        subgoal by (rule IH1) (auto intro!: tm_mul_range num_params_tm_mul_le IH1 IH2 1
              simp: Let_def div2_less_self)
        subgoal by (rule IH1) (auto intro!: tm_mul_range num_params_tm_mul_le IH1 IH2 1
              simp: Let_def div2_less_self)
        subgoal by assumption
        subgoal by (rule IH2) (auto simp: div2_less_self 1)
        subgoal by (rule IH2) (auto simp: div2_less_self 1)
        done
      subgoal
        by (auto simp: Let_def div2_less_self 1 intro!: IH2 num_params_tm_mul_le)
      done
  qed
qed

lemma num_params_tm_add_le:
  "num_params (tm_poly (tm_add t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  using that
  by (cases t1; cases t2)
     (auto simp: tm_add.simps
       intro!: num_params_tm_norm' num_params_polymul[THEN order_trans]
       num_params_polyadd[THEN order_trans])

lemma num_params_tm_neg_eq[simp]:
  "num_params (tm_poly (tm_neg t1)) = num_params (tm_poly t1)"
  by (cases t1) (auto simp: tm_neg.simps num_params_polyneg)

lemma num_params_tm_sub_le:
  "num_params (tm_poly (tm_sub t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X"
    "num_params (tm_poly t2) \<le> X"
  using that
  by (cases t1; cases t2) (auto simp: tm_sub.simps intro!: num_params_tm_add_le)

lemma num_params_eval_poly_le: "num_params (tm_poly (eval_poly_at_tm prec ord I a p t)) \<le> x"
  if "num_params (tm_poly t) \<le> x" "num_params p \<le> max 1 x"
  using that
  by (induction prec ord I a p t rule: eval_poly_at_tm.induct)
    (auto intro!: num_params_tm_add_le num_params_tm_sub_le num_params_tm_mul_le
      num_params_tm_pow_le)

lemma eval_poly_at_tm_range:
  assumes "num_params p \<le> 1"
  assumes tg_def: "e' 0 \<in>\<^sub>i range_tm e tg"
  assumes dev: "develops_at_within e a I" and params: "num_params (tm_poly tg) \<le> length I"
  shows "insertion e' p \<in>\<^sub>i range_tm e (eval_poly_at_tm prec ord I a p tg)"
  using assms(1) params
proof(induction p)
  case (C c) thus ?case
    using tg_def
    by (cases tg) (auto simp: tm_const_def range_tm_def real_interval_zero)
next
  case (Bound n) thus ?case
    using tg_def
    by simp
next
  case (Add p1l p1r) thus ?case 
    using tm_add_range by (simp add: func_plus)
next
  case (Sub p1l p1r) thus ?case 
    using tm_sub_range by (simp add: fun_diff_def)
next
  case (Mul p1l p1r) thus ?case
    by (auto intro!: tm_mul_range Mul dev num_params_eval_poly_le)
next
  case (Neg p1') thus ?case 
    using tm_neg_range by (simp add: fun_Compl_def)
next
  case (Pw p1' n) thus ?case 
    by (auto intro!: tm_pow_range Pw dev num_params_eval_poly_le)
next
  case (CN p1l n p1r) thus ?case 
    by (auto intro!: tm_mul_range tm_pow_range CN dev num_params_eval_poly_le tm_add_range tg_def)
qed

lemma tm_inc_err_range: "x \<in>\<^sub>i range_tm e (tm_inc_err i t)"
  if "x \<in>\<^sub>i range_tm e t + real_interval i"
  using that
  by (cases t) (auto simp: range_tm_def real_interval_plus ac_simps)

lemma num_params_tm_inc_err: "num_params (tm_poly (tm_inc_err i t)) \<le> X"
  if "num_params (tm_poly t) \<le> X"
  using that
  by (cases t) auto

lemma num_params_tm_comp_le: "num_params (tm_poly (tm_comp prec ord I a ga tf tg)) \<le> X"
  if "num_params (tm_poly tf) \<le> max 1 X" "num_params (tm_poly tg) \<le> X"
  using that
  by (cases tf) (auto intro!: num_params_tm_inc_err num_params_eval_poly_le num_params_tm_sub_le)

lemma tm_comp_range:
  assumes tf_def: "x \<in>\<^sub>i range_tm e' tf"
  assumes tg_def: "e' 0 \<in>\<^sub>i range_tm e (tm_sub tg (tm_const ga))"
  assumes params: "num_params (tm_poly tf) \<le> 1" "num_params (tm_poly tg) \<le> length I"
  assumes dev: "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_comp prec ord I a ga tf tg)"
proof-
  obtain pf ef where tf_decomp: "tf = TaylorModel pf ef" using taylor_model.exhaust by auto
  obtain pg eg where tg_decomp: "tg = TaylorModel pg eg" using taylor_model.exhaust by auto

  from params have params: "num_params pf \<le> Suc 0" "num_params pg \<le> length I"
    by (auto simp: tf_decomp tg_decomp)
  from tf_def obtain xe where x_def: "x = insertion e' pf + xe" "xe \<in>\<^sub>r ef"
    by (auto simp: tf_decomp range_tm_def elim!: plus_in_intervalE)
  show ?thesis
    using tg_def
    by (auto simp: tf_decomp tg_decomp x_def params dev
        intro!: tm_inc_err_range eval_poly_at_tm_range plus_in_intervalI num_params_tm_sub_le)
qed

lemma mid_centered_collapse:
  "interval_of (real_of_float (mid abs_bound)) + real_interval (centered abs_bound) =
    real_interval abs_bound"
  by (auto simp: centered_def interval_eq_iff)

lemmas [simp del] = tm_abs.simps
lemma tm_abs_range:
  assumes x: "x \<in>\<^sub>i range_tm e t"
  assumes n: "num_params (tm_poly t) \<le> length I" and d: "develops_at_within e a I"
  shows "abs x \<in>\<^sub>i range_tm e (tm_abs prec I a t)"
proof-
  obtain p e where t_def[simp]: "t = TaylorModel p e" using taylor_model.exhaust by auto
  define bound where "bound = compute_bound_tm prec I a t"
  have bound: "x \<in>\<^sub>r bound"
    unfolding bound_def
    using n d x
    by (rule compute_bound_tm_correct)
  define abs_bound where "abs_bound \<equiv> Ivl 0 (max \<bar>lower bound\<bar> \<bar>upper bound\<bar>)"
  have abs_bound: "\<bar>x\<bar> \<in>\<^sub>r abs_bound" using bound
    by (auto simp: abs_bound_def set_of_eq abs_real_def max_def min_def)
  have tm_abs_decomp: "tm_abs prec I a t = TaylorModel (poly.C (mid abs_bound)) (centered abs_bound)"
    by (simp add: bound_def abs_bound_def Let_def tm_abs.simps)
  show ?thesis
    unfolding tm_abs_decomp
    by (rule range_tmI) (auto simp: mid_centered_collapse abs_bound)
qed

lemma num_params_tm_abs_le: "num_params (tm_poly (tm_abs prec I a t)) \<le> X" if "num_params (tm_poly t) \<le> X"
  using that
  by (auto simp: tm_abs.simps Let_def)

lemma real_interval_sup: "real_interval (sup a b) = sup (real_interval a) (real_interval b)"
  by (auto simp: interval_eq_iff inf_real_def inf_float_def sup_float_def sup_real_def min_def max_def)

lemma in_interval_supI1: "x \<in>\<^sub>i a \<Longrightarrow> x \<in>\<^sub>i sup a b"
  and in_interval_supI2: "x \<in>\<^sub>i b \<Longrightarrow> x \<in>\<^sub>i sup a b"
  for x::"'a::lattice"
  by (auto simp: set_of_eq le_infI1 le_infI2 le_supI1 le_supI2)
  
lemma tm_union_range_left:
  assumes "x \<in>\<^sub>i range_tm e t1"
    "num_params (tm_poly t1) \<le> length I" "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_union prec I a t1 t2)"
proof-
  define b1 where "b1 \<equiv> compute_bound_tm prec I a t1"
  define b2 where "b2 \<equiv> compute_bound_tm prec I a t2"
  define b_combined where "b_combined \<equiv> sup b1 b2"

  obtain p e where tm_union_decomp: "tm_union prec I a t1 t2 = TaylorModel p e"
    using taylor_model.exhaust by auto
  then have p_def: "p = (mid b_combined)\<^sub>p"
    and e_def: "e = centered b_combined"
    by (auto simp: Let_def b1_def b2_def b_combined_def interval_eq_iff)
  have "x \<in>\<^sub>r b1"
    by (auto simp : b1_def intro!: compute_bound_tm_correct assms)
  then have "x \<in>\<^sub>r b_combined"
    by (auto simp: b_combined_def real_interval_sup in_interval_supI1)
  then show ?thesis
    unfolding tm_union_decomp
    by (auto simp: range_tm_def p_def e_def mid_centered_collapse)
qed

lemma tm_union_range_right:
  assumes "x \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t2) \<le> length I" "develops_at_within e a I"
  shows "x \<in>\<^sub>i range_tm e (tm_union prec I a t1 t2)"
  using tm_union_range_left[OF assms]
  by (simp add: interval_union_commute)

lemma num_params_tm_union_le:
  "num_params (tm_poly (tm_union prec I a t1 t2)) \<le> X"
  if "num_params (tm_poly t1) \<le> X" "num_params (tm_poly t2) \<le> X"
  using that
  by (auto simp: Let_def)
  
lemmas [simp del] = tm_union.simps tm_min.simps tm_max.simps

lemma tm_min_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t1) \<le> length I"
    "num_params (tm_poly t2) \<le> length I"
    "develops_at_within e a I"
  shows "min x y \<in>\<^sub>i range_tm e (tm_min prec I a t1 t2)"
  using assms
  by (auto simp: Let_def tm_min.simps min_def intro: tm_union_range_left tm_union_range_right)

lemma tm_max_range:
  assumes "x \<in>\<^sub>i range_tm e t1"
  assumes "y \<in>\<^sub>i range_tm e t2"
    "num_params (tm_poly t1) \<le> length I"
    "num_params (tm_poly t2) \<le> length I"
    "develops_at_within e a I"
  shows "max x y \<in>\<^sub>i range_tm e (tm_max prec I a t1 t2)"
  using assms
  by (auto simp: Let_def tm_max.simps max_def intro: tm_union_range_left tm_union_range_right)


subsection \<open>Computing Taylor models for multivariate expressions\<close>

text \<open>Compute Taylor models for expressions of the form "f (g x)", where f is an elementary function like exp or cos,
   by composing Taylor models for f and g. For our correctness proof, we need to make it explicit that the range
   of g on I is inside the domain of f, by introducing the \<open>f_exists_on\<close> predicate.\<close>
fun compute_tm_by_comp :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model option \<Rightarrow> (float interval \<Rightarrow> bool) \<Rightarrow> taylor_model option"
  where "compute_tm_by_comp prec ord I a f g f_exists_on = (
         case g
         of Some tg \<Rightarrow> (
           let gI = compute_bound_tm prec I a tg;
               ga = mid (compute_bound_tm prec a a tg)
           in if f_exists_on gI
              then map_option (\<lambda>tf. tm_comp prec ord I a ga tf tg ) (tm_floatarith prec ord [gI] [ga] f)
              else None)
         | _ \<Rightarrow> None
       )"

text \<open>Compute Taylor models with numerical precision \<open>prec\<close> of degree \<open>ord\<close>,
  with Taylor models in the environment \<open>env\<close> whose variables are jointly interpreted with domain
  \<open>I\<close> and expanded around point \<open>a\<close>.
  from floatarith expressions on a rectangular domain.\<close>
fun approx_tm :: "nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> floatarith \<Rightarrow> taylor_model list \<Rightarrow>
    taylor_model option"
  where "approx_tm _ _ I _ (Num c) env = Some (tm_const c)"
  | "approx_tm _ _ I a (Var n) env = (if n < length env then Some (env ! n) else None)"
  | "approx_tm prec ord I a (Add l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_add t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Minus f) env
         = map_option tm_neg (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Mult l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_mul prec ord I a t1 t2)
          | _ \<Rightarrow> None)"     
  | "approx_tm prec ord I a (Power f k) env
         = map_option (\<lambda>t. tm_pow prec ord I a t k)
                      (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Inverse f) env
         = compute_tm_by_comp prec ord I a (Inverse (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x \<or> upper x < 0)"
  | "approx_tm prec ord I a (Cos f) env
         = compute_tm_by_comp prec ord I a (Cos (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Arctan f) env
         = compute_tm_by_comp prec ord I a (Arctan (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Exp f) env
         = compute_tm_by_comp prec ord I a (Exp (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. True)"
  | "approx_tm prec ord I a (Ln f) env
         = compute_tm_by_comp prec ord I a (Ln (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x)"
  | "approx_tm prec ord I a (Sqrt f) env
         = compute_tm_by_comp prec ord I a (Sqrt (Var 0)) (approx_tm prec ord I a f env) (\<lambda>x. 0 < lower x)"
  | "approx_tm prec ord I a Pi env = Some (tm_pi prec)"
  | "approx_tm prec ord I a (Abs f) env
         = map_option (tm_abs prec I a) (approx_tm prec ord I a f env)"
  | "approx_tm prec ord I a (Min l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env) 
         of (Some t1, Some t2) \<Rightarrow> Some (tm_min prec I a t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Max l r) env = (
         case (approx_tm prec ord I a l env, approx_tm prec ord I a r env)
         of (Some t1, Some t2) \<Rightarrow> Some (tm_max prec I a t1 t2)
          | _ \<Rightarrow> None)"
  | "approx_tm prec ord I a (Powr l r) env = None" \<comment> \<open>TODO\<close>
  | "approx_tm prec ord I a (Floor l) env = None" \<comment> \<open>TODO\<close>

lemma mid_in_real_interval: "mid i \<in>\<^sub>r i"
  using lower_le_upper[of i]
  by (auto simp: mid_def set_of_eq powr_minus)

lemma set_of_real_interval_mono:"set_of (real_interval x) \<subseteq> set_of (real_interval y)"
  if "set_of x \<subseteq> set_of y"
  using that by (auto simp: set_of_eq)

lemmas [simp del] = compute_bound_poly.simps tm_floatarith.simps

(*
  assumes tx_valid: "valid_tm I a (interpret_floatarith g) tg"
  assumes t_def: "compute_tm_on_ivl_by_comp prec ord I a f (Some tg) c = Some t"
  assumes f_deriv: "\<And>x. x \<in>\<^sub>r (compute_bound_tm prec I a tg) \<Longrightarrow> c (compute_bound_tm prec I a tg) \<Longrightarrow> isDERIV 0 f [x]"
  shows "valid_tm I a ((\<lambda>x. interpret_floatarith f [x]) o interpret_floatarith g) t"
*)

lemmas [simp del] = tmf_ivl_cs.simps compute_bound_tm.simps tmf_polys.simps

lemma tm_floatarith_eq_Some_num_params:
  "tm_floatarith prec ord a b f = Some tf \<Longrightarrow> num_params (tm_poly tf) \<le> 1"
  by (auto simp: tm_floatarith.simps split_beta' Let_def those_eq_Some_iff num_params_tmf_polys1)

lemma compute_tm_by_comp_range:
  assumes "max_Var_floatarith f \<le> 1"
  assumes a: "a all_subset I"
  assumes tx_range: "x \<in>\<^sub>i range_tm e tg"
  assumes t_def: "compute_tm_by_comp prec ord I a f (Some tg) c = Some t"
  assumes f_deriv:
    "\<And>x. x \<in>\<^sub>r compute_bound_tm prec I a tg \<Longrightarrow> c (compute_bound_tm prec I a tg) \<Longrightarrow> isDERIV 0 f [x]"
  assumes params: "num_params (tm_poly tg) \<le> length I"
    and dev: "develops_at_within e a I"
  shows "interpret_floatarith f [x] \<in>\<^sub>i range_tm e t"
proof-
  from t_def[simplified, simplified Let_def]
  obtain tf
    where t1_def: "tm_floatarith prec ord [compute_bound_tm prec I (a) tg]
          [mid (compute_bound_tm prec a a tg)] f =
         Some tf"
      and t_decomp: "t = tm_comp prec ord I a (mid (compute_bound_tm prec a a tg)) tf tg "
      and c_true:   "c (compute_bound_tm prec I a tg)"
    by (auto simp: split_beta' Let_def split: if_splits)
  have a1: "mid (compute_bound_tm prec a a tg) \<in>\<^sub>r (compute_bound_tm prec I a tg)"
    apply(rule rev_subsetD[OF mid_in_real_interval])
    apply (rule set_of_real_interval_mono)
    apply (rule compute_bound_tm_mono)
    using params a
    by (auto simp add: set_of_eq elim!: range_tmD)
  from \<open>max_Var_floatarith f \<le> 1\<close>
  have [simp]: "\<And>x. 0 \<le> length x \<Longrightarrow> (\<lambda>x. interpret_floatarith f [x ! 0]) x = interpret_floatarith f x"
    by (induction f, simp_all)

  let ?mid = "real_of_float (mid (compute_bound_tm prec a a tg))"
  have 1: "interpret_floatarith f [x] \<in>\<^sub>i range_tm (\<lambda>_. x - ?mid) tf"
    apply (rule tm_floatarith[OF t1_def, simplified])
    subgoal
      apply (rule rev_subsetD)
      apply (rule mid_in_real_interval)
      apply (rule set_of_real_interval_mono)
      apply (rule compute_bound_tm_mono)
      using assms
      by (auto)
    subgoal
      by (rule compute_bound_tm_correct assms)+
    subgoal by (auto intro!: assms c_true)
    subgoal by (auto simp: )
    done
  show ?thesis
    unfolding t_decomp
    apply (rule tm_comp_range)
         apply (rule 1)
    using tm_floatarith_eq_Some_num_params[OF t1_def]
    by (auto simp: intro!: tm_sub_range assms )
qed

lemmas [simp del] = compute_tm_by_comp.simps

lemma compute_tm_by_comp_num_params_le:
  assumes "compute_tm_by_comp prec ord I a f (Some t0) i = Some t"
  assumes "1 \<le> X" "num_params (tm_poly t0) \<le> X"
  shows "num_params (tm_poly t) \<le> X"
  using assms
  by (auto simp: compute_tm_by_comp.simps Let_def intro!: num_params_tm_comp_le
      dest!: tm_floatarith_eq_Some_num_params
      split: option.splits if_splits)

lemma compute_tm_by_comp_eq_Some_iff: "compute_tm_by_comp prec ord I a f t0 i = Some t \<longleftrightarrow>
  (\<exists>z x2. t0 = Some x2 \<and>
    tm_floatarith prec ord [compute_bound_tm prec I a x2]
      [mid (compute_bound_tm prec a a x2)] f =
      Some z
   \<and> tm_comp prec ord I a
      (mid (compute_bound_tm prec a a x2)) z x2 = t
   \<and> i (compute_bound_tm prec I a x2))"
  by (auto simp: compute_tm_by_comp.simps Let_def split: option.splits)

lemma num_params_approx_tm:
  assumes "approx_tm prec ord I a f env = Some t"
  assumes "\<And>tm. tm \<in> set env \<Longrightarrow> num_params (tm_poly tm) \<le> length I"
  shows "num_params (tm_poly t) \<le> length I"
  using assms
proof (induction f arbitrary: t)
  case (Add f1 f2)
  then show ?case by (auto split: option.splits intro!: num_params_tm_add_le)
next
  case (Minus f)
  then show ?case by (auto split: option.splits)
next
  case (Mult f1 f2)
  then show ?case by (auto split: option.splits intro!: num_params_tm_mul_le)
next
  case (Inverse f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Cos f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Arctan f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Abs f)
  then show ?case
    by (auto simp: tm_abs.simps Let_def intro!: num_params_tm_union_le)
next
  case (Max f1 f2)
  then show ?case
    by (auto simp: tm_max.simps Let_def intro!: num_params_tm_union_le split: option.splits)
next
  case (Min f1 f2)
  then show ?case
    by (auto simp: tm_min.simps Let_def intro!: num_params_tm_union_le split: option.splits)
next
  case Pi
  then show ?case
    by (auto )
next
  case (Sqrt f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Exp f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Powr f1 f2)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Ln f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
case (Power f x2a)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_pow_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Floor f)
  then show ?case
    by (auto split: option.splits simp: Let_def compute_tm_by_comp_eq_Some_iff
        intro!: num_params_tm_comp_le dest!: tm_floatarith_eq_Some_num_params)
next
  case (Var x)
  then show ?case by (auto split: if_splits)
next
  case (Num x)
  then show ?case by auto
qed

lemma in_interval_realI: "a \<in>\<^sub>i I" if "a \<in>\<^sub>r I" using that by (auto simp: set_of_eq)

lemma all_subset_all_inI: "map interval_of a all_subset I" if "a all_in I"
  using that by (auto simp: in_interval_realI)

lemma compute_tm_by_comp_None: "compute_tm_by_comp p ord I a x None k = None"
  by (rule ccontr) (auto simp: compute_tm_by_comp_eq_Some_iff)

lemma approx_tm_num_Vars_None:
  assumes "max_Var_floatarith f > length env"
  shows "approx_tm p ord I a f env = None"
  using assms
  by (induction f) (auto split: option.splits if_splits simp: max_def compute_tm_by_comp_None)

lemma approx_tm_num_Vars:
  assumes "approx_tm prec ord I a f env = Some t"
  shows "max_Var_floatarith f \<le> length env"
  apply (rule ccontr)
  using approx_tm_num_Vars_None[of env f prec ord I a] assms
  by auto

definition "range_tms e xs = map (range_tm e) xs"

lemma approx_tm_range:
  assumes a: "a all_subset I"
  assumes t_def: "approx_tm prec ord I a f env = Some t"
  assumes allin: "xs all_in\<^sub>i range_tms e env"
  assumes devs: "develops_at_within e a I"
  assumes env: "\<And>tm. tm \<in> set env \<Longrightarrow> num_params (tm_poly tm) \<le> length I"
  shows "interpret_floatarith f xs \<in>\<^sub>i range_tm e t"
  using t_def
proof(induct f arbitrary: t)
  case (Var n)
  thus ?case
    using assms(2) allin approx_tm_num_Vars[of prec ord I a "Var n" env t]
      by (auto simp: all_in_i_def range_tms_def)
next
  case (Num c)
  thus ?case 
    using assms(2) by (auto simp add: assms(3))
next
  case (Add l r t)
  obtain t1 where t1_def: "approx_tm prec ord I a l env = Some t1"
    by (metis (no_types, lifting) Add(3) approx_tm.simps(3) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "approx_tm prec ord I a r env = Some t2"
    by (smt Add(3) approx_tm.simps(3) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_add t1 t2"
    using Add(3) t1_def t2_def
    by (metis approx_tm.simps(3) option.case(2) option.inject prod.case)

  have [simp]: "interpret_floatarith (floatarith.Add l r) = interpret_floatarith l + interpret_floatarith r"
    by auto
  show ?case
    using Add
    by (auto simp: t_def intro!: tm_add_range Add t1_def t2_def)
next
  case (Minus f t)
  have [simp]: "interpret_floatarith (Minus f) = -interpret_floatarith f"
    by auto

  obtain t1 where t1_def: "approx_tm prec ord I a f env = Some t1"
    by (metis Minus.prems(1) approx_tm.simps(4) map_option_eq_Some)
  have t_def: "t = tm_neg t1"
    by (metis Minus.prems(1) approx_tm.simps(4) option.inject option.simps(9) t1_def)

  show ?case
    by (auto simp: t_def intro!: tm_neg_range t1_def Minus)
next
  case (Mult l r t)
  obtain t1 where t1_def: "approx_tm prec ord I a l env = Some t1"
    by (metis (no_types, lifting) Mult(3) approx_tm.simps(5) option.case_eq_if option.collapse prod.case)
  obtain t2 where t2_def: "approx_tm prec ord I a r env = Some t2"
    by (smt Mult(3) approx_tm.simps(5) option.case_eq_if option.collapse prod.case)
  have t_def: "t = tm_mul prec ord I a t1 t2"
    using Mult(3) t1_def t2_def
    by (metis approx_tm.simps(5) option.case(2) option.inject prod.case)

  have [simp]: "interpret_floatarith (floatarith.Mult l r) = interpret_floatarith l * interpret_floatarith r"
    by auto
  show ?case
    using env Mult
    by (auto simp add: t_def intro!: tm_mul_range Mult t1_def t2_def devs
        num_params_approx_tm[OF t1_def] num_params_approx_tm[OF t2_def])
next
  case (Power f k t)
  from Power(2)
  obtain tm_f where tm_f_def: "approx_tm prec ord I a f env = Some tm_f"
    apply(simp) by metis
  have t_decomp: "t = tm_pow prec ord I a tm_f k"
    using Power(2) by (simp add: tm_f_def)
  show ?case
    using env Power
    by (auto simp add: t_def tm_f_def intro!: tm_pow_range Power  devs
        num_params_approx_tm[OF tm_f_def])
next
  case (Inverse f t)
  from Inverse obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have safe: "\<And>x. x \<in>\<^sub>r (compute_bound_tm prec I a tf) \<Longrightarrow>
          0 < lower (compute_bound_tm prec I a tf) \<or> upper (compute_bound_tm prec I a tf) < 0 \<Longrightarrow>
          isDERIV 0 (Inverse (Var 0)) [x]"
    by (simp add: set_of_eq , safe, simp_all)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      Inverse(1)[OF tf_def]
      Inverse(2)[unfolded approx_tm.simps tf_def]
      safe np devs]
  show ?case by simp
next
  case hyps: (Cos f t)
  from hyps obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      hyps(1)[OF tf_def]
      hyps(2)[unfolded approx_tm.simps tf_def]
      _ np devs]
  show ?case by simp
next
  case hyps: (Arctan f t)
  from hyps obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      hyps(1)[OF tf_def]
      hyps(2)[unfolded approx_tm.simps tf_def]
      _ np devs]
  show ?case by simp
next
  case hyps: (Exp f t)
  from hyps obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      hyps(1)[OF tf_def]
      hyps(2)[unfolded approx_tm.simps tf_def]
      _ np devs]
  show ?case by simp
next
  case hyps: (Ln f t)
  from hyps obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have safe: "\<And>x. x \<in>\<^sub>r compute_bound_tm prec I a tf \<Longrightarrow>
        0 < lower (compute_bound_tm prec I a tf) \<Longrightarrow> isDERIV 0 (Ln (Var 0)) [x]"
    by (auto simp: set_of_eq)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      hyps(1)[OF tf_def]
      hyps(2)[unfolded approx_tm.simps tf_def]
      safe np devs]
  show ?case by simp
next
  case hyps: (Sqrt f t)
  from hyps obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    by (auto simp: compute_tm_by_comp_eq_Some_iff)
  have safe: "\<And>x. x \<in>\<^sub>r compute_bound_tm prec I a tf \<Longrightarrow>
        0 < lower (compute_bound_tm prec I a tf) \<Longrightarrow> isDERIV 0 (Sqrt (Var 0)) [x]"
    by (auto simp: set_of_eq)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from compute_tm_by_comp_range[OF _ a
      hyps(1)[OF tf_def]
      hyps(2)[unfolded approx_tm.simps tf_def]
      safe np devs]
  show ?case by simp
next
  case (Pi t)
  hence "t = tm_pi prec" by simp
  then show ?case
    by (auto intro!: range_tm_tm_pi)
next
  case (Abs f t)
  from Abs(2) obtain tf where tf_def: "approx_tm prec ord I a f env = Some tf"
    and  t_def: "t = tm_abs prec I a tf"
    by (metis (no_types, lifting) approx_tm.simps(14) map_option_eq_Some)
  have np: "num_params (tm_poly tf) \<le> length I"
    using tf_def
    apply (rule num_params_approx_tm)
    using assms by auto
  from tm_abs_range[OF Abs(1)[OF tf_def] np devs]
  show ?case
    unfolding t_def interpret_floatarith.simps(9) comp_def
    by assumption
next
  case hyps: (Min l r t)
  from hyps(3)
  obtain t1 t2 where t_decomp: "t = tm_min prec I a t1 t2"
    and t1_def: "Some t1 = approx_tm prec ord I a l env"
    and t2_def: "approx_tm prec ord I a r env = Some t2"
    by (smt approx_tm.simps(15) option.case_eq_if option.collapse option.distinct(2) option.inject split_conv)
  from this(2,3) hyps(1-3)
  have t1_range: "(interpret_floatarith l xs) \<in>\<^sub>i range_tm e t1"
    and  t2_range: "(interpret_floatarith r xs) \<in>\<^sub>i range_tm e t2"
    by auto

  have [simp]: "interpret_floatarith (floatarith.Min l r) = (\<lambda>vs. min (interpret_floatarith l vs) (interpret_floatarith r vs))"
    by auto
  have np1: "num_params (tm_poly t1) \<le> length I"
    using t1_def[symmetric]
    apply (rule num_params_approx_tm)
    using assms by auto
  have np2: "num_params (tm_poly t2) \<le> length I"
    using t2_def
    apply (rule num_params_approx_tm)
    using assms by auto
  show ?case
    unfolding t_decomp(1)
    apply(simp del: tm_min.simps)
    using t1_range t2_range np1 np2
    by (auto intro!: tm_min_range devs)
next
  case hyps: (Max l r t)
  from hyps(3)
  obtain t1 t2 where t_decomp: "t = tm_max prec I a t1 t2"
    and t1_def: "Some t1 = approx_tm prec ord I a l env"
    and t2_def: "approx_tm prec ord I a r env = Some t2"
    by (smt approx_tm.simps(16) option.case_eq_if option.collapse option.distinct(2) option.inject split_conv)
  from this(2,3) hyps(1-3)
  have t1_range: "(interpret_floatarith l xs) \<in>\<^sub>i range_tm e t1"
    and  t2_range: "(interpret_floatarith r xs) \<in>\<^sub>i range_tm e t2"
    by auto

  have [simp]: "interpret_floatarith (floatarith.Min l r) = (\<lambda>vs. min (interpret_floatarith l vs) (interpret_floatarith r vs))"
    by auto
  have np1: "num_params (tm_poly t1) \<le> length I"
    using t1_def[symmetric]
    apply (rule num_params_approx_tm)
    using assms by auto
  have np2: "num_params (tm_poly t2) \<le> length I"
    using t2_def
    apply (rule num_params_approx_tm)
    using assms by auto
  show ?case
    unfolding t_decomp(1)
    apply(simp del: tm_min.simps)
    using t1_range t2_range np1 np2
    by (auto intro!: tm_max_range devs)
qed simp_all


text \<open>Evaluate expression with Taylor models in environment.\<close>

subsection \<open>Computing bounds for floatarith expressions\<close>

text \<open>TODO: compare parametrization of input vs. uncertainty for input...\<close>

definition "tm_of_ivl_par n ivl = TaylorModel (CN (C ((upper ivl + lower ivl)*Float 1 (-1))) n
  (C ((upper ivl - lower ivl)*Float 1 (-1)))) 0"
  \<comment> \<open>track uncertainty in parameter \<open>n\<close>, which is to be interpreted over standardized domain \<open>[-1, 1]\<close>.\<close>

value "tm_of_ivl_par 3 (Ivl (-1) 1)"

definition "tms_of_ivls ivls = map (\<lambda>(i, ivl). tm_of_ivl_par i ivl) (zip [0..<length ivls] ivls)"

value "tms_of_ivls [Ivl 1 2, Ivl 4 5]"

primrec approx_slp'::"nat \<Rightarrow> nat \<Rightarrow> float interval list \<Rightarrow> float interval list \<Rightarrow> slp \<Rightarrow>
  taylor_model list \<Rightarrow> taylor_model list option"
where
  "approx_slp' p ord I a [] xs = Some xs"
| "approx_slp' p ord I a (ea # eas) xs =
    do {
      r \<leftarrow> approx_tm p ord I a ea xs;
      approx_slp' p ord I a eas (r#xs)
    }"

lemma mem_range_tms_Cons_iff[simp]: "x#xs all_in\<^sub>i range_tms e (X#XS) \<longleftrightarrow> x \<in>\<^sub>i range_tm e X \<and> xs all_in\<^sub>i range_tms e XS"
  by (auto simp: range_tms_def all_in_i_def nth_Cons split: nat.splits)

lemma approx_slp'_range:
  assumes i: "i all_subset I"
  assumes dev: "develops_at_within e i I"
  assumes vs: "vs all_in\<^sub>i range_tms e VS" "(\<And>tm. tm \<in> set VS \<Longrightarrow> num_params (tm_poly tm) \<le> length I)"
  assumes appr: "approx_slp' p ord I i ra VS = Some X"
  shows "interpret_slp ra vs all_in\<^sub>i range_tms e X"
  using appr vs
proof (induction ra arbitrary: X vs VS)
  case (Cons ra ras)
  from Cons.prems
  obtain a where a: "approx_tm p ord I i ra VS = Some a"
    and r: "approx_slp' p ord I i ras (a # VS) = Some X"
    by (auto simp: bind_eq_Some_conv)
  from approx_tm_range[OF i a Cons.prems(2) dev Cons.prems(3)]
  have "interpret_floatarith ra vs \<in>\<^sub>i range_tm e a"
    by auto
  then have 1: "interpret_floatarith ra vs#vs all_in\<^sub>i range_tms e (a#VS)"
    using Cons.prems(2)
    by auto
  show ?case
    apply auto
    apply (rule Cons.IH)
      apply (rule r)
     apply (rule 1)
    apply auto
     apply (rule num_params_approx_tm)
      apply (rule a)
    by (auto intro!: Cons.prems)
qed auto

definition approx_slp::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> taylor_model list \<Rightarrow> taylor_model list option"
  where
    "approx_slp p ord d slp tms =
      map_option (take d)
        (approx_slp' p ord (replicate (length tms) (Ivl (-1) 1)) (replicate (length tms) 0) slp tms)"

lemma length_range_tms[simp]: "length (range_tms e VS) = length VS"
  by (auto simp: range_tms_def)

lemma set_of_Ivl: "set_of (Ivl a b) = {a .. b}" if "a \<le> b"
  by (auto simp: set_of_eq that min_def)

lemma set_of_zero[simp]: "set_of 0 = {0::'a::ordered_comm_monoid_add}"
  by (auto simp: set_of_eq)

theorem approx_slp_range_tms:
  assumes "approx_slp p ord d slp VS = Some X"
  assumes slp_def: "slp = slp_of_fas fas"
  assumes d_def: "d = length fas"
  assumes e: "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes vs: "vs all_in\<^sub>i range_tms e VS"
  assumes lens: "\<And>tm. tm \<in> set VS \<Longrightarrow> num_params (tm_poly tm) \<le> length vs"
  shows "interpret_floatariths fas vs all_in\<^sub>i range_tms e X"
proof -
  have "interpret_floatariths fas vs = take d (interpret_slp slp vs)"
    by (simp add: slp_of_fas slp_def d_def)
  also
  have lvs: "length vs = length VS"
    using assms by (auto simp: all_in_i_def)
  define i where "i = replicate (length vs) (0::float interval)"
  define I where "I = replicate (length vs) (Ivl (-1) 1::float interval)"
  from assms obtain XS where
    XS: "approx_slp' p ord I i slp VS = Some XS"
    and X: "take d XS = X"
    by (auto simp: approx_slp_def lvs i_def I_def)
  have iI: "i all_subset I"
    by (auto simp: i_def I_def set_of_Ivl)
  have dev: "develops_at_within e i I"
    using e
    by (auto simp: develops_at_within_def i_def I_def set_of_Ivl real_interval_Ivl
        real_interval_minus real_interval_zero set_of_eq Pi_iff min_def)
  from approx_slp'_range[OF iI dev vs _ XS] lens
  have "interpret_slp slp vs all_in\<^sub>i range_tms e XS" by (auto simp: I_def)
  then have "take d (interpret_slp slp vs) all_in\<^sub>i range_tms e (take d XS)"
    by (auto simp: all_in_i_def range_tms_def)
  also note \<open>take d XS = X\<close>
  finally show ?thesis .
qed

end

end