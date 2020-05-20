(*
  File:     Catalan_Numbers.thy
  Author:   Manuel Eberl (TUM)

  The recursive definition of Catalan numbers with a proof of several closed form
  expressions for them using generating functions. Also contains reasonably efficient
  code generation and a proof of their asymptotic growth.
*)

theory Catalan_Numbers
imports
  Complex_Main
  Catalan_Auxiliary_Integral
  "HOL-Analysis.Analysis"
  "HOL-Computational_Algebra.Formal_Power_Series"
  "HOL-Library.Landau_Symbols"
  Landau_Symbols.Landau_More
begin

subsection \<open> Other auxiliary lemmas\<close>

lemma mult_eq_imp_eq_div:
  assumes "a * b = c" "(a :: 'a :: semidom_divide) \<noteq> 0"
  shows   "b = c div a"
  by (simp add: assms(2) assms(1) [symmetric])

lemma Gamma_minus_one_half_real:
  "Gamma (-(1/2) :: real) = - 2 * sqrt pi"
  using rGamma_plus1[of "-1/2 :: real"]
  by (simp add: rGamma_inverse_Gamma divide_simps Gamma_one_half_real split: if_split_asm)

lemma gbinomial_asymptotic':
  assumes "z \<notin> \<nat>"
  shows   "(\<lambda>n. z gchoose (n + k)) \<sim>[at_top]
             (\<lambda>n. (-1)^(n+k) / (Gamma (-z) * of_nat n powr (z + 1)) :: real)"
proof -
  from assms have [simp]: "Gamma (-z) \<noteq> 0"
    by (simp_all add: Gamma_eq_zero_iff uminus_in_nonpos_Ints_iff)
  have "filterlim (\<lambda>n. n + k) at_top at_top"
    by (intro filterlim_subseq strict_mono_add)
  from asymp_equivI'_const[OF gbinomial_asymptotic[of z]] assms
    have "(\<lambda>n. z gchoose n) \<sim>[at_top] (\<lambda>n. (-1)^n / (Gamma (-z) * exp ((z+1) * ln (real n))))"
    by (simp add: Gamma_eq_zero_iff uminus_in_nonpos_Ints_iff field_simps)
  also have "eventually (\<lambda>n. exp ((z+1) * ln (real n)) = real n powr (z+1)) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim (simp add: powr_def)
  finally have "(\<lambda>x. z gchoose (x + k)) \<sim>[at_top]
                  (\<lambda>x. (- 1) ^ (x + k) / (Gamma (- z) * real (x + k) powr (z + 1)))"
    by (rule asymp_equiv_compose') (simp add: filterlim_subseq strict_mono_add)
  also have "(\<lambda>x. real x + real k) \<sim>[at_top] real"
    by (subst asymp_equiv_add_right) auto
  hence "(\<lambda>x. real (x + k) powr (z + 1)) \<sim>[at_top] (\<lambda>x. real x powr (z + 1))"
    by (intro asymp_equiv_powr_real) auto
  finally show ?thesis by - (simp_all add: asymp_equiv_intros)
qed



subsection \<open>Definition\<close>

text \<open>
  We define Catalan numbers by their well-known recursive definition. We shall later derive
  a few more equivalent definitions from this one.
\<close>

(*<*)
context
  notes [fundef_cong] = sum.cong
begin
(*>*)

fun catalan :: "nat \<Rightarrow> nat" where
  "catalan 0 = 1"
| "catalan (Suc n) = (\<Sum>i\<le>n. catalan i * catalan (n - i))"

(*<*)
end

declare catalan.simps(2) [simp del]
lemmas catalan_0 = catalan.simps(1)
lemmas catalan_Suc = catalan.simps(2)
lemma catalan_1 [simp]: "catalan (Suc 0) = 1" by (simp add: catalan_Suc)
(*>*)

text \<open>
  The easiest proof of the more profound properties of the Catalan numbers (such as their
  closed-form equation and their asymptotic growth) uses their ordinary generating function (OGF).
  This proof is almost mechanical in the sense that it does not require `guessing' the closed
  form; one can read it directly from the generating function.

  We therefore define the OGF of the Catalan numbers ($\sum_{n=0}^\infty C_n z^n$ in standard
  mathematical notation):
\<close>

definition "fps_catalan = Abs_fps (of_nat \<circ> catalan)"

lemma fps_catalan_nth [simp]: "fps_nth fps_catalan n = of_nat (catalan n)"
  by (simp add: fps_catalan_def)

text \<open>
  Given their recursive definition, it is easy to see that the OGF of the Catalan numbers
  satisfies the following recursive equation:
\<close>
lemma fps_catalan_recurrence:
  "fps_catalan = 1 + fps_X * fps_catalan^2"
proof (rule fps_ext)
  fix n :: nat
  show "fps_nth fps_catalan n = fps_nth (1 + fps_X * fps_catalan^2) n"
    by (cases n) (simp_all add: fps_square_nth catalan_Suc)
qed

text \<open>
  We can now easily solve this equation for @{term fps_catalan}: if we denote the unknown OGF as
  $F(z)$, we get $F(z) = \frac{1}{2}(1 - \sqrt{1 - 4z})$.

  Note that we do not actually use the square root as defined on real or complex numbers.
  Any $(1 + cz)^\alpha$ can be expressed using the formal power series whose coefficients are
  the generalised binomial coefficients, and thus we can do all of these transformations in a
  purely algebraic way: $\sqrt{1-4z} = (1+z)^{\frac{1}{2}} \circ (-4z)$ (where ${\circ}$ denotes
  composition of formal power series) and $(1+z)^\alpha$ has the well-known expansion
  $\sum_{n=0}^\infty {\alpha \choose n} z^n$.
\<close>
lemma fps_catalan_fps_binomial:
  "fps_catalan = (1/2 * (1 - (fps_binomial (1/2) oo (-4*fps_X)))) / fps_X"
proof (rule mult_eq_imp_eq_div)
  let ?F = "fps_catalan :: 'a fps"
  have "fps_X * (1 + fps_X * ?F^2) = fps_X * ?F" by (simp only: fps_catalan_recurrence [symmetric])
  hence "(1 / 2 - fps_X * ?F)\<^sup>2 = - fps_X + 1 / 4"
    by (simp add: algebra_simps power2_eq_square fps_numeral_simps)
  also have "\<dots> = (1/2 * (fps_binomial (1/2) oo (-4*fps_X)))^2"
    by (simp add: power_mult_distrib div_power fps_binomial_1 fps_binomial_power
                  fps_compose_power fps_compose_add_distrib ring_distribs)
  finally have "1/2 - fps_X * ?F = 1/2 * (fps_binomial (1/2) oo (-4*fps_X))"
    by (rule fps_power_eqD) simp_all
  thus "fps_X*?F = 1/2 * (1 - (fps_binomial (1/2) oo (-4*fps_X)))" by algebra
qed simp_all


subsection \<open>Closed-form formulae and more recurrences\<close>

text \<open>
  We can now read a closed-form formula for the Catalan numbers directly from the generating
  function $\frac{1}{2z}(1 - (1+z)^{\frac{1}{2}} \circ (-4z))$.
\<close>
theorem catalan_closed_form_gbinomial:
  "real (catalan n) = 2 * (- 4) ^ n * (1/2 gchoose Suc n)"
proof -
  have "(catalan n :: real) = fps_nth fps_catalan n" by simp
  also have "\<dots> = 2 * (- 4) ^ n * (1/2 gchoose Suc n)"
    by (subst fps_catalan_fps_binomial)
       (simp add: fps_div_fps_X_nth numeral_fps_const fps_compose_linear)
  finally show ?thesis .
qed

text \<open>
  This closed-form formula can easily be rewritten to the form $C_n = \frac{1}{n+1} {2n \choose n}$,
  which contains only `normal' binomial coefficients and not the generalised ones:
\<close>
lemma catalan_closed_form_aux:
  "catalan n * Suc n = (2*n) choose n"
proof -
  have "real ((2*n) choose n) = fact (2*n) / (fact n)^2"
    by (simp add: binomial_fact power2_eq_square)
  also have "(fact (2*n) :: real) = 4^n * pochhammer (1 / 2) n * fact n"
    by (simp add: fact_double power_mult)
  also have "\<dots> / (fact n)^2 / real (n+1) = real (catalan n)"
    by (simp add: catalan_closed_form_gbinomial gbinomial_pochhammer pochhammer_rec
          field_simps power2_eq_square power_mult_distrib [symmetric] del: of_nat_Suc)
  finally have "real (catalan n * Suc n) = real ((2*n) choose n)" by (simp add: field_simps)
  thus ?thesis by (simp only: of_nat_eq_iff)
qed

theorem of_nat_catalan_closed_form:
  "of_nat (catalan n) = (of_nat ((2*n) choose n) / of_nat (Suc n) :: 'a :: field_char_0)"
proof -
  have "of_nat (catalan n * Suc n) = of_nat ((2*n) choose n)"
    by (subst catalan_closed_form_aux) (rule refl)
  also have "of_nat (catalan n * Suc n) = of_nat (catalan n) * of_nat (Suc n)"
    by (simp only: of_nat_mult)
  finally show ?thesis by (simp add: divide_simps del: of_nat_Suc)
qed

theorem catalan_closed_form:
  "catalan n = ((2*n) choose n) div Suc n"
  by (subst catalan_closed_form_aux [symmetric]) (simp del: mult_Suc_right)

text \<open>
  The following is another nice closed-form formula for the Catalan numbers, which directly
  follows from the previous one:
\<close>
corollary catalan_closed_form':
  "catalan n = ((2*n) choose n) - ((2*n) choose (Suc n))"
proof (cases n)
  case (Suc m)
  have "real ((2*n) choose n) - real ((2*n) choose (Suc n)) =
          fact (2*m+2) / (fact (m+1))^2 - fact (2*m+2) / (real (m+2) * fact (m+1) * fact m)"
    by (subst (1 2) binomial_fact) (simp_all add: Suc power2_eq_square)
  also have "\<dots> = fact (2*m+2) / ((fact (m+1))^2 * real (m+2))"
    by (simp add: divide_simps power2_eq_square) (simp_all add: algebra_simps)
  also have "\<dots> = real (catalan n)"
    by (subst of_nat_catalan_closed_form, subst binomial_fact) (simp_all add: Suc power2_eq_square)
  finally show ?thesis by linarith
qed simp_all


text \<open>
  We can now easily show that the Catalan numbers also satisfy another, simpler recurrence,
  namely $C_{n+1} = \frac{2(2n+1)}{n+2} C_n$. We will later use this to prove code equations to
  compute the Catalan numbers more efficiently.
\<close>
lemma catalan_Suc_aux:
  "(n + 2) * catalan (Suc n) = 2 * (2 * n + 1) * catalan n"
proof -
  have "real (catalan (Suc n)) * real (n + 2) = real (catalan n) * 2 * real (2 * n + 1)"
  proof (cases n)
    case (Suc n)
    thus ?thesis
      by (subst (1 2) of_nat_catalan_closed_form, subst (1 2) binomial_fact)
         (simp_all add: divide_simps)
  qed simp_all
  hence "real ((n + 2) * catalan (Suc n)) = real (2 * (2 * n + 1) * catalan n)"
    by (simp only: mult_ac of_nat_mult)
  thus ?thesis by (simp only: of_nat_eq_iff)
qed

theorem of_nat_catalan_Suc':
  "of_nat (catalan (Suc n)) =
     (of_nat (2*(2*n+1)) / of_nat (n+2) * of_nat (catalan n) :: 'a :: field_char_0)"
proof -
  have "(of_nat (2*(2*n+1)) / of_nat (n+2) * of_nat (catalan n) :: 'a) =
          of_nat (2*(2*n + 1) * catalan n) / of_nat (n+2)"
    by (simp add: divide_simps mult_ac del: mult_Suc mult_Suc_right)
  also note catalan_Suc_aux[of n, symmetric]
  also have "of_nat ((n + 2) * catalan (Suc n)) / of_nat (n + 2) = (of_nat (catalan (Suc n)) :: 'a)"
    by (simp del: of_nat_Suc mult_Suc_right mult_Suc)
  finally show ?thesis ..
qed

theorem catalan_Suc':
  "catalan (Suc n) = (catalan n * (2*(2*n+1))) div (n+2)"
proof -
  from catalan_Suc_aux[of n] have "catalan n * (2*(2*n+1)) = catalan (Suc n) * (n+2)"
    by (simp add: algebra_simps)
  also have "\<dots> div (n+2) = catalan (Suc n)" by (simp del: mult_Suc mult_Suc_right)
  finally show ?thesis ..
qed



subsection \<open>Integral formula\<close>

text \<open>
  The recursive formula we have just proven allows us to derive an integral formula for 
  the Catalan numbers. The proof was adapted from a textbook proof by Steven Roman.~\cite{catalan}
\<close>

context
begin

private definition I :: "nat \<Rightarrow> real" where
  "I n = integral {0..4} (\<lambda>x. x powr (of_nat n - 1/2) * sqrt (4 - x))"

private lemma has_integral_I0: "((\<lambda>x. x powr (-(1/2)) * sqrt (4 - x)) has_integral 2*pi) {0..4}"
proof -
  have "\<And>x. x\<in>{0..4}-{} \<Longrightarrow> x powr (-(1/2)) * sqrt (4 - x) = sqrt ((4 - x) / x)"
    by (auto simp: powr_minus field_simps powr_half_sqrt real_sqrt_divide)
  thus ?thesis by (rule has_integral_spike[OF negligible_empty _ catalan_aux_integral])
qed

private lemma integrable_I: 
  "(\<lambda>x. x powr (of_nat n - 1/2) * sqrt (4 - x)) integrable_on {0..4}"
proof (cases "n = 0")
  case True
  with has_integral_I0 show ?thesis by (simp add: has_integral_integrable)
next
  case False
  thus ?thesis by (intro integrable_continuous_real continuous_on_mult continuous_on_powr')
                  (auto intro!: continuous_intros)
qed

private lemma I_Suc: "I (Suc n) = real (2 * (2*n + 1)) / real (n + 2) * I n"
proof -
  define u' u v v' 
    where "u' = (\<lambda>x. sqrt (4 - x :: real))" 
      and "u = (\<lambda>x. -2/3 * (4 - x) powr (3/2 :: real))"
      and "v = (\<lambda>x. x powr (real n + 1/2))" 
      and "v' = (\<lambda>x. (real n + 1/2) * x powr (real n - 1/2))"
  define c where "c = -2/3 * (real n + 1/2)"
  define i where "i = (\<lambda>n x. x powr (real n - 1/2) * sqrt (4 - x) :: real)"

  have "I (Suc n) = integral {0..4} (\<lambda>x. u' x * v x)"
    unfolding I_def by (simp add: algebra_simps u'_def v_def)
  have "((\<lambda>x. u' x * v x) has_integral - c * (4 * I n - I (Suc n))) {0..4}"
  proof (rule integration_by_parts_interior[OF bounded_bilinear_mult])
    show "continuous_on {0..4} u" unfolding u_def
      by (intro continuous_on_powr' continuous_on_mult) (auto intro!: continuous_intros)
    show "continuous_on {0..4} v" unfolding v_def
      by (intro continuous_on_powr' continuous_on_mult) (auto intro!: continuous_intros)
    fix x :: real assume x: "x \<in> {0<..<4}"
    from x show "(u has_vector_derivative u' x) (at x)"
      unfolding has_field_derivative_iff_has_vector_derivative [symmetric] u_def u'_def
      by (auto intro!: derivative_eq_intros simp: field_simps powr_half_sqrt)
    from x show "(v has_vector_derivative v' x) (at x)"
      unfolding has_field_derivative_iff_has_vector_derivative [symmetric] v_def v'_def
      by (auto intro!: derivative_eq_intros simp: field_simps)
  next
    show "((\<lambda>x. u x * v' x) has_integral u 4 * v 4 - u 0 * v 0 - - c * (4 * I n - I (Suc n))) {0..4}"
    proof (rule has_integral_spike; (intro ballI)?)
      fix x :: real assume x: "x \<in> {0..4}-{0}"
      have "u x * v' x = c * ((4 - x) powr (1 + 1/2) * x powr (real n - 1/2))"
        by (simp add: u_def v'_def c_def)
      also from x have "(4 - x) powr (1 + 1/2) = (4 - x) * sqrt (4 - x)"
        by (subst powr_add) (simp_all add: powr_half_sqrt)
      also have "\<dots> * x powr (real n - 1/2) = 4 * sqrt (4 - x) * x powr (real n - 1/2) - 
                     sqrt (4 - x) * x powr (real n - 1/2 + 1)"
        by (subst powr_add) (insert x, simp add: field_simps)
      also have "real n - 1/2 + 1 = real (Suc n) - 1/2" by simp
      finally show "u x * v' x = c * (4 * i n x - i (Suc n) x)" by (simp add: i_def)
    next
      have "((\<lambda>x. c * (4 * i n x - i (Suc n) x)) has_integral c * (4 * I n - I (Suc n))) {0..4}"
        unfolding i_def I_def 
        by (intro has_integral_mult_right has_integral_diff integrable_integral integrable_I)
      thus "((\<lambda>x. c * (4 * i n x - i (Suc n) x)) has_integral  u 4 * v 4 - u 0 * v 0 - -
               c * (4 * I n - I (Suc n))) {0..4}" by (simp add: u_def v_def)
    qed simp_all
  qed simp_all
  also have "(\<lambda>x. u' x * v x) = i (Suc n)" 
    by (rule ext) (simp add: u'_def v_def i_def algebra_simps)
  finally have "I (Suc n) = - c * (4 * I n - I (Suc n))" unfolding I_def i_def by blast
  hence "(1 - c) * I (Suc n) = -4 * c * I n" by algebra
  hence "I (Suc n) = (-4 * c) / (1 - c) * I n" by (simp add: field_simps c_def)
  also have "(-4 * c) / (1 - c) = real (2*(2*n + 1)) / real (n + 2)" 
    by (simp add: c_def field_simps)
  finally show ?thesis .
qed

private lemma catalan_eq_I: "real (catalan n) = I n / (2 * pi)"
proof (induction n)
  case 0
  thus ?case using has_integral_I0 by (simp add: I_def integral_unique)
next
  case (Suc n)
  show ?case by (simp add: of_nat_catalan_Suc' Suc.IH I_Suc)
qed

theorem catalan_integral_form:
  "((\<lambda>x. x powr (real n - 1 / 2) * sqrt (4 - x) / (2*pi)) 
       has_integral real (catalan n)) {0..4}"
proof -
  have "((\<lambda>x. x powr (real n - 1 / 2) * sqrt (4 - x) * inverse (2*pi)) has_integral 
           I n * inverse (2 * pi)) {0..4}" unfolding I_def
    by (intro has_integral_mult_left integrable_integral integrable_I)
  thus ?thesis by (simp add: catalan_eq_I field_simps)
qed

end


subsection \<open>Asymptotics\<close>

text \<open>
  Using the closed form $C_n = 2 \cdot (-4)^n {\frac{1}{2} \choose n+1}$ and the fact that
  ${\alpha \choose n} \sim \frac{(-1)^n}{\Gamma(-\alpha) n^{\alpha + 1}}$ for any
  $\alpha \notin \mathbb{N}$, wwe can now easily analyse the asymptotic behaviour of the
  Catalan numbers:
\<close>
theorem catalan_asymptotics:
  "catalan \<sim>[at_top] (\<lambda>n. 4 ^ n / (sqrt pi * n powr (3/2)))"
proof -
  have "catalan \<sim>[at_top] (\<lambda>n. 2 * (- 4) ^ n * (1/2 gchoose (n+1)))"
    by (subst catalan_closed_form_gbinomial) simp_all
  also have "(\<lambda>n. 1/2 gchoose (n+1)) \<sim>[at_top] (\<lambda>n. (-1)^(n+1) / (Gamma (-(1/2)) * real n powr (1/2 + 1)))"
    using fraction_not_in_nats[of 2 1] by (intro asymp_equiv_intros gbinomial_asymptotic') simp_all
  also have "(\<lambda>n. 2 * (- 4) ^ n * \<dots> n) = (\<lambda>n. 4 ^ n / (sqrt pi * n powr (3/2)))"
    by (intro ext) (simp add: Gamma_minus_one_half_real power_mult_distrib [symmetric])
  finally show ?thesis by - (simp_all add: asymp_equiv_intros)
qed


subsection \<open>Relation to binary trees\<close>

(*<*)
context
begin
(*>*)

text \<open>
  It is well-known that the Catalan number $C_n$ is the number of rooted binary trees with
  $n$ internal nodes (where internal nodes are those with two children and external nodes
  are those with no children).

  We will briefly show this here to show that the above asymptotic formula also describes the
  number of binary trees of a given size.
\<close>

qualified datatype tree = Leaf | Node tree tree

qualified primrec count_nodes :: "tree \<Rightarrow> nat" where
  "count_nodes Leaf = 0"
| "count_nodes (Node l r) = 1 + count_nodes l + count_nodes r"

qualified definition trees_of_size :: "nat \<Rightarrow> tree set" where
  "trees_of_size n = {t. count_nodes t = n}"

lemma count_nodes_eq_0_iff [simp]: "count_nodes t = 0 \<longleftrightarrow> t = Leaf"
  by (cases t) simp_all

lemma trees_of_size_0 [simp]: "trees_of_size 0 = {Leaf}"
  by (simp add: trees_of_size_def)

lemma trees_of_size_Suc:
  "trees_of_size (Suc n) = (\<lambda>(l,r). Node l r) ` (\<Union>k\<le>n. trees_of_size k \<times> trees_of_size (n - k))"
    (is "?lhs = ?rhs")
proof (rule set_eqI)
  fix t show "t \<in> ?lhs \<longleftrightarrow> t \<in> ?rhs" by (cases t) (auto simp: trees_of_size_def)
qed

lemma finite_trees_of_size [simp,intro]: "finite (trees_of_size n)"
  by (induction n rule: catalan.induct)
     (auto simp: trees_of_size_Suc intro!: finite_imageI finite_cartesian_product)

lemma trees_of_size_nonempty: "trees_of_size n \<noteq> {}"
  by (induction n rule: catalan.induct) (auto simp: trees_of_size_Suc)

lemma trees_of_size_disjoint:
  assumes "m \<noteq> n"
  shows   "trees_of_size m \<inter> trees_of_size n = {}"
  using assms by (auto simp: trees_of_size_def)

theorem card_trees_of_size: "card (trees_of_size n) = catalan n"
  by (induction n rule: catalan.induct)
     (simp_all add: catalan_Suc trees_of_size_Suc card_image inj_on_def
        trees_of_size_disjoint Times_Int_Times catalan_Suc card_UN_disjoint)

(*<*)
end
(*>*)


subsection \<open>Efficient computation\<close>

(*<*)
context
begin
(*>*)

text \<open>
  We shall now prove code equations that allow more efficient computation of Catalan numbers.
  In order to do this, we define a tail-recursive function that uses the recurrence
  @{thm catalan_Suc'[no_vars]}:
\<close>
qualified function catalan_aux where [simp del]:
  "catalan_aux n k acc =
     (if k \<ge> n then acc else catalan_aux n (Suc k) ((acc * (2*(2*k+1))) div (k+2)))"
  by auto
termination by (relation "Wellfounded.measure (\<lambda>(a,b,_). a - b)") simp_all

qualified lemma catalan_aux_simps:
  "k \<ge> n \<Longrightarrow> catalan_aux n k acc = acc"
  "k < n \<Longrightarrow> catalan_aux n k acc = catalan_aux n (Suc k) ((acc * (2*(2*k+1))) div (k+2))"
  by (subst catalan_aux.simps, simp)+

qualified lemma catalan_aux_correct:
  assumes "k \<le> n"
  shows   "catalan_aux n k (catalan k) = catalan n"
using assms
proof (induction n k "catalan k" rule: catalan_aux.induct)
  case (1 n k)
  show ?case
  proof (cases "k < n")
    case True
    hence "catalan_aux n k (catalan k) = catalan_aux n (Suc k) (catalan (Suc k))"
      by (subst catalan_Suc') (simp_all add: catalan_aux_simps)
    with 1 True show ?thesis by (simp add: catalan_Suc')
  qed (insert "1.prems", simp_all add: catalan_aux_simps)
qed

lemma catalan_code [code]: "catalan n = catalan_aux n 0 1"
  using catalan_aux_correct[of 0 n] by simp

(*<*)
end
(*>*)

end
