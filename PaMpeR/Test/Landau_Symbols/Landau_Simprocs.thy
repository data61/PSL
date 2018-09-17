(*
  File:   Landau_Simprocs.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Simplification procedures for Landau symbols, with a particular focus on functions into the reals.
*)
section {* Simplification procedures *}

theory Landau_Simprocs
imports Landau_Real_Products
begin

subsection {* Simplification under Landau symbols *}

text {* 
  The following can be seen as simpset for terms under Landau symbols. 
  When given a rule @{term "f \<in> \<Theta>(g)"}, the simproc will attempt to rewrite any occurrence of 
  @{term "f"} under a Landau symbol to @{term "g"}.
*}

named_theorems landau_simp "BigTheta rules for simplification of Landau symbols"
setup {*
  let
    val eq_thms = @{thms landau_theta.cong_bigtheta}
    fun eq_rule thm = get_first (try (fn eq_thm => eq_thm OF [thm])) eq_thms
  in
    Global_Theory.add_thms_dynamic
      (@{binding landau_simps},
        fn context =>
          Named_Theorems.get (Context.proof_of context) @{named_theorems landau_simp}
          |> map_filter eq_rule)
  end;
*}


lemma bigtheta_const [landau_simp]:
  "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (\<lambda>x. c) \<in> \<Theta>(\<lambda>x. 1)" by simp

lemmas [landau_simp] = bigtheta_const_ln bigtheta_const_ln_powr bigtheta_const_ln_pow

lemma bigtheta_const_ln' [landau_simp]: 
  "0 < a \<Longrightarrow> (\<lambda>x::real. ln (x * a)) \<in> \<Theta>(ln)"
  by (subst mult.commute) (rule bigtheta_const_ln)

lemma bigtheta_const_ln_powr' [landau_simp]: 
  "0 < a \<Longrightarrow> (\<lambda>x::real. ln (x * a) powr p) \<in> \<Theta>(\<lambda>x. ln x powr p)"
  by (subst mult.commute) (rule bigtheta_const_ln_powr)

lemma bigtheta_const_ln_pow' [landau_simp]: 
  "0 < a \<Longrightarrow> (\<lambda>x::real. ln (x * a) ^ p) \<in> \<Theta>(\<lambda>x. ln x ^ p)"
  by (subst mult.commute) (rule bigtheta_const_ln_pow)



subsection {* Simproc setup *}


lemma landau_gt_1_cong: 
  "landau_symbol L L' Lr \<Longrightarrow> (\<And>x::real. x > 1 \<Longrightarrow> f x = g x) \<Longrightarrow> L at_top (f) = L at_top (g)"
  by (auto intro: eventually_mono [OF eventually_gt_at_top[of 1]] elim!: landau_symbol.cong)

lemma landau_gt_1_in_cong: 
  "landau_symbol L L' Lr \<Longrightarrow> (\<And>x::real. x > 1 \<Longrightarrow> f x = g x) \<Longrightarrow> f \<in> L at_top (h) \<longleftrightarrow> g \<in> L at_top (h)"
  by (auto intro: eventually_mono [OF eventually_gt_at_top[of 1]] elim!: landau_symbol.in_cong)

lemma landau_prop_equalsI:
  "landau_symbol L L' Lr \<Longrightarrow> (\<And>x::real. x > 1 \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> (\<And>x. x > 1 \<Longrightarrow> g1 x = g2 x) \<Longrightarrow> 
     f1 \<in> L at_top (g1) \<longleftrightarrow> f2 \<in> L at_top (g2)"
apply (subst landau_gt_1_cong, assumption+)
apply (subst landau_gt_1_in_cong, assumption+)
apply (rule refl)
done


lemma ab_diff_conv_add_uminus': "(a::_::ab_group_add) - b = -b + a" by simp
lemma extract_diff_middle: "(a::_::ab_group_add) - (x + b) = -x + (a - b)" by simp

lemma divide_inverse': "(a::_::{division_ring,ab_semigroup_mult}) / b = inverse b * a"
  by (simp add: divide_inverse mult.commute)
lemma extract_divide_middle:"(a::_::{field}) / (x * b) = inverse x * (a / b)"
  by (simp add: divide_inverse algebra_simps)

lemmas landau_cancel = landau_symbol.mult_cancel_left

lemmas mult_cancel_left' = landau_symbol.mult_cancel_left[OF _ bigtheta_refl eventually_nonzeroD]

lemma mult_cancel_left_1:
  assumes "landau_symbol L L' Lr" "eventually_nonzero F f"
  shows   "f \<in> L F (\<lambda>x. f x * g2 x) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (g2)"
          "(\<lambda>x. f x * f2 x) \<in> L F (f) \<longleftrightarrow> f2 \<in> L F (\<lambda>_. 1)"
          "f \<in> L F (f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (\<lambda>_. 1)"
  using mult_cancel_left'[OF assms, of "\<lambda>_. 1"] mult_cancel_left'[OF assms, of _ "\<lambda>_. 1"]
        mult_cancel_left'[OF assms, of "\<lambda>_. 1" "\<lambda>_. 1"] by simp_all

lemmas landau_mult_cancel_simps = mult_cancel_left' mult_cancel_left_1

ML_file "landau_simprocs.ML"

lemmas bigtheta_simps = 
  landau_theta.cong_bigtheta[OF bigtheta_const_ln]
  landau_theta.cong_bigtheta[OF bigtheta_const_ln_powr]


text \<open>
  The following simproc attempts to cancel common factors in Landau symbols, i.\,e.\ in a
  goal like $f(x) h(x) \in L(g(x) h(x))$, the common factor $h(x)$ will be cancelled. This only
  works if the simproc can prove that $h(x)$ is eventually non-zero, for which it uses some
  heuristics.
\<close>
simproc_setup landau_cancel_factor (
    "f \<in> o[F](g)" | "f \<in> O[F](g)" | "f \<in> \<omega>[F](g)" | "f \<in> \<Omega>[F](g)" | "f \<in> \<Theta>[F](g)"
  ) = {* K Landau.cancel_factor_simproc *}

text \<open>
  The next simproc attempts to cancel dominated summands from Landau symbols; e.\,g.\ $O(x + \ln x)$
  is simplified to $O(x)$, since $\ln x \in o(x)$. This can be very slow on large terms, so it
  is not enabled by default.
\<close>
simproc_setup simplify_landau_sum (
    "o[F](\<lambda>x. f x)" | "O[F](\<lambda>x. f x)" | "\<omega>[F](\<lambda>x. f x)" | "\<Omega>[F](\<lambda>x. f x)" | "\<Theta>[F](\<lambda>x. f x)" |
    "f \<in> o[F](g)" | "f \<in> O[F](g)" | "f \<in> \<omega>[F](g)" | "f \<in> \<Omega>[F](g)" | "f \<in> \<Theta>[F](g)"
  ) = {* K (Landau.lift_landau_simproc Landau.simplify_landau_sum_simproc) *}


text \<open>
  This simproc attempts to simplify factors of an expression in a Landau symbol statement
  independently from another, i.\,e.\ in something like $O(f(x) g(x)$, a simp rule that rewrites
  $O(f(x))$ to $O(f'(x))$ will also rewrite $O(f(x) g(x))$ to $O(f'(x) g(x))$ without any further
  setup.
\<close>
simproc_setup simplify_landau_product (
    "o[F](\<lambda>x. f x)" | "O[F](\<lambda>x. f x)" | "\<omega>[F](\<lambda>x. f x)" | "\<Omega>[F](\<lambda>x. f x)" | "\<Theta>[F](\<lambda>x. f x)" |
    "f \<in> o[F](g)" | "f \<in> O[F](g)" | "f \<in> \<omega>[F](g)" | "f \<in> \<Omega>[F](g)" | "f \<in> \<Theta>[F](g)"
  ) = {* K (Landau.lift_landau_simproc Landau.simplify_landau_product_simproc) *}

text \<open>
  Lastly, the next very specialised simproc can solve goals of the form 
  $f(x) \in L(g(x))$ where $f$ and $g$ are real-valued functions consisting only of multiplications,
  powers of $x$, and powers of iterated logarithms of $x$. This is done by rewriting both sides
  into the form $x^a (\ln x)^b (\ln \ln x)^c$ etc.\ and then comparing the exponents
  lexicographically.

  Note that for historic reasons, this only works for $x\to\infty$.
\<close>
simproc_setup landau_real_prod (
    "(f :: real \<Rightarrow> real) \<in> o(g)" | "(f :: real \<Rightarrow> real) \<in> O(g)" |
    "(f :: real \<Rightarrow> real) \<in> \<omega>(g)" | "(f :: real \<Rightarrow> real) \<in> \<Omega>(g)" |
    "(f :: real \<Rightarrow> real) \<in> \<Theta>(g)"
  ) = {* K Landau.simplify_landau_real_prod_prop_simproc *}


subsection {* Tests *}

lemma asymp_equiv_plus_const_left: "(\<lambda>n. c + real n) \<sim>[at_top] (\<lambda>n. real n)"
  by (subst asymp_equiv_add_left) (auto intro!: asymp_equiv_intros eventually_gt_at_top)

lemma asymp_equiv_plus_const_right: "(\<lambda>n. real n + c) \<sim>[at_top] (\<lambda>n. real n)"
  using asymp_equiv_plus_const_left[of c] by (simp add: add.commute)


subsubsection {* Product simplification tests *}

lemma "(\<lambda>x::real. f x * x) \<in> O(\<lambda>x. g x / (h x / x)) \<longleftrightarrow> f \<in> O(\<lambda>x. g x / h x)"
  by simp

lemma "(\<lambda>x::real. x) \<in> \<omega>(\<lambda>x. g x / (h x / x)) \<longleftrightarrow> (\<lambda>x. 1) \<in> \<omega>(\<lambda>x. g x / h x)"
  by simp


subsubsection {* Real product decision procure tests *}

lemma "(\<lambda>x. x powr 1) \<in> O(\<lambda>x. x powr 2 :: real)"
  by simp

lemma "\<Theta>(\<lambda>x::real. 2*x powr 3 - 4*x powr 2) = \<Theta>(\<lambda>x::real. x powr 3)"
  by (simp add: landau_theta.absorb)

lemma "p < q \<Longrightarrow> (\<lambda>x::real. c * x powr p * ln x powr r) \<in> o(\<lambda>x::real. x powr q)"
  by simp

lemma "c \<noteq> 0 \<Longrightarrow> p > q \<Longrightarrow> (\<lambda>x::real. c * x powr p * ln x powr r) \<in> \<omega>(\<lambda>x::real. x powr q)"
  by simp

lemma "b > 0 \<Longrightarrow> (\<lambda>x::real. x / ln (2*b*x) * 2) \<in> o(\<lambda>x. x * ln (b*x))"
  by simp
lemma "o(\<lambda>x::real. x * ln (3*x)) = o(\<lambda>x. ln x * x)"
  by (simp add: mult.commute)
lemma "(\<lambda>x::real. x) \<in> o(\<lambda>x. x * ln (3*x))" by simp

ML_val {*
  Landau.simplify_landau_real_prod_prop_conv @{context} 
  @{cterm "(\<lambda>x::real. 5 * ln (ln x) ^ 2 / (2*x) powr 1.5 * inverse 2) \<in> 
           \<omega>(\<lambda>x. 3 * ln x * ln x / x * ln (ln (ln (ln x))))"}
*}

lemma "(\<lambda>x. 3 * ln x * ln x / x * ln (ln (ln (ln x)))) \<in> 
         \<omega>(\<lambda>x::real. 5 * ln (ln x) ^ 2 / (2*x) powr 1.5 * inverse 2)"
  by simp



subsubsection {* Sum cancelling tests *}

lemma "\<Theta>(\<lambda>x::real. 2 * x powr 3 + x * x^2/ln x) = \<Theta>(\<lambda>x::real. x powr 3)"
  by simp

(* TODO: tweak simproc with size threshold *)
lemma "\<Theta>(\<lambda>x::real. 2 * x powr 3 + x * x^2/ln x + 42 * x powr 9 + 213 * x powr 5 - 4 * x powr 7) = 
         \<Theta>(\<lambda>x::real. x ^ 3 + x / ln x * x powr (3/2) - 2*x powr 9)"
  using [[landau_sum_limit = 5]] by simp

lemma "(\<lambda>x::real. x + x * ln (3*x)) \<in> o(\<lambda>x::real. x^2 + ln (2*x) powr 3)" by simp

end
