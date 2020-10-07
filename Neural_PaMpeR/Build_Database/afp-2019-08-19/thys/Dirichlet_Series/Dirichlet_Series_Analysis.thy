(*
    File:      Dirichlet_Series_Analysis.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Analytic properties of Dirichlet series\<close>
theory Dirichlet_Series_Analysis
imports
  "HOL-Analysis.Analysis"
  "HOL-Library.Going_To_Filter"
  "HOL-Real_Asymp.Real_Asymp"
  Dirichlet_Series
  Moebius_Mu
  Partial_Summation
  Euler_Products
begin

(* TODO Move *)
lemma frequently_eventually_frequently:
  "frequently P F \<Longrightarrow> eventually Q F \<Longrightarrow> frequently (\<lambda>x. P x \<and> Q x) F"
  by (erule frequently_rev_mp, erule eventually_mono) auto

text \<open>
  The following illustrates a concept we will need later on: A property holds for
  \<open>f\<close> going to \<open>F\<close> if we can find e.\,g.\ a sequence that tends to \<open>F\<close> and whose elements
  eventually satisfy \<open>P\<close>.
\<close>
lemma frequently_going_toI:
  assumes "filterlim (\<lambda>n. f (g n)) F G"
  assumes "eventually (\<lambda>n. P (g n)) G"
  assumes "eventually (\<lambda>n. g n \<in> A) G"
  assumes "G \<noteq> bot"
  shows   "frequently P (f going_to F within A)"
  unfolding frequently_def
proof
  assume "eventually (\<lambda>x. \<not>P x) (f going_to F within A)"
  hence "eventually (\<lambda>x. \<not>P x) (inf (filtercomap f F) (principal A))"
    by (simp add: going_to_within_def)
  moreover have "filterlim (\<lambda>n. g n) (inf (filtercomap f F) (principal A)) G"
    using assms unfolding filterlim_inf filterlim_principal
    by (auto simp add: filterlim_iff_le_filtercomap filtercomap_filtercomap)
  ultimately have "eventually (\<lambda>n. \<not>P (g n)) G"
    by (rule eventually_compose_filterlim)
  with assms(2) have "eventually (\<lambda>_. False) G" by eventually_elim auto
  with assms(4) show False by simp
qed

lemma frequently_filtercomapI:
  assumes "filterlim (\<lambda>n. f (g n)) F G"
  assumes "eventually (\<lambda>n. P (g n)) G"
  assumes "G \<noteq> bot"
  shows   "frequently P (filtercomap f F)"
  using frequently_going_toI[of f g F G P UNIV] assms by (simp add: going_to_def)

lemma frequently_going_to_at_topE:
  fixes f :: "'a \<Rightarrow> real"
  assumes "frequently P (f going_to at_top)"
  obtains g where "\<And>n. P (g n)" and "filterlim (\<lambda>n. f (g n)) at_top sequentially"
proof -
  from assms have "\<forall>k. \<exists>x. f x \<ge> real k \<and> P x"
    by (auto simp: frequently_def eventually_going_to_at_top_linorder)
  hence "\<exists>g. \<forall>k. f (g k) \<ge> real k \<and> P (g k)"
    by metis
  then obtain g where g: "\<And>k. f (g k) \<ge> real k" "\<And>k. P (g k)"
    by blast
  have "filterlim (\<lambda>n. f (g n)) at_top sequentially"
    by (rule filterlim_at_top_mono[OF filterlim_real_sequentially]) (use g in auto)
  from g(2) and this show ?thesis using that[of g] by blast
qed

text \<open>
  Apostol often uses statements like `$P(s_k)$ for all $k$ in an infinite sequence
  $s_k$ such that $\mathfrak{R}(s_k)\longrightarrow\infty$ as $k\to\infty$'.

  Instead, we write @{prop "frequently P (Re going_to at_top)"}. This lemma shows that
  our statement is equivalent to his.
\<close>
lemma frequently_going_to_at_top_iff:
  "frequently P (f going_to (at_top :: real filter)) \<longleftrightarrow>
     (\<exists>g. \<forall>n. P (g n) \<and> filterlim (\<lambda>n. f (g n)) at_top sequentially)"
  by (auto intro: frequently_going_toI elim!: frequently_going_to_at_topE)
(* END TODO *)

lemma surj_bullet_1: "surj (\<lambda>s::'a::{real_normed_algebra_1, real_inner}. s \<bullet> 1)"
proof (rule surjI)
  fix x :: real show "(x *\<^sub>R 1) \<bullet> (1 :: 'a) = x"
    by (simp add: dot_square_norm)
qed  

lemma bullet_1_going_to_at_top_neq_bot [simp]:
  "((\<lambda>s::'a::{real_normed_algebra_1, real_inner}. s \<bullet> 1) going_to at_top) \<noteq> bot"
  unfolding going_to_def by (rule filtercomap_neq_bot_surj[OF _ surj_bullet_1]) auto



lemma fds_abs_converges_altdef:
  "fds_abs_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f n / nat_power n s) abs_summable_on {1..}"
  by (auto simp add: fds_abs_converges_def abs_summable_on_nat_iff
           intro!: summable_cong eventually_mono[OF eventually_gt_at_top[of 0]])

lemma fds_abs_converges_altdef':
  "fds_abs_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f n / nat_power n s) abs_summable_on UNIV"
  by (subst fds_abs_converges_altdef, rule abs_summable_on_cong_neutral) (auto simp: Suc_le_eq)

lemma eval_fds_altdef:
  assumes "fds_abs_converges f s"
  shows   "eval_fds f s = (\<Sum>\<^sub>an. fds_nth f n / nat_power n s)"
proof -
  have "fds_abs_converges f s \<longleftrightarrow> (\<lambda>n. fds_nth f n / nat_power n s) abs_summable_on UNIV"
    unfolding fds_abs_converges_altdef 
    by (intro abs_summable_on_cong_neutral) (auto simp: Suc_le_eq)
  with assms show ?thesis unfolding eval_fds_def fds_abs_converges_altdef
    by (intro infsetsum_nat' [symmetric]) simp_all
qed

lemma multiplicative_function_divide_nat_power:
  fixes f :: "nat \<Rightarrow> 'a :: {nat_power, field}"
  assumes "multiplicative_function f"
  shows   "multiplicative_function (\<lambda>n. f n / nat_power n s)"
proof
  interpret f: multiplicative_function f by fact
  show "f 0 / nat_power 0 s = 0" "f 1 / nat_power 1 s = 1"
    by simp_all
  fix a b :: nat assume "a > 1" "b > 1" "coprime a b"
  thus "f (a * b) / nat_power (a * b) s = f a / nat_power a s * (f b / nat_power b s)"
    by (simp_all add: f.mult_coprime nat_power_mult_distrib)
qed

lemma completely_multiplicative_function_divide_nat_power:
  fixes f :: "nat \<Rightarrow> 'a :: {nat_power, field}"
  assumes "completely_multiplicative_function f"
  shows   "completely_multiplicative_function (\<lambda>n. f n / nat_power n s)"
proof
  interpret f: completely_multiplicative_function f by fact
  show "f 0 / nat_power 0 s = 0" "f (Suc 0) / nat_power (Suc 0) s = 1"
    by simp_all
  fix a b :: nat assume "a > 1" "b > 1"
  thus "f (a * b) / nat_power (a * b) s = f a / nat_power a s * (f b / nat_power b s)"
    by (simp_all add: f.mult nat_power_mult_distrib)
qed

subsection \<open>Convergence and absolute convergence\<close>

class nat_power_normed_field = nat_power_field + real_normed_field + real_inner + real_algebra_1 +
  fixes real_power :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes real_power_nat_power: "n > 0 \<Longrightarrow> real_power (real n) c = nat_power n c"
  assumes real_power_1_right_aux: "d > 0 \<Longrightarrow> real_power d 1 = d *\<^sub>R 1"
  assumes real_power_add: "d > 0 \<Longrightarrow> real_power d (a + b) = real_power d a * real_power d b"
  assumes real_power_nonzero [simp]: "d > 0 \<Longrightarrow> real_power d a \<noteq> 0"
  assumes norm_real_power: "x > 0 \<Longrightarrow> norm (real_power x c) = x powr (c \<bullet> 1)"
  assumes nat_power_of_real_aux: "nat_power n (x *\<^sub>R 1) = ((real n powr x) *\<^sub>R 1)"
  assumes has_field_derivative_nat_power_aux:
            "\<And>x::'a. n > 0 \<Longrightarrow> LIM y inf_class.inf
              (Inf (principal ` {S. open S \<and> x \<in> S})) (principal (UNIV - {x})).
                (nat_power n y - nat_power n x - ln (real n) *\<^sub>R nat_power n x * (y - x)) /\<^sub>R
                norm (y - x) :> Inf (principal ` {S. open S \<and> 0 \<in> S})"
  assumes has_vector_derivative_real_power_aux:
            "x > 0 \<Longrightarrow> filterlim (\<lambda>y. (real_power y c - real_power x (c :: 'a) -
               (y - x) *\<^sub>R (c * real_power x (c - 1))) /\<^sub>R
               norm (y - x)) (INF S\<in>{S. open S \<and> 0 \<in> S}. principal S) (at x)"
  assumes norm_nat_power: "n > 0 \<Longrightarrow> norm (nat_power n y) = real n powr (y \<bullet> 1)"
begin

lemma real_power_diff: "d > 0 \<Longrightarrow> real_power d (a - b) = real_power d a / real_power d b"
  using real_power_add[of d b "a - b"] by (simp add: field_simps)

end

lemma real_power_1_right [simp]: "d > 0 \<Longrightarrow> real_power d 1 = of_real d"
  using real_power_1_right_aux[of d] by (simp add: scaleR_conv_of_real)


lemma has_vector_derivative_real_power [derivative_intros]:
  "x > 0 \<Longrightarrow> ((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x within A)"
  by (rule has_vector_derivative_at_within)
     (insert has_vector_derivative_real_power_aux[of x c],
      simp add: has_vector_derivative_def has_derivative_def
                nhds_def bounded_linear_scaleR_left)
              
lemma has_field_derivative_nat_power [derivative_intros]:
  "n > 0 \<Longrightarrow> ((\<lambda>y. nat_power n y) has_field_derivative ln (real n) *\<^sub>R nat_power n x)
     (at (x :: 'a :: nat_power_normed_field) within A)"
  by (rule has_field_derivative_at_within)
     (insert has_field_derivative_nat_power_aux[of n x],
      simp only: has_field_derivative_def has_derivative_def netlimit_at,
      simp add: nhds_def at_within_def bounded_linear_mult_right)
              
lemma continuous_on_real_power [continuous_intros]: 
  "A \<subseteq> {0<..} \<Longrightarrow> continuous_on A (\<lambda>x. real_power x s)"
  by (rule continuous_on_vector_derivative has_vector_derivative_real_power)+ auto

instantiation real :: nat_power_normed_field
begin

definition real_power_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  [simp]: "real_power_real = (powr)"
  
instance proof (standard, goal_cases)
  case (7 n x)
  hence "((\<lambda>x. nat_power n x) has_field_derivative ln (real n) *\<^sub>R nat_power n x) (at x)"
    by (auto intro!: derivative_eq_intros simp: powr_def)
  thus ?case unfolding has_field_derivative_def netlimit_at has_derivative_def
    by (simp add: nhds_def at_within_def)
next
  case (8 x c)
  hence "((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x)"
    by (auto intro!: derivative_eq_intros
             simp: has_field_derivative_iff_has_vector_derivative [symmetric])
  thus ?case by (simp add: has_vector_derivative_def has_derivative_def nhds_def)
qed (simp_all add: powr_add)

end


instantiation complex :: nat_power_normed_field
begin
  
definition nat_power_complex :: "nat \<Rightarrow> complex \<Rightarrow> complex" where
   [simp]: "nat_power_complex n z = of_nat n powr z"

definition real_power_complex :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  [simp]: "real_power_complex = (\<lambda>x y. of_real x powr y)"
  
instance proof
  fix m n :: nat and z :: complex
  assume "m > 0" "n > 0"
  thus "nat_power (m * n) z = nat_power m z * nat_power n z"
    unfolding nat_power_complex_def of_nat_mult by (subst powr_times_real) simp_all
next
  fix n :: nat and z :: complex
  assume "n > 0"
  show "norm (nat_power n z) = real n powr (z \<bullet> 1)" unfolding nat_power_complex_def
    using norm_powr_real_powr[of "of_nat n" z] by simp
next
  fix n :: nat and x :: complex assume n: "n > 0"
  hence "((\<lambda>x. nat_power n x) has_field_derivative ln (real n) *\<^sub>R nat_power n x) (at x)"
    by (auto intro!: derivative_eq_intros simp: powr_def scaleR_conv_of_real mult_ac)
  thus "LIM y inf_class.inf (Inf (principal ` {S. open S \<and> x \<in> S})) (principal (UNIV - {x})).
           (nat_power n y - nat_power n x - ln (real n) *\<^sub>R nat_power n x * (y - x)) /\<^sub>R
           cmod (y - x) :> (Inf (principal ` {S. open S \<and> 0 \<in> S}))"
    unfolding has_field_derivative_def netlimit_at has_derivative_def
    by (simp add: nhds_def at_within_def)
next
  fix x :: real and c :: complex assume "x > 0"
  hence "((\<lambda>y. real_power y c) has_vector_derivative c * real_power x (c - 1)) (at x)"
    by (auto intro!: derivative_eq_intros has_vector_derivative_real_complex)
  thus "LIM y at x. (real_power y c - real_power x c - (y - x) *\<^sub>R (c * real_power x (c - 1))) /\<^sub>R
           norm (y - x) :> INF S\<in>{S. open S \<and> 0 \<in> S}. principal S"
    by (simp add: has_vector_derivative_def has_derivative_def nhds_def)
next
  fix n :: nat and x :: real
  show "nat_power n (x *\<^sub>R 1 :: complex) = (real n powr x) *\<^sub>R 1"
    by (simp add: powr_Reals_eq scaleR_conv_of_real)
qed (auto simp: powr_def exp_add exp_of_nat_mult [symmetric] algebra_simps scaleR_conv_of_real
          simp del: Ln_of_nat)

end

lemma nat_power_of_real [simp]:
  "nat_power n (of_real x :: 'a :: nat_power_normed_field) = of_real (real n powr x)"
  using nat_power_of_real_aux[of n x] by (simp add: scaleR_conv_of_real)

lemma fds_abs_converges_of_real [simp]: 
  "fds_abs_converges (fds_of_real f) 
     (of_real s :: 'a :: {nat_power_normed_field,banach}) \<longleftrightarrow> fds_abs_converges f s"
  unfolding fds_abs_converges_def
  by (subst (1 2) summable_Suc_iff [symmetric]) (simp add: norm_divide norm_nat_power)

lemma eval_fds_of_real [simp]:
  assumes "fds_converges f s"
  shows   "eval_fds (fds_of_real f) (of_real s :: 'a :: {nat_power_normed_field,banach}) = 
             of_real (eval_fds f s)"
  using assms unfolding eval_fds_def by (auto simp: fds_converges_def suminf_of_real)

lemma fds_abs_summable_zeta_iff [simp]:
  fixes s :: "'a :: {banach, nat_power_normed_field}"
  shows "fds_abs_converges fds_zeta s \<longleftrightarrow> s \<bullet> 1 > (1 :: real)"
proof -
  have "fds_abs_converges fds_zeta s \<longleftrightarrow> summable (\<lambda>n. real n powr -(s \<bullet> 1))"
    unfolding fds_abs_converges_def
    by (intro summable_cong always_eventually)
       (auto simp: norm_divide fds_nth_zeta powr_minus norm_nat_power divide_simps)
  also have "\<dots> \<longleftrightarrow> s \<bullet> 1 > 1" by (simp add: summable_real_powr_iff)
  finally show ?thesis .
qed

lemma fds_abs_summable_zeta: 
  "(s :: 'a :: {banach, nat_power_normed_field}) \<bullet> 1 > 1 \<Longrightarrow> fds_abs_converges fds_zeta s"
  by simp


lemma fds_abs_converges_moebius_mu:
  fixes s :: "'a :: {banach,nat_power_normed_field}"
  assumes "s \<bullet> 1 > 1"
  shows   "fds_abs_converges (fds moebius_mu) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat
  show "norm (norm (fds_nth (fds moebius_mu) n / nat_power n s)) \<le> real n powr (-s \<bullet> 1)"
    by (auto simp: powr_minus divide_simps abs_moebius_mu_le norm_nat_power norm_divide
                   moebius_mu_def norm_power)
next
  from assms show "summable (\<lambda>n. real n powr (-s \<bullet> 1))" by (simp add: summable_real_powr_iff)
qed


definition conv_abscissa
    :: "'a :: {nat_power,banach,real_normed_field, real_inner} fds \<Rightarrow> ereal" where
  "conv_abscissa f = (INF s\<in>{s. fds_converges f s}. ereal (s \<bullet> 1))"

definition abs_conv_abscissa
    :: "'a :: {nat_power,banach,real_normed_field, real_inner} fds \<Rightarrow> ereal" where
  "abs_conv_abscissa f = (INF s\<in>{s. fds_abs_converges f s}. ereal (s \<bullet> 1))"

lemma conv_abscissa_mono:
  assumes "\<And>s. fds_converges g s \<Longrightarrow> fds_converges f s"
  shows   "conv_abscissa f \<le> conv_abscissa g"
  unfolding conv_abscissa_def by (rule INF_mono) (use assms in auto)

lemma abs_conv_abscissa_mono:
  assumes "\<And>s. fds_abs_converges g s \<Longrightarrow> fds_abs_converges f s"
  shows   "abs_conv_abscissa f \<le> abs_conv_abscissa g"
  unfolding abs_conv_abscissa_def by (rule INF_mono) (use assms in auto)


class dirichlet_series = euclidean_space + real_normed_field + nat_power_normed_field +
  assumes one_in_Basis: "1 \<in> Basis"
    
instance real :: dirichlet_series by standard simp_all
instance complex :: dirichlet_series by standard (simp_all add: Basis_complex_def)

context
  assumes "SORT_CONSTRAINT('a :: dirichlet_series)"
begin

lemma fds_abs_converges_Re_le:
  fixes f :: "'a fds"
  assumes "fds_abs_converges f z" "z \<bullet> 1 \<le> z' \<bullet> 1"
  shows   "fds_abs_converges f z'"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat assume n: "n \<ge> 1"
  thus "norm (norm (fds_nth f n / nat_power n z')) \<le> norm (fds_nth f n / nat_power n z)"
    using assms(2) by (simp add: norm_divide norm_nat_power divide_simps powr_mono mult_left_mono)
qed (insert assms(1), simp add: fds_abs_converges_def)

lemma fds_abs_converges:
  assumes "s \<bullet> 1 > abs_conv_abscissa (f :: 'a fds)"
  shows   "fds_abs_converges f s"
proof -
  from assms obtain s0 where "fds_abs_converges f s0" "s0 \<bullet> 1 < s \<bullet> 1"
    by (auto simp: INF_less_iff abs_conv_abscissa_def)
  with fds_abs_converges_Re_le[OF this(1), of s] this(2) show ?thesis by simp
qed

lemma fds_abs_diverges:
  assumes "s \<bullet> 1 < abs_conv_abscissa (f :: 'a fds)"
  shows   "\<not>fds_abs_converges f s"
proof
  assume "fds_abs_converges f s"
  hence "abs_conv_abscissa f \<le> s \<bullet> 1" unfolding abs_conv_abscissa_def
    by (intro INF_lower) auto
  with assms show False by simp
qed


lemma uniformly_Cauchy_eval_fds_aux:
  fixes s0 :: "'a :: dirichlet_series"
  assumes bounded: "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)"
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > s0 \<bullet> 1"
  shows   "uniformly_Cauchy_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
proof (cases "B = {}")
  case False
  show ?thesis
  proof (rule uniformly_Cauchy_onI', goal_cases)
    case (1 \<epsilon>)
    define \<sigma> where "\<sigma> = Inf ((\<lambda>s. s \<bullet> 1) ` B)"
    have \<sigma>_le: "s \<bullet> 1 \<ge> \<sigma>" if "s \<in> B" for s
      unfolding \<sigma>_def using that 
      by (intro cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded B) auto
    have "\<sigma> \<in> ((\<lambda>s. s \<bullet> 1) ` B)"
      unfolding \<sigma>_def using B \<open>B \<noteq> {}\<close>
      by (intro closed_contains_Inf bounded_inner_imp_bdd_below compact_imp_bounded B 
            compact_imp_closed compact_continuous_image continuous_intros) auto
    with B(2) have \<sigma>_gt: "\<sigma> > s0 \<bullet> 1" by auto
    define \<delta> where "\<delta> = \<sigma> - s0 \<bullet> 1"
      
    have "bounded B" by (rule compact_imp_bounded) fact
    then obtain norm_B_aux where norm_B_aux: "\<And>s. s \<in> B \<Longrightarrow> norm s \<le> norm_B_aux" 
      by (auto simp: bounded_iff)
    define norm_B where "norm_B = norm_B_aux + norm s0"
    from norm_B_aux have norm_B: "norm (s - s0) \<le> norm_B" if "s \<in> B" for s
      using norm_triangle_ineq4[of s s0] norm_B_aux[OF that] by (simp add: norm_B_def)
      
    define A where "A = sum_upto (\<lambda>k. fds_nth f k / nat_power k s0)"
    from bounded obtain C_aux where C_aux: "\<And>n. norm (\<Sum>k\<le>n. fds_nth f k / nat_power k s0) \<le> C_aux"
      by (auto simp: Bseq_def)
    define C where "C = max C_aux 1"
    have C_pos: "C > 0" by (simp add: C_def)
    have C: "norm (A x) \<le> C" for x
    proof -
      have "A x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. fds_nth f k / nat_power k s0)"
        unfolding A_def sum_upto_altdef by (intro sum.mono_neutral_left) auto
      also have "norm \<dots> \<le> C_aux" by (rule C_aux)
      also have "\<dots> \<le> C" by (simp add: C_def)
      finally show ?thesis .
    qed
    
    have "(\<lambda>m. 2 * C * (1 + norm_B / \<delta>) * real m powr (-\<delta>)) \<longlonglongrightarrow> 0" unfolding \<delta>_def using \<sigma>_gt
      by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially) simp_all
    from order_tendstoD(2)[OF this \<open>\<epsilon> > 0\<close>] obtain M where
      M: "\<And>m. m \<ge> M \<Longrightarrow> 2 * C * (1 + norm_B / \<delta>) * real m powr - \<delta> < \<epsilon>" 
      by (auto simp: eventually_at_top_linorder)
      
    show ?case
    proof (intro exI[of _ "max M 1"] ballI allI impI, goal_cases)
      case (1 s m n)
      from 1 have s: "s \<bullet> 1 > s0 \<bullet> 1" using B(2)[of s] by simp
      have mn: "m \<ge> M" "m < n" "m > 0" "n > 0" using 1 by (simp_all add: )
      have "dist (\<Sum>n\<le>m. fds_nth f n / nat_power n s) (\<Sum>n\<le>n. fds_nth f n / nat_power n s) =
              dist (\<Sum>n\<le>n. fds_nth f n / nat_power n s) (\<Sum>n\<le>m. fds_nth f n / nat_power n s)"
        by (simp add: dist_commute)
      also from 1 have "\<dots> = norm (\<Sum>k\<in>{..n}-{..m}. fds_nth f k / nat_power k s)"
        by (subst Groups_Big.sum_diff) (simp_all add: dist_norm)
      also from 1 have "{..n} - {..m} = real -` {real m<..real n}" by auto
      also have "(\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s) = 
                   (\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s0 * real_power (real k) (s0 - s))"
        (is "_ = ?S") by (intro sum.cong refl) (simp_all add: nat_power_diff real_power_nat_power)
      also have *: "((\<lambda>t. A t * ((s0 - s) * real_power t (s0 - s - 1))) has_integral
                    (A (real n) * real_power n (s0 - s) - A (real m) * real_power m (s0 - s) - ?S))
                    {real m..real n}" (is "(?h has_integral _) _") unfolding A_def using mn
        by (intro partial_summation_strong[of "{}"]) 
           (auto intro!: derivative_eq_intros continuous_intros)
      hence "?S = A (real n) * nat_power n (s0 - s) - A (real m) * nat_power m (s0 - s) -
                    integral {real m..real n} ?h"
        using mn by (simp add: has_integral_iff real_power_nat_power)
      also have "norm \<dots> \<le> norm (A (real n) * nat_power n (s0 - s)) +
                    norm (A (real m) * nat_power m (s0 - s)) + norm (integral {real m..real n} ?h)"
        by (intro order.trans[OF norm_triangle_ineq4] add_right_mono order.refl)
      also have "norm (A (real n) * nat_power n (s0 - s)) \<le> C * nat_power m ((s0 - s) \<bullet> 1)"
        using mn \<open>s \<in> B\<close> C_pos s
        by (auto simp: norm_mult norm_nat_power algebra_simps intro!: mult_mono C powr_mono2')
      also have "norm (A (real m) * nat_power m (s0 - s)) \<le> C * nat_power m ((s0 - s) \<bullet> 1)"
        using mn by (auto simp: norm_mult norm_nat_power intro!: mult_mono C)
      also have "norm (integral {real m..real n} ?h) \<le> 
                   integral {real m..real n} (\<lambda>t. C * (norm (s0 - s) * t powr ((s0 - s) \<bullet> 1 - 1)))"
      proof (intro integral_norm_bound_integral ballI, goal_cases)
        case 1
        with * show ?case by (simp add: has_integral_iff)
      next
        case 2
        from mn show ?case by (auto intro!: integrable_continuous_real continuous_intros)
      next
        case (3 t)
        thus ?case unfolding norm_mult using C_pos mn 
          by (intro mult_mono C) (auto simp: norm_real_power dot_square_norm algebra_simps)
      qed
      also have "\<dots> = C * norm (s0 - s) * integral {real m..real n} (\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1))"
        by (simp add: algebra_simps dot_square_norm)
      also {
        have "((\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1)) has_integral 
                     (real n powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1) - 
                      real m powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1))) {m..n}" 
          (is "(?l has_integral ?I) _") using mn s
          by (intro fundamental_theorem_of_calculus)
             (auto intro!: derivative_eq_intros 
                   simp: has_field_derivative_iff_has_vector_derivative [symmetric] inner_diff_left)
        hence "integral {real m..real n} ?l = ?I" by (simp add: has_integral_iff)
        also have "\<dots> \<le> -(real m powr ((s0 - s) \<bullet> 1) / ((s0 - s) \<bullet> 1))" using s mn
          by (simp add: divide_simps inner_diff_left)
        also have "\<dots> = 1 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1))"
          using s by (simp add: field_simps inner_diff_left)
        also have "\<dots> \<le> 2 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1))" using mn s
          by (intro mult_right_mono divide_nonneg_pos) (simp_all add: inner_diff_left)
        finally have "integral {m..n} ?l \<le> \<dots>" .
      }
      hence "C * norm (s0 - s) * integral {real m..real n} (\<lambda>t. t powr ((s0 - s) \<bullet> 1 - 1)) \<le>
               C * norm (s0 - s) * (2 * (real m powr ((s0 - s) \<bullet> 1) / ((s - s0) \<bullet> 1)))" 
        using C_pos mn
        by (intro mult_mono mult_nonneg_nonneg integral_nonneg
              integrable_continuous_real continuous_intros) auto
      also have "C * nat_power m ((s0 - s) \<bullet> 1) + C * nat_power m ((s0 - s) \<bullet> 1) + \<dots> =
                   2 * C * nat_power m ((s0 - s) \<bullet> 1) * (1 + norm (s - s0) / ((s - s0) \<bullet> 1))"
        by (simp add: algebra_simps norm_minus_commute)
      also have "\<dots> \<le> 2 * C * nat_power m (-\<delta>) * (1 + norm_B / \<delta>)" 
        using C_pos s mn \<sigma>_le[of s] \<open>s \<in> B\<close> \<sigma>_gt unfolding nat_power_real_def
        by (intro mult_mono mult_nonneg_nonneg powr_mono frac_le add_mono norm_B)
           (simp_all add: inner_diff_left \<delta>_def)
      also have "\<dots> = 2 * C * (1 + norm_B / \<delta>) * real m powr (-\<delta>)" by simp
      also from \<open>m \<ge> M\<close> have "\<dots> < \<epsilon>" by (rule M)
      finally show ?case by - simp_all
    qed
  qed
qed (auto simp: uniformly_Cauchy_on_def)

lemma uniformly_convergent_eval_fds_aux:
  assumes "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k (s0 :: 'a))"
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > s0 \<bullet> 1"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
  by (rule Cauchy_uniformly_convergent uniformly_Cauchy_eval_fds_aux assms)+

lemma uniformly_convergent_eval_fds_aux':
  assumes conv: "fds_converges f (s0 :: 'a)"
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > s0 \<bullet> 1"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
proof (rule uniformly_convergent_eval_fds_aux)
  from conv have "convergent (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)"
    by (simp add: fds_converges_def summable_iff_convergent')
  thus "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)" by (rule convergent_imp_Bseq)
qed (insert assms, auto)

lemma bounded_partial_sums_imp_fps_converges:
  fixes s0 :: "'a :: dirichlet_series"
  assumes "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)" and "s \<bullet> 1 > s0 \<bullet> 1"
  shows   "fds_converges f s"
proof -
  have "uniformly_convergent_on {s} (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)" using assms(2)
    by (intro uniformly_convergent_eval_fds_aux[OF assms(1)]) auto
  thus ?thesis
    by (auto simp: fds_converges_def summable_iff_convergent'
             dest: uniformly_convergent_imp_convergent)
qed

theorem fds_converges_Re_le:
  assumes "fds_converges f (s0 :: 'a)" "s \<bullet> 1 > s0 \<bullet> 1"
  shows   "fds_converges f s"
proof -
  have "uniformly_convergent_on {s} (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
    by (rule uniformly_convergent_eval_fds_aux' assms)+ (insert assms(2), auto)
  then obtain l where "uniform_limit {s} (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) l at_top"
    by (auto simp: uniformly_convergent_on_def)
  from tendsto_uniform_limitI[OF this, of s]
  have "(\<lambda>n. fds_nth f n / nat_power n s) sums l s" unfolding sums_def'
    by (simp add: atLeast0AtMost)
  thus ?thesis by (simp add: fds_converges_def sums_iff)
qed

lemma fds_converges:
  assumes "s \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "fds_converges f s"
proof -
  from assms obtain s0 where "fds_converges f s0" "s0 \<bullet> 1 < s \<bullet> 1"
    by (auto simp: INF_less_iff conv_abscissa_def)
  with fds_converges_Re_le[OF this(1), of s] this(2) show ?thesis by simp
qed

lemma fds_diverges:
  assumes "s \<bullet> 1 < conv_abscissa (f :: 'a fds)"
  shows   "\<not>fds_converges f s"
proof
  assume "fds_converges f s"
  hence "conv_abscissa f \<le> s \<bullet> 1" unfolding conv_abscissa_def
    by (intro INF_lower) auto
  with assms show False by simp
qed

theorem fds_converges_imp_abs_converges:
  assumes "fds_converges (f :: 'a fds) s" "s' \<bullet> 1 > s \<bullet> 1 + 1"
  shows   "fds_abs_converges f s'"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test_ev)
  from assms(2) show "summable (\<lambda>n. real n powr ((s - s') \<bullet> 1))"
    by (subst summable_real_powr_iff) (simp_all add: inner_diff_left)
next
  from assms(1) have "(\<lambda>n. fds_nth f n / nat_power n s) \<longlonglongrightarrow> 0"
    unfolding fds_converges_def by (rule summable_LIMSEQ_zero)
  from tendsto_norm[OF this] have "(\<lambda>n. norm (fds_nth f n / nat_power n s)) \<longlonglongrightarrow> 0" by simp
  hence "eventually (\<lambda>n. norm (fds_nth f n / nat_power n s) < 1) at_top"
    by (rule order_tendstoD) simp_all
  thus "eventually (\<lambda>n. norm (norm (fds_nth f n / nat_power n s')) \<le> 
          real n powr ((s - s') \<bullet> 1)) at_top"
  proof eventually_elim
    case (elim n)
    thus ?case
    proof (cases "n = 0")
      case False
      have "norm (fds_nth f n / nat_power n s') =
              norm (fds_nth f n) / real n powr (s' \<bullet> 1)" using False
        by (simp add: norm_divide norm_nat_power)
      also have "\<dots> = norm (fds_nth f n / nat_power n s) / real n powr ((s' - s) \<bullet> 1)" using False
        by (simp add: norm_divide norm_nat_power inner_diff_left powr_diff)
      also have "\<dots> \<le> 1 / real n powr ((s' - s) \<bullet> 1)" using elim
        by (intro divide_right_mono elim) simp_all
      also have "\<dots> = real n powr ((s - s') \<bullet> 1)" using False
        by (simp add: field_simps inner_diff_left powr_diff) 
      finally show ?thesis by simp
    qed simp_all
  qed
qed

lemma conv_le_abs_conv_abscissa: "conv_abscissa f \<le> abs_conv_abscissa f"
  unfolding conv_abscissa_def abs_conv_abscissa_def
  by (intro INF_superset_mono) auto

lemma conv_abscissa_PInf_iff: "conv_abscissa f = \<infinity> \<longleftrightarrow> (\<forall>s. \<not>fds_converges f s)"
  unfolding conv_abscissa_def by (subst Inf_eq_PInfty) auto

lemma conv_abscissa_PInfI [intro]: "(\<And>s. \<not>fds_converges f s) \<Longrightarrow> conv_abscissa f = \<infinity>"
  by (subst conv_abscissa_PInf_iff) auto
    
lemma conv_abscissa_MInf_iff: "conv_abscissa (f :: 'a fds) = -\<infinity> \<longleftrightarrow> (\<forall>s. fds_converges f s)"
proof safe
  assume *: "\<forall>s. fds_converges f s"
  have "conv_abscissa f \<le> B" for B :: real
    using spec[OF *, of "of_real B"] fds_diverges[of "of_real B" f]
    by (cases "conv_abscissa f \<le> B") simp_all
  thus "conv_abscissa f = -\<infinity>" by (rule ereal_bot)    
qed (auto intro: fds_converges)

lemma conv_abscissa_MInfI [intro]: "(\<And>s. fds_converges (f::'a fds) s) \<Longrightarrow> conv_abscissa f = -\<infinity>"
  by (subst conv_abscissa_MInf_iff) auto

lemma abs_conv_abscissa_PInf_iff: "abs_conv_abscissa f = \<infinity> \<longleftrightarrow> (\<forall>s. \<not>fds_abs_converges f s)"
  unfolding abs_conv_abscissa_def by (subst Inf_eq_PInfty) auto

lemma abs_conv_abscissa_PInfI [intro]: "(\<And>s. \<not>fds_converges f s) \<Longrightarrow> abs_conv_abscissa f = \<infinity>"
  by (subst abs_conv_abscissa_PInf_iff) auto

lemma abs_conv_abscissa_MInf_iff: 
  "abs_conv_abscissa (f :: 'a fds) = -\<infinity> \<longleftrightarrow> (\<forall>s. fds_abs_converges f s)"
proof safe
  assume *: "\<forall>s. fds_abs_converges f s"
  have "abs_conv_abscissa f \<le> B" for B :: real
    using spec[OF *, of "of_real B"] fds_abs_diverges[of "of_real B" f]
    by (cases "abs_conv_abscissa f \<le> B") simp_all
  thus "abs_conv_abscissa f = -\<infinity>" by (rule ereal_bot)    
qed (auto intro: fds_abs_converges)

lemma abs_conv_abscissa_MInfI [intro]: 
  "(\<And>s. fds_abs_converges (f::'a fds) s) \<Longrightarrow> abs_conv_abscissa f = -\<infinity>"
  by (subst abs_conv_abscissa_MInf_iff) auto

lemma conv_abscissa_geI:
  assumes "\<And>c'. ereal c' < c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> \<not>fds_converges f s"
  shows   "conv_abscissa (f :: 'a fds) \<ge> c"
proof (rule ccontr)
  assume "\<not>conv_abscissa f \<ge> c"
  hence "c > conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c > ereal c'" "c' > conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "\<not>fds_converges f s" by blast
  ultimately show False using fds_converges[of f s] by auto
qed

lemma conv_abscissa_leI:
  assumes "\<And>c'. ereal c' > c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> fds_converges f s"
  shows   "conv_abscissa (f :: 'a fds) \<le> c"
proof (rule ccontr)
  assume "\<not>conv_abscissa f \<le> c"
  hence "c < conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c < ereal c'" "c' < conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "fds_converges f s" by blast
  ultimately show False using fds_diverges[of s f] by auto
qed

lemma abs_conv_abscissa_geI:
  assumes "\<And>c'. ereal c' < c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> \<not>fds_abs_converges f s"
  shows   "abs_conv_abscissa (f :: 'a fds) \<ge> c"
proof (rule ccontr)
  assume "\<not>abs_conv_abscissa f \<ge> c"
  hence "c > abs_conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c > ereal c'" "c' > abs_conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "\<not>fds_abs_converges f s" by blast
  ultimately show False using fds_abs_converges[of f s] by auto
qed  

lemma abs_conv_abscissa_leI:
  assumes "\<And>c'. ereal c' > c \<Longrightarrow> \<exists>s. s \<bullet> 1 = c' \<and> fds_abs_converges f s"
  shows   "abs_conv_abscissa (f :: 'a fds) \<le> c"
proof (rule ccontr)
  assume "\<not>abs_conv_abscissa f \<le> c"
  hence "c < abs_conv_abscissa f" by simp
  from ereal_dense2[OF this] obtain c' where "c < ereal c'" "c' < abs_conv_abscissa f" by auto
  moreover from assms[OF this(1)] obtain s where "s \<bullet> 1 = c'" "fds_abs_converges f s" by blast
  ultimately show False using fds_abs_diverges[of s f] by auto
qed

lemma conv_abscissa_leI_weak:
  assumes "\<And>x. ereal x > d \<Longrightarrow> fds_converges f (of_real x)"
  shows   "conv_abscissa (f :: 'a fds) \<le> d"
proof (rule conv_abscissa_leI)
  fix x assume "d < ereal x"
  from assms[OF this] show "\<exists>s. s \<bullet> 1 = x \<and> fds_converges f s"
    by (intro exI[of _ "of_real x"]) auto
qed

lemma abs_conv_abscissa_leI_weak:
  assumes "\<And>x. ereal x > d \<Longrightarrow> fds_abs_converges f (of_real x)"
  shows   "abs_conv_abscissa (f :: 'a fds) \<le> d"
proof (rule abs_conv_abscissa_leI)
  fix x assume "d < ereal x"
  from assms[OF this] show "\<exists>s. s \<bullet> 1 = x \<and> fds_abs_converges f s"
    by (intro exI[of _ "of_real x"]) auto
qed

lemma conv_abscissa_truncate [simp]: 
  "conv_abscissa (fds_truncate m (f :: 'a fds)) = -\<infinity>"
  by (auto simp: conv_abscissa_MInf_iff)

lemma abs_conv_abscissa_truncate [simp]: 
  "abs_conv_abscissa (fds_truncate m (f :: 'a fds)) = -\<infinity>"
  by (auto simp: abs_conv_abscissa_MInf_iff)

  
theorem abs_conv_le_conv_abscissa_plus_1: "abs_conv_abscissa (f :: 'a fds) \<le> conv_abscissa f + 1"
proof (rule abs_conv_abscissa_leI)
  fix c assume less: "conv_abscissa f + 1 < ereal c"
  define c' where "c' = (if conv_abscissa f = -\<infinity> then c - 2
                     else (c - 1 + real_of_ereal (conv_abscissa f)) / 2)"
  from less have c': "conv_abscissa f < ereal c' \<and> c' < c - 1"
    by (cases "conv_abscissa f") (simp_all add: c'_def field_simps)
  
  from c' have "fds_converges f (of_real c')" 
    by (intro fds_converges) (simp_all add: inner_diff_left dot_square_norm)
  hence "fds_abs_converges f (of_real c)"
    by (rule fds_converges_imp_abs_converges) (insert c', simp_all)
  thus "\<exists>s. s \<bullet> 1 = c \<and> fds_abs_converges f s"
    by (intro exI[of _ "of_real c"]) auto
qed

  
lemma uniformly_convergent_eval_fds:
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z)"
proof (cases "B = {}")
  case False
  define \<sigma> where "\<sigma> = Inf ((\<lambda>s. s \<bullet> 1) ` B)"
  have \<sigma>_le: "s \<bullet> 1 \<ge> \<sigma>" if "s \<in> B" for s
    unfolding \<sigma>_def using that 
    by (intro cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded B) auto
  have "\<sigma> \<in> ((\<lambda>s. s \<bullet> 1) ` B)"
    unfolding \<sigma>_def using B \<open>B \<noteq> {}\<close>
    by (intro closed_contains_Inf bounded_inner_imp_bdd_below compact_imp_bounded B 
          compact_imp_closed compact_continuous_image continuous_intros) auto
  with B(2) have \<sigma>_gt: "\<sigma> > conv_abscissa f" by auto
  define s where "s = (if conv_abscissa f = -\<infinity> then \<sigma> - 1 else 
                         (\<sigma> + real_of_ereal (conv_abscissa f)) / 2)"
  from \<sigma>_gt have s: "conv_abscissa f < s \<and> s < \<sigma>"
    by (cases "conv_abscissa f") (auto simp: s_def)
  show ?thesis using s \<open>compact B\<close>
    by (intro uniformly_convergent_eval_fds_aux'[of f "of_real s"] fds_converges)
       (auto dest: \<sigma>_le)
qed auto
    
corollary uniformly_convergent_eval_fds':
  assumes B: "compact B" "\<And>z. z \<in> B \<Longrightarrow> z \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   "uniformly_convergent_on B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z)"
proof -
  from uniformly_convergent_eval_fds[OF assms] obtain l where
    "uniform_limit B (\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) l at_top" 
    by (auto simp: uniformly_convergent_on_def)
  also have "(\<lambda>N z. \<Sum>n\<le>N. fds_nth f n / nat_power n z) = 
                (\<lambda>N z. \<Sum>n<Suc N. fds_nth f n / nat_power n z)"
    by (simp only: lessThan_Suc_atMost)
  finally have "uniform_limit B (\<lambda>N z. \<Sum>n<N. fds_nth f n / nat_power n z) l at_top" 
    unfolding uniform_limit_iff by (subst (asm) eventually_sequentially_Suc)
  thus ?thesis by (auto simp: uniformly_convergent_on_def)
qed


subsection \<open>Derivative of a Dirichlet series\<close>

lemma fds_converges_deriv_aux:
  assumes conv: "fds_converges f (s0 :: 'a)" and gt: "s \<bullet> 1 > s0 \<bullet> 1"
  shows "fds_converges (fds_deriv f) s"
proof -
  have "Cauchy (\<lambda>n. \<Sum>k\<le>n. (-ln (real k) *\<^sub>R fds_nth f k) / nat_power k s)"
  proof (rule CauchyI', goal_cases)
    case (1 \<epsilon>)
    define \<delta> where "\<delta> = s \<bullet> 1 - s0 \<bullet> 1"
    define \<delta>' where "\<delta>' = \<delta> / 2"
    from gt have \<delta>_pos: "\<delta> > 0" by (simp add: \<delta>_def)
    define A where "A = sum_upto (\<lambda>k. fds_nth f k / nat_power k s0)"
    from conv have "convergent (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)"
      by (simp add: fds_converges_def summable_iff_convergent')
    hence "Bseq (\<lambda>n. \<Sum>k\<le>n. fds_nth f k / nat_power k s0)" by (rule convergent_imp_Bseq)
    then obtain C_aux where C_aux: "\<And>n. norm (\<Sum>k\<le>n. fds_nth f k / nat_power k s0) \<le> C_aux"
      by (auto simp: Bseq_def)
    define C where "C = max C_aux 1"
    have C_pos: "C > 0" by (simp add: C_def)
    have C: "norm (A x) \<le> C" for x
    proof -
      have "A x = (\<Sum>k\<le>nat \<lfloor>x\<rfloor>. fds_nth f k / nat_power k s0)"
        unfolding A_def sum_upto_altdef by (intro sum.mono_neutral_left) auto
      also have "norm \<dots> \<le> C_aux" by (rule C_aux)
      also have "\<dots> \<le> C" by (simp add: C_def)
      finally show ?thesis .
    qed
    define C' where "C' = 2 * C + C * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>"
  
    have "(\<lambda>m. C' * real m powr (-\<delta>')) \<longlonglongrightarrow> 0" unfolding \<delta>'_def using gt \<delta>_pos
      by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_real_sequentially) simp_all
    from order_tendstoD(2)[OF this \<open>\<epsilon> > 0\<close>] obtain M1 where
      M1: "\<And>m. m \<ge> M1 \<Longrightarrow> C' * real m powr - \<delta>' < \<epsilon>" 
      by (auto simp: eventually_at_top_linorder)
    have "((\<lambda>x. ln (real x) / real x powr \<delta>') \<longlongrightarrow> 0) at_top" using \<delta>_pos
      by (intro lim_ln_over_power) (simp_all add: \<delta>'_def)
    from order_tendstoD(2)[OF this zero_less_one] eventually_gt_at_top[of "1::nat"]
      have "eventually (\<lambda>n. ln (real n) \<le> n powr \<delta>') at_top" by eventually_elim simp_all
    then obtain M2 where M2: "\<And>n. n \<ge> M2 \<Longrightarrow> ln (real n) \<le> n powr \<delta>'"
      by (auto simp: eventually_at_top_linorder)
    let ?f' = "\<lambda>k. -ln (real k) *\<^sub>R fds_nth f k"

    show ?case
    proof (intro exI[of _ "max (max M1 M2) 1"] allI impI, goal_cases)
      case (1 m n)
      hence mn: "m \<ge> M1" "m \<ge> M2" "m > 0" "m < n" by simp_all
      define g :: "real \<Rightarrow> 'a" where "g = (\<lambda>t. real_power t (s0 - s) * of_real (ln t))"
      define g' :: "real \<Rightarrow> 'a"            
        where "g' = (\<lambda>t. real_power t (s0 - s - 1) * ((s0 - s) * of_real (ln t) + 1))"
      define norm_g' :: "real \<Rightarrow> real"
        where "norm_g' = (\<lambda>t. t powr (-\<delta> - 1) * (norm (s0 - s) * ln t + 1))"
      define norm_g :: "real \<Rightarrow> real"
        where "norm_g = (\<lambda>t. -(t powr -\<delta>) * (norm (s0 - s) * (\<delta> * ln t + 1) + \<delta>) / \<delta>^2)"
      have g_g': "(g has_vector_derivative g' t) (at t)" if "t \<in> {real m..real n}" for t 
        using mn that by (auto simp: g_def g'_def real_power_diff field_simps real_power_add 
                               intro!: derivative_eq_intros)
      have [continuous_intros]: "continuous_on {real m..real n} g" using mn
        by (auto simp: g_def intro!: continuous_intros)
        
      let ?S = "\<Sum>k\<in>real -` {real m<..real n}. fds_nth f k / nat_power k s0 * g k"
      have "dist (\<Sum>k\<le>m. ?f' k / nat_power k s) (\<Sum>k\<le>n. ?f' k / nat_power k s) =
              norm (\<Sum>k\<in>{..n} - {..m}. fds_nth f k / nat_power k s * of_real (ln (real k)))" 
        using mn by (subst sum_diff) 
           (simp_all add: dist_norm norm_minus_commute sum_negf scaleR_conv_of_real mult_ac)
      also have "{..n} - {..m} = real -` {real m<..real n}" by auto
      also have "(\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s * of_real (ln (real k))) = 
        (\<Sum>k\<in>\<dots>. fds_nth f k / nat_power k s0 * g k)" using mn unfolding g_def
        by (intro sum.cong refl) (auto simp: real_power_nat_power field_simps nat_power_diff)
      also have *: "((\<lambda>t. A t * g' t) has_integral
                    (A (real n) * g n - A (real m) * g m - ?S))
                    {real m..real n}" (is "(?h has_integral _) _") unfolding A_def using mn
        by (intro partial_summation_strong[of "{}"])
           (auto intro!: g_g' simp: field_simps continuous_intros)
      hence "?S = A (real n) * g n - A (real m) * g m - integral {real m..real n} ?h"
        using mn by (simp add: has_integral_iff field_simps)
      also have "norm \<dots> \<le> norm (A (real n) * g n) + norm (A (real m) * g m) + 
                             norm (integral {real m..real n} ?h)"
        by (intro order.trans[OF norm_triangle_ineq4] add_right_mono order.refl)
      also have "norm (A (real n) * g n) \<le> C * norm (g n)"
        unfolding norm_mult using mn C_pos by (intro mult_mono C) auto
      also have "norm (g n) \<le> n powr -\<delta> * n powr \<delta>'" using mn M2[of n]
        by (simp add: g_def norm_real_power norm_mult \<delta>_def inner_diff_left)
      also have "\<dots> = n powr -\<delta>'" using mn 
        by (simp add: \<delta>'_def powr_minus field_simps powr_add [symmetric])
      also have "norm (A (real m) * g m) \<le> C * norm (g m)"
        unfolding norm_mult using mn C_pos by (intro mult_mono C) auto
      also have "norm (g m) \<le> m powr -\<delta> * m powr \<delta>'" using mn M2[of m]
        by (simp add: g_def norm_real_power norm_mult \<delta>_def inner_diff_left)
      also have "\<dots> = m powr -\<delta>'" using mn 
        by (simp add: \<delta>'_def powr_minus field_simps powr_add [symmetric])
      also have "C * real n powr - \<delta>' \<le> C * real m powr - \<delta>'" using \<delta>_pos mn C_pos
        by (intro mult_left_mono powr_mono2') (simp_all add: \<delta>'_def)
      also have "\<dots> + \<dots> = 2 * \<dots>" by simp
      also have "norm (integral {m..n} ?h) \<le> integral {m..n} (\<lambda>t. C * norm_g' t)"
      proof (intro integral_norm_bound_integral ballI, goal_cases)
        case 1
        with * show ?case by (simp add: has_integral_iff)
      next
        case 2
        from mn show ?case 
          by (auto intro!: integrable_continuous_real continuous_intros simp: norm_g'_def)
      next
        case (3 t)
        have "norm (g' t) \<le> norm_g' t" unfolding g'_def norm_g'_def using 3 mn
          unfolding norm_mult
          by (intro mult_mono order.trans[OF norm_triangle_ineq])
             (auto simp: norm_real_power inner_diff_left dot_square_norm norm_mult \<delta>_def
                   intro!: mult_left_mono)
        thus ?case unfolding norm_mult using C_pos mn 
          by (intro mult_mono C) simp_all
      qed
      also have "\<dots> = C * integral {m..n} norm_g'"
        unfolding norm_g'_def by (simp add: norm_g'_def \<delta>_def inner_diff_left)
      also {
        have "(norm_g' has_integral (norm_g n - norm_g m)) {m..n}"
          unfolding norm_g'_def norm_g_def power2_eq_square using mn \<delta>_pos
          by (intro fundamental_theorem_of_calculus)
             (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] 
                 field_simps powr_diff intro!: derivative_eq_intros)
        hence "integral {m..n} norm_g' = norm_g n - norm_g m" by (simp add: has_integral_iff)
        also have "norm_g n \<le> 0" unfolding norm_g_def using \<delta>_pos mn
          by (intro divide_nonpos_pos mult_nonpos_nonneg add_nonneg_nonneg mult_nonneg_nonneg)
             simp_all
        hence "norm_g n - norm_g m \<le> -norm_g m" by simp
        also have "\<dots> = real m powr -\<delta> * ln (real m) * (norm (s0 - s)) / \<delta> +
                        real m powr -\<delta> * ((norm (s0 - s) / \<delta> + 1) / \<delta>)" using \<delta>_pos
          by (simp add: field_simps norm_g_def power2_eq_square)
        also {
          have "ln (real m) \<le> real m powr \<delta>'" using M2[of m] mn by simp
          also have "real m powr -\<delta> * \<dots> = real m powr -\<delta>'"
            by (simp add: powr_add [symmetric] \<delta>'_def)
          finally have "real m powr -\<delta> * ln (real m) * (norm (s0 - s)) / \<delta> \<le>
                          \<dots> * (norm (s0 - s)) / \<delta>" using \<delta>_pos
            by (intro divide_right_mono mult_right_mono) (simp_all add: mult_left_mono)
        }
        also have "real m powr -\<delta> * ((norm (s0 - s) / \<delta> + 1) / \<delta>) \<le>
                     real m powr -\<delta>' * ((norm (s0 - s) / \<delta> + 1) / \<delta>)" using mn \<delta>_pos
          by (intro mult_right_mono powr_mono) (simp_all add: \<delta>'_def)
        also have "real m powr - \<delta>' * norm (s0 - s) / \<delta> + \<dots> =
                     real m powr -\<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>" using \<delta>_pos
          by (simp add: field_simps power2_eq_square)
        finally have "integral {real m..real n} norm_g' \<le>
                        real m powr - \<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>" by - simp_all
      }
      also have "2 * (C * m powr - \<delta>') + C * (m powr - \<delta>' * (norm (s0 - s) * (1 + 1 / \<delta>) + 1) / \<delta>) =
                   C' * m powr -\<delta>'" by (simp add: algebra_simps C'_def)
      also have "\<dots> < \<epsilon>" using M1[of m] mn by simp
      finally show ?case using C_pos by - simp_all
    qed
  qed
  from Cauchy_convergent[OF this] 
    show ?thesis by (simp add: summable_iff_convergent' fds_converges_def fds_nth_deriv)
qed

theorem
  assumes "s \<bullet> 1 > conv_abscissa (f :: 'a fds)"
  shows   fds_converges_deriv: "fds_converges (fds_deriv f) s"
    and   has_field_derivative_eval_fds [derivative_intros]:
            "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s within A)"
proof -
  define s1 :: real where
    "s1 = (if conv_abscissa f = -\<infinity> then s \<bullet> 1 - 2 else
             (s \<bullet> 1 * 1 / 3 + real_of_ereal (conv_abscissa f) * 2 / 3))"
  define s2 :: real where
    "s2 = (if conv_abscissa f = -\<infinity> then s \<bullet> 1 - 1 else
             (s \<bullet> 1 * 2 / 3 + real_of_ereal (conv_abscissa f) * 1 / 3))"
  from assms have s: "conv_abscissa f < s1 \<and> s1 < s2 \<and> s2 < s \<bullet> 1"
    by (cases "conv_abscissa f") (auto simp: s1_def s2_def field_simps)
  from s have *: "fds_converges f (of_real s1)" by (intro fds_converges) simp_all
  thus conv': "fds_converges (fds_deriv f) s"
    by (rule fds_converges_deriv_aux) (insert s, simp_all)
  from * have conv: "fds_converges (fds_deriv f) (of_real s2)"
    by (rule fds_converges_deriv_aux) (insert s, simp_all)
      
  define \<delta> :: real where "\<delta> = (s \<bullet> 1 - s2) / 2"
  from s have \<delta>_pos: "\<delta> > 0" by (simp add: \<delta>_def)
  
  have "uniformly_convergent_on (cball s \<delta>) 
          (\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s)"
  proof (intro uniformly_convergent_eval_fds_aux'[OF conv])
    fix s'' :: 'a assume s'': "s'' \<in> cball s \<delta>"
    have "dist (s \<bullet> 1) (s'' \<bullet> 1) \<le> dist s s''" 
      by (intro Euclidean_dist_upper) (simp_all add: one_in_Basis)
    also from s'' have "\<dots> \<le> \<delta>" by simp
    finally show "s'' \<bullet> 1 > (of_real s2 :: 'a) \<bullet> 1" using s
      by (auto simp: \<delta>_def dist_real_def abs_if split: if_splits)
  qed (insert \<delta>_pos, auto)
  then obtain l where 
     "uniform_limit (cball s \<delta>) (\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s) l at_top"
    by (auto simp: uniformly_convergent_on_def)
  also have "(\<lambda>n s. \<Sum>k\<le>n. fds_nth (fds_deriv f) k / nat_power k s) =
               (\<lambda>n s. \<Sum>k<Suc n. fds_nth (fds_deriv f) k / nat_power k s)"
    by (simp only: lessThan_Suc_atMost)
  finally have "uniform_limit (cball s \<delta>) (\<lambda>n s. \<Sum>k<n. fds_nth (fds_deriv f) k / nat_power k s) 
                  l at_top"
    unfolding uniform_limit_iff by (subst (asm) eventually_sequentially_Suc)
  hence *: "uniformly_convergent_on (cball s \<delta>) 
              (\<lambda>n s. \<Sum>k<n. fds_nth (fds_deriv f) k / nat_power k s)"
    unfolding uniformly_convergent_on_def by blast
      
  have "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s)"
    unfolding eval_fds_def
  proof (rule has_field_derivative_series'(2)[OF _ _ *])
    show "s \<in> cball s \<delta>" "s \<in> interior (cball s \<delta>)" using s by (simp_all add: \<delta>_def)
    show "summable (\<lambda>n. fds_nth f n / nat_power n s)"
      using assms fds_converges[of f s] by (simp add: fds_converges_def)
  next
    fix s' :: 'a and n :: nat
    show "((\<lambda>s. fds_nth f n / nat_power n s) has_field_derivative
            fds_nth (fds_deriv f) n / nat_power n s') (at s' within cball s \<delta>)"
      by (cases "n = 0") 
         (simp, auto intro!: derivative_eq_intros simp: fds_nth_deriv field_simps)
  qed (auto simp: fds_nth_deriv intro!: derivative_eq_intros)
  thus "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s within A)"
    by (rule has_field_derivative_at_within)
qed

lemmas has_field_derivative_eval_fds' [derivative_intros] = 
  DERIV_chain2[OF has_field_derivative_eval_fds]

lemma continuous_eval_fds [continuous_intros]:
  assumes "s \<bullet> 1 > conv_abscissa f"
  shows   "continuous (at s within A) (eval_fds (f :: 'a :: dirichlet_series fds))"
proof -
  have "isCont (eval_fds f) s"
    by (rule has_field_derivative_eval_fds DERIV_isCont assms)+
  thus ?thesis by (rule continuous_within_subset) auto
qed

lemma continuous_eval_fds' [continuous_intros]:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "continuous (at s within A) g" "g s \<bullet> 1 > conv_abscissa f"
  shows   "continuous (at s within A) (\<lambda>x. eval_fds f (g x))"
  by (rule continuous_within_compose3[OF _ assms(1)] continuous_intros assms)+

lemma continuous_on_eval_fds [continuous_intros]:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "A \<subseteq> {s. s \<bullet> 1 > conv_abscissa f}"
  shows   "continuous_on A (eval_fds f)"
  by (rule DERIV_continuous_on derivative_intros)+ (insert assms, auto)

lemma continuous_on_eval_fds' [continuous_intros]:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "continuous_on A g" "g ` A \<subseteq> {s. s \<bullet> 1 > conv_abscissa f}"
  shows   "continuous_on A (\<lambda>x. eval_fds f (g x))"
  by (rule continuous_on_compose2[OF continuous_on_eval_fds assms(1)])
     (insert assms, auto simp: image_iff)

lemma conv_abscissa_deriv_le:
  fixes f :: "'a fds"
  shows "conv_abscissa (fds_deriv f) \<le> conv_abscissa f"
proof (rule conv_abscissa_leI)
  fix c' :: real
  assume "ereal c' > conv_abscissa f"
  thus "\<exists>s. s \<bullet> 1 = c' \<and> fds_converges (fds_deriv f) s"
    by (intro exI[of _ "of_real c'"]) (auto simp: fds_converges_deriv)
qed

lemma abs_conv_abscissa_integral:
  fixes f :: "'a fds"
  shows "abs_conv_abscissa (fds_integral a f) = abs_conv_abscissa f"
proof (rule antisym)
  show "abs_conv_abscissa (fds_integral a f) \<le> abs_conv_abscissa f"
  proof (rule abs_conv_abscissa_leI, goal_cases)
    case (1 c)
    have "fds_abs_converges (fds_integral a f) (of_real c)"
      unfolding fds_abs_converges_def
    proof (rule summable_comparison_test_ev)
      from 1 have "fds_abs_converges f (of_real c)"
        by (intro fds_abs_converges) auto
      thus "summable (\<lambda>n. norm (fds_nth f n / nat_power n (of_real c)))"
        by (simp add: fds_abs_converges_def)
    next
      show "\<forall>\<^sub>F n in sequentially. norm (norm (fds_nth (fds_integral a f) n / nat_power n (of_real c))) \<le> 
              norm (fds_nth f n / nat_power n (of_real c))"
        using eventually_gt_at_top[of 3]
      proof eventually_elim
        case (elim n)
        from elim and exp_le have "ln (exp 1) \<le> ln (real n)"
          by (subst ln_le_cancel_iff) auto
        hence "1 * norm (fds_nth f n) \<le> ln (real n) * norm (fds_nth f n)"
          by (intro mult_right_mono) auto
        with elim show ?case
          by (simp add: norm_divide norm_nat_power fds_integral_def field_simps)
      qed
    qed
    thus ?case by (intro exI[of _ "of_real c"]) auto
  qed
next
  show "abs_conv_abscissa f \<le> abs_conv_abscissa (fds_integral a f)" (is "_ \<le> ?s0")
  proof (cases "abs_conv_abscissa (fds_integral a f) = \<infinity>")
    case False
    show ?thesis
    proof (rule abs_conv_abscissa_leI)
      fix c :: real
      define \<epsilon> where "\<epsilon> = (if ?s0 = -\<infinity> then 1 else (c - real_of_ereal ?s0) / 2)"
      assume "ereal c > ?s0"
      with False have \<epsilon>: "\<epsilon> > 0" "c - \<epsilon> > ?s0"
        by (cases ?s0; force simp: \<epsilon>_def field_simps)+
  
      have "fds_abs_converges f (of_real c)"
        unfolding fds_abs_converges_def
      proof (rule summable_comparison_test_ev)
        from \<epsilon> have "fds_abs_converges (fds_integral a f) (of_real (c - \<epsilon>))"
          by (intro fds_abs_converges) (auto simp: algebra_simps)
        thus "summable (\<lambda>n. norm (fds_nth (fds_integral a f) n / nat_power n (of_real (c - \<epsilon>))))"
          by (simp add: fds_abs_converges_def)
      next
        have "\<forall>\<^sub>F n in at_top. ln (real n) / real n powr \<epsilon> < 1"
          by (rule order_tendstoD lim_ln_over_power \<open>\<epsilon> > 0\<close> zero_less_one)+
        thus "\<forall>\<^sub>F n in sequentially. norm (norm (fds_nth f n / nat_power n (of_real c)))
                \<le> norm (fds_nth (fds_integral a f) n / nat_power n (of_real (c - \<epsilon>)))"
          using eventually_gt_at_top[of 1]
        proof eventually_elim
          case (elim n)
          hence "ln (real n) * norm (fds_nth f n) \<le> real n powr \<epsilon> * norm (fds_nth f n)"
            by (intro mult_right_mono) auto
          with elim show ?case
            by (simp add: norm_divide norm_nat_power field_simps 
                          powr_diff inner_diff_left fds_integral_def)
        qed
      qed
      thus "\<exists>s. s \<bullet> 1 = c \<and> fds_abs_converges f s"
        by (intro exI[of _ "of_real c"]) auto
    qed
  qed auto
qed

lemma abs_conv_abscissa_ln: 
  "abs_conv_abscissa (fds_ln l (f :: 'a :: dirichlet_series fds)) = 
     abs_conv_abscissa (fds_deriv f / f)"
  by (simp add: fds_ln_def abs_conv_abscissa_integral)

lemma abs_conv_abscissa_deriv:
  fixes f :: "'a fds"
  shows "abs_conv_abscissa (fds_deriv f) = abs_conv_abscissa f"
proof -
  have "abs_conv_abscissa (fds_deriv f) = 
          abs_conv_abscissa (fds_integral (fds_nth f 1) (fds_deriv f))"
    by (rule abs_conv_abscissa_integral [symmetric])
  also have "fds_integral (fds_nth f 1) (fds_deriv f) = f"
    by (rule fds_integral_fds_deriv)
  finally show ?thesis .
qed

lemma abs_conv_abscissa_higher_deriv:
  "abs_conv_abscissa ((fds_deriv ^^ n) f) = abs_conv_abscissa (f :: 'a :: dirichlet_series fds)"
  by (induction n) (simp_all add: abs_conv_abscissa_deriv)

lemma conv_abscissa_higher_deriv_le:
  "conv_abscissa ((fds_deriv ^^ n) f) \<le> conv_abscissa (f :: 'a :: dirichlet_series fds)"
  by (induction n) (auto intro: order.trans[OF conv_abscissa_deriv_le])

lemma abs_conv_abscissa_restrict:
  "abs_conv_abscissa (fds_subseries P f) \<le> abs_conv_abscissa f"
  by (rule abs_conv_abscissa_mono) auto

lemma eval_fds_deriv:
  fixes f :: "'a fds"
  assumes "s \<bullet> 1 > conv_abscissa f"
  shows   "eval_fds (fds_deriv f) s = deriv (eval_fds f) s"
  by (intro DERIV_imp_deriv [symmetric] derivative_intros assms)

lemma eval_fds_higher_deriv:
  assumes "(s :: 'a :: dirichlet_series) \<bullet> 1 > conv_abscissa f"
  shows   "eval_fds ((fds_deriv ^^ n) f) s = (deriv ^^ n) (eval_fds f) s"
  using assms
proof (induction n arbitrary: f s)
  case (Suc n f s)
  have ev: "eventually (\<lambda>s. s \<in> {s. s \<bullet> 1 > conv_abscissa f}) (nhds s)"
    using Suc.prems open_halfspace_gt[of _ "1::'a"]
    by (intro eventually_nhds_in_open, cases "conv_abscissa f")
       (auto simp: open_halfspace_gt inner_commute)
  have "eval_fds ((fds_deriv ^^ Suc n) f) s = eval_fds ((fds_deriv ^^ n) (fds_deriv f)) s"
    by (subst funpow_Suc_right) simp
  also have "\<dots> = (deriv ^^ n) (eval_fds (fds_deriv f)) s"
    by (intro Suc.IH le_less_trans[OF conv_abscissa_deriv_le] Suc.prems)
  also have "\<dots> = (deriv ^^ n) (deriv (eval_fds f)) s"
    by (intro higher_deriv_cong_ev refl eventually_mono[OF ev] eval_fds_deriv) auto
  also have "\<dots> = (deriv ^^ Suc n) (eval_fds f) s"
    by (subst funpow_Suc_right) simp
  finally show ?case .
qed auto

end


subsection \<open>Multiplication of two series\<close>

lemma 
  fixes f g :: "nat \<Rightarrow> 'a :: {banach, real_normed_field, second_countable_topology, nat_power}"
  fixes s :: 'a
  assumes [simp]: "f 0 = 0" "g 0 = 0"
  assumes summable: "summable (\<lambda>n. norm (f n / nat_power n s))"
                    "summable (\<lambda>n. norm (g n / nat_power n s))"
  shows   summable_dirichlet_prod: "summable (\<lambda>n. norm (dirichlet_prod f g n / nat_power n s))"
    and   suminf_dirichlet_prod:
            "(\<Sum>n. dirichlet_prod f g n / nat_power n s) = 
               (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s)"
proof -
  have summable': "(\<lambda>n. f n / nat_power n s) abs_summable_on A"
                  "(\<lambda>n. g n / nat_power n s) abs_summable_on A" for A
    by ((rule abs_summable_on_subset[OF _ subset_UNIV], insert summable, 
        simp add: abs_summable_on_nat_iff'); fail)+
  have f_g: "f a / nat_power a s * (g b / nat_power b s) =
              f a * g b / nat_power (a * b) s" for a b
    by (cases "a * b = 0") (auto simp: nat_power_mult_distrib)

  have eq: "(\<Sum>\<^sub>a(m, n)\<in>{(m, n). m * n = x}. f m * g n / nat_power x s) =
              dirichlet_prod f g x / nat_power x s" for x :: nat
  proof (cases "x > 0")
    case False
    hence "(\<Sum>\<^sub>a(m,n) | m * n = x. f m * g n / nat_power x s) = (\<Sum>\<^sub>a(m,n) | m * n = x. 0)"
      by (intro infsetsum_cong) auto
    with False show ?thesis by simp
  next
    case True
    from finite_divisors_nat'[OF this] show ?thesis 
      by (simp add: dirichlet_prod_altdef2 case_prod_unfold sum_divide_distrib)
  qed

  have "(\<lambda>(m,n). (f m / nat_power m s) * (g n / nat_power n s)) abs_summable_on UNIV \<times> UNIV"
    using summable' by (intro abs_summable_on_product) auto
  also have "?this \<longleftrightarrow> (\<lambda>(m,n). f m * g n / nat_power (m*n) s) abs_summable_on UNIV"
    using f_g by (intro abs_summable_on_cong) auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,(m,n)). f m * g n / nat_power (m*n) s) abs_summable_on 
                           (SIGMA x:UNIV. {(m,n). m * n = x})"
    unfolding case_prod_unfold
    by (rule abs_summable_on_reindex_bij_betw [symmetric]) 
       (auto simp: bij_betw_def inj_on_def image_iff)
  also have "\<dots> \<longleftrightarrow> (\<lambda>(x,(m,n)). f m * g n / nat_power x s) abs_summable_on 
                           (SIGMA x:UNIV. {(m,n). m * n = x})"
    by (intro abs_summable_on_cong) auto
  finally have summable'': \<dots> .
  from abs_summable_on_Sigma_project1'[OF this]
    show summable''': "summable (\<lambda>n. norm (dirichlet_prod f g n / nat_power n s))"
    by (simp add: eq abs_summable_on_nat_iff')

  have "(\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s) =
          (\<Sum>\<^sub>an. f n / nat_power n s) * (\<Sum>\<^sub>an. g n / nat_power n s)"
    using summable' by (simp add: infsetsum_nat')
  also have "\<dots> = (\<Sum>\<^sub>a(m,n). (f m / nat_power m s) * (g n / nat_power n s))"
    using summable' by (subst infsetsum_product [symmetric]) simp_all
  also have "\<dots> = (\<Sum>\<^sub>a(m,n). f m * g n / nat_power (m * n) s)"
    using f_g by (intro infsetsum_cong refl) auto
  also have "\<dots> = (\<Sum>\<^sub>a(x,(m,n))\<in>(SIGMA x:UNIV. {(m,n). m * n = x}). 
                      f m * g n / nat_power (m * n) s)" 
    unfolding case_prod_unfold
    by (rule infsetsum_reindex_bij_betw [symmetric]) (auto simp: bij_betw_def inj_on_def image_iff)
  also have "\<dots> = (\<Sum>\<^sub>a(x,(m,n))\<in>(SIGMA x:UNIV. {(m,n). m * n = x}). 
                      f m * g n / nat_power x s)"
    by (intro infsetsum_cong refl) (auto simp: case_prod_unfold)
  also have "\<dots> = (\<Sum>\<^sub>ax. dirichlet_prod f g x / nat_power x s)"
    (is "_ = infsetsum ?T _") using summable'' by (subst infsetsum_Sigma) (auto simp: eq)
  also have "\<dots> = (\<Sum>x. dirichlet_prod f g x / nat_power x s)"
    using summable''' by (intro infsetsum_nat') (simp_all add: abs_summable_on_nat_iff')
  finally show "\<dots> = (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / nat_power n s)" ..
qed

lemma 
  fixes f g :: "nat \<Rightarrow> real"
  fixes s :: real
  assumes "f 0 = 0" "g 0 = 0"
  assumes summable: "summable (\<lambda>n. norm (f n / real n powr s))"
                    "summable (\<lambda>n. norm (g n / real n powr s))"
  shows   summable_dirichlet_prod_real: "summable (\<lambda>n. norm (dirichlet_prod f g n / real n powr s))"
    and   suminf_dirichlet_prod_real:
            "(\<Sum>n. dirichlet_prod f g n / real n powr s) = 
               (\<Sum>n. f n / nat_power n s) * (\<Sum>n. g n / real n powr s)"
  using summable_dirichlet_prod[of f g s] suminf_dirichlet_prod[of f g s] assms by simp_all

lemma fds_abs_converges_mult: 
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "fds_abs_converges (f * g) s"
  using summable_dirichlet_prod[OF _ _ assms[unfolded fds_abs_converges_def]]
  by (simp add: fds_abs_converges_def fds_nth_mult)

lemma fds_abs_converges_power: 
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  shows "fds_abs_converges f s \<Longrightarrow> fds_abs_converges (f ^ n) s"
  by (induction n) (auto intro!: fds_abs_converges_mult)

lemma fds_abs_converges_prod: 
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  shows "(\<And>x. x \<in> A \<Longrightarrow> fds_abs_converges (f x) s) \<Longrightarrow> fds_abs_converges (prod f A) s"
  by (induction A rule: infinite_finite_induct) (auto intro!: fds_abs_converges_mult)

lemma abs_conv_abscissa_mult_le:
  "abs_conv_abscissa (f * g :: 'a :: dirichlet_series fds) \<le> 
      max (abs_conv_abscissa f) (abs_conv_abscissa g)"
proof (rule abs_conv_abscissa_leI, goal_cases)
  case (1 c')
  thus ?case
    by (auto intro!: exI[of _ "of_real c'"] fds_abs_converges_mult intro: fds_abs_converges)
qed

lemma abs_conv_abscissa_mult_leI:
  "abs_conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow>
   abs_conv_abscissa g \<le> d \<Longrightarrow> abs_conv_abscissa (f * g) \<le> d"
  using abs_conv_abscissa_mult_le[of f g] by (auto simp add: le_max_iff_disj)

lemma abs_conv_abscissa_shift [simp]:
  "abs_conv_abscissa (fds_shift c f) = abs_conv_abscissa (f :: 'a :: dirichlet_series fds) + c \<bullet> 1"
proof -
  have "abs_conv_abscissa (fds_shift c f) \<le> abs_conv_abscissa f + c \<bullet> 1" for c :: 'a and f
  proof (rule abs_conv_abscissa_leI)
    fix d assume "abs_conv_abscissa f + c \<bullet> 1 < ereal d"
    hence "abs_conv_abscissa f < ereal (d - c \<bullet> 1)" by (cases "abs_conv_abscissa f") auto
    hence "fds_abs_converges (fds_shift c f) (of_real d)"
      by (auto intro!: fds_abs_converges_shift fds_abs_converges simp: algebra_simps)
    thus "\<exists>s. s \<bullet> 1 = d \<and> fds_abs_converges (fds_shift c f) s"
      by (auto intro!: exI[of _ "of_real d"])
  qed
  note * = this[of c f] this[of "-c" "fds_shift c f"]
  show ?thesis by (cases "abs_conv_abscissa (fds_shift c f)"; cases "abs_conv_abscissa f")
                  (insert *, auto intro!: antisym)
qed

lemma eval_fds_mult:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges g s"
  shows   "eval_fds (f * g) s = eval_fds f s * eval_fds g s"
  using suminf_dirichlet_prod[OF _ _ assms[unfolded fds_abs_converges_def]]
  by (simp_all add: eval_fds_def fds_nth_mult)

lemma eval_fds_power:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s"
  shows "eval_fds (f ^ n) s = eval_fds f s ^ n"
  using assms by (induction n) (simp_all add: eval_fds_mult fds_abs_converges_power)

lemma eval_fds_prod:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "(\<And>x. x \<in> A \<Longrightarrow> fds_abs_converges (f x) s)"
  shows "eval_fds (prod f A) s = (\<Prod>x\<in>A. eval_fds (f x) s)" using assms
  by (induction A rule: infinite_finite_induct) (auto simp: eval_fds_mult fds_abs_converges_prod)

lemma eval_fds_inverse:
  fixes s :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology}"
  assumes "fds_abs_converges f s" "fds_abs_converges (inverse f) s" "fds_nth f 1 \<noteq> 0"
  shows   "eval_fds (inverse f) s = inverse (eval_fds f s)"
proof -
  have "eval_fds (inverse f * f) s = eval_fds (inverse f) s * eval_fds f s"
    by (intro eval_fds_mult assms)
  also have "inverse f * f = 1" by (intro fds_left_inverse assms)
  also have "eval_fds 1 s = 1" by simp
  finally show ?thesis by (auto simp: divide_simps)
qed

lemma eval_fds_integral_has_field_derivative:
  fixes s :: "'a :: dirichlet_series"
  assumes "ereal (s \<bullet> 1) > abs_conv_abscissa f"
  assumes "fds_nth f 1 = 0"
  shows   "(eval_fds (fds_integral c f) has_field_derivative eval_fds f s) (at s)"
proof -
  have "conv_abscissa (fds_integral c f) \<le> abs_conv_abscissa (fds_integral c f)"
    by (rule conv_le_abs_conv_abscissa)
  also from assms have "\<dots> < ereal (s \<bullet> 1)" by (simp add: abs_conv_abscissa_integral)
  finally have "(eval_fds (fds_integral c f) has_field_derivative 
                  eval_fds (fds_deriv (fds_integral c f)) s) (at s)"
    by (intro derivative_eq_intros) auto
  also from assms have "fds_deriv (fds_integral c f) = f"
    by simp
  finally show ?thesis .
qed

lemma holomorphic_fds_eval [holomorphic_intros]:
  "A \<subseteq> {z. Re z > conv_abscissa f} \<Longrightarrow> eval_fds f holomorphic_on A"
  unfolding holomorphic_on_def field_differentiable_def
  by (rule ballI exI derivative_intros)+ auto
    
lemma analytic_fds_eval [holomorphic_intros]:
  assumes "A \<subseteq> {z. Re z > conv_abscissa f}"
  shows   "eval_fds f analytic_on A"
proof -
  have "eval_fds f analytic_on {z. Re z > conv_abscissa f}"
  proof (subst analytic_on_open)
    show "open {z. Re z > conv_abscissa f}"
      by (cases "conv_abscissa f") (simp_all add: open_halfspace_Re_gt)
  qed (intro holomorphic_intros, simp_all)
  from analytic_on_subset[OF this assms] show ?thesis .
qed

lemma conv_abscissa_0 [simp]: 
  "conv_abscissa (0 :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: conv_abscissa_MInf_iff)

lemma abs_conv_abscissa_0 [simp]: 
  "abs_conv_abscissa (0 :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: abs_conv_abscissa_MInf_iff)

lemma conv_abscissa_1 [simp]: 
  "conv_abscissa (1 :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: conv_abscissa_MInf_iff)

lemma abs_conv_abscissa_1 [simp]: 
  "abs_conv_abscissa (1 :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: abs_conv_abscissa_MInf_iff)

lemma conv_abscissa_const [simp]: 
  "conv_abscissa (fds_const (c :: 'a :: dirichlet_series)) = -\<infinity>"
  by (auto simp: conv_abscissa_MInf_iff)

lemma abs_conv_abscissa_const [simp]: 
  "abs_conv_abscissa (fds_const (c :: 'a :: dirichlet_series)) = -\<infinity>"
  by (auto simp: abs_conv_abscissa_MInf_iff)

lemma conv_abscissa_numeral [simp]: 
  "conv_abscissa (numeral n :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: numeral_fds)

lemma abs_conv_abscissa_numeral [simp]: 
  "abs_conv_abscissa (numeral n :: 'a :: dirichlet_series fds) = -\<infinity>"
  by (auto simp: numeral_fds)

lemma abs_conv_abscissa_power_le:
  "abs_conv_abscissa (f ^ n :: 'a :: dirichlet_series fds) \<le> abs_conv_abscissa f"
  by (induction n) (auto intro!: order.trans[OF abs_conv_abscissa_mult_le])

lemma abs_conv_abscissa_power_leI:
  "abs_conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> abs_conv_abscissa (f ^ n) \<le> d"
  by (rule order.trans[OF abs_conv_abscissa_power_le])

lemma abs_conv_abscissa_prod_le:
  assumes "\<And>x. x \<in> A \<Longrightarrow> abs_conv_abscissa (f x :: 'a :: dirichlet_series fds) \<le> d"
  shows   "abs_conv_abscissa (prod f A) \<le> d" using assms
  by (induction A rule: infinite_finite_induct) (auto intro!: abs_conv_abscissa_mult_leI)

lemma conv_abscissa_add_le:
  "conv_abscissa (f + g :: 'a :: dirichlet_series fds) \<le> max (conv_abscissa f) (conv_abscissa g)"
  by (rule conv_abscissa_leI_weak) (auto intro!: fds_converges_add intro: fds_converges)

lemma conv_abscissa_add_leI:
  "conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> conv_abscissa g \<le> d \<Longrightarrow> 
     conv_abscissa (f + g) \<le> d"
  using conv_abscissa_add_le[of f g] by (auto simp: le_max_iff_disj)

lemma conv_abscissa_sum_leI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> conv_abscissa (f x :: 'a :: dirichlet_series fds) \<le> d"
  shows   "conv_abscissa (sum f A) \<le> d" using assms
  by (induction A rule: infinite_finite_induct) (auto intro!: conv_abscissa_add_leI)

lemma abs_conv_abscissa_add_le:
  "abs_conv_abscissa (f + g :: 'a :: dirichlet_series fds) \<le> max (abs_conv_abscissa f) (abs_conv_abscissa g)"
  by (rule abs_conv_abscissa_leI_weak) (auto intro!: fds_abs_converges_add intro: fds_abs_converges)

lemma abs_conv_abscissa_add_leI:
  "abs_conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> abs_conv_abscissa g \<le> d \<Longrightarrow> 
     abs_conv_abscissa (f + g) \<le> d"
  using abs_conv_abscissa_add_le[of f g] by (auto simp: le_max_iff_disj)

lemma abs_conv_abscissa_sum_leI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> abs_conv_abscissa (f x :: 'a :: dirichlet_series fds) \<le> d"
  shows   "abs_conv_abscissa (sum f A) \<le> d" using assms
  by (induction A rule: infinite_finite_induct) (auto intro!: abs_conv_abscissa_add_leI)

lemma fds_converges_cmult_left [intro]:
  assumes "fds_converges f s"
  shows   "fds_converges (fds_const c * f) s"
proof -
  from assms have "summable (\<lambda>n. c * (fds_nth f n / nat_power n s))"
    by (intro summable_mult) (auto simp: fds_converges_def)
  thus ?thesis by (simp add: fds_converges_def mult_ac)
qed

lemma fds_converges_cmult_right [intro]:
  assumes "fds_converges f s"
  shows   "fds_converges (f * fds_const c) s"
  using fds_converges_cmult_left[OF assms] by (simp add: mult_ac)

lemma conv_abscissa_cmult_left [simp]:
  fixes c :: "'a :: dirichlet_series" assumes "c \<noteq> 0"
  shows "conv_abscissa (fds_const c * f) = conv_abscissa f"
proof -
  have "fds_converges (fds_const c * f) s \<longleftrightarrow> fds_converges f s" for s
  proof
    assume "fds_converges (fds_const c * f) s"
    hence "fds_converges (fds_const (inverse c) * (fds_const c * f)) s"
      by (rule fds_converges_cmult_left)
    also have "fds_const (inverse c) * (fds_const c * f) = fds_const (inverse c * c) * f"
      by simp
    also have "inverse c * c = 1"
      using assms by simp
    finally show "fds_converges f s" by simp
  qed auto
  thus ?thesis by (simp add: conv_abscissa_def)
qed

lemma conv_abscissa_cmult_right [simp]:
  fixes c :: "'a :: dirichlet_series" assumes "c \<noteq> 0"
  shows "conv_abscissa (f * fds_const c) = conv_abscissa f"
  using assms by (subst mult.commute) auto

lemma abs_conv_abscissa_cmult: 
  fixes c :: "'a :: dirichlet_series" assumes "c \<noteq> 0"
  shows "abs_conv_abscissa (fds_const c * f) = abs_conv_abscissa f"
proof (intro antisym)
  have "abs_conv_abscissa (fds_const (inverse c) * (fds_const c * f)) \<le> 
          abs_conv_abscissa (fds_const c * f)"
    using abs_conv_abscissa_mult_le[of "fds_const (inverse c)" "fds_const c * f"]
    by (auto simp: max_def)
  also have "fds_const (inverse c) * (fds_const c * f) = fds_const (inverse c * c) * f"
    by (simp add: mult_ac)
  also have "inverse c * c = 1" using assms by simp
  finally show "abs_conv_abscissa f \<le> abs_conv_abscissa (fds_const c * f)" by simp
qed (insert abs_conv_abscissa_mult_le[of "fds_const c" f], auto simp: max_def)

lemma conv_abscissa_minus [simp]:
  fixes f :: "'a :: dirichlet_series fds"
  shows "conv_abscissa (-f) = conv_abscissa f"
  using conv_abscissa_cmult_left[of "-1" f] by simp

lemma abs_conv_abscissa_minus [simp]:
  fixes f :: "'a :: dirichlet_series fds"
  shows "abs_conv_abscissa (-f) = abs_conv_abscissa f"
  using abs_conv_abscissa_cmult[of "-1" f] by simp

lemma conv_abscissa_diff_le:
  "conv_abscissa (f - g :: 'a :: dirichlet_series fds) \<le> max (conv_abscissa f) (conv_abscissa g)"
  using conv_abscissa_add_le[of f "-g"] by simp

lemma conv_abscissa_diff_leI:
  "conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> conv_abscissa g \<le> d \<Longrightarrow> 
     conv_abscissa (f - g) \<le> d"
  using conv_abscissa_add_le[of f "-g"] by (auto simp: le_max_iff_disj)

lemma abs_conv_abscissa_diff_le:
  "abs_conv_abscissa (f - g :: 'a :: dirichlet_series fds) \<le>
     max (abs_conv_abscissa f) (abs_conv_abscissa g)"
  using abs_conv_abscissa_add_le[of f "-g"] by simp

lemma abs_conv_abscissa_diff_leI:
  "abs_conv_abscissa (f :: 'a :: dirichlet_series fds) \<le> d \<Longrightarrow> abs_conv_abscissa g \<le> d \<Longrightarrow> 
     abs_conv_abscissa (f - g) \<le> d"
  using abs_conv_abscissa_add_le[of f "-g"] by (auto simp: le_max_iff_disj)

lemmas eval_fds_integral_has_field_derivative' [derivative_intros] = 
  DERIV_chain'[OF _ eval_fds_integral_has_field_derivative]

lemma abs_conv_abscissa_completely_multiplicative_log_deriv:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "completely_multiplicative_function (fds_nth f)" "fds_nth f 1 \<noteq> 0"
  shows   "abs_conv_abscissa (fds_deriv f / f) \<le> abs_conv_abscissa f"
proof -
  have "fds_deriv f = - fds (\<lambda>n. fds_nth f n * mangoldt n) * f"
    using assms by (subst completely_multiplicative_fds_deriv') simp_all
  also have "\<dots> / f = - fds (\<lambda>n. fds_nth f n * mangoldt n) * (f * inverse f)"
    by (simp add: divide_fds_def)
  also have "f * inverse f = 1" using assms by (intro fds_right_inverse)
  finally have "fds_deriv f / f = - fds (\<lambda>n. fds_nth f n * mangoldt n)" by simp
  also have "abs_conv_abscissa \<dots> = 
               abs_conv_abscissa (fds (\<lambda>n. fds_nth f n * mangoldt n))" 
    (is "_ = abs_conv_abscissa ?f") by (rule abs_conv_abscissa_minus)
  also have "\<dots> \<le> abs_conv_abscissa f"
  proof (rule abs_conv_abscissa_leI, goal_cases)
    case (1 c)
    have "fds_abs_converges ?f (of_real c)" unfolding fds_abs_converges_def
    proof (rule summable_comparison_test_ev)
      from 1 have "fds_abs_converges (fds_deriv f) (of_real c)" 
        by (intro fds_abs_converges) (auto simp: abs_conv_abscissa_deriv)
      thus "summable (\<lambda>n. \<bar>ln (real n)\<bar> * norm (fds_nth f n) / norm (nat_power n (of_real c :: 'a)))"
        by (simp add: fds_abs_converges_def fds_deriv_def fds_nth_fds' 
                      scaleR_conv_of_real powr_minus norm_mult norm_divide norm_nat_power)
    next
      show "\<forall>\<^sub>F n in sequentially.
              norm (norm (fds_nth (fds (\<lambda>n. fds_nth f n * mangoldt n)) n /
                 nat_power n (of_real c)))
              \<le> \<bar>ln (real n)\<bar> * norm (fds_nth f n) / norm (nat_power n (of_real c) :: 'a)"
        using eventually_gt_at_top[of 0]
      proof eventually_elim
        case (elim n)
        have "norm (norm (fds_nth (fds (\<lambda>n. fds_nth f n * mangoldt n)) n /
                  nat_power n (of_real c))) =
                norm (fds_nth f n) * mangoldt n / real n powr c"
          using elim by (simp add: fds_nth_fds' norm_mult norm_divide 
                                   norm_nat_power abs_mult mangoldt_nonneg)
        also have "\<dots> \<le> norm (fds_nth f n) * ln n / real n powr c" using elim
          by (intro mult_left_mono divide_right_mono mangoldt_le)
             (simp_all add: mangoldt_def)
        finally show ?case using elim by (simp add: norm_nat_power algebra_simps)
      qed
    qed
    thus ?case by (intro exI[of _ "of_real c"]) auto
  qed
  finally show ?thesis .
qed

  
subsection \<open>Uniqueness\<close>
  
context
  assumes "SORT_CONSTRAINT ('a :: dirichlet_series)"
begin

lemma norm_dirichlet_series_cutoff_le:
  assumes "fds_abs_converges f (s0 :: 'a)" "N > 0" "s \<bullet> 1 \<ge> c" "c \<ge> s0 \<bullet> 1"
  shows   "summable (\<lambda>n. fds_nth f (n + N) / nat_power (n + N) s)"
          "summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)"
    and   "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s) \<le> 
             (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c) / nat_power N (s \<bullet> 1 - c)"
proof -
  from assms have "fds_abs_converges f (of_real c)" 
    using fds_abs_converges_Re_le[of f s0 "of_real c"] by auto
  hence "summable (\<lambda>n. norm (fds_nth f (n + N) / nat_power (n + N) (of_real c)))"
    unfolding fds_abs_converges_def by (rule summable_ignore_initial_segment)
  also have "?this \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)"
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: norm_divide norm_nat_power)
  finally show *: "summable (\<lambda>n. norm (fds_nth f (n + N)) / nat_power (n + N) c)" .

  from assms have "fds_abs_converges f s" using fds_abs_converges_Re_le[of f s0 s] by auto
  hence **: "summable (\<lambda>n. norm (fds_nth f (n + N) / nat_power (n + N) s))"
    unfolding fds_abs_converges_def by (rule summable_ignore_initial_segment)
  thus "summable (\<lambda>n. fds_nth f (n + N) / nat_power (n + N) s)"
    by (rule summable_norm_cancel)

  have "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s)
          \<le> (\<Sum>n. norm (fds_nth f (n + N) / nat_power (n + N) s))"
    by (intro summable_norm **) 
  also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c / nat_power N (s \<bullet> 1 - c))"
  proof (intro suminf_le * ** summable_divide allI)
    fix n :: nat
    have "real N powr (s \<bullet> 1 - c) \<le> real (n + N) powr (s \<bullet> 1 - c)"
      using assms by (intro powr_mono2) simp_all
    also have "real (n + N) powr c * \<dots> = real (n + N) powr (s \<bullet> 1)"
      by (simp add: powr_diff)
    finally have "norm (fds_nth f (n + N)) / real (n + N) powr (s \<bullet> 1) \<le>
                    norm (fds_nth f (n + N)) / (real (n + N) powr c * real N powr (s \<bullet> 1 - c))"
      using \<open>N > 0\<close> by (intro divide_left_mono) (simp_all add: mult_left_mono)
    thus "norm (fds_nth f (n + N) / nat_power (n + N) s) \<le> 
            norm (fds_nth f (n + N)) / nat_power (n + N) c / nat_power N (s \<bullet> 1 - c)"
      using \<open>N > 0\<close> by (simp add: norm_divide norm_nat_power )
  qed
  also have "\<dots> = (\<Sum>n. norm (fds_nth f (n + N)) / nat_power (n + N) c) / nat_power N (s \<bullet> 1 - c)"
    using * by (rule suminf_divide)
  finally show "norm (\<Sum>n. fds_nth f (n + N) / nat_power (n + N) s) \<le> \<dots>" .
qed

lemma eval_fds_zeroD_aux:
  fixes h :: "'a fds"
  assumes conv: "fds_abs_converges h (s0 :: 'a)"
  assumes freq: "frequently (\<lambda>s. eval_fds h s = 0) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  shows   "h = 0"
proof (rule ccontr)
  assume "h \<noteq> 0"
  hence ex: "\<exists>n>0. fds_nth h n \<noteq> 0" by (auto simp: fds_eq_iff)
  define N :: nat where "N = (LEAST n. n > 0 \<and> fds_nth h n \<noteq> 0)"
  have N: "N > 0" "fds_nth h N \<noteq> 0" 
    using LeastI_ex[OF ex, folded N_def] by auto
  have less_N: "fds_nth h n = 0" if "n < N" for n
    using Least_le[of "\<lambda>n. n > 0 \<and> fds_nth h n \<noteq> 0" n, folded N_def] that
    by (cases "n = 0") (auto simp: not_less)
      
  define c where "c = s0 \<bullet> 1"
  define remainder where "remainder = (\<lambda>s. (\<Sum>n. fds_nth h (n + Suc N) / nat_power (n + Suc N) s))"
  define A where "A = (\<Sum>n. norm (fds_nth h (n + Suc N)) / nat_power (n + Suc N) c) *
                         nat_power (Suc N) c"

  have eq: "fds_nth h N = nat_power N s * eval_fds h s - nat_power N s * remainder s"
    if "s \<bullet> 1 \<ge> c" for s :: 'a
  proof -
    from conv and that have conv': "fds_abs_converges h s" 
      unfolding c_def by (rule fds_abs_converges_Re_le)
    hence conv'': "fds_converges h s" by blast
    from conv'' have "(\<lambda>n. fds_nth h n / nat_power n s) sums eval_fds h s"
      by (simp add: fds_converges_iff)
    hence "(\<lambda>n. fds_nth h (n + Suc N) / nat_power (n + Suc N) s) sums 
             (eval_fds h s - (\<Sum>n<Suc N. fds_nth h n / nat_power n s))"
      by (rule sums_split_initial_segment)
    also have "(\<Sum>n<Suc N. fds_nth h n / nat_power n s) = 
                 (\<Sum>n<Suc N. if n = N then fds_nth h N / nat_power N s else 0)"
      by (intro sum.cong refl) (auto simp: less_N)
    also have "\<dots> = fds_nth h N / nat_power N s" by (subst sum.delta) auto
    finally show ?thesis unfolding remainder_def using \<open>N > 0\<close> by (auto simp: sums_iff field_simps)
  qed
  
  have remainder_bound: "norm (remainder s) \<le> A / real (Suc N) powr (s \<bullet> 1)"
    if "s \<bullet> 1 \<ge> c" for s :: 'a
  proof -
    note * = norm_dirichlet_series_cutoff_le[of h s0 "Suc N" c s, folded remainder_def]
    have "norm (remainder s) \<le> (\<Sum>n. norm (fds_nth h (n + Suc N)) /
           nat_power (n + Suc N) c) / nat_power (Suc N) (s \<bullet> 1 - c)"
      using that assms unfolding remainder_def by (intro *) (simp_all add: c_def)
    also have "\<dots> = A / real (Suc N) powr (s \<bullet> 1)" by (simp add: A_def powr_diff)
    finally show ?thesis .
  qed

  from freq have "\<forall>c. \<exists>s. s \<bullet> 1 \<ge> c \<and> eval_fds h s = 0"
    unfolding frequently_def by (auto simp: eventually_going_to_at_top_linorder)
  hence "\<forall>k. \<exists>s. s \<bullet> 1 \<ge> real k \<and> eval_fds h s = 0" by blast
  then obtain S where S: "\<And>k. S k \<bullet> 1 \<ge> real k \<and> eval_fds h (S k) = 0"
    by metis
  have S_limit: "filterlim (\<lambda>k. S k \<bullet> 1) at_top sequentially"
    by (rule filterlim_at_top_mono[OF filterlim_real_sequentially]) (use S in auto)

  have "eventually (\<lambda>k. real k \<ge> c) sequentially" by real_asymp
  hence "eventually (\<lambda>k. norm (fds_nth h N) \<le> 
           (real N / real (Suc N)) powr (S k \<bullet> 1) * A) sequentially"
  proof eventually_elim
    case (elim k)
    hence "norm (fds_nth h N) = real N powr (S k \<bullet> 1) *  norm (remainder (S k))"
      (is "_ = _ * ?X") using \<open>N > 0\<close> S[of k] eq[of "S k"]
      by (auto simp: norm_mult norm_nat_power c_def)
    also have "norm (remainder (S k)) \<le> A / real (Suc N) powr (S k \<bullet> 1)"
      using elim S[of k] by (intro remainder_bound) (simp_all add: c_def)
    finally show ?case
      using N by (simp add: mult_left_mono powr_divide field_simps del: of_nat_Suc)
  qed
  moreover have "((\<lambda>k. (real N / real (Suc N)) powr (S k \<bullet> 1) * A) \<longlongrightarrow> 0) sequentially"
    by (rule filterlim_compose[OF _ S_limit]) (use \<open>N > 0\<close> in real_asymp)
  ultimately have "((\<lambda>_. fds_nth h N) \<longlongrightarrow> 0) sequentially"
    by (rule Lim_null_comparison)
  hence "fds_nth h N = 0" by (simp add: tendsto_const_iff)
  with \<open>fds_nth h N \<noteq> 0\<close> show False by contradiction
qed

lemma eval_fds_zeroD:
  fixes h :: "'a fds"
  assumes conv: "conv_abscissa h < \<infinity>"
  assumes freq: "frequently (\<lambda>s. eval_fds h s = 0) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  shows   "h = 0"
proof -
  have [simp]: "2 \<bullet> (1 :: 'a) = 2"
    using of_real_inner_1[of 2] unfolding of_real_numeral by simp
  from conv obtain s where "fds_converges h s"
    by auto
  hence "fds_abs_converges h (s + 2)"
    by (rule fds_converges_imp_abs_converges) (auto simp: algebra_simps)
  from this assms(2-) show ?thesis by (rule eval_fds_zeroD_aux)
qed

lemma eval_fds_eqD:
  fixes f g :: "'a fds"
  assumes conv: "conv_abscissa f < \<infinity>" "conv_abscissa g < \<infinity>"
  assumes eq:   "frequently (\<lambda>s. eval_fds f s = eval_fds g s) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  shows   "f = g"
proof -
  have conv': "conv_abscissa (f - g) < \<infinity>"
    using assms by (intro le_less_trans[OF conv_abscissa_diff_le]) (auto simp: max_def)

  have "max (conv_abscissa f) (conv_abscissa g) < \<infinity>"
    using conv by (auto simp: max_def)
  from ereal_dense2[OF this] obtain c where c: "max (conv_abscissa f) (conv_abscissa g) < ereal c"
    by auto

  (* TODO: something like "frequently_elim" would be great here *)
  have "frequently (\<lambda>s. eval_fds f s = eval_fds g s \<and> s \<bullet> 1 \<ge> c) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
    using eq by (rule frequently_eventually_frequently) auto
  hence *: "frequently (\<lambda>s. eval_fds (f - g) s = 0) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  proof (rule frequently_mono [rotated], safe, goal_cases)
    case (1 s)
    thus ?case using c
      by (subst eval_fds_diff) (auto intro!: fds_converges intro: less_le_trans)
  qed
  have "f - g = 0" by (rule eval_fds_zeroD fds_abs_converges_diff assms * conv')+
  thus ?thesis by simp
qed

end


subsection \<open>Limit at infinity\<close>

lemma eval_fds_at_top_tail_bound:
  fixes f :: "'a :: dirichlet_series fds"
  assumes c: "ereal c > abs_conv_abscissa f"
  defines "B \<equiv> (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) * 2 powr c"
  assumes s: "s \<bullet> 1 \<ge> c"
  shows   "norm (eval_fds f s - fds_nth f 1) \<le> B / 2 powr (s \<bullet> 1)"
proof -
  from c have "fds_abs_converges f (of_real c)" by (intro fds_abs_converges) simp_all
  also have "?this \<longleftrightarrow> summable (\<lambda>n. norm (fds_nth f n) / real n powr c)"
    unfolding fds_abs_converges_def
    by (intro summable_cong eventually_mono[OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: norm_divide norm_nat_power norm_powr_real_powr)
  finally have summable_c: \<dots> .

  note c
  also from s have "ereal c \<le> ereal (s \<bullet> 1)" by simp
  finally have "fds_abs_converges f s" by (intro fds_abs_converges) auto
  hence summable: "summable (\<lambda>n. norm (fds_nth f n / nat_power n s))"
    by (simp add: fds_abs_converges_def)
  from summable_norm_cancel[OF this]
    have "(\<lambda>n. fds_nth f n / nat_power n s) sums eval_fds f s"
    by (simp add: eval_fds_def sums_iff)
  from sums_split_initial_segment[OF this, of "Suc (Suc 0)"]
    have "norm (eval_fds f s - fds_nth f 1) = norm (\<Sum>n. fds_nth f (n+2) / nat_power (n+2) s)"
    by (auto simp: sums_iff)
  also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n+2) / nat_power (n+2) s))"
    by (intro summable_norm summable_ignore_initial_segment summable)
  also have "\<dots> \<le> (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c / 2 powr (s \<bullet> 1 - c))"
  proof (intro suminf_le allI)
    fix n :: nat
    have "norm (fds_nth f (n + 2) / nat_power (n + 2) s) =
            norm (fds_nth f (n + 2)) / real (n+2) powr c / real (n+2) powr (s \<bullet> 1 - c)"
      by (simp add: field_simps powr_diff norm_divide norm_nat_power)
    also have "\<dots> \<le> norm (fds_nth f (n + 2)) / real (n+2) powr c / 2 powr (s \<bullet> 1 - c)" using s
      by (intro divide_left_mono divide_nonneg_pos powr_mono2 mult_pos_pos) simp_all
    finally show "norm (fds_nth f (n + 2) / nat_power (n + 2) s) \<le> \<dots>" .
  qed (intro summable_ignore_initial_segment summable summable_divide summable_c)+
  also have "\<dots> = (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) / 2 powr (s \<bullet> 1 - c)"
    by (intro suminf_divide summable_ignore_initial_segment summable_c)
  also have "\<dots> = B / 2 powr (s \<bullet> 1)" by (simp add: B_def powr_diff)
  finally show ?thesis .
qed

lemma tendsto_eval_fds_Re_at_top:
  assumes "conv_abscissa (f :: 'a :: dirichlet_series fds) \<noteq> \<infinity>"
  assumes lim: "filterlim (\<lambda>x. S x \<bullet> 1) at_top F"
  shows   "((\<lambda>x. eval_fds f (S x)) \<longlongrightarrow> fds_nth f 1) F"
proof -
  from assms(1) have "abs_conv_abscissa f < \<infinity>"
    using abs_conv_le_conv_abscissa_plus_1[of f] by auto
  from ereal_dense2[OF this] obtain c where c: "abs_conv_abscissa f < ereal c" by auto
  define B where "B = (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) * 2 powr c"

  have *: "norm (eval_fds f s - fds_nth f 1) \<le> B / 2 powr (s \<bullet> 1)" if s: "s \<bullet> 1 \<ge> c" for s
    using eval_fds_at_top_tail_bound[of f c s] that c by (simp add: B_def)
  moreover from lim have "eventually (\<lambda>x. S x \<bullet> 1 \<ge> c) F" by (auto simp: filterlim_at_top)
  ultimately have "eventually (\<lambda>x. norm (eval_fds f (S x) - fds_nth f 1) \<le> 
                      B / 2 powr (S x \<bullet> 1)) F" by (auto elim!: eventually_mono)
  moreover have "((\<lambda>x. B / 2 powr (S x \<bullet> 1)) \<longlongrightarrow> 0) F"
    using filterlim_tendsto_pos_mult_at_top[OF tendsto_const[of "ln 2"] _ lim]
    by (intro real_tendsto_divide_at_top[OF tendsto_const])
       (auto simp: powr_def mult_ac intro!: filterlim_compose[OF exp_at_top])
  ultimately have "((\<lambda>x. eval_fds f (S x) - fds_nth f 1) \<longlongrightarrow> 0) F"
    by (rule Lim_null_comparison)
  thus ?thesis by (subst (asm) Lim_null [symmetric])
qed

lemma tendsto_eval_fds_Re_at_top':
  assumes "conv_abscissa (f :: complex fds) \<noteq> \<infinity>"
  shows   "uniform_limit UNIV (\<lambda>\<sigma> t. eval_fds f (of_real \<sigma> + of_real t * \<i>)
                       ) (\<lambda>_ .fds_nth f 1) at_top"
proof -
  from assms(1) have "abs_conv_abscissa f < \<infinity>"
    using abs_conv_le_conv_abscissa_plus_1[of f] by auto
  from ereal_dense2[OF this] obtain c where c: "abs_conv_abscissa f < ereal c" by auto
  define B where "B \<equiv> (\<Sum>n. norm (fds_nth f (n+2)) / real (n+2) powr c) * 2 powr c"

  show ?thesis
    unfolding uniform_limit_iff
  proof safe
    fix \<epsilon> :: real assume "\<epsilon> > 0"
    hence "eventually (\<lambda>\<sigma>. B / 2 powr \<sigma> < \<epsilon>) at_top"
      by real_asymp
    thus "eventually (\<lambda>\<sigma>. \<forall>t\<in>UNIV.
            dist (eval_fds f (of_real \<sigma> + of_real t * \<i>)) (fds_nth f 1) < \<epsilon>) at_top"
      using eventually_ge_at_top[of c]
    proof eventually_elim
      case (elim \<sigma>)
      show ?case
      proof
        fix t :: real
        have "dist (eval_fds f (of_real \<sigma> + of_real t * \<i>)) (fds_nth f 1) \<le> B / 2 powr \<sigma>"
          using eval_fds_at_top_tail_bound[of f c "of_real \<sigma> + of_real t * \<i>"] elim c
          by (simp add: dist_norm B_def)
        also have "\<dots> < \<epsilon>" by fact
        finally show "dist (eval_fds f (of_real \<sigma> + of_real t * \<i>)) (fds_nth f 1) < \<epsilon>" .
      qed
    qed
  qed
qed

lemma tendsto_eval_fds_Re_going_to_at_top:
  assumes "conv_abscissa (f :: 'a :: dirichlet_series fds) \<noteq> \<infinity>"
  shows   "((\<lambda>s. eval_fds f s) \<longlongrightarrow> fds_nth f 1) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
  using assms by (rule tendsto_eval_fds_Re_at_top) auto

lemma tendsto_eval_fds_Re_going_to_at_top':
  assumes "conv_abscissa (f :: complex fds) \<noteq> \<infinity>"
  shows   "((\<lambda>s. eval_fds f s) \<longlongrightarrow> fds_nth f 1) (Re going_to at_top)"
  using assms by (rule tendsto_eval_fds_Re_at_top) auto

text \<open>
  Any Dirichlet series that is not identically zero and does not diverge everywhere
  has a half-plane in which it converges and is non-zero.
\<close>
theorem fds_nonzero_halfplane_exists:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "conv_abscissa f < \<infinity>" "f \<noteq> 0"
  shows   "eventually (\<lambda>s. fds_converges f s \<and> eval_fds f s \<noteq> 0) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
proof -
  from ereal_dense2[OF assms(1)] obtain c where c: "conv_abscissa f < ereal c" by auto
  have "eventually (\<lambda>s::'a. s \<bullet> 1 > c) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
    using eventually_gt_at_top[of c] by auto
  hence "eventually (\<lambda>s. fds_converges f s) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
    by eventually_elim (use c in \<open>auto intro!: fds_converges simp: less_le_trans\<close>)
  moreover have "eventually (\<lambda>s. eval_fds f s \<noteq> 0) ((\<lambda>s. s \<bullet> 1) going_to at_top)"
    using eval_fds_zeroD[OF assms(1)] assms(2) by (auto simp: frequently_def)
  ultimately show ?thesis by (rule eventually_conj)
qed 


subsection \<open>Normed series\<close>

lemma fds_converges_norm_iff [simp]: 
  fixes s :: "'a :: {nat_power_normed_field,banach}"
  shows "fds_converges (fds_norm f) (s \<bullet> 1) \<longleftrightarrow> fds_abs_converges f s"
  unfolding fds_converges_def fds_abs_converges_def
  by (rule summable_cong [OF eventually_mono[OF eventually_gt_at_top[of 0]]])
     (simp add: fds_abs_converges_def fds_norm_def fds_nth_fds' norm_divide norm_nat_power)

lemma fds_abs_converges_norm_iff [simp]: 
  fixes s :: "'a :: {nat_power_normed_field,banach}"
  shows "fds_abs_converges (fds_norm f) (s \<bullet> 1) \<longleftrightarrow> fds_abs_converges f s"
  unfolding fds_abs_converges_def
  by (rule summable_cong [OF eventually_mono[OF eventually_gt_at_top[of 0]]])
     (simp add: fds_abs_converges_def fds_norm_def fds_nth_fds' norm_divide norm_nat_power)

lemma fds_converges_norm_iff': 
  fixes f :: "'a :: {nat_power_normed_field,banach} fds"
  shows "fds_converges (fds_norm f) s \<longleftrightarrow> fds_abs_converges f (of_real s)"
  unfolding fds_converges_def fds_abs_converges_def
  by (rule summable_cong [OF eventually_mono[OF eventually_gt_at_top[of 0]]])
     (simp add: fds_abs_converges_def fds_norm_def fds_nth_fds' norm_divide norm_nat_power)

lemma fds_abs_converges_norm_iff': 
  fixes f :: "'a :: {nat_power_normed_field,banach} fds"
  shows "fds_abs_converges (fds_norm f) s \<longleftrightarrow> fds_abs_converges f (of_real s)"
  unfolding fds_abs_converges_def
  by (rule summable_cong [OF eventually_mono[OF eventually_gt_at_top[of 0]]])
     (simp add: fds_abs_converges_def fds_norm_def fds_nth_fds' norm_divide norm_nat_power)

lemma abs_conv_abscissa_norm [simp]: 
  fixes f :: "'a :: dirichlet_series fds"
  shows "abs_conv_abscissa (fds_norm f) = abs_conv_abscissa f"
proof (rule antisym)
  show "abs_conv_abscissa f \<le> abs_conv_abscissa (fds_norm f)"
  proof (rule abs_conv_abscissa_leI_weak)
    fix x assume "abs_conv_abscissa (fds_norm f) < ereal x"
    hence "fds_abs_converges (fds_norm f) (of_real x)" by (intro fds_abs_converges) auto
    thus "fds_abs_converges f (of_real x)" by (simp add: fds_abs_converges_norm_iff')
  qed
qed (auto intro!: abs_conv_abscissa_leI_weak simp: fds_abs_converges_norm_iff' fds_abs_converges)

lemma conv_abscissa_norm [simp]: 
  fixes f :: "'a :: dirichlet_series fds"
  shows "conv_abscissa (fds_norm f) = abs_conv_abscissa f"
proof (rule antisym)
  show "abs_conv_abscissa f \<le> conv_abscissa (fds_norm f)"
  proof (rule abs_conv_abscissa_leI_weak)
    fix x assume "conv_abscissa (fds_norm f) < ereal x"
    hence "fds_converges (fds_norm f) (of_real x)" by (intro fds_converges) auto
    thus "fds_abs_converges f (of_real x)" by (simp add: fds_converges_norm_iff')
  qed
qed (auto intro!: conv_abscissa_leI_weak simp: fds_abs_converges)

lemma 
  fixes f g :: "'a :: dirichlet_series fds"
  assumes "fds_abs_converges (fds_norm f) s" "fds_abs_converges (fds_norm g) s"
  shows   fds_abs_converges_norm_mult: "fds_abs_converges (fds_norm (f * g)) s"
  and     eval_fds_norm_mult_le: 
            "eval_fds (fds_norm (f * g)) s \<le> eval_fds (fds_norm f) s * eval_fds (fds_norm g) s"
proof -
  show conv: "fds_abs_converges (fds_norm (f * g)) s" unfolding fds_abs_converges_def
  proof (rule summable_comparison_test_ev)
    have "fds_abs_converges (fds_norm f * fds_norm g) s" by (rule fds_abs_converges_mult assms)+
    thus "summable (\<lambda>n. norm (fds_nth (fds_norm f * fds_norm g) n) / nat_power n s)"
      by (simp add: fds_abs_converges_def)
  qed (auto intro!: always_eventually divide_right_mono order.trans[OF fds_nth_norm_mult_le] 
            simp: norm_divide)
  have conv': "fds_abs_converges (fds_norm f * fds_norm g) s"
    by (intro fds_abs_converges_mult assms)
  hence "eval_fds (fds_norm (f * g)) s \<le> eval_fds (fds_norm f * fds_norm g) s"
    using conv unfolding eval_fds_def fds_abs_converges_def norm_divide
    by (intro suminf_le allI divide_right_mono) (simp_all add: norm_mult fds_nth_norm_mult_le)
  also have "\<dots> = eval_fds (fds_norm f) s * eval_fds (fds_norm g) s"
    by (intro eval_fds_mult assms)
  finally show "eval_fds (fds_norm (f * g)) s \<le> eval_fds (fds_norm f) s * eval_fds (fds_norm g) s" .
qed

lemma eval_fds_norm_nonneg:
  assumes "fds_abs_converges (fds_norm f) s"
  shows   "eval_fds (fds_norm f) s \<ge> 0"
  using assms unfolding eval_fds_def fds_abs_converges_def
  by (intro suminf_nonneg) auto

lemma
  fixes f :: "'a :: dirichlet_series fds"
  assumes "fds_abs_converges (fds_norm f) s"
  shows   fds_abs_converges_norm_power: "fds_abs_converges (fds_norm (f ^ n)) s"
  and     eval_fds_norm_power_le: 
            "eval_fds (fds_norm (f ^ n)) s \<le> eval_fds (fds_norm f) s ^ n"
proof -
  show *: "fds_abs_converges (fds_norm (f ^ n)) s" for n
    by (induction n) (auto intro!: fds_abs_converges_norm_mult assms)
  show "eval_fds (fds_norm (f ^ n)) s \<le> eval_fds (fds_norm f) s ^ n"
    by (induction n) (auto intro!: order.trans[OF eval_fds_norm_mult_le] assms * 
                                   mult_left_mono eval_fds_norm_nonneg)
qed


subsection \<open>Logarithms of Dirichlet series\<close>

(* TODO: Move ? *)
lemma eventually_gt_ereal_at_top: "c \<noteq> \<infinity> \<Longrightarrow> eventually (\<lambda>x. ereal x > c) at_top"
  by (cases c) auto

lemma eval_fds_log_deriv:
  fixes s :: "'a :: dirichlet_series"
  assumes "fds_nth f 1 \<noteq> 0" "s \<bullet> 1 > abs_conv_abscissa f" 
           "s \<bullet> 1 > abs_conv_abscissa (fds_deriv f / f)"
  assumes "eval_fds f s \<noteq> 0"
  shows   "eval_fds (fds_deriv f / f) s = eval_fds (fds_deriv f) s / eval_fds f s"
proof -
  have "eval_fds (fds_deriv f / f * f) s = eval_fds (fds_deriv f / f) s * eval_fds f s"
    using assms by (intro eval_fds_mult fds_abs_converges) auto
  also have "fds_deriv f / f * f = fds_deriv f * (f * inverse f)"
    by (simp add: divide_fds_def algebra_simps)
  also have "f * inverse f = 1" using assms by (intro fds_right_inverse)
  finally show ?thesis using assms by simp
qed

text \<open>
  Given a sufficiently nice absolutely convergent Dirichlet series that converges
  to some function $f(s)$ and a holomorphic branch of $\ln f(s)$, we can construct 
  a Dirichlet series that absolutely converges to that logarithm.
\<close>
lemma eval_fds_ln:
  fixes s0 :: ereal
  assumes nz: "\<And>s. Re s > s0 \<Longrightarrow> eval_fds f s \<noteq> 0" "fds_nth f 1 \<noteq> 0"
  assumes l: "exp l = fds_nth f 1" "((g \<circ> of_real) \<longlongrightarrow> l) at_top"
  assumes g: "\<And>s. Re s > s0 \<Longrightarrow> exp (g s) = eval_fds f s"
  assumes holo_g: "g holomorphic_on {s. Re s > s0}"
  assumes "ereal (Re s) > s0"
  assumes "s0 \<ge> abs_conv_abscissa f" and "s0 \<ge> abs_conv_abscissa (fds_deriv f / f)"
  shows   "eval_fds (fds_ln l f) s = g s"
proof -
  let ?s0 = "abs_conv_abscissa f" and ?s1 = "abs_conv_abscissa (inverse f)"
  let ?h = "\<lambda>s. eval_fds (fds_ln l f) s - g s"
  let ?A = "{s. Re s > s0}"
  have open_A: "open ?A" by (cases s0) (auto simp: open_halfspace_Re_gt)

  have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
  moreover from assms have "\<dots> \<noteq> \<infinity>" by auto
  ultimately have "conv_abscissa f \<noteq> \<infinity>" by auto

  have "conv_abscissa (fds_ln l f) \<le> abs_conv_abscissa (fds_ln l f)"
    by (rule conv_le_abs_conv_abscissa)
  also have "\<dots> \<le> abs_conv_abscissa (fds_deriv f / f)"
    unfolding fds_ln_def by (simp add: abs_conv_abscissa_integral)
  finally have "conv_abscissa (fds_ln l f) \<noteq> \<infinity>"
    using assms by (auto simp: max_def abs_conv_abscissa_deriv split: if_splits)

  have deriv_g [derivative_intros]:
    "(g has_field_derivative eval_fds (fds_deriv f) s / eval_fds f s) (at s within B)"
    if s: "Re s > s0" for s B
  proof -
    have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> \<le> s0" using assms by simp
    also have "\<dots> < Re s" by fact
    finally have s': "Re s > conv_abscissa f" .

    have deriv_g: "(g has_field_derivative deriv g s) (at s)"
      using holomorphic_derivI[OF holo_g open_A, of s] s
      by (auto simp: at_within_open[OF _ open_A])
    have "((\<lambda>s. exp (g s)) has_field_derivative eval_fds f s * deriv g s) (at s)" (is ?P)
      by (rule derivative_eq_intros deriv_g s)+ (insert s, simp_all add: g)
    also from s have ev: "eventually (\<lambda>t. t \<in> ?A) (nhds s)"
      by (intro eventually_nhds_in_open open_A) auto
    have "?P \<longleftrightarrow> (eval_fds f has_field_derivative eval_fds f s * deriv g s) (at s)"
      by (intro DERIV_cong_ev refl eventually_mono[OF ev]) (auto simp: g)
    finally have "(eval_fds f has_field_derivative eval_fds f s * deriv g s) (at s)" .
    moreover have "(eval_fds f has_field_derivative eval_fds (fds_deriv f) s) (at s)"
      using s' assms by (intro derivative_intros) auto
    ultimately have "eval_fds f s * deriv g s = eval_fds (fds_deriv f) s"
      by (rule DERIV_unique)
    hence "deriv g s = eval_fds (fds_deriv f) s / eval_fds f s"
      using s nz by (simp add: field_simps)
    with deriv_g show ?thesis by (auto intro: has_field_derivative_at_within)
  qed  

  have "\<exists>c. \<forall>z\<in>{z. Re z > s0}. ?h z = c"
  proof (rule DERIV_zero_constant, goal_cases)
    case 1
    show ?case using convex_halfspace_gt[of _ "1::complex"]
      by (cases s0) auto
  next
    case (2 z)
    have "conv_abscissa (fds_ln l f) \<le> abs_conv_abscissa (fds_ln l f)"
      by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> \<le> abs_conv_abscissa (fds_deriv f / f)"
      by (simp add: abs_conv_abscissa_ln)
    also have "\<dots> < Re z" using 2 assms by (auto simp: abs_conv_abscissa_deriv)
    finally have s1: "conv_abscissa (fds_ln l f) < ereal (Re z)" .

    have "conv_abscissa f \<le> abs_conv_abscissa f"
      by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> < Re z" using 2 assms by auto
    finally have s2: "conv_abscissa f < ereal (Re z)" .

    from l have "fds_nth f 1 \<noteq> 0" by auto
    with 2 assms have *: "eval_fds (fds_deriv f / f) z = eval_fds (fds_deriv f) z / (eval_fds f z)"
      by (auto simp: eval_fds_log_deriv)
    have "eval_fds f z \<noteq> 0" using 2 assms by auto
    show ?case using s1 s2 2 nz
      by (auto intro!: derivative_eq_intros simp: * field_simps)
  qed
  then obtain c where c: "\<And>z. Re z > s0 \<Longrightarrow> ?h z = c" by blast

  have "(at_top :: real filter) \<noteq> bot" by simp
  moreover from assms have "s0 \<noteq> \<infinity>" by auto
  have "eventually (\<lambda>x. c = (?h \<circ> of_real) x) at_top"
    using eventually_gt_ereal_at_top[OF \<open>s0 \<noteq> \<infinity>\<close>] by eventually_elim (simp add: c)
  hence "((?h \<circ> of_real) \<longlongrightarrow> c) at_top"
    by (rule Lim_transform_eventually) auto
  moreover have "((?h \<circ> of_real) \<longlongrightarrow> fds_nth (fds_ln l f) 1 - l) at_top"
    using \<open>conv_abscissa (fds_ln l f) \<noteq> \<infinity>\<close> and l unfolding o_def
    by (intro tendsto_intros tendsto_eval_fds_Re_at_top) (auto simp: filterlim_ident)
  ultimately have "c = fds_nth (fds_ln l f) 1 - l"
    by (rule tendsto_unique)
  with c[OF \<open>Re s > s0\<close>] and l and nz show ?thesis
    by (simp add: exp_minus field_simps)
qed

text \<open>
  Less explicitly: For a sufficiently nice absolutely convergent Dirichlet series converging
  to a function $f(s)$, the formal logarithm absolutely converges to some logarithm of $f(s)$.
\<close>
lemma eval_fds_ln':
  fixes s0 :: ereal
  assumes "ereal (Re s) > s0"
  assumes "s0 \<ge> abs_conv_abscissa f" and "s0 \<ge> abs_conv_abscissa (fds_deriv f / f)"
      and nz: "\<And>s. Re s > s0 \<Longrightarrow> eval_fds f s \<noteq> 0" "fds_nth f 1 \<noteq> 0"
  assumes l: "exp l = fds_nth f 1"
  shows   "exp (eval_fds (fds_ln l f) s) = eval_fds f s"
proof -
  let ?s0 = "abs_conv_abscissa f" and ?s1 = "abs_conv_abscissa (inverse f)"
  let ?h = "\<lambda>s. eval_fds f s * exp (-eval_fds (fds_ln l f) s)"

  have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
  moreover from assms have "\<dots> \<noteq> \<infinity>" by auto
  ultimately have "conv_abscissa f \<noteq> \<infinity>" by auto

  have "conv_abscissa (fds_ln l f) \<le> abs_conv_abscissa (fds_ln l f)"
    by (rule conv_le_abs_conv_abscissa)
  also have "\<dots> \<le> abs_conv_abscissa (fds_deriv f / f)"
    unfolding fds_ln_def by (simp add: abs_conv_abscissa_integral)
  finally have "conv_abscissa (fds_ln l f) \<noteq> \<infinity>"
    using assms by (auto simp: max_def abs_conv_abscissa_deriv split: if_splits)

  have "\<exists>c. \<forall>z\<in>{z. Re z > s0}. ?h z = c"
  proof (rule DERIV_zero_constant, goal_cases)
    case 1
    show ?case using convex_halfspace_gt[of _ "1::complex"]
      by (cases s0) auto
  next
    case (2 z)
    have "conv_abscissa (fds_ln l f) \<le> abs_conv_abscissa (fds_ln l f)"
      by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> \<le> abs_conv_abscissa (fds_deriv f / f)"
      unfolding fds_ln_def by (simp add: abs_conv_abscissa_integral)
    also have "\<dots> < Re z" using 2 assms by (auto simp: abs_conv_abscissa_deriv)
    finally have s1: "conv_abscissa (fds_ln l f) < ereal (Re z)" .

    have "conv_abscissa f \<le> abs_conv_abscissa f"
      by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> < Re z" using 2 assms by auto
    finally have s2: "conv_abscissa f < ereal (Re z)" .

    from l have "fds_nth f 1 \<noteq> 0" by auto
    with 2 assms have *: "eval_fds (fds_deriv f / f) z = eval_fds (fds_deriv f) z / (eval_fds f z)"
      by (subst eval_fds_log_deriv) auto
    have "eval_fds f z \<noteq> 0" using 2 assms by auto
    thus ?case using s1 s2
      by (auto intro!: derivative_eq_intros simp: *)
  qed
  then obtain c where c: "\<And>z. Re z > s0 \<Longrightarrow> ?h z = c" by blast

  have "(at_top :: real filter) \<noteq> bot" by simp
  moreover from assms have "s0 \<noteq> \<infinity>" by auto
  have "eventually (\<lambda>x. c = (?h \<circ> of_real) x) at_top"
    using eventually_gt_ereal_at_top[OF \<open>s0 \<noteq> \<infinity>\<close>] by eventually_elim (simp add: c)
  hence "((?h \<circ> of_real) \<longlongrightarrow> c) at_top"
    by (rule Lim_transform_eventually) auto
  moreover have "((?h \<circ> of_real) \<longlongrightarrow> fds_nth f 1 * exp (-fds_nth (fds_ln l f) 1)) at_top"
    unfolding o_def using \<open>conv_abscissa (fds_ln l f) \<noteq> \<infinity>\<close> and \<open>conv_abscissa f \<noteq> \<infinity>\<close>
    by (intro tendsto_intros tendsto_eval_fds_Re_at_top) (auto simp: filterlim_ident)
  ultimately have "c = fds_nth f 1 * exp (-fds_nth (fds_ln l f) 1)"
    by (rule tendsto_unique)
  with c[OF \<open>Re s > s0\<close>] and l and nz show ?thesis
    by (simp add: exp_minus field_simps)
qed

lemma fds_ln_completely_multiplicative:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "completely_multiplicative_function (fds_nth f)"
  assumes "fds_nth f 1 \<noteq> 0"
  shows   "fds_ln l f = fds (\<lambda>n. if n = 1 then l else fds_nth f n * mangoldt n /\<^sub>R ln n)"
proof -
  have "fds_ln l f = fds_integral l (fds_deriv f / f)"
    by (simp add: fds_ln_def)
  also have "fds_deriv f = -fds (\<lambda>n. fds_nth f n * mangoldt n) * f"
    by (intro completely_multiplicative_fds_deriv' assms)
  also have "\<dots> / f = -fds (\<lambda>n. fds_nth f n * mangoldt n) * (f * inverse f)"
    by (simp add: divide_fds_def)
  also from assms have "f * inverse f = 1"
    by (simp add: fds_right_inverse)
  also have "fds_integral l (- fds (\<lambda>n. fds_nth f n * mangoldt n) * 1) = 
               fds (\<lambda>n. if n = 1 then l else fds_nth f n * mangoldt n /\<^sub>R ln n)"
    by (simp add: fds_integral_def cong: if_cong)
  finally show ?thesis .
qed

lemma eval_fds_ln_completely_multiplicative_strong:
  fixes s :: "'a :: dirichlet_series" and l :: 'a and f :: "'a fds" and g :: "nat \<Rightarrow> 'a"
  defines "h \<equiv> fds (\<lambda>n. fds_nth (fds_ln l f) n * g n)"
  assumes "fds_abs_converges h s"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_nth f 1 \<noteq> 0"
  shows  "(\<lambda>(p,k). (fds_nth f p / nat_power p s) ^ Suc k * g (p ^ Suc k) / of_nat (Suc k))
            abs_summable_on ({p. prime p} \<times> UNIV)" (is ?th1)
    and  "eval_fds h s = l * g 1 + (\<Sum>\<^sub>a(p, k)\<in>{p. prime p}\<times>UNIV.
            (fds_nth f p / nat_power p s) ^ Suc k * g (p ^ Suc k) / of_nat (Suc k))" (is ?th2)
proof -
  let ?P = "{p::nat. prime p}"
  interpret f: completely_multiplicative_function "fds_nth f" by fact
  from assms have *: "(\<lambda>n. fds_nth h n / nat_power n s) abs_summable_on UNIV"
    by (auto simp: abs_summable_on_nat_iff' fds_abs_converges_def)
  have eq: "h = fds (\<lambda>n. if n = 1 then l * g 1 else fds_nth f n * g n * mangoldt n /\<^sub>R ln (real n))"
    using fds_ln_completely_multiplicative [OF assms(3), of l] 
    by (simp add: h_def fds_eq_iff)

  note *
  also have "(\<lambda>n. fds_nth h n / nat_power n s) abs_summable_on UNIV \<longleftrightarrow>
          (\<lambda>x. if x = Suc 0 then l * g 1 else fds_nth f x * g x * mangoldt x /\<^sub>R ln (real x) /
                nat_power x s) abs_summable_on {1} \<union> Collect primepow"
    using eq by (intro abs_summable_on_cong_neutral) (auto simp: fds_nth_fds mangoldt_def)
  finally have sum1: "(\<lambda>x. if x = Suc 0 then l * g 1 else 
                        fds_nth f x * g x * mangoldt x /\<^sub>R ln (real x) / nat_power x s)
                      abs_summable_on Collect primepow"
    by (rule abs_summable_on_subset) auto
  also have "?this \<longleftrightarrow> (\<lambda>x. fds_nth f x * g x * mangoldt x /\<^sub>R ln (real x) / nat_power x s) 
                         abs_summable_on Collect primepow" 
    by (intro abs_summable_on_cong) (insert primepow_gt_Suc_0, auto)
  also have "\<dots> \<longleftrightarrow> (\<lambda>(p,k). fds_nth f (p ^ Suc k) * g (p ^ Suc k) * mangoldt (p ^ Suc k)
                 /\<^sub>R ln (real (p ^ Suc k)) / nat_power (p ^ Suc k) s) abs_summable_on (?P \<times> UNIV)"
    using bij_betw_primepows unfolding case_prod_unfold
    by (intro abs_summable_on_reindex_bij_betw [symmetric])
  also have "\<dots> \<longleftrightarrow> ?th1"
    by (intro abs_summable_on_cong)
       (auto simp: f.mult f.power mangoldt_def aprimedivisor_prime_power ln_realpow prime_gt_0_nat 
          nat_power_power_left divide_simps scaleR_conv_of_real simp del: power_Suc)
  finally show ?th1 .

  have "eval_fds h s = (\<Sum>\<^sub>an. fds_nth h n / nat_power n s)"
    using * unfolding eval_fds_def by (subst infsetsum_nat') auto
  also have "\<dots> = (\<Sum>\<^sub>an \<in> {1} \<union> {n. primepow n}.
        if n = 1 then l * g 1 else fds_nth f n * g n * mangoldt n /\<^sub>R ln (real n) /  nat_power n s)"
    by (intro infsetsum_cong_neutral) (auto simp: eq fds_nth_fds mangoldt_def)
  also have "\<dots> = l * g 1 + (\<Sum>\<^sub>an | primepow n.
         if n = 1 then l * g 1 else fds_nth f n * g n * mangoldt n /\<^sub>R ln (real n) / nat_power n s)"
    (is "_ = _ + ?x") using sum1 primepow_gt_Suc_0 by (subst infsetsum_Un_disjoint) auto
  also have "?x =
    (\<Sum>\<^sub>an\<in>Collect primepow. fds_nth f n * g n * mangoldt n /\<^sub>R ln (real n) / nat_power n s)"
    (is "_ = infsetsum ?f _") by (intro infsetsum_cong refl) (insert primepow_gt_Suc_0, auto)
  also have "\<dots> = (\<Sum>\<^sub>a(p,k)\<in>(?P \<times> UNIV). fds_nth f (p ^ Suc k) * g (p ^ Suc k) *
                    mangoldt (p ^ Suc k) /\<^sub>R ln (p ^ Suc k) / nat_power (p ^ Suc k) s)"
     using bij_betw_primepows unfolding case_prod_unfold 
     by (intro infsetsum_reindex_bij_betw [symmetric])
   also have "\<dots> = (\<Sum>\<^sub>a(p,k)\<in>(?P \<times> UNIV). 
                     (fds_nth f p / nat_power p s) ^ Suc k * g (p ^ Suc k) / of_nat (Suc k))"
    by (intro infsetsum_cong)
       (auto simp: f.mult f.power mangoldt_def aprimedivisor_prime_power ln_realpow prime_gt_0_nat 
          nat_power_power_left divide_simps scaleR_conv_of_real simp del: power_Suc)
  finally show ?th2 .
qed    

lemma eval_fds_ln_completely_multiplicative:
  fixes s :: "'a :: dirichlet_series" and l :: 'a and f :: "'a fds"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_nth f 1 \<noteq> 0"
  assumes "s \<bullet> 1 > abs_conv_abscissa (fds_deriv f / f)"
  shows  "(\<lambda>(p,k). (fds_nth f p / nat_power p s) ^ Suc k / of_nat (Suc k))
            abs_summable_on ({p. prime p} \<times> UNIV)" (is ?th1)
    and  "eval_fds (fds_ln l f) s =
                  l + (\<Sum>\<^sub>a(p, k)\<in>{p. prime p}\<times>UNIV.
                        (fds_nth f p / nat_power p s) ^ Suc k / of_nat (Suc k))" (is ?th2)
proof -
  from assms have "fds_abs_converges (fds_ln l f) s"
    by (intro fds_abs_converges_ln) (auto intro!: fds_abs_converges_mult intro: fds_abs_converges)
  hence "fds_abs_converges (fds (\<lambda>n. fds_nth (fds_ln l f) n * 1)) s"
    by simp
  from eval_fds_ln_completely_multiplicative_strong [OF this assms(1,2)] show ?th1 ?th2 
    by simp_all
qed

subsection \<open>Exponential and logarithm\<close>

lemma summable_fds_exp_aux:
  assumes "fds_nth f' 1 = (0 :: 'a :: real_normed_algebra_1)"
  shows   "summable (\<lambda>k. fds_nth (f' ^ k) n /\<^sub>R fact k)"
proof (rule summable_finite)
  fix k assume "k \<notin> {..n}"
  hence "n < k" by simp
  also have "\<dots> < 2 ^ k" by (induction k) auto
  finally have "fds_nth (f' ^ k) n = 0"
    using assms by (intro fds_nth_power_eq_0) auto
  thus "fds_nth (f' ^ k) n /\<^sub>R fact k = 0" by simp
qed auto

lemma
  fixes f :: "'a :: dirichlet_series fds"
  assumes "fds_abs_converges f s"
  shows   fds_abs_converges_exp: "fds_abs_converges (fds_exp f) s"
  and     eval_fds_exp: "eval_fds (fds_exp f) s = exp (eval_fds f s)"
proof -
  have conv: "fds_abs_converges (fds_exp f) s" and ev: "eval_fds (fds_exp f) s = exp (eval_fds f s)"
    if "fds_abs_converges f s" and [simp]: "fds_nth f (Suc 0) = 0" for f
  proof -
    have [simp]: "fds (\<lambda>n. if n = Suc 0 then 0 else fds_nth f n) = f"
      by (intro fds_eqI) simp_all
    have  "(\<lambda>(k,n). fds_nth (f ^ k) n / fact k / nat_power n s) abs_summable_on (UNIV \<times> {1..})"
    proof (subst abs_summable_on_Sigma_iff, safe, goal_cases)
      case (3 k)
      from that have "fds_abs_converges (f ^ k) s" by (intro fds_abs_converges_power)
      hence "(\<lambda>n. fds_nth (f ^ k) n / nat_power n s * inverse (fact k)) abs_summable_on {1..}"
        unfolding fds_abs_converges_altdef by (intro abs_summable_on_cmult_left)
      thus ?case by (simp add: field_simps)
    next
      case 4
      show ?case unfolding abs_summable_on_nat_iff'
      proof (rule summable_comparison_test_ev[OF always_eventually[OF allI]])
        fix k :: nat
        from that have *: "fds_abs_converges (fds_norm (f ^ k)) (s \<bullet> 1)"
          by (auto simp: fds_abs_converges_power)
        have "(\<Sum>\<^sub>an\<in>{1..}. norm (fds_nth (f ^ k) n / fact k / nat_power n s)) =
                (\<Sum>\<^sub>an\<in>{1..}. fds_nth (fds_norm (f ^ k)) n / nat_power n (s \<bullet> 1) / fact k)" 
          (is "?S = _") by (intro infsetsum_cong) (simp_all add: norm_divide norm_mult norm_nat_power)
        also have "\<dots> = (\<Sum>\<^sub>an\<in>{1..}. fds_nth (fds_norm (f ^ k)) n / nat_power n (s \<bullet> 1)) /\<^sub>R fact k"
          (is "_ = ?S' /\<^sub>R _") using * unfolding fds_abs_converges_altdef
          by (subst infsetsum_cdiv) (auto simp: abs_summable_on_nat_iff scaleR_conv_of_real divide_simps)
        also have "?S' = eval_fds (fds_norm (f ^ k)) (s \<bullet> 1)"
          using * unfolding fds_abs_converges_altdef eval_fds_def
          by (subst infsetsum_nat) (auto intro!: suminf_cong)
        finally have eq: "?S = \<dots> /\<^sub>R fact k" .
        note eq
        also have "?S \<ge> 0" by (intro infsetsum_nonneg) auto
        hence "?S = norm (norm ?S)" by simp
        also have "eval_fds (fds_norm (f ^ k)) (s \<bullet> 1) \<le> eval_fds (fds_norm f) (s \<bullet> 1) ^ k"
          using that by (intro eval_fds_norm_power_le) auto
        finally show "norm (norm (\<Sum>\<^sub>an\<in>{1..}. norm (fds_nth (f ^ k) n / fact k / nat_power n s))) \<le>
                        eval_fds (fds_norm f) (s \<bullet> 1) ^ k /\<^sub>R fact k" 
          by (simp add: divide_right_mono)
      next
        from exp_converges[of "eval_fds (fds_norm f) (s \<bullet> 1)"]
        show "summable (\<lambda>x. eval_fds (fds_norm f) (s \<bullet> 1) ^ x /\<^sub>R fact x)"
          by (simp add: sums_iff)
      qed
    qed auto
    hence summable:
      "(\<lambda>(n,k). fds_nth (f ^ k) n / fact k / nat_power n s) abs_summable_on {1..} \<times> UNIV"
      by (subst abs_summable_on_Times_swap) (simp add: case_prod_unfold)
  
    have summable': "(\<lambda>k. fds_nth (f ^ k) n / fact k) abs_summable_on UNIV" for n
      using abs_summable_on_cmult_left[of "nat_power n s",
              OF abs_summable_on_Sigma_project2 [OF summable, of n]] by (cases "n = 0") simp_all
  
    have "(\<lambda>n. \<Sum>\<^sub>ak. fds_nth (f ^ k) n / fact k / nat_power n s) abs_summable_on {1..}"
      using summable by (rule abs_summable_on_Sigma_project1') auto
    also have "?this \<longleftrightarrow> (\<lambda>n. (\<Sum>k. fds_nth (f ^ k) n / fact k) * inverse (nat_power n s)) 
                           abs_summable_on {1..}"
    proof (intro abs_summable_on_cong refl, goal_cases)
      case (1 n)
      hence "(\<Sum>\<^sub>ak. fds_nth (f ^ k) n / fact k / nat_power n s) =
              (\<Sum>\<^sub>ak. fds_nth (f ^ k) n / fact k) * inverse (nat_power n s)"
        using summable'[of n]
        by (subst infsetsum_cmult_left [symmetric]) (auto simp: field_simps)
      also have "(\<Sum>\<^sub>ak. fds_nth (f ^ k) n / fact k) = (\<Sum>k. fds_nth (f ^ k) n / fact k)"
        using summable'[of n] 1 by (intro abs_summable_on_cong refl infsetsum_nat') auto
      finally show ?case .
    qed
    finally show "fds_abs_converges (fds_exp f) s"
      by (simp add: fds_exp_def fds_nth_fds' abs_summable_on_Sigma_iff scaleR_conv_of_real 
                    fds_abs_converges_altdef field_simps)
  
    have "eval_fds (fds_exp f) s = (\<Sum>n. (\<Sum>k. fds_nth (f ^ k) n /\<^sub>R fact k) / nat_power n s)"
      by (simp add: fds_exp_def eval_fds_def fds_nth_fds')
    also have "\<dots> = (\<Sum>n. (\<Sum>\<^sub>ak. fds_nth (f ^ k) n /\<^sub>R fact k) / nat_power n s)"
    proof (intro suminf_cong, goal_cases)
      case (1 n)
      show ?case
      proof (cases "n = 0")
        case False
        have "(\<Sum>k. fds_nth (f ^ k) n /\<^sub>R fact k) = (\<Sum>\<^sub>ak. fds_nth (f ^ k) n /\<^sub>R fact k)"
          using summable'[of n] False
          by (intro infsetsum_nat' [symmetric]) (auto simp: scaleR_conv_of_real field_simps)
        thus ?thesis by simp
      qed simp_all
    qed
    also have "\<dots> = (\<Sum>\<^sub>an. (\<Sum>\<^sub>ak. fds_nth (f ^ k) n /\<^sub>R fact k) / nat_power n s)"
    proof (intro infsetsum_nat' [symmetric], goal_cases)
      case 1
      have *: "UNIV - {Suc 0..} = {0}" by auto
      have "(\<lambda>x. \<Sum>\<^sub>ay. fds_nth (f ^ y) x / fact y / nat_power x s) abs_summable_on {1..}"
        by (intro abs_summable_on_Sigma_project1'[OF summable]) auto
      also have "?this \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>ay. fds_nth (f ^ y) x / fact y) * inverse (nat_power x s)) 
                    abs_summable_on {1..}"
        using summable' by (intro abs_summable_on_cong refl, subst infsetsum_cmult_left [symmetric])
                           (auto simp: field_simps)
      also have "\<dots> \<longleftrightarrow> (\<lambda>x. (\<Sum>\<^sub>ay. fds_nth (f ^ y) x /\<^sub>R fact y) / (nat_power x s)) 
                    abs_summable_on {1..}" by (simp add: field_simps scaleR_conv_of_real)
      finally show ?case by (rule abs_summable_on_finite_diff) (use * in auto)
    qed
    also have "\<dots> = (\<Sum>\<^sub>an. (\<Sum>\<^sub>ak. fds_nth (f ^ k) n /\<^sub>R fact k * inverse (nat_power n s)))"
      using summable' by (subst infsetsum_cmult_left) (auto simp: field_simps scaleR_conv_of_real)
    also have "\<dots> = (\<Sum>\<^sub>an\<in>{1..}. (\<Sum>\<^sub>ak. fds_nth (f ^ k) n /\<^sub>R fact k * inverse (nat_power n s)))"
      by (intro infsetsum_cong_neutral) (auto simp: Suc_le_eq)
    also have "\<dots> = (\<Sum>\<^sub>ak. \<Sum>\<^sub>an\<in>{1..}. fds_nth (f ^ k) n / nat_power n s /\<^sub>R fact k)" using summable 
      by (subst infsetsum_swap) (auto simp: field_simps scaleR_conv_of_real case_prod_unfold)
    also have "\<dots> = (\<Sum>\<^sub>ak. (\<Sum>\<^sub>an\<in>{1..}. fds_nth (f ^ k) n / nat_power n s) /\<^sub>R fact k)"
      by (subst infsetsum_scaleR_right) simp
    also have "\<dots> = (\<Sum>\<^sub>ak. eval_fds f s ^ k /\<^sub>R fact k)"
    proof (intro infsetsum_cong refl, goal_cases)
      case (1 k)
      have *: "fds_abs_converges (f ^ k) s" by (intro fds_abs_converges_power that)
      have "(\<Sum>\<^sub>an\<in>{1..}. fds_nth (f ^ k) n / nat_power n s) =
              (\<Sum>\<^sub>an. fds_nth (f ^ k) n / nat_power n s)"
        by (intro infsetsum_cong_neutral) (auto simp: Suc_le_eq)
      also have "\<dots> = eval_fds (f ^ k) s" using * unfolding eval_fds_def 
        by (intro infsetsum_nat') (auto simp: fds_abs_converges_def abs_summable_on_nat_iff')
      also from that have "\<dots> = eval_fds f s ^ k" by (simp add: eval_fds_power)
      finally show ?case by simp
    qed
    also have "\<dots> = (\<Sum>k. eval_fds f s ^ k /\<^sub>R fact k)"
      using exp_converges[of "norm (eval_fds f s)"]
      by (intro infsetsum_nat') (auto simp: abs_summable_on_nat_iff' sums_iff field_simps norm_power)
    also have "\<dots> = exp (eval_fds f s)" by (simp add: exp_def)
    finally show "eval_fds (fds_exp f) s = exp (eval_fds f s)" .
  qed
  
  define f' where "f' = f - fds_const (fds_nth f 1)"
  have *: "fds_abs_converges (fds_exp f') s" 
    by (auto simp: f'_def intro!: fds_abs_converges_diff conv assms)
  have "fds_abs_converges (fds_const (exp (fds_nth f 1)) * fds_exp f') s"
    unfolding f'_def
    by (intro fds_abs_converges_mult conv fds_abs_converges_diff assms) auto
  thus "fds_abs_converges (fds_exp f) s" unfolding f'_def
    by (simp add: fds_exp_times_fds_nth_0)
  have "eval_fds (fds_exp f) s = eval_fds (fds_const (exp (fds_nth f 1)) * fds_exp f') s"
    by (simp add: f'_def fds_exp_times_fds_nth_0)
  also have "\<dots> = exp (fds_nth f (Suc 0)) * eval_fds (fds_exp f') s" using *
    using assms by (subst eval_fds_mult) (simp_all)
  also have "\<dots> = exp (eval_fds f s)" using ev[of f'] assms unfolding f'_def
    by (auto simp: fds_abs_converges_diff eval_fds_diff fds_abs_converges_imp_converges exp_diff)
  finally show "eval_fds (fds_exp f) s = exp (eval_fds f s)" .
qed

lemma fds_exp_add:
  fixes f :: "'a :: dirichlet_series fds"
  shows   "fds_exp (f + g) = fds_exp f * fds_exp g"
proof (rule fds_eqI_truncate)
  fix m :: nat assume m: "m > 0"
  let ?T = "fds_truncate m"
  have "?T (fds_exp (f + g)) = ?T (fds_exp (?T f + ?T g))"
    by (simp add: fds_truncate_exp fds_truncate_add_strong [symmetric])
  also have "fds_exp (?T f + ?T g) = fds_exp (?T f) * fds_exp (?T g)"
  proof (rule eval_fds_eqD)
    have "fds_abs_converges (fds_exp (?T f + ?T g)) 0"
      by (intro fds_abs_converges_exp fds_abs_converges_add) auto
    thus "conv_abscissa (fds_exp (?T f + ?T g)) < \<infinity>"
      using conv_abscissa_PInf_iff by blast
    hence "fds_abs_converges (fds_exp (fds_truncate m f) * fds_exp (fds_truncate m g)) 0"
      by (intro fds_abs_converges_mult fds_abs_converges_exp) auto
    thus "conv_abscissa (fds_exp (fds_truncate m f) * fds_exp (fds_truncate m g)) < \<infinity>"
      using conv_abscissa_PInf_iff by blast
    show "frequently (\<lambda>s. eval_fds (fds_exp (fds_truncate m f + fds_truncate m g)) s =
                          eval_fds (fds_exp (fds_truncate m f) * fds_exp (fds_truncate m g)) s)
            ((\<lambda>s. s \<bullet> 1) going_to at_top)"
      by (auto simp: eval_fds_add eval_fds_mult eval_fds_exp fds_abs_converges_add 
                     fds_abs_converges_exp exp_add)
  qed
  also have "?T \<dots> = ?T (fds_exp f * fds_exp g)"
    by (subst fds_truncate_mult [symmetric], subst (1 2) fds_truncate_exp)
       (simp add: fds_truncate_mult)
  finally show "?T (fds_exp (f + g)) = \<dots>" .
qed

lemma fds_exp_minus:
  fixes f :: "'a :: dirichlet_series fds"
  shows   "fds_exp (-f) = inverse (fds_exp f)"
proof (rule fds_right_inverse_unique)
  have "fds_exp f * fds_exp (- f) = fds_exp (f + (-f))"
    by (subst fds_exp_add) simp_all
  also have "f + (-f) = 0" by simp
  also have "fds_exp \<dots> = 1" by simp
  finally show "fds_exp f * fds_exp (-f) = 1" .
qed

lemma abs_conv_abscissa_exp: 
  fixes f :: "'a :: dirichlet_series fds"
  shows "abs_conv_abscissa (fds_exp f) \<le> abs_conv_abscissa f"
  by (intro abs_conv_abscissa_mono fds_abs_converges_exp)

lemma fds_deriv_exp [simp]:
  fixes f :: "'a :: dirichlet_series fds"
  shows   "fds_deriv (fds_exp f) = fds_exp f * fds_deriv f"
proof (rule fds_eqI_truncate)
  fix m :: nat assume m: "m > 0"
  let ?T = "fds_truncate m"
  have "abs_conv_abscissa (fds_deriv (?T f)) = -\<infinity>"
    by (simp add: abs_conv_abscissa_deriv)

  have "?T (fds_deriv (fds_exp f)) = ?T (fds_deriv (fds_exp (?T f)))"
    by (simp add: fds_truncate_deriv fds_truncate_exp)
  also have "fds_deriv (fds_exp (?T f)) = fds_exp (?T f) * fds_deriv (?T f)"
  proof (rule eval_fds_eqD)
    note abscissa = conv_le_abs_conv_abscissa abs_conv_abscissa_exp
    note abscissa' = abscissa[THEN le_less_trans]
    have "fds_abs_converges (fds_deriv (fds_exp (fds_truncate m f))) 0"
      by (intro fds_abs_converges )
         (auto simp: abs_conv_abscissa_deriv intro: le_less_trans[OF abs_conv_abscissa_exp])
    thus "conv_abscissa (fds_deriv (fds_exp (fds_truncate m f))) < \<infinity>"
      using conv_abscissa_PInf_iff by blast
    have "fds_abs_converges (fds_exp (fds_truncate m f) * fds_deriv (fds_truncate m f)) 0"
      by (intro fds_abs_converges_mult fds_abs_converges_exp)
         (auto intro: fds_abs_converges simp add: fds_truncate_deriv [symmetric])
    thus "conv_abscissa (fds_exp (fds_truncate m f) * fds_deriv (fds_truncate m f)) < \<infinity>"
      using conv_abscissa_PInf_iff by blast
    show "\<exists>\<^sub>F s in (\<lambda>s. s \<bullet> 1) going_to at_top.
            eval_fds (fds_deriv (fds_exp (?T f))) s =
            eval_fds (fds_exp (?T f) * fds_deriv (?T f)) s"
    proof (intro always_eventually eventually_frequently allI, goal_cases)
      case (2 s)
      have "eval_fds (fds_deriv (fds_exp (?T f))) s =
              deriv (eval_fds (fds_exp (?T f))) s"
        by (auto simp: eval_fds_exp eval_fds_mult fds_abs_converges_mult fds_abs_converges_exp
                  fds_abs_converges eval_fds_deriv abscissa')
      also have "eval_fds (fds_exp (?T f)) = (\<lambda>s. exp (eval_fds (?T f) s))"
        by (intro ext eval_fds_exp) auto
      also have "deriv \<dots>  = (\<lambda>s. exp (eval_fds (?T f) s) * deriv (eval_fds (?T f)) s)"
        by (auto intro!: DERIV_imp_deriv derivative_eq_intros simp: eval_fds_deriv)
      also have "\<dots> = eval_fds (fds_exp (?T f) * fds_deriv (?T f))"
        by (auto simp: eval_fds_exp eval_fds_mult fds_abs_converges_mult fds_abs_converges_exp
                       fds_abs_converges eval_fds_deriv abs_conv_abscissa_deriv)
      finally show ?case .
    qed auto
  qed
  also have "?T \<dots> = ?T (fds_exp f * fds_deriv f)"
    by (subst fds_truncate_mult [symmetric])
       (simp add: fds_truncate_exp fds_truncate_deriv [symmetric], simp add: fds_truncate_mult)
  finally show "?T (fds_deriv (fds_exp f)) = \<dots>" .
qed

lemma fds_exp_ln_strong:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "fds_nth f (Suc 0) \<noteq> 0"
  shows   "fds_exp (fds_ln l f) = fds_const (exp l / fds_nth f (Suc 0)) * f"
proof -
  let ?c = "exp l / fds_nth f (Suc 0)"
  have "f * fds_const ?c = f * (fds_exp (-fds_ln l f) * fds_exp (fds_ln l f)) * fds_const ?c" 
    (is "_ = _ * (?g * ?h) * _") by (subst fds_exp_add [symmetric]) simp
  also have "\<dots> = fds_const ?c * (f * ?g) * ?h" by (simp add: mult_ac)
  also have "f * ?g = fds_const (inverse ?c)"
  proof (rule fds_deriv_eq_imp_eq)
    have "fds_deriv (f * fds_exp (-fds_ln l f)) = 
            fds_exp (- fds_ln l f) * fds_deriv f * (1 - f / f)"
      by (simp add: divide_fds_def algebra_simps)
    also from assms have "f / f = 1" by (simp add: divide_fds_def fds_right_inverse)
    finally show "fds_deriv (f * fds_exp (-fds_ln l f)) = fds_deriv (fds_const (inverse ?c))" 
      by simp
  qed (insert assms, auto simp: exp_minus field_simps)
  also have "fds_const ?c * fds_const (inverse ?c) = 1"
    using assms by (subst fds_const_mult [symmetric]) (simp add: divide_simps)
  finally show ?thesis by (simp add: mult_ac)
qed

lemma fds_exp_ln [simp]:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "exp l = fds_nth f (Suc 0)"
  shows   "fds_exp (fds_ln l f) = f"
  using assms by (subst fds_exp_ln_strong) auto

lemma fds_ln_exp [simp]:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "l = fds_nth f (Suc 0)"
  shows   "fds_ln l (fds_exp f) = f"
proof (rule fds_deriv_eq_imp_eq)
  have "fds_deriv (fds_ln l (fds_exp f)) = fds_deriv f * (fds_exp f / fds_exp f)"
    by (simp add: algebra_simps divide_fds_def)
  also have "fds_exp f / fds_exp f = 1" by (simp add: divide_fds_def fds_right_inverse)
  finally show "fds_deriv (fds_ln l (fds_exp f)) = fds_deriv f" by simp
qed (insert assms, auto simp: field_simps)


subsection \<open>Euler products\<close>

lemma fds_euler_product_LIMSEQ:
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then \<Sum>i. fds_nth f (p ^ i) / nat_power (p ^ i) s else 1) \<longlonglongrightarrow> 
             eval_fds f s"
  unfolding eval_fds_def
proof (rule euler_product_LIMSEQ)
  show "multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_euler_product_LIMSEQ':
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1) \<longlonglongrightarrow> 
             eval_fds f s"
  unfolding eval_fds_def
proof (rule euler_product_LIMSEQ')
  show "completely_multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule completely_multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_euler_product:
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "abs_convergent_prod 
             (\<lambda>p. if prime p then \<Sum>i. fds_nth f (p ^ i) / nat_power (p ^ i) s else 1)"
  unfolding eval_fds_def
proof (rule abs_convergent_euler_product)
  show "multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_euler_product':
  fixes f :: "'a :: {nat_power, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)" and "fds_abs_converges f s"
  shows   "abs_convergent_prod 
             (\<lambda>p. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1)"
  unfolding eval_fds_def
proof (rule abs_convergent_euler_product')
  show "completely_multiplicative_function (\<lambda>n. fds_nth f n / nat_power n s)"
    by (rule completely_multiplicative_function_divide_nat_power) fact+
qed (insert assms, auto simp: fds_abs_converges_def)

lemma fds_abs_convergent_zero_iff:
  fixes f :: "'a :: {nat_power_field, real_normed_field, banach, second_countable_topology} fds"
  assumes "completely_multiplicative_function (fds_nth f)"
  assumes "fds_abs_converges f s"
  shows   "eval_fds f s = 0 \<longleftrightarrow> (\<exists>p. prime p \<and> fds_nth f p = nat_power p s)"
proof -
  let ?g = "\<lambda>p. if prime p then inverse (1 - fds_nth f p / nat_power p s) else 1" 
  have lim: "(\<lambda>n. \<Prod>p\<le>n. ?g p) \<longlonglongrightarrow> eval_fds f s"
    by (intro fds_euler_product_LIMSEQ' assms)
  have conv: "convergent_prod ?g"
    by (intro abs_convergent_prod_imp_convergent_prod fds_abs_convergent_euler_product' assms)

  {
    assume "eval_fds f s = 0"
    from convergent_prod_to_zero_iff[OF conv] and this and lim
      have "\<exists>p. prime p \<and> fds_nth f p = nat_power p s" 
      by (auto split: if_splits)
  } moreover {
    assume "\<exists>p. prime p \<and> fds_nth f p = nat_power p s"
    then obtain p where "prime p" "fds_nth f p = nat_power p s" by blast
    moreover from this have "nat_power p s \<noteq> 0" 
      by (intro nat_power_nonzero) (auto simp: prime_gt_0_nat)
    ultimately have "(\<lambda>n. \<Prod>p\<le>n. ?g p) \<longlonglongrightarrow> 0"
      using convergent_prod_to_zero_iff[OF conv]
      by (auto intro!: exI[of _ p] split: if_splits)
    from tendsto_unique[OF _ lim this] have "eval_fds f s = 0"
      by simp
  }
  ultimately show ?thesis by blast
qed

lemma 
  fixes s :: "'a :: {nat_power_normed_field,banach,euclidean_space}"
  assumes "s \<bullet> 1 > 1"
  shows   euler_product_fds_zeta: 
            "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / nat_power p s) else 1)
                \<longlonglongrightarrow> eval_fds fds_zeta s" (is ?th1)
  and     eval_fds_zeta_nonzero: "eval_fds fds_zeta s \<noteq> 0"
proof -
  have *: "completely_multiplicative_function (fds_nth fds_zeta)"
    by standard auto
  have lim: "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - fds_nth fds_zeta p / nat_power p s) else 1) 
          \<longlonglongrightarrow> eval_fds fds_zeta s" (is "filterlim ?g _ _")
    using assms by (intro fds_euler_product_LIMSEQ' * fds_abs_summable_zeta)
  also have "?g = (\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - 1 / nat_power p s) else 1)"
    by (intro ext prod.cong refl) (auto simp: fds_zeta_def fds_nth_fds)
  finally show ?th1 .

  {
    fix p :: nat assume "prime p"
    from this have "p > 1" by (simp add: prime_gt_Suc_0_nat)
    hence "norm (nat_power p s) = real p powr (s \<bullet> 1)" 
      by (simp add: norm_nat_power)
    also have "\<dots> > real p powr 0" using assms and \<open>p > 1\<close> 
      by (intro powr_less_mono) auto
    finally have "nat_power p s \<noteq> 1"
      using \<open>p > 1\<close> by auto
  }
  hence **: "\<nexists>p. prime p \<and> fds_nth fds_zeta p = nat_power p s"
    by (auto simp: fds_zeta_def fds_nth_fds)
  show "eval_fds fds_zeta s \<noteq> 0"
    using assms * ** by (subst fds_abs_convergent_zero_iff) simp_all
qed

lemma fds_primepow_subseries_euler_product_cm:
  fixes f :: "'a :: dirichlet_series fds"
  assumes "completely_multiplicative_function (fds_nth f)" "prime p"
  assumes "s \<bullet> 1 > abs_conv_abscissa f"
  shows   "eval_fds (fds_primepow_subseries p f) s = 1 / (1 - fds_nth f p / nat_power p s)"
proof -
  let ?f = "(\<lambda>n. \<Prod>pa\<le>n. if prime pa then inverse (1 - fds_nth (fds_primepow_subseries p f) pa /
                 nat_power pa s) else 1)"
  have "sequentially \<noteq> bot" by simp
  moreover have "?f \<longlonglongrightarrow> eval_fds (fds_primepow_subseries p f) s" 
    by (intro fds_euler_product_LIMSEQ' completely_multiplicative_function_only_pows assms
          fds_abs_converges_subseries) (insert assms, auto intro!: fds_abs_converges)
  moreover have "eventually (\<lambda>n. ?f n = 1 / (1 - fds_nth f p / nat_power p s)) at_top"
    using eventually_ge_at_top[of p]
  proof eventually_elim
    case (elim n)
    have "(\<Prod>pa\<le>n. if prime pa then inverse (1 - fds_nth (fds_primepow_subseries p f) pa /
              nat_power pa s) else 1) = 
          (\<Prod>q\<le>n. if q = p then inverse (1 - fds_nth f p / nat_power p s) else 1)" using \<open>prime p\<close>
      by (intro prod.cong) (auto simp: fds_nth_subseries prime_prime_factors)
    also have "\<dots> = 1 / (1 - fds_nth f p / nat_power p s)"
      using elim by (subst prod.delta) (auto simp: divide_simps)
    finally show ?case .
  qed
  hence "?f \<longlonglongrightarrow> 1 / (1 - fds_nth f p / nat_power p s)" by (rule Lim_eventually)
  ultimately show ?thesis by (rule tendsto_unique)
qed


subsection \<open>Non-negative Dirichlet series\<close>

lemma nonneg_Reals_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<real>\<^sub>\<ge>\<^sub>0) \<Longrightarrow> sum f A \<in> \<real>\<^sub>\<ge>\<^sub>0"
  by (induction A rule: infinite_finite_induct) auto

locale nonneg_dirichlet_series =
  fixes f :: "'a :: dirichlet_series fds"
  assumes nonneg_coeffs_aux: "n > 0 \<Longrightarrow> fds_nth f n \<in> \<real>\<^sub>\<ge>\<^sub>0"
begin

lemma nonneg_coeffs: "fds_nth f n \<in> \<real>\<^sub>\<ge>\<^sub>0"
  using nonneg_coeffs_aux[of n] by (cases "n = 0") auto

end

lemma nonneg_dirichlet_series_0 [simp,intro]: "nonneg_dirichlet_series 0"
  by standard (auto simp: zero_fds_def)

lemma nonneg_dirichlet_series_1 [simp,intro]: "nonneg_dirichlet_series 1"
  by standard (auto simp: one_fds_def)

lemma nonneg_dirichlet_series_const [simp,intro]: 
  "c \<in> \<real>\<^sub>\<ge>\<^sub>0 \<Longrightarrow> nonneg_dirichlet_series (fds_const c)"
  by standard (auto simp: fds_const_def)

lemma nonneg_dirichlet_series_add [intro]:
  assumes "nonneg_dirichlet_series f" "nonneg_dirichlet_series g"
  shows   "nonneg_dirichlet_series (f + g)"
proof -
  interpret f: nonneg_dirichlet_series f by fact
  interpret g: nonneg_dirichlet_series g by fact
  show ?thesis
    by standard (auto intro!: nonneg_Reals_add_I f.nonneg_coeffs g.nonneg_coeffs)
qed

lemma nonneg_dirichlet_series_mult [intro]:
  assumes "nonneg_dirichlet_series f" "nonneg_dirichlet_series g"
  shows   "nonneg_dirichlet_series (f * g)"
proof -
  interpret f: nonneg_dirichlet_series f by fact
  interpret g: nonneg_dirichlet_series g by fact
  show ?thesis
    by standard (auto intro!: nonneg_Reals_sum nonneg_Reals_mult_I f.nonneg_coeffs g.nonneg_coeffs 
                      simp: fds_nth_mult dirichlet_prod_def)
qed

lemma nonneg_dirichlet_series_power [intro]:
  assumes "nonneg_dirichlet_series f"
  shows   "nonneg_dirichlet_series (f ^ n)"
  using assms by (induction n) auto

context nonneg_dirichlet_series
begin

lemma nonneg_exp [intro]: "nonneg_dirichlet_series (fds_exp f)"
proof
  fix n :: nat assume "n > 0"
  define c where "c = exp (fds_nth f (Suc 0))"
  define f' where "f' = fds (\<lambda>n. if n = Suc 0 then 0 else fds_nth f n)"
  from nonneg_coeffs[of 1] obtain c' where "fds_nth f (Suc 0) = of_real c'"
    by (auto elim!: nonneg_Reals_cases)
  hence "c = of_real (exp c')" by (simp add: c_def exp_of_real)
  hence c: "c \<in> \<real>\<^sub>\<ge>\<^sub>0" by simp
  have less: "n < 2 ^ k" if "n < k" for k
  proof -
    have "n < k" by fact
    also have "\<dots> < 2 ^ k" by (induction k) auto
    finally show ?thesis .
  qed
  have nonneg_power: "fds_nth (f' ^ k) n \<in> \<real>\<^sub>\<ge>\<^sub>0" for k
  proof -
    have "nonneg_dirichlet_series f'"
      by standard (insert nonneg_coeffs, auto simp: f'_def)
    interpret nonneg_dirichlet_series "f' ^ k"
      by (intro nonneg_dirichlet_series_power) fact+
    from nonneg_coeffs[of n] show ?thesis .
  qed
  hence "fds_nth (fds_exp f) n = c * (\<Sum>k. fds_nth (f' ^ k) n /\<^sub>R fact k)"
    by (simp add: fds_exp_def fds_nth_fds' f'_def c_def)
  also have "(\<Sum>k. fds_nth (f' ^ k) n /\<^sub>R fact k) = (\<Sum>k\<le>n. fds_nth (f' ^ k) n /\<^sub>R fact k)"
    by (intro suminf_finite) (auto intro!: fds_nth_power_eq_0 less simp: f'_def not_le)
  also have "c * \<dots> \<in> \<real>\<^sub>\<ge>\<^sub>0" unfolding scaleR_conv_of_real
    by (intro nonneg_Reals_mult_I nonneg_Reals_sum nonneg_power, unfold nonneg_Reals_of_real_iff )
       (auto simp: c)
  finally show "fds_nth (fds_exp f) n \<in> \<real>\<^sub>\<ge>\<^sub>0" .
qed

end

lemma nonneg_dirichlet_series_lnD: 
  assumes "nonneg_dirichlet_series (fds_ln l f)" "exp l = fds_nth f (Suc 0)"
  shows   "nonneg_dirichlet_series f"
proof -
  from assms have "nonneg_dirichlet_series (fds_exp (fds_ln l f))"
    by (intro nonneg_dirichlet_series.nonneg_exp)
  thus ?thesis using assms by simp
qed

context nonneg_dirichlet_series
begin

lemma fds_of_real_norm: "fds_of_real (fds_norm f) = f"
proof (rule fds_eqI)
  fix n :: nat assume n: "n > 0"
  show "fds_nth (fds_of_real (fds_norm f)) n = fds_nth f n"
    using nonneg_coeffs[of n] by (auto elim!: nonneg_Reals_cases)
qed

end

(* TODO: Simplify proof *)
lemma pringsheim_landau_aux:
  fixes c :: real and f :: "complex fds"
  assumes "nonneg_dirichlet_series f"
  assumes abscissa: "c \<ge> abs_conv_abscissa f"
  assumes g: "\<And>s. s \<in> A \<Longrightarrow> Re s > c \<Longrightarrow> g s = eval_fds f s"
  assumes "g holomorphic_on A" "open A" "c \<in> A"
  shows   "\<exists>x. x < c \<and> fds_abs_converges f (of_real x)"
proof -
  interpret nonneg_dirichlet_series f by fact
  define a where "a = 1 + c"

  define g' where "g' = (\<lambda>s. if s \<in> {s. Re s > c} then eval_fds f s else g s)"

  \<comment> \<open>We can find some $\varepsilon > 0$ such that the Dirichlet series can be continued
      analytically in a ball of radius $1 + \varepsilon$ around $a$.\<close>
  from \<open>open A\<close> \<open>c \<in> A\<close> obtain \<delta> where \<delta>: "\<delta> > 0" "ball c \<delta> \<subseteq> A"
    by (auto simp: open_contains_ball)
  define \<epsilon> where "\<epsilon> = sqrt (1 + \<delta>^2) - 1"
  from \<delta> have \<epsilon>: "\<epsilon> > 0" by (simp add: \<epsilon>_def)

  have ball_a_subset: "ball a (1 + \<epsilon>) \<subseteq> {s. Re s > c} \<union> A"
  proof (intro subsetI)
    fix s :: complex assume s: "s \<in> ball a (1 + \<epsilon>)"
    define x y where "x = Re s" and "y = Im s"
    have [simp]: "s = x + \<i> * y" by (simp add: complex_eq_iff x_def y_def)
    show "s \<in> {s. Re s > c} \<union> A"
    proof (cases "Re s \<le> c")
      case True
      hence "(c - x)\<^sup>2 + y\<^sup>2 \<le> (1 + c - x)\<^sup>2 + y\<^sup>2 - 1"
        by (simp add: power2_eq_square algebra_simps)
      also from s have "(1 + c - x)\<^sup>2 + y\<^sup>2 - 1 < \<delta>\<^sup>2"
        by (auto simp: dist_norm cmod_def a_def \<epsilon>_def)
      finally have "sqrt ((c - x)\<^sup>2 + y\<^sup>2) < \<delta>" using \<delta>
        by (intro real_less_lsqrt) auto
      hence "s \<in> ball c \<delta>" by (auto simp: dist_norm cmod_def)
      also have "\<dots> \<subseteq> A" by fact
      finally show ?thesis ..
    qed auto
  qed

  have holo: "g' holomorphic_on ball a (1 + \<epsilon>)" unfolding g'_def
  proof (intro holomorphic_on_subset[OF _ ball_a_subset] holomorphic_on_If_Un)
    have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
    also have "\<dots> \<le> ereal c" by fact
    finally have*:  "conv_abscissa f \<le> ereal c" .
    show "eval_fds f holomorphic_on {s. c < Re s}"
      by (intro holomorphic_intros) (auto intro: le_less_trans[OF *])
  qed (insert assms, auto intro!: holomorphic_intros open_halfspace_Re_gt)

  define f' where "f' = fds_norm f"
  have f_f': "f = fds_of_real f'" by (simp add: f'_def fds_of_real_norm)
  have f'_nonneg: "fds_nth f' n \<ge> 0" for n
    using nonneg_coeffs[of n] by (auto elim!: nonneg_Reals_cases simp: f'_def)

  have deriv: "(\<lambda>n. (deriv ^^ n) g' a) = (\<lambda>n. eval_fds ((fds_deriv ^^ n) f) a)"
  proof
    fix n :: nat
    have ev: "eventually (\<lambda>s. s \<in> {s. Re s > c}) (nhds (complex_of_real a))"
      by (intro eventually_nhds_in_open open_halfspace_Re_gt) (auto simp: a_def)
    have "(deriv ^^ n) g' a = (deriv ^^ n) (eval_fds f) a"
      by (intro higher_deriv_cong_ev refl eventually_mono[OF ev]) (auto simp: g'_def)
    also have "\<dots> = eval_fds ((fds_deriv ^^ n) f) a"
    proof (intro eval_fds_higher_deriv [symmetric])
      have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
      also have "\<dots> \<le> ereal c" by (rule assms)
      also have "\<dots> < a" by (simp add: a_def)
      finally show "conv_abscissa f < ereal (complex_of_real a \<bullet> 1)" by simp
    qed
    finally show "(deriv ^^ n) g' a = eval_fds ((fds_deriv ^^ n) f) a" .
  qed

  have nth_deriv_conv: "fds_abs_converges ((fds_deriv ^^ n) f) (of_real a)" for n
    by (intro fds_abs_converges)
       (auto simp: abs_conv_abscissa_higher_deriv a_def intro!: le_less_trans[OF abscissa])

  have nth_deriv_eq: "(fds_deriv ^^ n) f = fds (\<lambda>k. (-1) ^ n * fds_nth f k * ln (real k) ^ n)" for n
  proof -
    have "fds_nth ((fds_deriv ^^ n) f) k = (-1) ^ n * fds_nth f k * ln (real k) ^ n" for k
      by (induction n) (simp_all add: fds_deriv_def fds_eq_iff fds_nth_fds' scaleR_conv_of_real)
    thus ?thesis by (intro fds_eqI) simp_all
  qed

  have deriv': "(\<lambda>n. eval_fds ((fds_deriv ^^ n) f) (complex_of_real a)) =
      (\<lambda>n. (- 1) ^ n * complex_of_real (\<Sum>\<^sub>ak. fds_nth f' k * ln (real k) ^ n / real k powr a))"
  proof
    fix n
    have "eval_fds ((fds_deriv ^^ n) f) (of_real a) = 
                 (\<Sum>\<^sub>ak. fds_nth ((fds_deriv ^^ n) f) k / of_nat k powr complex_of_real a)"
      using nth_deriv_conv by (subst eval_fds_altdef) auto
    hence "eval_fds ((fds_deriv ^^ n) f) (of_real a) = 
                 (\<Sum>\<^sub>ak. (- 1) ^ n *\<^sub>R (fds_nth f k * ln (real k) ^ n / k powr a))"
      by (simp add: nth_deriv_eq fds_nth_fds' powr_Reals_eq scaleR_conv_of_real algebra_simps)
    also have "\<dots> = (- 1) ^ n * (\<Sum>\<^sub>ak. of_real (fds_nth f' k * ln (real k) ^ n / k powr a))"
      by (subst infsetsum_scaleR_right) (simp_all add: scaleR_conv_of_real f_f')
    also have "\<dots> = (- 1) ^ n * of_real (\<Sum>\<^sub>ak. fds_nth f' k * ln (real k) ^ n / k powr a)"
      by (subst infsetsum_of_real) (rule refl)
    finally show "eval_fds ((fds_deriv ^^ n) f) (complex_of_real a) =
      (- 1) ^ n * complex_of_real (\<Sum>\<^sub>ak. fds_nth f' k * ln (real k) ^ n / real k powr a)" .
  qed

  define s :: complex where "s = c - \<epsilon> / 2"
  have s: "Re s < c" using assms \<delta> by (simp_all add: s_def \<epsilon>_def field_simps)
  have "s \<in> ball a (1 + \<epsilon>)" using s by (simp add: a_def dist_norm cmod_def s_def)
  from holomorphic_power_series[OF holo this]
    have sums: "(\<lambda>n. (deriv ^^ n) g' a / fact n * (s - a) ^ n) sums g' s" by simp
  also note deriv
  also have "s - a = -of_real (1 + \<epsilon> / 2)" by (simp add: s_def a_def)
  also have "(\<lambda>n. \<dots> ^ n) = (\<lambda>n. of_real ((-1) ^ n * (1 + \<epsilon> / 2) ^ n))"
    by (intro ext) (subst power_minus, auto)
  also have "(\<lambda>n. eval_fds ((fds_deriv ^^ n) f) a / fact n * \<dots> n) =
               (\<lambda>n. of_real ((-1) ^ n * eval_fds ((fds_deriv ^^ n) f') a / fact n * (1+\<epsilon>/2) ^ n))"
    using nth_deriv_conv by (simp add: f_f' fds_abs_converges_imp_converges mult_ac)
  finally have "summable \<dots>" by (simp add: sums_iff)
  hence summable: "summable (\<lambda>n. (-1)^n * eval_fds ((fds_deriv ^^ n) f') a / fact n * (1+\<epsilon>/2)^n)"
    by (subst (asm) summable_of_real_iff)

  have "(\<lambda>(n,k). (-1)^n * fds_nth f k * ln (real k) ^ n / (real k powr a) * ((s-a) ^ n / fact n))
          abs_summable_on (UNIV \<times> UNIV)"
  proof (subst abs_summable_on_Sigma_iff, safe, goal_cases)
    case (3 n)
    from nth_deriv_conv[of n] show ?case
      unfolding fds_abs_converges_altdef'
      by (intro abs_summable_on_cmult_left) (simp add: nth_deriv_eq fds_nth_fds' powr_Reals_eq)
  next
    case 4
    have nth_deriv_f_f': "(fds_deriv ^^ n) f = fds_of_real ((fds_deriv ^^ n) f')" for n
      by (induction n) (auto simp: f'_def fds_of_real_norm)
    have norm_nth_deriv_f: "norm (fds_nth ((fds_deriv ^^ n) f) k) = 
                                 (-1) ^ n * of_real (fds_nth ((fds_deriv ^^ n) f') k)" for n k
    proof (induction n)
      case (Suc n)
      thus ?case by (cases k) (auto simp: f_f' fds_nth_deriv scaleR_conv_of_real norm_mult)
    qed (auto simp: f'_nonneg f_f')

    note summable
    also have "(\<lambda>n. (-1)^n * eval_fds ((fds_deriv ^^ n) f') a / fact n * (1+\<epsilon>/2)^n) =
               (\<lambda>n. \<Sum>\<^sub>ak. norm ((- 1) ^ n * fds_nth f k * ln (real k) ^ n /
                    (real k powr a) * ((s - a) ^ n / fact n)))" (is "_ = ?h")
    proof (rule ext, goal_cases)
      case (1 n)
      have "(\<Sum>\<^sub>ak. norm ((- 1) ^ n * fds_nth f k * ln (real k) ^ n /
                    (real k powr a) * ((s - a) ^ n / fact n))) =
            (norm ((s - a) ^ n / fact n) * (-1) ^ n) *\<^sub>R 
              (\<Sum>\<^sub>ak. (-1) ^ n * norm (fds_nth ((fds_deriv ^^ n) f) k / real k powr a))" (is "_ = _ *\<^sub>R ?S")
        by (subst infsetsum_scaleR_right [symmetric])
           (auto simp: norm_mult norm_divide norm_power mult_ac nth_deriv_eq fds_nth_fds')
      also have "?S = (\<Sum>\<^sub>ak. fds_nth ((fds_deriv ^^ n) f') k / real k powr a)"
        by (intro infsetsum_cong) (auto simp: norm_mult norm_divide norm_power norm_nth_deriv_f)
      also have "\<dots> = eval_fds ((fds_deriv ^^ n) f') a"
        using nth_deriv_conv[of n] by (subst eval_fds_altdef) (auto simp: f'_def nth_deriv_f_f')
      also have "(norm ((s - a) ^ n / fact n) * (- 1) ^ n) *\<^sub>R eval_fds ((fds_deriv ^^ n) f') a =
                  (-1) ^ n * eval_fds ((fds_deriv ^^ n) f') a / fact n * norm (s - a) ^ n"
        by (simp add: norm_divide norm_power)
      also have s_a: "s - a = -of_real (1 + \<epsilon> / 2)" by (simp add: s_def a_def)
      have "norm (s - a) = 1 + \<epsilon> / 2" unfolding s_a norm_minus_cancel norm_of_real using \<epsilon> by simp
      finally show ?case ..
    qed
    also have "?h n \<ge> 0" for n by (intro infsetsum_nonneg) auto
    hence "?h = (\<lambda>n. norm (?h n))" by simp
    finally show ?case unfolding abs_summable_on_nat_iff' .
  qed auto
  hence "(\<lambda>(k,n). (-1)^n * fds_nth f k * ln (real k) ^ n / (real k powr a) * ((s-a) ^ n / fact n))
          abs_summable_on (UNIV \<times> UNIV)"
    by (subst (asm) abs_summable_on_Times_swap) (simp add: case_prod_unfold)
  hence "(\<lambda>k. \<Sum>\<^sub>an. (- 1) ^ n * fds_nth f k * ln (real k) ^ n / (k powr a) *
           ((s - a) ^ n / fact n)) abs_summable_on UNIV" (is "?h abs_summable_on _")
    by (rule abs_summable_on_Sigma_project1') auto
  also have "?this \<longleftrightarrow> (\<lambda>k. fds_nth f k / nat_power k s) abs_summable_on UNIV"
  proof (intro abs_summable_on_cong refl, goal_cases)
    case (1 k)
    have "?h k = (fds_nth f' k / k powr a) *\<^sub>R (\<Sum>\<^sub>an. (-ln (real k) * (s - a)) ^ n / fact n)"
      by (subst infsetsum_scaleR_right [symmetric], rule infsetsum_cong) 
         (simp_all add: scaleR_conv_of_real f_f' power_minus' power_mult_distrib divide_simps)
    also have "(\<Sum>\<^sub>an. (-ln (real k) * (s - a)) ^ n / fact n) = exp (-ln (real k) * (s - a))"
      using exp_converges[of "-ln k * (s - a)"] exp_converges[of "norm (-ln k * (s - a))"]
      by (subst infsetsum_nat') (auto simp: abs_summable_on_nat_iff' sums_iff scaleR_conv_of_real
                                            divide_simps norm_divide norm_mult norm_power)
    also have "(fds_nth f' k / k powr a) *\<^sub>R \<dots> = fds_nth f k / nat_power k s"
      by (auto simp: scaleR_conv_of_real f_f' powr_def exp_minus
                     field_simps exp_of_real [symmetric] exp_diff)
    finally show ?case .
  qed
  finally have "fds_abs_converges f s"
    by (simp add: fds_abs_converges_def abs_summable_on_nat_iff')
  thus ?thesis by (intro exI[of _ "(c - \<epsilon> / 2)"]) (auto simp: s_def a_def \<epsilon>)
qed

theorem pringsheim_landau:
  fixes c :: real and f :: "complex fds"
  assumes "nonneg_dirichlet_series f"
  assumes abscissa: "abs_conv_abscissa f = c"
  assumes g: "\<And>s. s \<in> A \<Longrightarrow> Re s > c \<Longrightarrow> g s = eval_fds f s"
  assumes "g holomorphic_on A" "open A" "c \<in> A"
  shows   False
proof -
  have "\<exists>x<c. fds_abs_converges f (complex_of_real x)"
    by (rule pringsheim_landau_aux[where g = g and A = A]) (insert assms, auto)
  then obtain x where x: "x < c" "fds_abs_converges f (complex_of_real x)" by blast
  hence "abs_conv_abscissa f \<le> complex_of_real x \<bullet> 1" 
    unfolding abs_conv_abscissa_def 
    by (intro Inf_lower) (auto simp: image_iff intro!: exI[of _ "of_real x"])
  also have "\<dots> < abs_conv_abscissa f" using assms x by simp
  finally show False by simp
qed    

corollary entire_continuation_imp_abs_conv_abscissa_MInfty:
  assumes "nonneg_dirichlet_series f"
  assumes c: "c \<ge> abs_conv_abscissa f"
  assumes g: "\<And>s. Re s > c \<Longrightarrow> g s = eval_fds f s"
  assumes holo: "g holomorphic_on UNIV"
  shows   "abs_conv_abscissa f = -\<infinity>"
proof (rule ccontr)
  assume "abs_conv_abscissa f \<noteq> -\<infinity>"
  with c obtain a where abscissa [simp]: "abs_conv_abscissa f = ereal a"
    by (cases "abs_conv_abscissa f") auto
  show False
  proof (rule pringsheim_landau[OF assms(1) abscissa _ holo])
    fix s assume s: "Re s > a"
    show "g s = eval_fds f s"
    proof (rule sym, rule analytic_continuation_open[of _ _ _ g])
      show "g holomorphic_on {s. Re s > a}" by (rule holomorphic_on_subset[OF holo]) auto
      from assms show "{s. Re s > c} \<subseteq> {s. Re s > a}" by auto
    next
      have "conv_abscissa f \<le> abs_conv_abscissa f" by (rule conv_le_abs_conv_abscissa)
      also have "\<dots> = ereal a" by simp
      finally show "eval_fds f holomorphic_on {s. Re s > a}"
        by (intro holomorphic_intros) (auto intro: le_less_trans)
    qed (insert assms s, auto intro!: exI[of _ "of_real (c + 1)"] 
           open_halfspace_Re_gt convex_connected convex_halfspace_Re_gt)
  qed auto
qed



subsection \<open>Convergence of the $\zeta$ and M\"{o}bius $\mu$ series\<close>

lemma fds_abs_summable_zeta_real_iff [simp]:
  "fds_abs_converges fds_zeta s \<longleftrightarrow> s > (1 :: real)"
proof -
  have "fds_abs_converges fds_zeta s \<longleftrightarrow> summable (\<lambda>n. real n powr -s)"
    unfolding fds_abs_converges_def
    by (intro summable_cong always_eventually)
       (auto simp: fds_nth_zeta powr_minus divide_simps)
  also have "\<dots> \<longleftrightarrow> s > 1" by (simp add: summable_real_powr_iff)
  finally show ?thesis .
qed

lemma fds_abs_summable_zeta_real: "s > (1 :: real) \<Longrightarrow> fds_abs_converges fds_zeta s"
  by simp

lemma fds_abs_converges_moebius_mu_real: 
  assumes "s > (1 :: real)"
  shows   "fds_abs_converges (fds moebius_mu) s"
  unfolding fds_abs_converges_def
proof (rule summable_comparison_test, intro exI allI impI)
  fix n :: nat
  show "norm (norm (fds_nth (fds moebius_mu) n / nat_power n s)) \<le> n powr (-s)"
    by (simp add: powr_minus divide_simps abs_moebius_mu_le)
next
  from assms show "summable (\<lambda>n. real n powr -s)" by (simp add: summable_real_powr_iff)
qed


subsection \<open>Application to the M\"{o}bius $\mu$ function\<close>

lemma inverse_squares_sums': "(\<lambda>n. 1 / real n ^ 2) sums (pi ^ 2 / 6)"
  using inverse_squares_sums sums_Suc_iff[of "\<lambda>n. 1 / real n ^ 2" "pi^2 / 6"] by simp

lemma norm_summable_moebius_over_square: 
  "summable (\<lambda>n. norm (moebius_mu n / real n ^ 2))"
proof (subst summable_Suc_iff [symmetric], rule summable_comparison_test)
  show "summable (\<lambda>n. 1 / real (Suc n) ^ 2)"
    using inverse_squares_sums by (simp add: sums_iff)
qed (auto simp del: of_nat_Suc simp: field_simps abs_moebius_mu_le)

lemma summable_moebius_over_square:
  "summable (\<lambda>n. moebius_mu n / real n ^ 2)"
  using norm_summable_moebius_over_square by (rule summable_norm_cancel)

lemma moebius_over_square_sums: "(\<lambda>n. moebius_mu n / n\<^sup>2) sums (6 / pi\<^sup>2)"
proof -
  have "1 = eval_fds (1 :: real fds) 2" by simp
  also have "(1 :: real fds) = fds_zeta * fds moebius_mu" 
    by (rule fds_zeta_times_moebius_mu [symmetric])
  also have "eval_fds \<dots> 2 = eval_fds fds_zeta 2 * eval_fds (fds moebius_mu) 2"
    by (intro eval_fds_mult fds_abs_converges_moebius_mu_real) simp_all
  also have "\<dots> = pi ^ 2 / 6 * (\<Sum>n. moebius_mu n / (real n)\<^sup>2)"
    using inverse_squares_sums' by (simp add: eval_fds_at_numeral suminf_fds_zeta_aux sums_iff)
  finally have "(\<Sum>n. moebius_mu n / (real n)\<^sup>2) = 6 / pi ^ 2" by (simp add: field_simps)
  with summable_moebius_over_square show ?thesis by (simp add: sums_iff)
qed

end
