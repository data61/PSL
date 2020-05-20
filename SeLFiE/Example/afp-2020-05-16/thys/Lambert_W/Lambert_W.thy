(*
  File:    Lambert_W.thy
  Author:  Manuel Eberl, TU München

  Definition and basic properties of the two real-valued branches of the Lambert W function,
*)
section \<open>The Lambert $W$ Function on the reals\<close>
theory Lambert_W
imports
  Complex_Main
  "HOL-Library.FuncSet"
  "HOL-Real_Asymp.Real_Asymp"
begin

(*<*)
text \<open>Some lemmas about asymptotic equivalence:\<close>

lemma asymp_equiv_sandwich':
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>c'. c' \<in> {l<..<c} \<Longrightarrow> eventually (\<lambda>x. f x \<ge> c' * g x) F"
  assumes "\<And>c'. c' \<in> {c<..<u} \<Longrightarrow> eventually (\<lambda>x. f x \<le> c' * g x) F"
  assumes "l < c" "c < u" and [simp]: "c \<noteq> 0"
  shows   "f \<sim>[F] (\<lambda>x. c * g x)"
proof -
  have "(\<lambda>x. f x - c * g x) \<in> o[F](g)"
  proof (rule landau_o.smallI)
    fix e :: real assume e: "e > 0"
    define C1 where "C1 = min (c + e) ((c + u) / 2)"
    have C1: "C1 \<in> {c<..<u}" "C1 - c \<le> e"
      using e assms by (auto simp: C1_def min_def)
    define C2 where "C2 = max (c - e) ((c + l) / 2)"
    have C2: "C2 \<in> {l<..<c}" "c - C2 \<le> e"
      using e assms by (auto simp: C2_def max_def field_simps)

    show "eventually (\<lambda>x. norm (f x - c * g x) \<le> e * norm (g x)) F"
      using assms(2)[OF C1(1)] assms(1)[OF C2(1)]
    proof eventually_elim
      case (elim x)
      show ?case
      proof (cases "f x \<ge> c * g x")
        case True
        hence "norm (f x - c * g x) = f x - c * g x"
          by simp
        also have "\<dots> \<le> (C1 - c) * g x"
          using elim by (simp add: algebra_simps)
        also have "\<dots> \<le> (C1 - c) * norm (g x)"
          using C1 by (intro mult_left_mono) auto
        also have "\<dots> \<le> e * norm (g x)"
          using C1 elim by (intro mult_right_mono) auto
        finally show ?thesis using elim by simp
      next
        case False
        hence "norm (f x - c * g x) = c * g x - f x"
          by simp
        also have "\<dots> \<le> (c - C2) * g x"
          using elim by (simp add: algebra_simps)
        also have "\<dots> \<le> (c - C2) * norm (g x)"
          using C2 by (intro mult_left_mono) auto
        also have "\<dots> \<le> e * norm (g x)"
          using C2 elim by (intro mult_right_mono) auto
        finally show ?thesis using elim by simp
      qed
    qed
  qed
  also have "g \<in> O[F](\<lambda>x. c * g x)"
    by simp
  finally show ?thesis
    unfolding asymp_equiv_altdef by blast
qed

lemma asymp_equiv_sandwich'':
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>c'. c' \<in> {l<..<1} \<Longrightarrow> eventually (\<lambda>x. f x \<ge> c' * g x) F"
  assumes "\<And>c'. c' \<in> {1<..<u} \<Longrightarrow> eventually (\<lambda>x. f x \<le> c' * g x) F"
  assumes "l < 1" "1 < u"
  shows   "f \<sim>[F] (g)"
  using asymp_equiv_sandwich'[of l 1 g f F u] assms by simp
(*>*)

subsection \<open>Properties of the function $x\mapsto x e^{x}$\<close>

lemma exp_times_self_gt:
  assumes "x \<noteq> -1"
  shows   "x * exp x > -exp (-1::real)"
proof -
  define f where "f = (\<lambda>x::real. x * exp x)"
  define f' where "f' = (\<lambda>x::real. (x + 1) * exp x)"
  have "(f has_field_derivative f' x) (at x)" for x
    by (auto simp: f_def f'_def intro!: derivative_eq_intros simp: algebra_simps)
  define l r where "l = min x (-1)" and "r = max x (-1)"

  have "\<exists>z. z > l \<and> z < r \<and> f r - f l = (r - l) * f' z"
    unfolding f_def f'_def l_def r_def using assms
    by (intro MVT2) (auto intro!: derivative_eq_intros simp: algebra_simps)
  then obtain z where z: "z \<in> {l<..<r}" "f r - f l = (r - l) * f' z"
    by auto
  from z have "f x = f (-1) + (x + 1) * f' z"
    using assms by (cases "x \<ge> -1") (auto simp: l_def r_def max_def min_def algebra_simps)
  moreover have "sgn ((x + 1) * f' z) = 1"
    using z assms
    by (cases x "(-1) :: real" rule: linorder_cases; cases z "(-1) :: real" rule: linorder_cases)
       (auto simp: f'_def sgn_mult l_def r_def)
  hence "(x + 1) * f' z > 0" using sgn_greater by fastforce
  ultimately show ?thesis by (simp add: f_def)
qed

lemma exp_times_self_ge: "x * exp x \<ge> -exp (-1::real)"
  using exp_times_self_gt[of x] by (cases "x = -1") auto

lemma exp_times_self_strict_mono:
  assumes "x \<ge> -1" "x < (y :: real)"
  shows   "x * exp x < y * exp y"
  using assms(2)
proof (rule DERIV_pos_imp_increasing_open)
  fix t assume t: "x < t" "t < y"
  have "((\<lambda>x. x * exp x) has_real_derivative (t + 1) * exp t) (at t)"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  moreover have "(t + 1) * exp t > 0"
    using t assms by (intro mult_pos_pos) auto
  ultimately show "\<exists>y. ((\<lambda>a. a * exp a) has_real_derivative y) (at t) \<and> 0 < y" by blast
qed (auto intro!: continuous_intros)

lemma exp_times_self_strict_antimono:
  assumes "y \<le> -1" "x < (y :: real)"
  shows   "x * exp x > y * exp y"
proof -
  have "-x * exp x < -y * exp y"
    using assms(2)
  proof (rule DERIV_pos_imp_increasing_open)
    fix t assume t: "x < t" "t < y"
    have "((\<lambda>x. -x * exp x) has_real_derivative (-(t + 1)) * exp t) (at t)"
      by (auto intro!: derivative_eq_intros simp: algebra_simps)
    moreover have "(-(t + 1)) * exp t > 0"
      using t assms by (intro mult_pos_pos) auto
    ultimately show "\<exists>y. ((\<lambda>a. -a * exp a) has_real_derivative y) (at t) \<and> 0 < y" by blast
  qed (auto intro!: continuous_intros)
  thus ?thesis by simp
qed

lemma exp_times_self_mono:
  assumes "x \<ge> -1" "x \<le> (y :: real)"
  shows   "x * exp x \<le> y * exp y"
  using exp_times_self_strict_mono[of x y] assms by (cases "x = y") auto

lemma exp_times_self_antimono:
  assumes "y \<le> -1" "x \<le> (y :: real)"
  shows   "x * exp x \<ge> y * exp y"
  using exp_times_self_strict_antimono[of y x] assms by (cases "x = y") auto

lemma exp_times_self_inj: "inj_on (\<lambda>x::real. x * exp x) {-1..}"
proof
  fix x y :: real
  assume "x \<in> {-1..}" "y \<in> {-1..}" "x * exp x = y * exp y"
  thus "x = y"
    using exp_times_self_strict_mono[of x y] exp_times_self_strict_mono[of y x]
    by (cases x y rule: linorder_cases) auto
qed

lemma exp_times_self_inj': "inj_on (\<lambda>x::real. x * exp x) {..-1}"
proof
  fix x y :: real
  assume "x \<in> {..-1}" "y \<in> {..-1}" "x * exp x = y * exp y"
  thus "x = y"
    using exp_times_self_strict_antimono[of x y] exp_times_self_strict_antimono[of y x]
    by (cases x y rule: linorder_cases) auto
qed


subsection \<open>Definition\<close>

text \<open>
  The following are the two branches $W_0(x)$ and $W_{-1}(x)$ of the Lambert $W$ function on the
  real numbers. These are the inverse functions of the function $x\mapsto xe^x$, i.\,e.\ 
  we have $W(x)e^{W(x)} = x$ for both branches wherever they are defined. The two branches
  meet at the point $x = -\frac{1}{e}$.

  $W_0(x)$ is the principal branch, whose domain is $[-\frac{1}{e}; \infty)$ and whose
  range is $[-1; \infty)$.
  $W_{-1}(x)$ has the domain $[-\frac{1}{e}; 0)$ and the range $(-\infty;-1]$.
  Figure~\ref{fig:lambertw} shows plots of these two branches for illustration.
\<close>

text \<open>
\definecolor{myblue}{HTML}{3869b1}
\definecolor{myred}{HTML}{cc2428}
\begin{figure}
\begin{center}
\begin{tikzpicture}
  \begin{axis}[
          xmin=-0.5, xmax=6.6, ymin=-3.8, ymax=1.5, axis lines=middle, ytick = {-3, -2, -1, 1}, xtick = {1,...,10}, yticklabel pos = right,
          yticklabel style={right,xshift=1mm},
          extra x tick style={tick label style={above,yshift=1mm}},
          extra x ticks={-0.367879441},
          extra x tick labels={$-\frac{1}{e}$},
          width=\textwidth, height=0.8\textwidth,
          xlabel={$x$}, tick style={thin,black}
  ] 
  \addplot [color=black, line width=0.5pt, densely dashed, mark=none,domain=-5:0,samples=200] ({-exp(-1)}, {x}); 
  \addplot [color=myblue, line width=1pt, mark=none,domain=-1:1.5,samples=200] ({x*exp(x)}, {x}); 
  \addplot [color=myred, line width=1pt, mark=none,domain=-5:-1,samples=200] ({x*exp(x)}, {x}); 
  \end{axis}
\end{tikzpicture}
\end{center}
\caption{The two real branches of the Lambert $W$ function: $W_0$ (blue) and $W_{-1}$ (red).}
\label{fig:lambertw}
\end{figure}
\<close>

definition Lambert_W :: "real \<Rightarrow> real" where
  "Lambert_W x = (if x < -exp(-1) then -1 else (THE w. w \<ge> -1 \<and> w * exp w = x))"

definition Lambert_W' :: "real \<Rightarrow> real" where
  "Lambert_W' x = (if x \<in> {-exp(-1)..<0} then (THE w. w \<le> -1 \<and> w * exp w = x) else -1)"

lemma Lambert_W_ex1:
  assumes "(x::real) \<ge> -exp (-1)"
  shows   "\<exists>!w. w \<ge> -1 \<and> w * exp w = x"
proof (rule ex_ex1I)
  have "filterlim (\<lambda>w::real. w * exp w) at_top at_top"
    by real_asymp
  hence "eventually (\<lambda>w. w * exp w \<ge> x) at_top"
    by (auto simp: filterlim_at_top)
  hence "eventually (\<lambda>w. w \<ge> 0 \<and> w * exp w \<ge> x) at_top"
    by (intro eventually_conj eventually_ge_at_top)
  then obtain w' where w': "w' * exp w' \<ge> x" "w' \<ge> 0"
    by (auto simp: eventually_at_top_linorder)
  from w' assms have "\<exists>w. -1 \<le> w \<and> w \<le> w' \<and> w * exp w = x"
    by (intro IVT' continuous_intros) auto
  thus "\<exists>w. w \<ge> -1 \<and> w * exp w = x" by blast
next
  fix w w' :: real
  assume ww': "w \<ge> -1 \<and> w * exp w = x" "w' \<ge> -1 \<and> w' * exp w' = x"
  hence "w * exp w = w' * exp w'" by simp
  thus "w = w'"
    using exp_times_self_strict_mono[of w w'] exp_times_self_strict_mono[of w' w] ww'
    by (cases w w' rule: linorder_cases) auto
qed

lemma Lambert_W'_ex1:
  assumes "(x::real) \<in> {-exp (-1)..<0}"
  shows   "\<exists>!w. w \<le> -1 \<and> w * exp w = x"
proof (rule ex_ex1I)
  have "eventually (\<lambda>w. x \<le> w * exp w) at_bot"
    using assms by real_asymp
  hence "eventually (\<lambda>w. w \<le> -1 \<and> w * exp w \<ge> x) at_bot"
    by (intro eventually_conj eventually_le_at_bot)
  then obtain w' where w': "w' * exp w' \<ge> x" "w' \<le> -1"
    by (auto simp: eventually_at_bot_linorder)

  from w' assms have "\<exists>w. w' \<le> w \<and> w \<le> -1 \<and> w * exp w = x"
    by (intro IVT2' continuous_intros) auto
  thus "\<exists>w. w \<le> -1 \<and> w * exp w = x" by blast
next
  fix w w' :: real
  assume ww': "w \<le> -1 \<and> w * exp w = x" "w' \<le> -1 \<and> w' * exp w' = x"
  hence "w * exp w = w' * exp w'" by simp
  thus "w = w'"
    using exp_times_self_strict_antimono[of w w'] exp_times_self_strict_antimono[of w' w] ww'
    by (cases w w' rule: linorder_cases) auto
qed

lemma Lambert_W_times_exp_self: 
  assumes "x \<ge> -exp (-1)"
  shows   "Lambert_W x * exp (Lambert_W x) = x"
  using theI'[OF Lambert_W_ex1[OF assms]] assms by (auto simp: Lambert_W_def)

lemma Lambert_W_times_exp_self':
  assumes "x \<ge> -exp (-1)"
  shows   "exp (Lambert_W x) * Lambert_W x = x"
  using Lambert_W_times_exp_self[of x] assms by (simp add: mult_ac)

lemma Lambert_W'_times_exp_self: 
  assumes "x \<in> {-exp (-1)..<0}"
  shows   "Lambert_W' x * exp (Lambert_W' x) = x"
  using theI'[OF Lambert_W'_ex1[OF assms]] assms by (auto simp: Lambert_W'_def)

lemma Lambert_W'_times_exp_self':
  assumes "x \<in> {-exp (-1)..<0}"
  shows   "exp (Lambert_W' x) * Lambert_W' x = x"
  using Lambert_W'_times_exp_self[of x] assms by (simp add: mult_ac)

lemma Lambert_W_ge: "Lambert_W x \<ge> -1"
  using theI'[OF Lambert_W_ex1[of x]] by (auto simp: Lambert_W_def)

lemma Lambert_W'_le: "Lambert_W' x \<le> -1"
  using theI'[OF Lambert_W'_ex1[of x]] by (auto simp: Lambert_W'_def)

lemma Lambert_W_eqI:
  assumes "w \<ge> -1" "w * exp w = x"
  shows   "Lambert_W x = w"
proof -
  from assms exp_times_self_ge[of w] have "x \<ge> -exp (-1)"
    by (cases "x \<ge> -exp (-1)") auto
  from Lambert_W_ex1[OF this] Lambert_W_times_exp_self[OF this] Lambert_W_ge[of x] assms
    show ?thesis by metis
  qed

lemma Lambert_W'_eqI:
  assumes "w \<le> -1" "w * exp w = x"
  shows   "Lambert_W' x = w"
proof -
  from assms exp_times_self_ge[of w] have "x \<ge> -exp (-1)"
    by (cases "x \<ge> -exp (-1)") auto
  moreover from assms have "w * exp w < 0"
    by (intro mult_neg_pos) auto
  ultimately have "x \<in> {-exp (-1)..<0}"
    using assms by auto

  from Lambert_W'_ex1[OF this(1)] Lambert_W'_times_exp_self[OF this(1)] Lambert_W'_le assms
    show ?thesis by metis
  qed

text \<open>
  $W_0(x)$ and $W_{-1}(x)$ together fully cover all solutions of $we^w = x$:
\<close>
lemma exp_times_self_eqD:
  assumes "w * exp w = x"
  shows   "x \<ge> -exp (-1)" and "w = Lambert_W x \<or> x < 0 \<and> w = Lambert_W' x"
proof -
  from assms show "x \<ge> -exp (-1)"
    using exp_times_self_ge[of w] by auto
  show "w = Lambert_W x \<or> x < 0 \<and> w = Lambert_W' x"
  proof (cases "w \<ge> -1")
    case True
    hence "Lambert_W x = w"
      using assms by (intro Lambert_W_eqI) auto
    thus ?thesis by auto
  next
    case False
    from False have "w * exp w < 0"
      by (intro mult_neg_pos) auto
    from False have "Lambert_W' x = w"
      using assms by (intro Lambert_W'_eqI) auto
    thus ?thesis using assms \<open>w * exp w < 0\<close> by auto
  qed
qed

theorem exp_times_self_eq_iff:
  "w * exp w = x \<longleftrightarrow> x \<ge> -exp (-1) \<and> (w = Lambert_W x \<or> x < 0 \<and> w = Lambert_W' x)"
  using exp_times_self_eqD[of w x]
  by (auto simp: Lambert_W_times_exp_self Lambert_W'_times_exp_self)

lemma Lambert_W_exp_times_self [simp]: "x \<ge> -1 \<Longrightarrow> Lambert_W (x * exp x) = x"
  by (rule Lambert_W_eqI) auto

lemma Lambert_W_exp_times_self' [simp]: "x \<ge> -1 \<Longrightarrow> Lambert_W (exp x * x) = x"
  by (rule Lambert_W_eqI) auto

lemma Lambert_W'_exp_times_self [simp]: "x \<le> -1 \<Longrightarrow> Lambert_W' (x * exp x) = x"
  by (rule Lambert_W'_eqI) auto

lemma Lambert_W'_exp_times_self' [simp]: "x \<le> -1 \<Longrightarrow> Lambert_W' (exp x * x) = x"
  by (rule Lambert_W'_eqI) auto

lemma Lambert_W_times_ln_self:
  assumes "x \<ge> exp (-1)"
  shows   "Lambert_W (x * ln x) = ln x"
proof -
  have "0 < exp (-1 :: real)"
    by simp
  also note \<open>\<dots> \<le> x\<close>
  finally have "x > 0" .
  from assms have "ln (exp (-1)) \<le> ln x"
    using \<open>x > 0\<close> by (subst ln_le_cancel_iff) auto
  hence "Lambert_W (exp (ln x) * ln x) = ln x"
    by (subst Lambert_W_exp_times_self') auto
  thus ?thesis using \<open>x > 0\<close> by simp
qed

lemma Lambert_W_times_ln_self':
  assumes "x \<ge> exp (-1)"
  shows   "Lambert_W (ln x  * x) = ln x"
  using Lambert_W_times_ln_self[OF assms] by (simp add: mult.commute)

lemma Lambert_W_eq_minus_exp_minus1 [simp]: "Lambert_W (-exp (-1)) = -1"
  by (rule Lambert_W_eqI) auto

lemma Lambert_W'_eq_minus_exp_minus1 [simp]: "Lambert_W' (-exp (-1)) = -1"
  by (rule Lambert_W'_eqI) auto

lemma Lambert_W_0 [simp]: "Lambert_W 0 = 0"
  by (rule Lambert_W_eqI) auto


subsection \<open>Monotonicity properties\<close>

lemma Lambert_W_strict_mono:
  assumes "x \<ge> -exp(-1)" "x < y"
  shows   "Lambert_W x < Lambert_W y"
proof (rule ccontr)
  assume "\<not>(Lambert_W x < Lambert_W y)"
  hence "Lambert_W x * exp (Lambert_W x) \<ge> Lambert_W y * exp (Lambert_W y)"
    by (intro exp_times_self_mono) (auto simp: Lambert_W_ge)
  hence "x \<ge> y"
    using assms by (simp add: Lambert_W_times_exp_self)
  with assms show False by simp
qed

lemma Lambert_W_mono:
  assumes "x \<ge> -exp(-1)" "x \<le> y"
  shows   "Lambert_W x \<le> Lambert_W y"
  using Lambert_W_strict_mono[of x y] assms by (cases "x = y") auto

lemma Lambert_W_eq_iff [simp]:
  "x \<ge> -exp(-1) \<Longrightarrow> y \<ge> -exp(-1) \<Longrightarrow> Lambert_W x = Lambert_W y \<longleftrightarrow> x = y"
  using Lambert_W_strict_mono[of x y] Lambert_W_strict_mono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W_le_iff [simp]:
  "x \<ge> -exp(-1) \<Longrightarrow> y \<ge> -exp(-1) \<Longrightarrow> Lambert_W x \<le> Lambert_W y \<longleftrightarrow> x \<le> y"
  using Lambert_W_strict_mono[of x y] Lambert_W_strict_mono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W_less_iff [simp]:
  "x \<ge> -exp(-1) \<Longrightarrow> y \<ge> -exp(-1) \<Longrightarrow> Lambert_W x < Lambert_W y \<longleftrightarrow> x < y"
  using Lambert_W_strict_mono[of x y] Lambert_W_strict_mono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W_le_minus_one:
  assumes "x \<le> -exp(-1)"
  shows   "Lambert_W x = -1"
proof (cases "x = -exp(-1)")
  case False
  thus ?thesis using assms
    by (auto simp: Lambert_W_def)
qed auto

lemma Lambert_W_pos_iff [simp]: "Lambert_W x > 0 \<longleftrightarrow> x > 0"
proof (cases "x \<ge> -exp (-1)")
  case True
  thus ?thesis
    using Lambert_W_less_iff[of 0 x] by (simp del: Lambert_W_less_iff)
next
  case False
  hence "x < - exp(-1)" by auto
  also have "\<dots> \<le> 0" by simp
  finally show ?thesis using False
    by (auto simp: Lambert_W_le_minus_one)
qed

lemma Lambert_W_eq_0_iff [simp]: "Lambert_W x = 0 \<longleftrightarrow> x = 0"
  using Lambert_W_eq_iff[of x 0]
  by (cases "x \<ge> -exp (-1)") (auto simp: Lambert_W_le_minus_one simp del: Lambert_W_eq_iff)

lemma Lambert_W_nonneg_iff [simp]: "Lambert_W x \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using Lambert_W_pos_iff[of x]
  by (cases "x = 0") (auto simp del: Lambert_W_pos_iff)

lemma Lambert_W_neg_iff [simp]: "Lambert_W x < 0 \<longleftrightarrow> x < 0"
  using Lambert_W_nonneg_iff[of x] by (auto simp del: Lambert_W_nonneg_iff)

lemma Lambert_W_nonpos_iff [simp]: "Lambert_W x \<le> 0 \<longleftrightarrow> x \<le> 0"
  using Lambert_W_pos_iff[of x] by (auto simp del: Lambert_W_pos_iff)

lemma Lambert_W_geI:
  assumes "y * exp y \<le> x"
  shows   "Lambert_W x \<ge> y"
proof (cases "y \<ge> -1")
  case False
  hence "y \<le> -1" by simp
  also have "-1 \<le> Lambert_W x" by (rule Lambert_W_ge)
  finally show ?thesis .
next
  case True
  have "Lambert_W x \<ge> Lambert_W (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W_mono) auto
  thus ?thesis using assms True by simp
qed

lemma Lambert_W_gtI:
  assumes "y * exp y < x"
  shows   "Lambert_W x > y"
proof (cases "y \<ge> -1")
  case False
  hence "y < -1" by simp
  also have "-1 \<le> Lambert_W x" by (rule Lambert_W_ge)
  finally show ?thesis .
next
  case True
  have "Lambert_W x > Lambert_W (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W_strict_mono) auto
  thus ?thesis using assms True by simp
qed

lemma Lambert_W_leI:
  assumes "y * exp y \<ge> x" "y \<ge> -1" "x \<ge> -exp (-1)"
  shows   "Lambert_W x \<le> y"
proof -
  have "Lambert_W x \<le> Lambert_W (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W_mono) auto
  thus ?thesis using assms by simp
qed

lemma Lambert_W_lessI:
  assumes "y * exp y > x" "y \<ge> -1" "x \<ge> -exp (-1)"
  shows   "Lambert_W x < y"
proof -
  have "Lambert_W x < Lambert_W (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W_strict_mono) auto
  thus ?thesis using assms by simp
qed



lemma Lambert_W'_strict_antimono:
  assumes "-exp (-1) \<le> x" "x < y" "y < 0"
  shows   "Lambert_W' x > Lambert_W' y"
proof (rule ccontr)
  assume "\<not>(Lambert_W' x > Lambert_W' y)"
  hence "Lambert_W' x * exp (Lambert_W' x) \<ge> Lambert_W' y * exp (Lambert_W' y)"
    using assms by (intro exp_times_self_antimono Lambert_W'_le) auto
  hence "x \<ge> y"
    using assms by (simp add: Lambert_W'_times_exp_self)
  with assms show False by simp
qed

lemma Lambert_W'_antimono:
  assumes "x \<ge> -exp(-1)" "x \<le> y" "y < 0"
  shows   "Lambert_W' x \<ge> Lambert_W' y"
  using Lambert_W'_strict_antimono[of x y] assms by (cases "x = y") auto

lemma Lambert_W'_eq_iff [simp]:
  "x \<in> {-exp(-1)..<0} \<Longrightarrow> y \<in> {-exp(-1)..<0} \<Longrightarrow> Lambert_W' x = Lambert_W' y \<longleftrightarrow> x = y"
  using Lambert_W'_strict_antimono[of x y] Lambert_W'_strict_antimono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W'_le_iff [simp]:
  "x \<in> {-exp(-1)..<0} \<Longrightarrow> y \<in> {-exp(-1)..<0} \<Longrightarrow> Lambert_W' x \<le> Lambert_W' y \<longleftrightarrow> x \<ge> y"
  using Lambert_W'_strict_antimono[of x y] Lambert_W'_strict_antimono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W'_less_iff [simp]:
  "x \<in> {-exp(-1)..<0} \<Longrightarrow> y \<in> {-exp(-1)..<0} \<Longrightarrow> Lambert_W' x < Lambert_W' y \<longleftrightarrow> x > y"
  using Lambert_W'_strict_antimono[of x y] Lambert_W'_strict_antimono[of y x]
  by (cases x y rule: linorder_cases) auto

lemma Lambert_W'_le_minus_one:
  assumes "x \<le> -exp(-1)"
  shows   "Lambert_W' x = -1"
proof (cases "x = -exp(-1)")
  case False
  thus ?thesis using assms
    by (auto simp: Lambert_W'_def)
qed auto

lemma Lambert_W'_ge_zero: "x \<ge> 0 \<Longrightarrow> Lambert_W' x = -1"
  by (simp add: Lambert_W'_def)

lemma Lambert_W'_neg: "Lambert_W' x < 0"
  by (rule le_less_trans[OF Lambert_W'_le]) auto

lemma Lambert_W'_nz [simp]: "Lambert_W' x \<noteq> 0"
  using Lambert_W'_neg[of x] by simp

lemma Lambert_W'_geI:
  assumes "y * exp y \<ge> x" "y \<le> -1" "x \<ge> -exp(-1)"
  shows   "Lambert_W' x \<ge> y"
proof -
  from assms have "y * exp y < 0"
    by (intro mult_neg_pos) auto
  hence "Lambert_W' x \<ge> Lambert_W' (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W'_antimono) auto
  thus ?thesis using assms by simp
qed

lemma Lambert_W'_gtI:
  assumes "y * exp y > x" "y \<le> -1" "x \<ge> -exp(-1)"
  shows   "Lambert_W' x \<ge> y"
proof -
  from assms have "y * exp y < 0"
    by (intro mult_neg_pos) auto
  hence "Lambert_W' x > Lambert_W' (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W'_strict_antimono) auto
  thus ?thesis using assms by simp
qed

lemma Lambert_W'_leI:
  assumes "y * exp y \<le> x" "x < 0"
  shows   "Lambert_W' x \<le> y"
proof (cases "y \<le> -1")
  case True
  have "Lambert_W' x \<le> Lambert_W' (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W'_antimono) auto
  thus ?thesis using assms True by simp
next
  case False
  have "Lambert_W' x \<le> -1"
    by (rule Lambert_W'_le)
  also have "\<dots> < y"
    using False by simp
  finally show ?thesis by simp
qed

lemma Lambert_W'_lessI:
  assumes "y * exp y < x" "x < 0"
  shows   "Lambert_W' x < y"
proof (cases "y \<le> -1")
  case True
  have "Lambert_W' x < Lambert_W' (y * exp y)"
    using assms exp_times_self_ge[of y] by (intro Lambert_W'_strict_antimono) auto
  thus ?thesis using assms True by simp
next
  case False
  have "Lambert_W' x \<le> -1"
    by (rule Lambert_W'_le)
  also have "\<dots> < y"
    using False by simp
  finally show ?thesis by simp
qed


lemma bij_betw_exp_times_self_atLeastAtMost:
  fixes a b :: real
  assumes "a \<ge> -1" "a \<le> b"
  shows   "bij_betw (\<lambda>x. x * exp x) {a..b} {a * exp a..b * exp b}"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>x. x * exp x) {a..b}"
    by (rule inj_on_subset[OF exp_times_self_inj]) (use assms in auto)
next
  show "(\<lambda>x. x * exp x) ` {a..b} = {a * exp a..b * exp b}"
  proof safe
    fix x assume "x \<in> {a..b}"
    thus "x * exp x \<in> {a * exp a..b * exp b}"
      using assms by (auto intro!: exp_times_self_mono)
  next
    fix x assume x: "x \<in> {a * exp a..b * exp b}"
    have "(-1) * exp (-1) \<le> a * exp a"
      using assms by (intro exp_times_self_mono) auto
    also have "\<dots> \<le> x" using x by simp
    finally have "x \<ge> -exp (-1)" by simp

    have "Lambert_W x \<in> {a..b}"
      using x \<open>x \<ge> -exp (-1)\<close> assms by (auto intro!: Lambert_W_geI Lambert_W_leI)
    moreover have "Lambert_W x * exp (Lambert_W x) = x"
      using \<open>x \<ge> -exp (-1)\<close> by (simp add: Lambert_W_times_exp_self)
    ultimately show "x \<in> (\<lambda>x. x * exp x) ` {a..b}"
      unfolding image_iff by metis
  qed
qed

lemma bij_betw_exp_times_self_atLeastAtMost':
  fixes a b :: real
  assumes "a \<le> b" "b \<le> -1"
  shows   "bij_betw (\<lambda>x. x * exp x) {a..b} {b * exp b..a * exp a}"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>x. x * exp x) {a..b}"
    by (rule inj_on_subset[OF exp_times_self_inj']) (use assms in auto)
next
  show "(\<lambda>x. x * exp x) ` {a..b} = {b * exp b..a * exp a}"
  proof safe
    fix x assume "x \<in> {a..b}"
    thus "x * exp x \<in> {b * exp b..a * exp a}"
      using assms by (auto intro!: exp_times_self_antimono)
  next
    fix x assume x: "x \<in> {b * exp b..a * exp a}"
    from assms have "a * exp a < 0"
      by (intro mult_neg_pos) auto
    with x have "x < 0" by auto
    have "(-1) * exp (-1) \<le> b * exp b"
      using assms by (intro exp_times_self_antimono) auto
    also have "\<dots> \<le> x" using x by simp
    finally have "x \<ge> -exp (-1)" by simp

    have "Lambert_W' x \<in> {a..b}"
      using x \<open>x \<ge> -exp (-1)\<close> \<open>x < 0\<close> assms 
      by (auto intro!: Lambert_W'_geI Lambert_W'_leI)
    moreover have "Lambert_W' x * exp (Lambert_W' x) = x"
      using \<open>x \<ge> -exp (-1)\<close> \<open>x < 0\<close> by (auto simp: Lambert_W'_times_exp_self)
    ultimately show "x \<in> (\<lambda>x. x * exp x) ` {a..b}"
      unfolding image_iff by metis
  qed
qed

lemma bij_betw_exp_times_self_atLeast:
  fixes a :: real
  assumes "a \<ge> -1"
  shows   "bij_betw (\<lambda>x. x * exp x) {a..} {a * exp a..}"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>x. x * exp x) {a..}"
    by (rule inj_on_subset[OF exp_times_self_inj]) (use assms in auto)
next
  show "(\<lambda>x. x * exp x) ` {a..} = {a * exp a..}"
  proof safe
    fix x assume "x \<ge> a"
    thus "x * exp x \<ge> a * exp a"
      using assms by (auto intro!: exp_times_self_mono)
  next
    fix x assume x: "x \<ge> a * exp a"
    have "(-1) * exp (-1) \<le> a * exp a"
      using assms by (intro exp_times_self_mono) auto
    also have "\<dots> \<le> x" using x by simp
    finally have "x \<ge> -exp (-1)" by simp

    have "Lambert_W x \<in> {a..}"
      using x \<open>x \<ge> -exp (-1)\<close> assms by (auto intro!: Lambert_W_geI Lambert_W_leI)
    moreover have "Lambert_W x * exp (Lambert_W x) = x"
      using \<open>x \<ge> -exp (-1)\<close> by (simp add: Lambert_W_times_exp_self)
    ultimately show "x \<in> (\<lambda>x. x * exp x) ` {a..}"
      unfolding image_iff by metis
  qed
qed


subsection \<open>Basic identities and bounds\<close>

lemma Lambert_W_2_ln_2 [simp]: "Lambert_W (2 * ln 2) = ln 2"
proof -
  have "-1 \<le> (0 :: real)"
    by simp
  also have "\<dots> \<le> ln 2"
    by simp
  finally have "-1 \<le> (ln 2 :: real)" .
  thus ?thesis
    by (intro Lambert_W_eqI) auto
qed

lemma Lambert_W_exp_1 [simp]: "Lambert_W (exp 1) = 1"
  by (rule Lambert_W_eqI) auto

lemma Lambert_W_neg_ln_over_self:
  assumes "x \<in> {exp (-1)..exp 1}"
  shows   "Lambert_W (-ln x / x) = -ln x"
proof -
  have "0 < (exp (-1) :: real)"
    by simp
  also have "\<dots> \<le> x"
    using assms by simp
  finally have "x > 0" .
  from \<open>x > 0\<close> assms have "ln x \<le> ln (exp 1)"
    by (subst ln_le_cancel_iff) auto
  also have "ln (exp 1) = (1 :: real)"
    by simp
  finally have "ln x \<le> 1" .
  show ?thesis
    using assms \<open>x > 0\<close> \<open>ln x \<le> 1\<close>
    by (intro Lambert_W_eqI) (auto simp: exp_minus field_simps)
qed

lemma Lambert_W'_neg_ln_over_self:
  assumes "x \<ge> exp 1"
  shows   "Lambert_W' (-ln x / x) = -ln x"
proof (rule Lambert_W'_eqI)
  have "0 < (exp 1 :: real)"
    by simp
  also have "\<dots> \<le> x"
    by fact
  finally have "x > 0" .
  from assms \<open>x > 0\<close> have "ln x \<ge> ln (exp 1)"
    by (subst ln_le_cancel_iff) auto
  thus "-ln x \<le> -1" by simp
  show "-ln x * exp (-ln x) = -ln x / x"
    using \<open>x > 0\<close> by (simp add: field_simps exp_minus)
qed

lemma exp_Lambert_W: "x \<ge> -exp (-1) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> exp (Lambert_W x) = x / Lambert_W x"
  using Lambert_W_times_exp_self[of x] by (auto simp add: divide_simps mult_ac)

lemma exp_Lambert_W': "x \<in> {-exp (-1)..<0} \<Longrightarrow> exp (Lambert_W' x) = x / Lambert_W' x"
  using Lambert_W'_times_exp_self[of x] by (auto simp add: divide_simps mult_ac)

lemma ln_Lambert_W:
  assumes "x > 0"
  shows   "ln (Lambert_W x) = ln x - Lambert_W x"
proof -
  have "-exp (-1) \<le> (0 :: real)"
    by simp
  also have "\<dots> < x" by fact
  finally have x: "x > -exp(-1)" .

  have "exp (ln (Lambert_W x)) = exp (ln x - Lambert_W x)"
    using assms x by (subst exp_diff) (auto simp: exp_Lambert_W)
  thus ?thesis by (subst (asm) exp_inj_iff)
qed

lemma ln_minus_Lambert_W':
  assumes "x \<in> {-exp (-1)..<0}"
  shows   "ln (-Lambert_W' x) = ln (-x) - Lambert_W' x"
proof -
  have "exp (ln (-x) - Lambert_W' x) = -Lambert_W' x"
    using assms by (simp add: exp_diff exp_Lambert_W')
  also have "\<dots> = exp (ln (-Lambert_W' x))"
    using Lambert_W'_neg[of x] by simp
  finally show ?thesis by simp
qed

lemma Lambert_W_plus_Lambert_W_eq:
  assumes "x > 0" "y > 0"
  shows   "Lambert_W x + Lambert_W y = Lambert_W (x * y * (1 / Lambert_W x + 1 / Lambert_W y))"
proof (rule sym, rule Lambert_W_eqI)
  have "x > -exp(-1)" "y > -exp (-1)"
    by (rule less_trans[OF _ assms(1)] less_trans[OF _ assms(2)], simp)+
  with assms show "(Lambert_W x + Lambert_W y) * exp (Lambert_W x + Lambert_W y) =
                     x * y * (1 / Lambert_W x + 1 / Lambert_W y)"
    by (auto simp: field_simps exp_add exp_Lambert_W)
  have "-1 \<le> (0 :: real)"
    by simp
  also from assms have "\<dots> \<le> Lambert_W x + Lambert_W y"
    by (intro add_nonneg_nonneg) auto
  finally show "\<dots> \<ge> -1" .
qed

lemma Lambert_W'_plus_Lambert_W'_eq:
  assumes "x \<in> {-exp(-1)..<0}" "y \<in> {-exp(-1)..<0}"
  shows   "Lambert_W' x + Lambert_W' y = Lambert_W' (x * y * (1 / Lambert_W' x + 1 / Lambert_W' y))"
proof (rule sym, rule Lambert_W'_eqI)
  from assms show "(Lambert_W' x + Lambert_W' y) * exp (Lambert_W' x + Lambert_W' y) =
                     x * y * (1 / Lambert_W' x + 1 / Lambert_W' y)"
    by (auto simp: field_simps exp_add exp_Lambert_W')
  have "Lambert_W' x + Lambert_W' y \<le> -1 + -1"
    by (intro add_mono Lambert_W'_le)
  also have "\<dots> \<le> -1" by simp
  finally show "Lambert_W' x + Lambert_W' y \<le> -1" .
qed

lemma Lambert_W_gt_ln_minus_ln_ln:
  assumes "x > exp 1"
  shows   "Lambert_W x > ln x - ln (ln x)"
proof (rule Lambert_W_gtI)
  have "x > 1"
    by (rule less_trans[OF _ assms]) auto
  have "ln x > ln (exp 1)"
    by (subst ln_less_cancel_iff) (use \<open>x > 1\<close> assms in auto)
  thus "(ln x - ln (ln x)) * exp (ln x - ln (ln x)) < x"
    using assms \<open>x > 1\<close> by (simp add: exp_diff field_simps)
qed

lemma Lambert_W_less_ln:
  assumes "x > exp 1"
  shows   "Lambert_W x < ln x"
proof (rule Lambert_W_lessI)
  have "x > 0"
    by (rule less_trans[OF _ assms]) auto
  have "ln x > ln (exp 1)"
    by (subst ln_less_cancel_iff) (use \<open>x > 0\<close> assms in auto)
  thus "x < ln x * exp (ln x)"
    using \<open>x > 0\<close> by simp
  show "ln x \<ge> -1"
    by (rule less_imp_le[OF le_less_trans[OF _ \<open>ln x > _\<close>]]) auto
  show "x \<ge> -exp (-1)"
    by (rule less_imp_le[OF le_less_trans[OF _ \<open>x > 0\<close>]]) auto
qed


subsection \<open>Limits, continuity, and differentiability\<close>

lemma filterlim_Lambert_W_at_top [tendsto_intros]: "filterlim Lambert_W at_top at_top"
  unfolding filterlim_at_top
proof
  fix C :: real
  have "eventually (\<lambda>x. x \<ge> C * exp C) at_top"
    by (rule eventually_ge_at_top)
  thus "eventually (\<lambda>x. Lambert_W x \<ge> C) at_top"
  proof eventually_elim
    case (elim x)
    thus ?case
      by (intro Lambert_W_geI) auto
  qed
qed

lemma filterlim_Lambert_W_at_left_0 [tendsto_intros]:
  "filterlim Lambert_W' at_bot (at_left 0)"
  unfolding filterlim_at_bot
proof
  fix C :: real
  define C' where "C' = min C (-1)"
  have "C' < 0" "C' \<le> C"
    by (simp_all add: C'_def)
  have "C' * exp C' < 0"
    using \<open>C' < 0\<close> by (intro mult_neg_pos) auto
  hence "eventually (\<lambda>x. x \<ge> C' * exp C') (at_left 0)"
    by real_asymp
  moreover have "eventually (\<lambda>x::real. x < 0) (at_left 0)"
    by real_asymp
  ultimately show "eventually (\<lambda>x. Lambert_W' x \<le> C) (at_left 0)"
  proof eventually_elim
    case (elim x)
    hence "Lambert_W' x \<le> C'"
      by (intro Lambert_W'_leI) auto
    also have "\<dots> \<le> C" by fact
    finally show ?case .
  qed
qed

lemma continuous_on_Lambert_W [continuous_intros]: "continuous_on {-exp (-1)..} Lambert_W"
proof -
  have *: "continuous_on {-exp (-1)..b * exp b} Lambert_W" if "b \<ge> 0" for b
  proof -
    have "continuous_on ((\<lambda>x. x * exp x) ` {-1..b}) Lambert_W"
      by (rule continuous_on_inv) (auto intro!: continuous_intros)
    also have "(\<lambda>x. x * exp x) ` {-1..b} = {-exp (-1)..b * exp b}"
      using bij_betw_exp_times_self_atLeastAtMost[of "-1" b] \<open>b \<ge> 0\<close>
      by (simp add: bij_betw_def)
    finally show ?thesis .
  qed

  have "continuous (at x) Lambert_W" if "x \<ge> 0" for x
  proof -
    have x: "-exp (-1) < x"
      by (rule less_le_trans[OF _ that]) auto
    
    define b where "b = Lambert_W x + 1"
    have "b \<ge> 0"
      using Lambert_W_ge[of x] by (simp add: b_def)
    have "x = Lambert_W x * exp (Lambert_W x)"
      using that x by (subst Lambert_W_times_exp_self) auto
    also have "\<dots> < b * exp b"
      by (intro exp_times_self_strict_mono) (auto simp: b_def Lambert_W_ge)
    finally have "b * exp b > x" .
    have "continuous_on {-exp(-1)<..<b * exp b} Lambert_W"
      by (rule continuous_on_subset[OF *[of b]]) (use \<open>b \<ge> 0\<close> in auto)
    moreover have "x \<in> {-exp(-1)<..<b * exp b}"
      using \<open>b * exp b > x\<close> x by (auto simp: )
    ultimately show "continuous (at x) Lambert_W"
      by (subst (asm) continuous_on_eq_continuous_at) auto
  qed
  hence "continuous_on {0..} Lambert_W"
    by (intro continuous_at_imp_continuous_on) auto
  moreover have "continuous_on {-exp (-1)..0} Lambert_W"
    using *[of 0] by simp
  ultimately have "continuous_on ({-exp (-1)..0} \<union> {0..}) Lambert_W"
    by (intro continuous_on_closed_Un) auto
  also have "{-exp (-1)..0} \<union> {0..} = {-exp (-1::real)..}"
    using order.trans[of "-exp (-1)::real" 0] by auto
  finally show ?thesis .
qed

lemma continuous_on_Lambert_W_alt [continuous_intros]:
  assumes "continuous_on A f" "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> -exp (-1)"
  shows   "continuous_on A (\<lambda>x. Lambert_W (f x))"
  using continuous_on_compose2[OF continuous_on_Lambert_W assms(1)] assms by auto

lemma continuous_on_Lambert_W' [continuous_intros]: "continuous_on {-exp (-1)..<0} Lambert_W'"
proof -
  have *: "continuous_on {-exp (-1)..-b * exp (-b)} Lambert_W'" if "b \<ge> 1" for b
  proof -
    have "continuous_on ((\<lambda>x. x * exp x) ` {-b..-1}) Lambert_W'"
      by (intro continuous_on_inv ballI) (auto intro!: continuous_intros)
    also have "(\<lambda>x. x * exp x) ` {-b..-1} = {-exp (-1)..-b * exp (-b)}"
      using bij_betw_exp_times_self_atLeastAtMost'[of "-b" "-1"] that
      by (simp add: bij_betw_def)
    finally show ?thesis .
  qed

  have "continuous (at x) Lambert_W'" if "x > -exp (-1)" "x < 0" for x
  proof - 
    define b where "b = Lambert_W x + 1"
    have "eventually (\<lambda>b. -b * exp (-b) > x) at_top"
      using that by real_asymp
    hence "eventually (\<lambda>b. b \<ge> 1 \<and> -b * exp (-b) > x) at_top"
      by (intro eventually_conj eventually_ge_at_top)
    then obtain b where b: "b \<ge> 1" "-b * exp (-b) > x"
      by (auto simp: eventually_at_top_linorder)

    have "continuous_on {-exp(-1)<..<-b * exp (-b)} Lambert_W'"
      by (rule continuous_on_subset[OF *[of b]]) (use \<open>b \<ge> 1\<close> in auto)
    moreover have "x \<in> {-exp(-1)<..<-b * exp (-b)}"
      using b that by auto
    ultimately show "continuous (at x) Lambert_W'"
      by (subst (asm) continuous_on_eq_continuous_at) auto
  qed
  hence **: "continuous_on {-exp (-1)<..<0} Lambert_W'"
    by (intro continuous_at_imp_continuous_on) auto

  show ?thesis
    unfolding continuous_on_def
  proof
    fix x :: real assume x: "x \<in> {-exp(-1)..<0}"
    show "(Lambert_W' \<longlongrightarrow> Lambert_W' x) (at x within {-exp(-1)..<0})"
    proof (cases "x = -exp(-1)")
      case False
      hence "isCont Lambert_W' x"
        using x ** by (auto simp: continuous_on_eq_continuous_at)
      thus ?thesis
        using continuous_at filterlim_within_subset by blast
    next
      case True
      define a :: real where "a = -2 * exp (-2)"
      have a: "a > -exp (-1)"
        using exp_times_self_strict_antimono[of "-1" "-2"] by (auto simp: a_def)
      from True have "x \<in> {-exp (-1)..<a}"
        using a by (auto simp: a_def)
      have "continuous_on {-exp (-1)..<a} Lambert_W'"
        unfolding a_def by (rule continuous_on_subset[OF *[of 2]]) auto
      hence "(Lambert_W' \<longlongrightarrow> Lambert_W' x) (at x within {-exp (-1)..<a})"
        using \<open>x \<in> {-exp (-1)..<a}\<close> by (auto simp: continuous_on_def)
      also have "at x within {-exp (-1)..<a} = at_right x"
        using a by (intro at_within_nhd[of _ "{..<a}"]) (auto simp: True)
      also have "\<dots> = at x within {-exp (-1)..<0}"
        using a by (intro at_within_nhd[of _ "{..<0}"]) (auto simp: True)
      finally show ?thesis .
    qed
  qed
qed

lemma continuous_on_Lambert_W'_alt [continuous_intros]:
  assumes "continuous_on A f" "\<And>x. x \<in> A \<Longrightarrow> f x \<in> {-exp (-1)..<0}"
  shows   "continuous_on A (\<lambda>x. Lambert_W' (f x))"
  using continuous_on_compose2[OF continuous_on_Lambert_W' assms(1)] assms
  by (auto simp: subset_iff)


lemma tendsto_Lambert_W_1:
  assumes "(f \<longlongrightarrow> L) F" "eventually (\<lambda>x. f x \<ge> -exp (-1)) F"
  shows   "((\<lambda>x. Lambert_W (f x)) \<longlongrightarrow> Lambert_W L) F"
proof (cases "F = bot")
  case [simp]: False
  from tendsto_lowerbound[OF assms] have "L \<ge> -exp (-1)" by simp
  thus ?thesis
    using continuous_on_tendsto_compose[OF continuous_on_Lambert_W assms(1)] assms(2) by simp
qed auto

lemma tendsto_Lambert_W_2:
  assumes "(f \<longlongrightarrow> L) F" "L > -exp (-1)"
  shows   "((\<lambda>x. Lambert_W (f x)) \<longlongrightarrow> Lambert_W L) F"
  using order_tendstoD(1)[OF assms] assms
  by (intro tendsto_Lambert_W_1) (auto elim: eventually_mono)

lemma tendsto_Lambert_W [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "eventually (\<lambda>x. f x \<ge> -exp (-1)) F \<or> L > -exp (-1)"
  shows   "((\<lambda>x. Lambert_W (f x)) \<longlongrightarrow> Lambert_W L) F"
  using assms(2)
proof
  assume "L > -exp (-1)"
  from order_tendstoD(1)[OF assms(1) this] assms(1) show ?thesis
    by (intro tendsto_Lambert_W_1) (auto elim: eventually_mono)  
qed (use tendsto_Lambert_W_1[OF assms(1)] in auto)

lemma tendsto_Lambert_W'_1:
  assumes "(f \<longlongrightarrow> L) F" "eventually (\<lambda>x. f x \<ge> -exp (-1)) F" "L < 0"
  shows   "((\<lambda>x. Lambert_W' (f x)) \<longlongrightarrow> Lambert_W' L) F"
proof (cases "F = bot")
  case [simp]: False
  from tendsto_lowerbound[OF assms(1,2)] have L_ge: "L \<ge> -exp (-1)" by simp
  from order_tendstoD(2)[OF assms(1,3)] have ev: "eventually (\<lambda>x. f x < 0) F"
    by auto
  with assms(2) have "eventually (\<lambda>x. f x \<in> {-exp (-1)..<0}) F"
    by eventually_elim auto
  thus ?thesis using L_ge assms(3)
    by (intro continuous_on_tendsto_compose[OF continuous_on_Lambert_W' assms(1)]) auto
qed auto

lemma tendsto_Lambert_W'_2:
  assumes "(f \<longlongrightarrow> L) F" "L > -exp (-1)" "L < 0"
  shows   "((\<lambda>x. Lambert_W' (f x)) \<longlongrightarrow> Lambert_W' L) F"
  using order_tendstoD(1)[OF assms(1,2)] assms
  by (intro tendsto_Lambert_W'_1) (auto elim: eventually_mono)

lemma tendsto_Lambert_W' [tendsto_intros]:
  assumes "(f \<longlongrightarrow> L) F" "eventually (\<lambda>x. f x \<ge> -exp (-1)) F \<or> L > -exp (-1)" "L < 0"
  shows   "((\<lambda>x. Lambert_W' (f x)) \<longlongrightarrow> Lambert_W' L) F"
  using assms(2)
proof
  assume "L > -exp (-1)"
  from order_tendstoD(1)[OF assms(1) this] assms(1,3) show ?thesis
    by (intro tendsto_Lambert_W'_1) (auto elim: eventually_mono)  
qed (use tendsto_Lambert_W'_1[OF assms(1) _ assms(3)] in auto)


lemma continuous_Lambert_W [continuous_intros]:
  assumes "continuous F f" "f (Lim F (\<lambda>x. x)) > -exp (-1) \<or> eventually (\<lambda>x. f x \<ge> -exp (-1)) F"
  shows   "continuous F (\<lambda>x. Lambert_W (f x))"
  using assms unfolding continuous_def by (intro tendsto_Lambert_W) auto

lemma continuous_Lambert_W' [continuous_intros]:
  assumes "continuous F f" "f (Lim F (\<lambda>x. x)) > -exp (-1) \<or> eventually (\<lambda>x. f x \<ge> -exp (-1)) F"
          "f (Lim F (\<lambda>x. x)) < 0"
  shows   "continuous F (\<lambda>x. Lambert_W' (f x))"
  using assms unfolding continuous_def by (intro tendsto_Lambert_W') auto


lemma has_field_derivative_Lambert_W [derivative_intros]:
  assumes x: "x > -exp (-1)"
  shows   "(Lambert_W has_real_derivative inverse (x + exp (Lambert_W x))) (at x within A)"
proof -
  write Lambert_W ("W")
  from x have "W x > W (-exp (-1))"
    by (subst Lambert_W_less_iff) auto
  hence "W x > -1" by simp

  note [derivative_intros] = DERIV_inverse_function[where g = Lambert_W]
  have "((\<lambda>x. x * exp x) has_real_derivative (1 + W x) * exp (W x)) (at (W x))"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  hence "(W has_real_derivative inverse ((1 + W x) * exp (W x))) (at x)"
    by (rule DERIV_inverse_function[where a = "-exp (-1)" and b = "x + 1"])
       (use x \<open>W x > -1\<close> in \<open>auto simp: Lambert_W_times_exp_self Lim_ident_at
                                  intro!: continuous_intros\<close>)
  also have "(1 + W x) * exp (W x) = x + exp (W x)"
    using x by (simp add: algebra_simps Lambert_W_times_exp_self)
  finally show ?thesis by (rule has_field_derivative_at_within)
qed

lemma has_field_derivative_Lambert_W_gen [derivative_intros]:
  assumes "(f has_real_derivative f') (at x within A)" "f x > -exp (-1)"
  shows   "((\<lambda>x. Lambert_W (f x)) has_real_derivative
             (f' / (f x + exp (Lambert_W (f x))))) (at x within A)"
  using DERIV_chain2[OF has_field_derivative_Lambert_W[OF assms(2)] assms(1)]
  by (simp add: field_simps)

lemma has_field_derivative_Lambert_W' [derivative_intros]:
  assumes x: "x \<in> {-exp (-1)<..<0}"
  shows   "(Lambert_W' has_real_derivative inverse (x + exp (Lambert_W' x))) (at x within A)"
proof -
  write Lambert_W' ("W")
  from x have "W x < W (-exp (-1))"
    by (subst Lambert_W'_less_iff) auto
  hence "W x < -1" by simp

  note [derivative_intros] = DERIV_inverse_function[where g = Lambert_W]
  have "((\<lambda>x. x * exp x) has_real_derivative (1 + W x) * exp (W x)) (at (W x))"
    by (auto intro!: derivative_eq_intros simp: algebra_simps)
  hence "(W has_real_derivative inverse ((1 + W x) * exp (W x))) (at x)"
    by (rule DERIV_inverse_function[where a = "-exp (-1)" and b = "0"])
       (use x \<open>W x < -1\<close> in \<open>auto simp: Lambert_W'_times_exp_self Lim_ident_at
                                        intro!: continuous_intros\<close>)
  also have "(1 + W x) * exp (W x) = x + exp (W x)"
    using x by (simp add: algebra_simps Lambert_W'_times_exp_self)
  finally show ?thesis by (rule has_field_derivative_at_within)
qed

lemma has_field_derivative_Lambert_W'_gen [derivative_intros]:
  assumes "(f has_real_derivative f') (at x within A)" "f x \<in> {-exp (-1)<..<0}"
  shows   "((\<lambda>x. Lambert_W' (f x)) has_real_derivative
             (f' / (f x + exp (Lambert_W' (f x))))) (at x within A)"
  using DERIV_chain2[OF has_field_derivative_Lambert_W'[OF assms(2)] assms(1)]
  by (simp add: field_simps)


subsection \<open>Asymptotic expansion\<close>

text \<open>
  Lastly, we prove some more detailed asymptotic expansions of $W$ and $W'$ at their
  singularities. First, we show that:
  \begin{align*}
    W(x) &= \log x - \log\log x + o(\log\log x) &&\text{for}\ x\to\infty\\
    W'(x) &= \log (-x) - \log (-\log (-x)) + o(\log (-\log (-x))) &&\text{for}\ x\to 0^{-}
  \end{align*}
\<close>
theorem Lambert_W_asymp_equiv_at_top:
  "(\<lambda>x. Lambert_W x - ln x) \<sim>[at_top] (\<lambda>x. -ln (ln x))"
proof -
  have "(\<lambda>x. Lambert_W x - ln x) \<sim>[at_top] (\<lambda>x. (-1) * ln (ln x))"
  proof (rule asymp_equiv_sandwich')
    fix c' :: real assume c': "c' \<in> {-2<..<-1}"
    have "eventually (\<lambda>x. (ln x + c' * ln (ln x)) * exp (ln x + c' * ln (ln x)) \<le> x) at_top"
         "eventually (\<lambda>x. ln x + c' * ln (ln x) \<ge> -1) at_top"
      using c' by real_asymp+
    thus "eventually (\<lambda>x. Lambert_W x - ln x \<ge> c' * ln (ln x)) at_top"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<ge> ln x + c' * ln (ln x)"
        by (intro Lambert_W_geI)
      thus ?case by simp
    qed
  next
    fix c' :: real assume c': "c' \<in> {-1<..<0}"
    have "eventually (\<lambda>x. (ln x + c' * ln (ln x)) * exp (ln x + c' * ln (ln x)) \<ge> x) at_top"
         "eventually (\<lambda>x. ln x + c' * ln (ln x) \<ge> -1) at_top"
      using c' by real_asymp+
    thus "eventually (\<lambda>x. Lambert_W x - ln x \<le> c' * ln (ln x)) at_top"
      using eventually_ge_at_top[of "-exp (-1)"]
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<le> ln x + c' * ln (ln x)"
        by (intro Lambert_W_leI)
      thus ?case by simp
    qed
  qed auto
  thus ?thesis by simp
qed

lemma Lambert_W_asymp_equiv_at_top' [asymp_equiv_intros]:
  "Lambert_W \<sim>[at_top] ln"
proof -
  have "(\<lambda>x. Lambert_W x - ln x) \<in> \<Theta>(\<lambda>x. -ln (ln x))"
    by (intro asymp_equiv_imp_bigtheta Lambert_W_asymp_equiv_at_top)
  also have "(\<lambda>x::real. -ln (ln x)) \<in> o(ln)"
    by real_asymp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed

theorem Lambert_W'_asymp_equiv_at_left_0:
  "(\<lambda>x. Lambert_W' x - ln (-x)) \<sim>[at_left 0] (\<lambda>x. -ln (-ln (-x)))"
proof -
  have "(\<lambda>x. Lambert_W' x - ln (-x)) \<sim>[at_left 0] (\<lambda>x. (-1) * ln (-ln (-x)))"
  proof (rule asymp_equiv_sandwich')
    fix c' :: real assume c': "c' \<in> {-2<..<-1}"
    have "eventually (\<lambda>x. x \<le> (ln (-x) + c' * ln (-ln (-x))) * exp (ln (-x) + c' * ln (-ln (-x)))) (at_left 0)"
         "eventually (\<lambda>x::real. ln (-x) + c' * ln (-ln (-x)) \<le> -1) (at_left 0)"
         "eventually (\<lambda>x::real. -exp (-1) \<le> x) (at_left 0)"
      using c' by real_asymp+
    thus "eventually (\<lambda>x. Lambert_W' x - ln (-x) \<ge> c' * ln (-ln (-x))) (at_left 0)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W' x \<ge> ln (-x) + c' * ln (-ln (-x))"
        by (intro Lambert_W'_geI)
      thus ?case by simp
    qed
  next
    fix c' :: real assume c': "c' \<in> {-1<..<0}"
    have "eventually (\<lambda>x. x \<ge> (ln (-x) + c' * ln (-ln (-x))) * exp (ln (-x) + c' * ln (-ln (-x)))) (at_left 0)"
      using c' by real_asymp
    moreover have "eventually (\<lambda>x::real. x < 0) (at_left 0)"
      by (auto simp: eventually_at intro: exI[of _ 1])
    ultimately show "eventually (\<lambda>x. Lambert_W' x - ln (-x) \<le> c' * ln (-ln (-x))) (at_left 0)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W' x \<le> ln (-x) + c' * ln (-ln (-x))"
        by (intro Lambert_W'_leI)
      thus ?case by simp
    qed
  qed auto
  thus ?thesis by simp
qed

lemma Lambert_W'_asymp_equiv'_at_left_0 [asymp_equiv_intros]:
  "Lambert_W' \<sim>[at_left 0] (\<lambda>x. ln (-x))"
proof -
  have "(\<lambda>x. Lambert_W' x - ln (-x)) \<in> \<Theta>[at_left 0](\<lambda>x. -ln (-ln (-x)))"
    by (intro asymp_equiv_imp_bigtheta Lambert_W'_asymp_equiv_at_left_0)
  also have "(\<lambda>x::real. -ln (-ln (-x))) \<in> o[at_left 0](\<lambda>x. ln (-x))"
    by real_asymp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed


text \<open>
  Next, we look at the branching point $a := \tfrac{1}{e}$. Here, the asymptotic behaviour
  is as follows:
  \begin{align*}
    W(x) &= -1 + \sqrt{2e}(x - a)^{\frac{1}{2}} - \tfrac{2}{3}e(x-a) + o(x-a) &&\text{for} x\to a^+\\
    W'(x) &= -1 - \sqrt{2e}(x - a)^{\frac{1}{2}} - \tfrac{2}{3}e(x-a) + o(x-a) &&\text{for} x\to a^+
  \end{align*}
\<close>
lemma sqrt_sqrt_mult:
  assumes "x \<ge> (0 :: real)"
  shows   "sqrt x * (sqrt x * y) = x * y"
  using assms by (subst mult.assoc [symmetric]) auto

theorem Lambert_W_asymp_equiv_at_right_minus_exp_minus1:
  defines "e \<equiv> exp 1"
  defines "a \<equiv> -exp (-1)"
  defines "C1 \<equiv> sqrt (2 * exp 1)"
  defines "f \<equiv> (\<lambda>x. -1 + C1 * sqrt (x - a))"
  shows   "(\<lambda>x. Lambert_W x - f x) \<sim>[at_right a] (\<lambda>x. -2/3 * e * (x - a))"
proof -
  define C :: "real \<Rightarrow> real" where "C = (\<lambda>c. sqrt (2/e)/3 * (2*e+3*c))"
  have asymp_equiv: "(\<lambda>x. (f x + c * (x - a)) * exp (f x + c * (x - a)) - x)
                       \<sim>[at_right a] (\<lambda>x. C c * (x - a) powr (3/2))" if "c \<noteq> -2/3 * e" for c
  proof -
    from that have "C c \<noteq> 0"
      by (auto simp: C_def e_def)
    have "(\<lambda>x. (f x + c * (x - a)) * exp (f x + c * (x - a)) - x - C c * (x - a) powr (3/2))
            \<in> o[at_right a](\<lambda>x. (x - a) powr (3/2))"
      unfolding f_def a_def C_def C1_def e_def
      by (real_asymp simp: field_simps real_sqrt_mult real_sqrt_divide sqrt_sqrt_mult
                           exp_minus simp flip: sqrt_def)
    thus ?thesis
      using \<open>C c \<noteq> 0\<close> by (intro smallo_imp_asymp_equiv) auto
  qed
      
  show ?thesis
  proof (rule asymp_equiv_sandwich')
    fix c' :: real assume c': "c' \<in> {-e<..<-2/3*e}"
    hence neq: "c' \<noteq> -2/3 * e" by auto
    from c' have neg: "C c' < 0" unfolding C_def by (auto intro!: mult_pos_neg)
    hence "eventually (\<lambda>x. C c' * (x - a) powr (3 / 2) < 0) (at_right a)"
      by real_asymp
    hence "eventually (\<lambda>x. (f x + c' * (x - a)) * exp (f x + c' * (x - a)) - x < 0) (at_right a)"
      using asymp_equiv_eventually_neg_iff[OF asymp_equiv[OF neq]]
      by eventually_elim (use neg in auto)
    thus "eventually (\<lambda>x. Lambert_W x - f x \<ge> c' * (x - a)) (at_right a)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<ge> f x + c' * (x - a)"
        by (intro Lambert_W_geI) auto
      thus ?case by simp
    qed
  next
    fix c' :: real assume c': "c' \<in> {-2/3*e<..<0}"
    hence neq: "c' \<noteq> -2/3 * e" by auto
    from c' have pos: "C c' > 0" unfolding C_def by auto
    hence "eventually (\<lambda>x. C c' * (x - a) powr (3 / 2) > 0) (at_right a)"
      by real_asymp
    hence "eventually (\<lambda>x. (f x + c' * (x - a)) * exp (f x + c' * (x - a)) - x > 0) (at_right a)"
      using asymp_equiv_eventually_pos_iff[OF asymp_equiv[OF neq]]
      by eventually_elim (use pos in auto)
    moreover have "eventually (\<lambda>x. - 1 \<le> f x + c' * (x - a)) (at_right a)"
                  "eventually (\<lambda>x. x > a) (at_right a)"
      unfolding a_def f_def C1_def c' by real_asymp+
    ultimately show "eventually (\<lambda>x. Lambert_W x - f x \<le> c' * (x - a)) (at_right a)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<le> f x + c' * (x - a)"
        by (intro Lambert_W_leI) (auto simp: a_def)
      thus ?case by simp
    qed
  qed (auto simp: e_def)
qed

theorem Lambert_W'_asymp_equiv_at_right_minus_exp_minus1:
  defines "e \<equiv> exp 1"
  defines "a \<equiv> -exp (-1)"
  defines "C1 \<equiv> sqrt (2 * exp 1)"
  defines "f \<equiv> (\<lambda>x. -1 - C1 * sqrt (x - a))"
  shows   "(\<lambda>x. Lambert_W' x - f x) \<sim>[at_right a] (\<lambda>x. -2/3 * e * (x - a))"
proof -
  define C :: "real \<Rightarrow> real" where "C = (\<lambda>c. -sqrt (2/e)/3 * (2*e+3*c))"

  have asymp_equiv: "(\<lambda>x. (f x + c * (x - a)) * exp (f x + c * (x - a)) - x)
                       \<sim>[at_right a] (\<lambda>x. C c * (x - a) powr (3/2))" if "c \<noteq> -2/3 * e" for c
  proof -
    from that have "C c \<noteq> 0"
      by (auto simp: C_def e_def)
    have "(\<lambda>x. (f x + c * (x - a)) * exp (f x + c * (x - a)) - x - C c * (x - a) powr (3/2))
            \<in> o[at_right a](\<lambda>x. (x - a) powr (3/2))"
      unfolding f_def a_def C_def C1_def e_def
      by (real_asymp simp: field_simps real_sqrt_mult real_sqrt_divide sqrt_sqrt_mult
                           exp_minus simp flip: sqrt_def)
    thus ?thesis
      using \<open>C c \<noteq> 0\<close> by (intro smallo_imp_asymp_equiv) auto
  qed
      
  show ?thesis
  proof (rule asymp_equiv_sandwich')
    fix c' :: real assume c': "c' \<in> {-e<..<-2/3*e}"
    hence neq: "c' \<noteq> -2/3 * e" by auto
    from c' have pos: "C c' > 0" unfolding C_def by (auto intro!: mult_pos_neg)
    hence "eventually (\<lambda>x. C c' * (x - a) powr (3 / 2) > 0) (at_right a)"
      by real_asymp
    hence "eventually (\<lambda>x. (f x + c' * (x - a)) * exp (f x + c' * (x - a)) - x > 0) (at_right a)"
      using asymp_equiv_eventually_pos_iff[OF asymp_equiv[OF neq]]
      by eventually_elim (use pos in auto)
    moreover have "eventually (\<lambda>x. x > a) (at_right a)"
                  "eventually (\<lambda>x. f x + c' * (x - a) \<le> -1) (at_right a)"
      unfolding a_def f_def C1_def c' by real_asymp+
    ultimately show "eventually (\<lambda>x. Lambert_W' x - f x \<ge> c' * (x - a)) (at_right a)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W' x \<ge> f x + c' * (x - a)"
        by (intro Lambert_W'_geI) (auto simp: a_def)
      thus ?case by simp
    qed
  next
    fix c' :: real assume c': "c' \<in> {-2/3*e<..<0}"
    hence neq: "c' \<noteq> -2/3 * e" by auto
    from c' have neg: "C c' < 0" unfolding C_def by auto
    hence "eventually (\<lambda>x. C c' * (x - a) powr (3 / 2) < 0) (at_right a)"
      by real_asymp
    hence "eventually (\<lambda>x. (f x + c' * (x - a)) * exp (f x + c' * (x - a)) - x < 0) (at_right a)"
      using asymp_equiv_eventually_neg_iff[OF asymp_equiv[OF neq]]
      by eventually_elim (use neg in auto)
    moreover have "eventually (\<lambda>x. x < 0) (at_right a)"
      unfolding a_def by real_asymp
    ultimately show "eventually (\<lambda>x. Lambert_W' x - f x \<le> c' * (x - a)) (at_right a)"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W' x \<le> f x + c' * (x - a)"
        by (intro Lambert_W'_leI) auto
      thus ?case by simp
    qed
  qed (auto simp: e_def)
qed


text \<open>
  Lastly, just for fun, we derive a slightly more accurate expansion of $W_0(x)$ for $x\to\infty$:
\<close>
theorem Lambert_W_asymp_equiv_at_top'':
  "(\<lambda>x. Lambert_W x - ln x + ln (ln x)) \<sim>[at_top] (\<lambda>x. ln (ln x) / ln x)"
proof -
  have "(\<lambda>x. Lambert_W x - ln x + ln (ln x)) \<sim>[at_top] (\<lambda>x. 1 * (ln (ln x) / ln x))"
  proof (rule asymp_equiv_sandwich')
    fix c' :: real assume c': "c' \<in> {0<..<1}"
    define a where "a = (\<lambda>x::real. ln x - ln (ln x) + c' * (ln (ln x) / ln x))"
    have "eventually (\<lambda>x. a x * exp (a x) \<le> x) at_top"
      using c' unfolding a_def by real_asymp+
    thus "eventually (\<lambda>x. Lambert_W x - ln x + ln (ln x) \<ge> c' * (ln (ln x) / ln x)) at_top"
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<ge> a x"
        by (intro Lambert_W_geI)
      thus ?case by (simp add: a_def)
    qed
  next
    fix c' :: real assume c': "c' \<in> {1<..<2}"
    define a where "a = (\<lambda>x::real. ln x - ln (ln x) + c' * (ln (ln x) / ln x))"
    have "eventually (\<lambda>x. a x * exp (a x) \<ge> x) at_top"
         "eventually (\<lambda>x. a x \<ge> -1) at_top"
      using c' unfolding a_def by real_asymp+
    thus "eventually (\<lambda>x. Lambert_W x - ln x + ln (ln x) \<le> c' * (ln (ln x) / ln x)) at_top"
      using eventually_ge_at_top[of "-exp (-1)"]
    proof eventually_elim
      case (elim x)
      hence "Lambert_W x \<le> a x"
        by (intro Lambert_W_leI)
      thus ?case by (simp add: a_def)
    qed
  qed auto
  thus ?thesis by simp
qed

end