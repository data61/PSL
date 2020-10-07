(*
  File:     Newman_Ingham_Tauberian.thy
  Author:   Manuel Eberl (TU München)

  A proof of Newman's "analytic theorem", originally stated by Ingham
*)
section \<open>Ingham's Tauberian Theorem\<close>
theory Newman_Ingham_Tauberian
imports
  "HOL-Real_Asymp.Real_Asymp"
  Prime_Number_Theorem_Library
begin

text \<open>
  In his proof of the Prime Number Theorem, Newman~\cite{newman1998analytic} uses a Tauberian 
  theorem that was first proven by Ingham. Newman gives a nice and straightforward proof of this
  theorem based on contour integration. This section will be concerned with proving this theorem.
  
  This Tauberian theorem is probably the part of the Newman's proof of the Prime Number Theorem
  where most of the ``heavy lifting'' is done. Its purpose is to extend the summability of a 
  Dirichlet series with bounded coefficients from the region $\mathfrak{R}(s)>1$ to 
  $\mathfrak{R}(s)\geq 1$.

  In order to show it, we first require a number of auxiliary bounding lemmas.
\<close>
lemma newman_ingham_aux1:
  fixes R :: real and z :: complex
  assumes R: "R > 0" and z : "norm z = R"
  shows   "norm (1 / z + z / R\<^sup>2) = 2 * \<bar>Re z\<bar> / R\<^sup>2"
proof -
  from z and R have [simp]: "z \<noteq> 0" by auto
  have "1 / z + z / R\<^sup>2 = (R\<^sup>2 + z\<^sup>2) * (1 / R\<^sup>2 / z)" using R
    by (simp add: field_simps power2_eq_square)
  also have "norm \<dots> = norm (R\<^sup>2 + z\<^sup>2) / R ^ 3"
    by (simp add: numeral_3_eq_3 z norm_divide norm_mult power2_eq_square)
  also have "R\<^sup>2 + z\<^sup>2 = z * (z + cnj z)" using complex_norm_square[of z]
    by (simp add: z power2_eq_square algebra_simps)
  also have "norm \<dots> = 2 * \<bar>Re z\<bar> * R"
    by (subst complex_add_cnj) (simp_all add: z norm_mult)
  also have "\<dots> / R ^ 3 = 2 * \<bar>Re z\<bar> / R\<^sup>2"
    using R by (simp add: field_simps numeral_3_eq_3 power2_eq_square)
  finally show ?thesis .
qed

lemma newman_ingham_aux2:
  fixes m :: nat and w z :: complex
  assumes "1 \<le> m" "1 \<le> Re w" "0 < Re z" and f: "\<And>n. 1 \<le> n \<Longrightarrow> norm (f n) \<le> C"
  shows "norm (\<Sum>n=1..m. f n / n powr (w - z)) \<le> C * (m powr Re z) * (1 / m + 1 / Re z)"
proof -
  have [simp]: "C \<ge> 0" by (rule order.trans[OF _ f[of 1]]) auto
  have "norm (\<Sum>n=1..m. f n / n powr (w - z)) \<le> (\<Sum>n=1..m. C / n powr (1 - Re z))"
    by (rule sum_norm_le)
       (insert assms, auto simp: norm_divide norm_powr_real_powr intro!: frac_le assms powr_mono)
  also have "\<dots> = C * (\<Sum>n=1..m. n powr (Re z - 1))"
    by (subst sum_distrib_left) (simp_all add: powr_diff)
  also have "\<dots> \<le> C * (m powr Re z * (1 / Re z + 1 / m))"
    using zeta_partial_sum_le'[of "Re z" m] assms by (intro mult_left_mono) auto
  finally show ?thesis by (simp add: mult_ac add_ac)
qed

lemma hurwitz_zeta_real_bound_aux:
  fixes a x :: real
  assumes ax: "a > 0" "x > 1"
  shows "(\<Sum>i. (a + real (Suc i)) powr (-x)) \<le> a powr (1 - x) / (x - 1)"
proof (rule decreasing_sum_le_integral, goal_cases)
  have "((\<lambda>t. (a + t) powr -x) has_integral -(a powr (-x + 1)) / (-x + 1)) (interior {0..})"
    using powr_has_integral_at_top[of 0 a "-x"] using ax by (simp add: interior_real_atLeast)
  also have "-(a powr (- x + 1)) / (- x + 1) = a powr (1 - x) / (x - 1)"
    using ax by (simp add: field_simps)
  finally show "((\<lambda>t. (a + t) powr -x) has_integral a powr (1 - x) / (x - 1)) {0..}"
    by (subst (asm) has_integral_interior) auto
qed (insert ax, auto intro!: powr_mono2')


text \<open>
  Given a function that is analytic on some vertical line segment, we can find a rectangle
  around that line segment on which the function is also analytic.
\<close>
lemma analytic_on_axis_extend:
  fixes y1 y2 x :: real
  defines "S \<equiv> {z. Re z = x \<and> Im z \<in> {y1..y2}}"
  assumes "y1 \<le> y2"
  assumes "f analytic_on S"
  obtains x1 x2 :: real where "x1 < x" "x2 > x" "f analytic_on cbox (Complex x1 y1) (Complex x2 y2)"
proof -
  define C where "C = {box a b |a b z. f analytic_on box a b \<and> z \<in> box a b \<and> z \<in> S}"
  have "S = cbox (Complex x y1) (Complex x y2)"
    by (auto simp: S_def in_cbox_complex_iff)
  also have "compact \<dots>" by simp
  finally have 1: "compact S" .

  have 2: "S \<subseteq> \<Union>C"
  proof (intro subsetI)
    fix z assume "z \<in> S"
    from \<open>f analytic_on S\<close> and this obtain a b where "z \<in> box a b" "f analytic_on box a b"
      by (blast elim: analytic_onE_box)
    with \<open>z \<in> S\<close> show "z \<in> \<Union>C" unfolding C_def by blast
  qed

  have 3: "open X" if "X \<in> C" for X using that by (auto simp: C_def)
  from compactE[OF 1 2 3] obtain T where T: "T \<subseteq> C" "finite T" "S \<subseteq> \<Union>T"
    by blast

  define x1 where "x1 = Max (insert (x - 1) ((\<lambda>X. x + (Inf (Re ` X) - x) / 2) ` T))"
  define x2 where "x2 = Min (insert (x + 1) ((\<lambda>X. x + (Sup (Re ` X) - x) / 2) ` T))"

  have *: "x + (Inf (Re ` X) - x) / 2 < x \<and> x + (Sup (Re ` X) - x) / 2 > x" if "X \<in> T" for X
  proof -
    from that and T obtain a b s where [simp]: "X = box a b" and s: "s \<in> box a b" "s \<in> S"
      by (force simp: C_def)
    hence le: "Re a < Re b" "Im a < Im b" by (auto simp: in_box_complex_iff)
    show ?thesis using le s
      unfolding \<open>X = box a b\<close> Re_image_box[OF le] Im_image_box[OF le]
      by (auto simp: S_def in_box_complex_iff)
  qed
  from * T have "x1 < x" unfolding x1_def by (subst Max_less_iff) auto
  from * T have "x2 > x" unfolding x2_def by (subst Min_gr_iff) auto

  have "f analytic_on (\<Union>T)"
    using T by (subst analytic_on_Union) (auto simp: C_def)
  moreover have "z \<in> \<Union>T" if "z \<in> cbox (Complex x1 y1) (Complex x2 y2)" for z
  proof -
    from that have "Complex x (Im z) \<in> S"
      by (auto simp: in_cbox_complex_iff S_def)
    with T obtain X where X: "X \<in> T" "Complex x (Im z) \<in> X"
      by auto
    with T obtain a b where [simp]: "X = box a b" by (auto simp: C_def)
    from X have le: "Re a < Re b" "Im a < Im b" by (auto simp: in_box_complex_iff)

    from that have "Re z \<le> x2" by (simp add: in_cbox_complex_iff)
    also have "\<dots> \<le> x + (Sup (Re ` X) - x) / 2"
      unfolding x2_def by (rule Min.coboundedI)(use T X in auto)
    also have "\<dots> = (x + Re b) / 2"
      using le unfolding \<open>X = box a b\<close> Re_image_box[OF le] by (simp add: field_simps)
    also have "\<dots> < (Re b + Re b) / 2"
      using X by (intro divide_strict_right_mono add_strict_right_mono)
                 (auto simp: in_box_complex_iff)
    also have "\<dots> = Re b" by simp
    finally have [simp]: "Re z < Re b" .

    have "Re a = (Re a + Re a) / 2" by simp
    also have "\<dots> < (x + Re a) / 2"
      using X by (intro divide_strict_right_mono add_strict_right_mono)
                 (auto simp: in_box_complex_iff)
    also have "\<dots> = x + (Inf (Re ` X) - x) / 2"
      using le unfolding \<open>X = box a b\<close> Re_image_box[OF le] by (simp add: field_simps)
    also have "\<dots> \<le> x1" unfolding x1_def by (rule Max.coboundedI)(use T X in auto)
    also have "\<dots> \<le> Re z" using that by (simp add: in_cbox_complex_iff)
    finally have [simp]: "Re z > Re a" .

    from X have "z \<in> X" by (simp add: in_box_complex_iff)
    with T X show ?thesis by blast
  qed
  hence "cbox (Complex x1 y1) (Complex x2 y2) \<subseteq> \<Union>T" by blast
  ultimately have "f analytic_on cbox (Complex x1 y1) (Complex x2 y2)"
    by (rule analytic_on_subset)

  with \<open>x1 < x\<close> and \<open>x2 > x\<close> and that[of x1 x2] show ?thesis by blast
qed


text \<open>
  We will now prove the theorem. The precise setting is this:
  Consider a Dirichlet series $F(s) = \sum a_n n^{-s}$ with bounded coefficients. Clearly,
  this converges to an analytic function $f(s)$ on $\{s\mid \mathfrak R(s)>1\}$.

  If $f(s)$ is analytic on the larger set $\{s\mid \mathfrak R(s)\geq 1\}$, $F$ converges
  to $f(s)$ for all $\mathfrak R(s) \geq 1$.

  The proof follows Newman's argument very closely, but some of the precise bounds we use
  are a bit different from his. Also, like Harrison, we choose a combination of a semicircle
  and a rectangle as our contour, whereas Newman uses a circle with a vertical cut-off. The result
  of the Residue theorem is the same in both cases, but the bounding of the contributions of the
  different parts is somewhat different.

  The reason why we picked Harrison's contour over Newman's is because we could not understand how
  his bounding of the different contributions fits to his contour, and it seems likely that this
  is also the reason why Harrison altered the contour in the first place.
\<close>
lemma Newman_Ingham_1:
  fixes F :: "complex fds" and f :: "complex \<Rightarrow> complex"
  assumes coeff_bound:   "fds_nth F \<in> O(\<lambda>_. 1)"
  assumes f_analytic:    "f analytic_on {s. Re s \<ge> 1}"
  assumes F_conv_f:      "\<And>s. Re s > 1 \<Longrightarrow> eval_fds F s = f s"
  assumes w:             "Re w \<ge> 1"
  shows   "fds_converges F w" and "eval_fds F w = f w"
proof -
  \<comment> \<open>We get a bound on our coefficients and call it \<open>C\<close>.\<close>
  obtain C where C: "C \<ge> 1" "\<And>n. norm (fds_nth F n) \<le> C"
    using natfun_bigo_1E[OF coeff_bound, where lb = 1] by blast
  write contour_integral ("\<ointegral>[_]")

  \<comment> \<open>We show convergence directly by showing that the difference between the 
      partial sums and the limit vanishes.\<close>
  have "(\<lambda>N. eval_fds (fds_truncate N F) w) \<longlonglongrightarrow> f w"
    unfolding tendsto_iff dist_norm norm_minus_commute[of "eval_fds F s" for F s]
  proof safe
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    \<comment> \<open>We choose an integration radius that is big enough for the error to be sufficiently small.\<close>
    define R where "R = max 1 (3 * C / \<epsilon>)"
    have R: "R \<ge> 3 * C / \<epsilon>" "R \<ge> 1" by (auto simp: R_def)

    \<comment> \<open>Next, we extend the analyticity of \<open>f (w + z)\<close> to the left of the complex plane
        within a thin rectangle that is at least as high as the circle.\<close>
    obtain l where l: "l > 0"
      "(\<lambda>z. f (w + z)) analytic_on {s. Re s > 0 \<or> Im s \<in> {-R-1<..<R+1} \<and> Re s > -l}"
    proof -
      have f_analytic': "(\<lambda>z. f (w + z)) analytic_on {s. Re s \<ge> 0}"
        by (rule analytic_on_compose_gen[OF _ f_analytic, unfolded o_def])
           (insert w, auto intro: analytic_intros)
      hence "(\<lambda>z. f (w + z)) analytic_on {s. Re s = 0 \<and> Im s \<in> {-R-1..R+1}}"
        by (rule analytic_on_subset) auto
      from analytic_on_axis_extend[OF _ this] obtain x1 x2 where x12: 
        "x1 < 0" "x2 > 0" "(\<lambda>z. f (w + z)) analytic_on cbox (Complex x1 (-R-1)) (Complex x2 (R+1))"
        using \<open>R \<ge> 1\<close> by auto
      from this(3) have "(\<lambda>z. f (w + z)) analytic_on {s. Re s \<in> {x1..0} \<and> Im s \<in> {-R-1..R+1}}"
        by (rule analytic_on_subset) (insert x12, auto simp: in_cbox_complex_iff)
      with f_analytic' have "(\<lambda>z. f (w + z)) analytic_on
                               ({s. Re s \<ge> 0} \<union> {s. Re s \<in> {x1..0} \<and> Im s \<in> {-R-1..R+1}})"
        by (subst analytic_on_Un) auto
      hence "(\<lambda>z. f (w + z)) analytic_on {s. Re s > 0 \<or> Im s \<in> {-R-1<..<R+1} \<and> Re s > x1}"
        by (rule analytic_on_subset) auto
      with \<open>x1 < 0\<close> and that[of "-x1"] show ?thesis by auto
    qed

    \<comment> \<open>The function \<open>f (w + z)\<close> is now analytic on the open box $(-l; R+1) + i(-R+1; R+1)$.
        We call this region \<open>X\<close>.\<close>
    define X where "X = box (Complex (-l) (-R-1)) (Complex (R+1) (R+1))"
    have [simp, intro]: "open X" "convex X" by (simp_all add: X_def open_box)
    from R l have [simp]: "0 \<in> X" by (auto simp: X_def in_box_complex_iff)
    have analytic: "(\<lambda>z. f (w + z)) analytic_on X"
      by (rule analytic_on_subset[OF l(2)]) (auto simp: X_def in_box_complex_iff)
    note f_analytic' [analytic_intros] = analytic_on_compose_gen[OF _ analytic, unfolded o_def]
    note f_holo [holomorphic_intros] =
      holomorphic_on_compose_gen[OF _ analytic_imp_holomorphic[OF analytic], unfolded o_def]
    note f_cont [continuous_intros] = continuous_on_compose2[OF 
      holomorphic_on_imp_continuous_on[OF analytic_imp_holomorphic[OF analytic]]]

    \<comment> \<open>We now pick a smaller closed box \<open>X'\<close> inside the big open box \<open>X\<close>. This is because
        we need a compact set for the next step. our integration path still lies entirely
        within \<open>X'\<close>, and since \<open>X'\<close> is compact, \<open>f (w + z)\<close> is bounded on it,
        so we obtain such a bound and call it \<open>M\<close>.\<close>
    define \<delta> where "\<delta> = min (1/2) (l/2)"
    from l have \<delta>: "\<delta> > 0" "\<delta> \<le> 1/2" "\<delta> < l" by (auto simp: \<delta>_def)
    define X' where "X' = cbox (Complex (-\<delta>) (-R)) (Complex R R)"
    have "X' \<subseteq> X" unfolding X'_def X_def using l(1) R \<delta>
      by (intro subset_box_imp) (auto simp: Basis_complex_def)
    have [intro]: "compact X'" by (simp add: X'_def)
    moreover have "continuous_on X' (\<lambda>z. f (w + z))"
      using w \<open>X' \<subseteq> X\<close> by (auto intro!: continuous_intros)
    ultimately obtain M where M: "M \<ge> 0" "\<And>z. z \<in> X' \<Longrightarrow> norm (f (w + z)) \<le> M"
      using continuous_on_compact_bound by blast

    \<comment> \<open>Our objective is now to show that the difference between the \<open>N\<close>-th partial sum
        and the limit is below a certain bound (depending on \<open>N\<close>) which tends to \<open>0\<close> 
        for \<open>N \<rightarrow> \<infinity>\<close>. We use the following bound:\<close>
    define bound where
      "bound = (\<lambda>N::nat. (2*C/R + C/N + 3*M / (pi*R*ln N) + 3*R*M / (\<delta>*pi * N powr \<delta>)))"
    have "2 * C / R < \<epsilon>" using M(1) R C(1) \<delta>(1) \<epsilon>
      by (auto simp: field_simps)
    \<comment> \<open>Evidently this is below @{term \<epsilon>} for sufficiently large \<open>N\<close>.\<close>
    hence "eventually (\<lambda>N::nat. bound N < \<epsilon>) at_top"
      using M(1) R C(1) \<delta>(1) \<epsilon> unfolding bound_def by real_asymp

    \<comment> \<open>It now only remains to show that the difference is indeed less than the claimed bound.\<close>
    thus "eventually (\<lambda>N. norm (f w - eval_fds (fds_truncate N F) w) < \<epsilon>) at_top"
      using eventually_gt_at_top[of 1]
    proof eventually_elim
      case (elim N)
      note N = this

      \<comment> \<open>Like Harrison (and unlike Newman), our integration path \<open>\<Gamma>\<close> consists of a semicircle \<open>A\<close>
          of radius \<open>R\<close> in the right-halfplane and a box of width \<open>\<delta>\<close> and height \<open>2R\<close> on
          the left halfplane. The latter consists of three straight lines, which we call \<open>B1\<close>
          to \<open>B3\<close>.\<close>
      define A where "A = part_circlepath 0 R (-pi/2) (pi/2)"
      define B2 where "B2 = linepath (Complex (-\<delta>) R) (Complex (-\<delta>) (-R))"
      define B1 where "B1 = linepath (R * \<i>) (R * \<i> - \<delta>)"
      define B3 where "B3 = linepath (-R * \<i> - \<delta>) (-R * \<i>)"
      define \<Gamma> where "\<Gamma> = A +++ B1 +++ B2 +++ B3"

      \<comment> \<open>We first need to show some basic facts about the geometry of our integration path.\<close>
      have [simp, intro]:
        "path A" "path B1" "path B3" "path B2"
        "valid_path A" "valid_path B1" "valid_path B3" "valid_path B2"
        "arc A" "arc B1" "arc B3" "arc B2"
        "pathstart A = -\<i> * R" "pathfinish A = \<i> * R"
        "pathstart B1 = \<i> * R" "pathfinish B1 = R * \<i> - \<delta>"
        "pathstart B3 = -R * \<i> - \<delta>" "pathfinish B3 = -\<i> * R"
        "pathstart B2 = R * \<i> - \<delta>" "pathfinish B2 = -R * \<i> - \<delta>" using R \<delta>
        by (simp_all add: A_def B1_def B3_def exp_eq_polar B2_def Complex_eq arc_part_circlepath)
      hence [simp, intro]: "valid_path \<Gamma>" 
        by (simp add: \<Gamma>_def A_def B1_def B3_def B2_def exp_eq_polar Complex_eq)
      hence [simp, intro]: "path \<Gamma>" using valid_path_imp_path by blast
      have [simp]: "pathfinish \<Gamma> = pathstart \<Gamma>" by (simp add: \<Gamma>_def exp_eq_polar)
    
      have image_B2: "path_image B2 = {s. Re s = -\<delta> \<and> Im s \<in> {-R..R}}"
        using R by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl B2_def)
      have image_B1: "path_image B1 = {s. Re s \<in> {-\<delta>..0} \<and> Im s = R}"
       and image_B3: "path_image B3 = {s. Re s \<in> {-\<delta>..0} \<and> Im s = -R}"
        using \<delta> by (auto simp: B1_def B3_def closed_segment_same_Im closed_segment_eq_real_ivl)
      have image_A: "path_image A = {s. Re s \<ge> 0 \<and> norm s = R}"
        unfolding A_def using R by (subst path_image_semicircle_Re_ge) auto
      also have "z \<in> \<dots> \<longrightarrow> z \<in> X' - {0}" for z
        using complex_Re_le_cmod[of z] abs_Im_le_cmod[of z] \<delta> R
        by (auto simp: X'_def in_cbox_complex_iff)
      hence "{s. Re s \<ge> 0 \<and> norm s = R} \<subseteq> X' - {0}" by auto
      finally have "path_image B2 \<subseteq> X' - {0}" "path_image A \<subseteq> X' - {0}"
           "path_image B1 \<subseteq> X' - {0}" "path_image B3 \<subseteq> X' - {0}" using \<open>\<delta> > 0\<close>
        by (auto simp: X'_def in_cbox_complex_iff image_B2 image_B1 image_B3)
      note path_images = this \<open>X' \<subseteq> X\<close>

      \<comment> \<open>\<open>\<Gamma>\<close> is a simple path, which, combined with its simple geometric shape, makes
          reasoning about its winding numbers trivial.\<close>
      from R have "simple_path A" unfolding A_def
        by (subst simple_path_part_circlepath) auto
      have "simple_path \<Gamma>" unfolding \<Gamma>_def
      proof (intro simple_path_join_loop subsetI arc_join, goal_cases)
        fix z assume z: "z \<in> path_image A \<inter> path_image (B1 +++ B2 +++ B3)"
        with image_A have "Re z \<ge> 0" "norm z = R" by auto
        with z R \<delta> show "z \<in> {pathstart A, pathstart (B1 +++ B2 +++ B3)}"
          by (auto simp: path_image_join image_B1 image_B2 image_B3 complex_eq_iff)
      qed (insert R, auto simp: image_B1 image_B3 path_image_join image_B2 complex_eq_iff)
    
      \<comment> \<open>We define the integrands in the same fashion as Newman:\<close>
      define g where "g = (\<lambda>z::complex. f (w + z) * N powr z * (1 / z + z / R\<^sup>2))"
      define S where "S = eval_fds (fds_truncate N F)"
      define g_S where "g_S = (\<lambda>z::complex. S (w + z) * N powr z * (1 / z + z / R\<^sup>2))"
      define rem where "rem = (\<lambda>z::complex. f z - S z)"
      define g_rem where "g_rem = (\<lambda>z::complex. rem (w + z) * N powr z * (1 / z + z / R\<^sup>2))"

      have g_holo: "g holomorphic_on X - {0}" unfolding g_def
        by (auto intro!: holomorphic_intros analytic_imp_holomorphic'[OF analytic])

      have rem_altdef: "rem z = eval_fds (fds_remainder N F) z" if "Re z > 1" for z
      proof -
      have abscissa: "abs_conv_abscissa F \<le> 1"
        using assms by (intro bounded_coeffs_imp_abs_conv_abscissa_le_1)
                       (simp_all add: natfun_bigo_iff_Bseq)
        from assms and that have "f z = eval_fds F z" by auto
        also have "F = fds_truncate N F + fds_remainder N F" 
          by (rule fds_truncate_plus_remainder [symmetric])
        also from that have "eval_fds \<dots> z = S z + eval_fds (fds_remainder N F) z" unfolding S_def
          by (subst eval_fds_add) (auto intro!: fds_abs_converges_imp_converges 
                                                fds_abs_converges[OF le_less_trans[OF abscissa]])
        finally show ?thesis by (simp add: rem_def)
      qed

      \<comment> \<open>We now come to the first application of the residue theorem along the path \<open>\<Gamma>\<close>:\<close>
      have "\<ointegral>[\<Gamma>] g = 2 * pi * \<i> * winding_number \<Gamma> 0 * residue g 0"
      proof (subst Residue_theorem)
        show "g holomorphic_on X - {0}" by fact
        show "path_image \<Gamma> \<subseteq> X - {0}" using path_images
          by (auto simp: \<Gamma>_def path_image_join)
        thus "\<forall>z. z \<notin> X \<longrightarrow> winding_number \<Gamma> z = 0"
          by (auto intro!: simply_connected_imp_winding_number_zero[of X]
                           convex_imp_simply_connected)
      qed (insert path_images, auto intro: convex_connected)
      also have "winding_number \<Gamma> 0 = 1"
      proof (rule simple_closed_path_winding_number_pos)
        from R \<delta> have "\<forall>g\<in>{A, B1, B2, B3}. Re (winding_number g 0) > 0"
          unfolding A_def B1_def B2_def B3_def
          by (auto intro!: winding_number_linepath_pos_lt winding_number_part_circlepath_pos_less)
        hence "valid_path \<Gamma> \<and> 0 \<notin> path_image \<Gamma> \<and> Re (winding_number \<Gamma> 0) > 0"
          unfolding \<Gamma>_def using path_images(1-4) by (intro winding_number_join_pos_combined') auto
        thus "Re (winding_number \<Gamma> 0) > 0" by simp
      qed (insert path_images \<open>simple_path \<Gamma>\<close>, auto simp: \<Gamma>_def path_image_join)
      also have "residue g 0 = f w"
      proof -
        have "g = (\<lambda>z::complex. f (w + z) * N powr z * (1 + z\<^sup>2 / R\<^sup>2) / z)"
          by (auto simp: g_def divide_simps fun_eq_iff power2_eq_square
                   simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
        moreover from N have "residue \<dots> 0 = f w"
          by (subst residue_simple'[of X])
             (auto intro!: holomorphic_intros analytic_imp_holomorphic[OF analytic])
        ultimately show ?thesis by (simp only:)
      qed
      finally have "2 * pi * \<i> * f w = \<ointegral>[\<Gamma>] g" by simp
      also have "\<dots> = \<ointegral>[A] g + \<ointegral>[B2] g + \<ointegral>[B1] g + \<ointegral>[B3] g" unfolding \<Gamma>_def
        by (subst contour_integral_join, (insert path_images,
            auto intro!: contour_integral_join contour_integrable_holomorphic_simple g_holo)[4])+
           (simp_all add: add_ac)
      finally have integral1: "2 * pi * \<i> * f w = \<ointegral>[A] g + \<ointegral>[B2] g + \<ointegral>[B1] g + \<ointegral>[B3] g" .

      \<comment> \<open>Next, we apply the residue theorem along a circle of radius \<open>R\<close> to another
          integrand that is related to the partial sum:\<close>
      have "\<ointegral>[circlepath 0 R] g_S = 2 * pi * \<i> * residue g_S 0"
      proof (subst Residue_theorem)
        show "g_S holomorphic_on UNIV - {0}"
          by (auto simp: g_S_def S_def intro!: holomorphic_intros)
      qed (insert R, auto simp: winding_number_circlepath_centre)
      also have "residue g_S 0 = S w"
      proof -
        have "g_S = (\<lambda>z::complex. S (w + z) * N powr z * (1 + z\<^sup>2 / R\<^sup>2) / z)"
          by (auto simp: g_S_def divide_simps fun_eq_iff power2_eq_square
                   simp del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
        moreover from N have "residue \<dots> 0 = S w"
          by (subst residue_simple'[of X])
             (auto intro!: holomorphic_intros simp: S_def)
        ultimately show ?thesis by (simp only:)
      qed
      finally have "2 * pi * \<i> * S w = \<ointegral>[circlepath 0 R] g_S" ..

      \<comment> \<open>We split this integral into integrals along two semicircles in the left and right
          half-plane, respectively:\<close>
      also have "\<dots> = \<ointegral>[part_circlepath 0 R (-pi/2) (3*pi/2)] g_S"
      proof (rule Cauchy_theorem_homotopic_loops)
        show "homotopic_loops (-{0}) (circlepath 0 R)
                (part_circlepath 0 R (- pi / 2) (3 * pi / 2))" unfolding circlepath_def using R
          by (intro homotopic_loops_part_circlepath[where k = 1]) auto
      qed (auto simp: g_S_def S_def intro!: holomorphic_intros)
      also have "\<dots> = \<ointegral>[A +++ -A] g_S"
      proof (rule Cauchy_theorem_homotopic_paths)
        have *: "-A = part_circlepath 0 R (pi/2) (3*pi/2)" unfolding A_def
          by (intro part_circlepath_mirror[where k = 0]) auto
        from R show "homotopic_paths (-{0}) (part_circlepath 0 R (-pi/2) (3*pi/2)) (A +++ -A)"
          unfolding * unfolding A_def
          by (intro homotopic_paths_part_circlepath) (auto dest!: in_path_image_part_circlepath)
      qed (auto simp: g_S_def S_def A_def exp_eq_polar intro!: holomorphic_intros)
      also have "\<dots> = \<ointegral>[A] g_S + \<ointegral>[-A] g_S" using R
        by (intro contour_integral_join contour_integrable_holomorphic_simple[of _ "-{0}"])
           (auto simp: A_def g_S_def S_def path_image_mirror dest!: in_path_image_part_circlepath
                 intro!: holomorphic_intros)
      also have "\<ointegral>[-A] g_S = -\<ointegral>[A] (\<lambda>x. g_S (-x))"
        by (simp add: A_def contour_integral_mirror contour_integral_neg)
      finally have integral2: "2 * pi * \<i> * S w = \<ointegral>[A] g_S - \<ointegral>[A] (\<lambda>x. g_S (-x))"
        by simp

      \<comment> \<open>Next, we show a small bounding lemma that we will need for the final estimate:\<close>
      have circle_bound: "norm (1 / z + z / R\<^sup>2) \<le> 2 / R" if [simp]: "norm z = R" for z :: complex
      proof -
        have "norm (1 / z + z / R\<^sup>2) \<le> 1 / R + 1 / R"
          by (intro order.trans[OF norm_triangle_ineq] add_mono)
             (insert R, simp_all add: norm_divide norm_mult power2_eq_square)
        thus ?thesis by simp
      qed

      \<comment> \<open>The next bound differs somewhat from Newman's, but it works just as well.
          Its purpose is to bound the contribution of the two short horizontal line segments.\<close>
      have B12_bound: "norm (integral {- \<delta>..0} (\<lambda>x. g (x + R' * \<i>))) \<le> 3 * M / R / ln N"
        (is "?I \<le> _") if "\<bar>R'\<bar> = R" for R' 
      proof -
        have "?I \<le> integral {-\<delta>..0} (\<lambda>x. 3 * M / R * N powr x)"
        proof (rule integral_norm_bound_integral)
          fix x assume x: "x \<in> {-\<delta>..0}"
          define z where "z = x + \<i> * R'"
          from R that have [simp]: "z \<noteq> 0" "Re z = x" "Im z = R'"
            by (auto simp: z_def complex_eq_iff)
          from x R that have "z \<in> X'" by (auto simp: z_def X'_def in_cbox_complex_iff)
          from x R that have "norm z \<le> \<delta> + R"
            by (intro order.trans[OF cmod_le add_mono]) auto
      
          hence "norm (1 / z + z / R\<^sup>2) \<le> 1 / R + (\<delta> / R + 1) / R"
            using R that abs_Im_le_cmod[of z]
            by (intro order.trans[OF norm_triangle_ineq add_mono])
               (auto simp: norm_divide norm_mult power2_eq_square field_simps )
          also have "\<delta> / R \<le> 1" using \<delta> R by auto
          finally have "norm (1 / z + z / R\<^sup>2) \<le> 3 / R"
            using R by (simp add: divide_right_mono)
          hence "norm (g z) \<le> M * N powr x * (3 / R)"
            unfolding g_def norm_mult using \<open>M \<ge> 0\<close> \<open>z \<in> X'\<close>
            by (intro mult_mono mult_nonneg_nonneg M) (auto simp: norm_powr_real_powr)
          thus "norm (g (x + R' * \<i>)) \<le> 3 * M / R * N powr x" by (simp add: mult_ac z_def)
        qed (insert N R l that \<delta>, auto intro!: integrable_continuous_real continuous_intros
                                  simp: g_def X_def complex_eq_iff in_box_complex_iff)
        also have "\<dots> = 3 * M / R * integral {-\<delta>..0} (\<lambda>x. N powr x)" by simp
        also have "((\<lambda>x. N powr x) has_integral (N powr 0 / ln N - N powr (-\<delta>) / ln N)) {-\<delta>..0}"
          using \<delta> N
          by (intro fundamental_theorem_of_calculus)
             (auto simp: has_field_derivative_iff_has_vector_derivative [symmetric] powr_def
                   intro!: derivative_eq_intros)
        hence "integral {-\<delta>..0} (\<lambda>x. N powr x) = 1 / ln (real N) - real N powr - \<delta> / ln (real N)"
          using N by (simp add: has_integral_iff)
        also have "\<dots> \<le> 1 / ln (real N)" using N by simp
        finally show ?thesis using M R by (simp add: mult_left_mono divide_right_mono)
      qed

      \<comment> \<open>We combine the two results from the residue theorem and obtain an integral
          representation of the difference between the partial sums and the limit:\<close>
      have "2 * pi * \<i> * (f w - S w) =
              \<ointegral>[A] g - \<ointegral>[A] g_S + \<ointegral>[A] (\<lambda>x. g_S (-x)) + \<ointegral>[B1] g + \<ointegral>[B3] g + \<ointegral>[B2] g"
        unfolding ring_distribs integral1 integral2 by (simp add: algebra_simps)
      also have "\<ointegral>[A] g - \<ointegral>[A] g_S = \<ointegral>[A] (\<lambda>x. g x - g_S x)" using path_images
        by (intro contour_integral_diff [symmetric])
           (auto intro!: contour_integrable_holomorphic_simple[of _ "X - {0}"] holomorphic_intros
                 simp: g_S_def g_holo S_def)
      also have "\<dots> = \<ointegral>[A] g_rem"
        by (simp add: g_rem_def g_def g_S_def algebra_simps rem_def)
      finally have "2 * pi * \<i> * (f w - S w) =
                      \<ointegral>[A] g_rem + \<ointegral>[A] (\<lambda>x. g_S (- x)) + \<ointegral>[B1] g + \<ointegral>[B3] g + \<ointegral>[B2] g" .

      \<comment> \<open>We now bound each of these integrals individually:\<close>
      also have "norm \<dots> \<le> 2 * C * pi / R  +  2 * C * pi * (1 / N + 1 / R)  +  3 * M / R / ln N  +
                             3 * M / R / ln N  +  6 * R * M * N powr (-\<delta>) / \<delta>"
      proof (rule order.trans[OF norm_triangle_ineq] add_mono)+
        have "\<ointegral>[B1] g = -\<ointegral>[reversepath B1] g" by (simp add: contour_integral_reversepath)
        also have "\<ointegral>[reversepath B1] g = integral {-\<delta>..0} (\<lambda>x. g (x + R * \<i>))"
          unfolding B1_def reversepath_linepath using \<delta>
          by (subst contour_integral_linepath_same_Im) auto
        also have "norm (-\<dots>) = norm \<dots>" by simp
        also have "\<dots> \<le> 3 * M / R / ln N" using R by (intro B12_bound) auto
        finally show "norm (\<ointegral>[B1] g) \<le> \<dots>" .
      next
        have "\<ointegral>[B3] g = integral {-\<delta>..0} (\<lambda>x. g (x + (-R) * \<i>))" unfolding B3_def using \<delta>
          by (subst contour_integral_linepath_same_Im) auto
        also have "norm \<dots> \<le> 3 * M / R / ln N" using R by (intro B12_bound) auto
        finally show "norm (\<ointegral>[B3] g) \<le> \<dots>" .
      next
        have "norm (\<ointegral>[B2] g) \<le> M * N powr (-\<delta>) * (3 / \<delta>) *
                norm (Complex (- \<delta>) (-R) - Complex (- \<delta>) R)" unfolding B2_def
        proof ((rule contour_integral_bound_linepath; (fold B2_def)?), goal_cases)
          case (3 z)
          from 3 \<delta> R have [simp]: "z \<noteq> 0" and Re_z: "Re z = -\<delta>" and Im_z: "Im z \<in> {-R..R}"
            by (auto simp: closed_segment_same_Re closed_segment_eq_real_ivl)
          from 3 have "z \<in> X'" using R \<delta> path_images by (auto simp: B2_def)
          from 3 \<delta> R have "norm z \<le> sqrt (\<delta>^2 + R^2)" unfolding cmod_def using Re_z Im_z
            by (intro real_sqrt_le_mono add_mono) (auto simp: power2_le_iff_abs_le)
          from power_mono[OF this, of 2] have norm_sqr: "norm z ^ 2 \<le> \<delta>\<^sup>2 + R\<^sup>2" by simp
    
          have "norm (1 / z + z / R\<^sup>2) \<le> (1 + (norm z)\<^sup>2 / R\<^sup>2) / \<delta>"
            unfolding add_divide_distrib using \<delta> R abs_Re_le_cmod[of z]
            by (intro order.trans[OF norm_triangle_ineq] add_mono)
               (auto simp: norm_divide norm_mult field_simps power2_eq_square Re_z)
          also have "\<dots> \<le> (1 + (1 + \<delta>\<^sup>2 / R\<^sup>2)) / \<delta>" using \<delta> R \<open>z \<in> X'\<close> norm_sqr unfolding X'_def
            by (intro divide_right_mono add_left_mono)
               (auto simp: field_simps in_cbox_complex_iff intro!: power_mono)
          also have "\<delta>\<^sup>2 / R\<^sup>2 \<le> 1"
            using \<delta> R by (auto simp: field_simps intro!: power_mono)
          finally have "norm (1 / z + z / R\<^sup>2) \<le> 3 / \<delta>" using \<delta> by(simp add: divide_right_mono)
          with \<open>z \<in> X'\<close> show "norm (g z) \<le> M * N powr (-\<delta>) * (3 / \<delta>)" unfolding g_def norm_mult
            by (intro mult_mono mult_nonneg_nonneg M) (auto simp: norm_powr_real_powr Re_z)
        qed (insert path_images M \<delta>, auto intro!: contour_integrable_holomorphic_simple[OF g_holo])
        thus "norm (\<ointegral>[B2] g) \<le> 6 * R * M * N powr (-\<delta>) / \<delta>"
          using R by (simp add: field_simps cmod_def real_sqrt_mult)
      next
        have "norm (\<ointegral>[A] (\<lambda>x. g_S (- x))) \<le> (2 * C / (real N * R) + 2 * C / R\<^sup>2) * 
                                R * ((pi/2) - (-pi/2))" unfolding A_def
        proof ((rule contour_integral_bound_part_circlepath_strong[where k = "{R * \<i>, -R*\<i>}"];
               (fold A_def)?), goal_cases)
          case (6 z)
          hence [simp]: "z \<noteq> 0" and "norm z = R" using R
            by (auto simp: A_def dest!: in_path_image_part_circlepath)
          from 6 have "Re z \<noteq> 0"
            using \<open>norm z = R\<close> by (auto simp: cmod_def abs_if complex_eq_iff split: if_splits)
          with 6 have "Re z > 0" using image_A by auto
          have "S (w - z) = (\<Sum>k = 1..N. fds_nth F k / of_nat k powr (w - z))"
            by (simp add: S_def eval_fds_truncate)
          also have "norm \<dots> \<le> C * N powr Re z * (1 / N + 1 / Re z)"
            using \<open>Re z > 0\<close> w N by (intro newman_ingham_aux2 C) auto
          finally have "norm (S (w - z)) \<le> \<dots>" .
          hence "norm (g_S (-z)) \<le>
                   (C * N powr (Re z) * (1 / N + 1 / Re z)) * N powr (-Re z) * (2 * Re z / R\<^sup>2)"
            unfolding g_S_def norm_mult 
            using newman_ingham_aux1[OF _ \<open>norm z = R\<close>] \<open>Re z > 0\<close> \<open>C \<ge> 1\<close> R
            by (intro mult_mono mult_nonneg_nonneg circle_bound)
               (auto simp: norm_powr_real_powr norm_uminus_minus)
          also have "\<dots> = 2 * C * (Re z / N + 1) / R\<^sup>2" using R N \<open>Re z > 0\<close>
            by (simp add: powr_minus algebra_simps)
          also have "\<dots> \<le> 2 * C / (N * R) + 2 * C / R\<^sup>2" unfolding add_divide_distrib ring_distribs
            using R N abs_Re_le_cmod[of z] \<open>norm z = R\<close> \<open>Re z > 0\<close> \<open>C \<ge> 1\<close>
            by (intro add_mono) (auto simp: power2_eq_square field_simps mult_mono)
          finally show ?case .
        qed (insert R N image_A C, auto intro!: contour_integrable_holomorphic_simple[of _ "-{0}"]
                                                holomorphic_intros simp: g_S_def S_def)
        also have "\<dots> = 2 * C * pi * (1 / N + 1 / R)" using R N
          by (simp add: power2_eq_square field_simps)
        finally show "norm (\<ointegral>[A] (\<lambda>x. g_S (- x))) \<le> \<dots>" .
      next
        have "norm (\<ointegral>[A] g_rem) \<le> (2 * C / R\<^sup>2) * R * ((pi/2) - (-pi/2))" unfolding A_def
        proof ((rule contour_integral_bound_part_circlepath_strong[where k = "{R * \<i>, -R*\<i>}"];
               (fold A_def)?), goal_cases)
          case (6 z)
          hence [simp]: "z \<noteq> 0" and "norm z = R" using R
            by (auto simp: A_def dest!: in_path_image_part_circlepath)
          from 6 have "Re z \<noteq> 0"
            using \<open>norm z = R\<close> by (auto simp: cmod_def abs_if complex_eq_iff split: if_splits)
          with 6 have "Re z > 0" using image_A by auto
    
          have summable: "summable (\<lambda>n. C * (1 / (Suc n + N) powr (Re w + Re z)))"
            using summable_hurwitz_zeta_real[of "Re w + Re z" "Suc N"] \<open>Re z > 0\<close> w
            unfolding powr_minus by (intro summable_mult) (auto simp: field_simps)
          have "rem (w + z) = (\<Sum>n. fds_nth F (Suc n + N) / (Suc n + N) powr (w + z))"
            using \<open>Re z > 0\<close> w by (simp add: rem_altdef eval_fds_remainder)
          also have "norm \<dots> \<le> (\<Sum>n. C / (Suc n + N) powr Re (w + z))" using summable
            by (intro norm_suminf_le)
               (auto simp: norm_divide norm_powr_real_powr intro!: divide_right_mono C)
          also have "\<dots> = (\<Sum>n. C * (Suc n + N) powr -Re (w + z))"
            unfolding powr_minus by (simp add: field_simps)
          also have "\<dots> = C * (\<Sum>n. (Suc n + N) powr -Re (w + z))"
            using summable_hurwitz_zeta_real[of "Re w + Re z" "Suc N"] \<open>Re z > 0\<close> w
            by (subst suminf_mult) (auto simp: add_ac)
          also have "(\<Sum>n. (Suc n + N) powr -Re (w + z)) \<le>
                       N powr (1 - Re (w + z)) / (Re (w + z) - 1)"
            using \<open>Re z > 0\<close> w N hurwitz_zeta_real_bound_aux[of N "Re (w + z)"]
            by (auto simp: add_ac)
          also have "\<dots> \<le> N powr -Re z / Re z"
            using w N \<open>Re z > 0\<close> by (intro frac_le powr_mono) auto
          finally have "norm (rem (w + z)) \<le> C / (Re z * N powr Re z)"
            using C by (simp add: mult_left_mono mult_right_mono powr_minus field_simps)
          hence "norm (g_rem z) \<le> (C / (Re z * N powr Re z)) * N powr (Re z) * (2 * Re z / R\<^sup>2)"
            unfolding g_rem_def norm_mult
            using newman_ingham_aux1[OF _ \<open>norm z = R\<close>] R \<open>Re z > 0\<close> C
            by (intro mult_mono mult_nonneg_nonneg circle_bound)
               (auto simp: norm_powr_real_powr norm_uminus_minus)
          also have "\<dots> = 2 * C / R\<^sup>2" using R N \<open>Re z > 0\<close>
            by (simp add: powr_minus field_simps)
          finally show ?case .
        next
          show "g_rem contour_integrable_on A" using path_images
            by (auto simp: g_rem_def rem_def S_def
                     intro!: contour_integrable_holomorphic_simple[of _ "X-{0}"] holomorphic_intros)
        qed (insert R N C, auto)
        also have "(2 * C / R\<^sup>2) * R * ((pi/2) - (-pi/2)) = 2 * C * pi / R"
          using R by (simp add: power2_eq_square field_simps)
        finally show "norm (\<ointegral>[A] g_rem) \<le> \<dots>" .
      qed
      also have "\<dots> = 4*C*pi/R + 2*C*pi/N + 6*M/R / ln N + 6*R*M*N powr - \<delta> / \<delta>"
        by (simp add: algebra_simps)
      also have "\<dots> = 2*pi * (2*C/R + C/N + 3*M / (pi*R*ln N) + 3*R*M / (\<delta>*pi * N powr \<delta>))"
        by (simp add: field_simps powr_minus )
      also have "norm (2 * pi * \<i> * (f w - S w)) = 2 * pi * norm (f w - S w)"
        by (simp add: norm_mult)
      finally have "norm (f w - S w) \<le> bound N" by (simp add: bound_def)
      also have "bound N < \<epsilon>" by fact
      finally show "norm (f w - S w) < \<epsilon>" .
    qed
  qed
  thus "fds_converges F w"
    by (auto simp: fds_converges_altdef2 intro: convergentI)
  thus "eval_fds F w = f w"
    using \<open>(\<lambda>N. eval_fds (fds_truncate N F) w) \<longlonglongrightarrow> f w\<close>
    by (intro tendsto_unique[OF _ tendsto_eval_fds_truncate]) auto
qed

text \<open>
  The theorem generalises in a trivial way; we can replace the requirement that the
  coefficients of $f(s)$ be $O(1)$ by $O(n^{\sigma-1})$ for some $\sigma\in\mathbb{R}$, then
  $f(s)$ converges for $\mathfrak{R}(s)>\sigma$. If it can be analytically continued to
  $\mathfrak{R}(s)\geq\sigma$, it is also convergent there.
\<close>
theorem Newman_Ingham:
  fixes F :: "complex fds" and f :: "complex \<Rightarrow> complex"
  assumes coeff_bound:   "fds_nth F \<in> O(\<lambda>n. n powr of_real (\<sigma> - 1))"
  assumes f_analytic:    "f analytic_on {s. Re s \<ge> \<sigma>}"
  assumes F_conv_f:      "\<And>s. Re s > \<sigma> \<Longrightarrow> eval_fds F s = f s"
  assumes w:             "Re w \<ge> \<sigma>"
  shows   "fds_converges F w" and "eval_fds F w = f w"
proof -
  define F' where "F' = fds_shift (-of_real (\<sigma> - 1)) F"
  define f' where "f' = f \<circ> (\<lambda>s. s + of_real (\<sigma> - 1))"

  have "fds_nth F' = (\<lambda>n. fds_nth F n * of_nat n powr -of_real(\<sigma> - 1))"
    by (auto simp: fun_eq_iff F'_def)
  also have "\<dots> \<in> O(\<lambda>n. of_nat n powr of_real (\<sigma> - 1) * of_nat n powr -of_real(\<sigma> - 1))"
    by (intro landau_o.big.mult_right assms)
  also have "(\<lambda>n. of_nat n powr of_real (\<sigma> - 1) * of_nat n powr -of_real (\<sigma> - 1)) \<in> \<Theta>(\<lambda>_. 1)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: powr_minus powr_diff)
  finally have bigo: "fds_nth F' \<in> O(\<lambda>_. 1)" .

  from f_analytic have analytic: "f' analytic_on {s. Re s \<ge> 1}" unfolding f'_def
    by (intro analytic_on_compose_gen[OF _ f_analytic]) (auto intro!: analytic_intros)

  have F'_f: "eval_fds F' s = f' s" if "Re s > 1" for s
    using assms that by (auto simp: F'_def f'_def algebra_simps)

  have w': "1 \<le> Re (w - of_real (\<sigma> - 1))"
    using w by simp
  
  have 1: "fds_converges F' (w - of_real (\<sigma> - 1))"
    using bigo analytic F'_f w' by (rule Newman_Ingham_1)
  thus "fds_converges F w" by (auto simp: F'_def)

  have 2: "eval_fds F' (w - of_real (\<sigma> - 1)) = f' (w - of_real (\<sigma> - 1))"
    using bigo analytic F'_f w' by (rule Newman_Ingham_1)
  thus "eval_fds F w = f w"
    using assms by (simp add: F'_def f'_def)
qed

end