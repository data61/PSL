(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Classification of isometries on a Gromov hyperbolic space\<close>

theory Isometries_Classification
  imports Gromov_Boundary Busemann_Function
begin

text \<open>Isometries of Gromov hyperbolic spaces are of three types:
\begin{itemize}
\item Elliptic ones, for which orbits are bounded.
\item Parabolic ones, which are not elliptic and have exactly one fixed point
at infinity.
\item Loxodromic ones, which are not elliptic and have exactly two fixed points
at infinity.
\end{itemize}
In this file, we show that all isometries are indeed of this form, and give
further properties for each type.

For the definition, we use another characterization in terms of stable translation length: for
isometries which are not elliptic, then they are parabolic if the stable translation length is $0$,
loxodromic if it is positive. This gives a very efficient definition, and it is clear from this
definition that the three categories of isometries are disjoint. All the work is then to go from
this general definition to the dynamical properties in terms of fixed points on the boundary.
\<close>


subsection \<open>The translation length\<close>

text \<open>The translation length is the minimal translation distance of an isometry. The stable
translation length is the limit of the translation length of $f^n$ divided by $n$.\<close>

definition translation_length::"(('a::metric_space) \<Rightarrow> 'a) \<Rightarrow> real"
  where "translation_length f = Inf {dist x (f x)|x. True}"

lemma translation_length_nonneg [simp, mono_intros]:
  "translation_length f \<ge> 0"
unfolding translation_length_def by (rule cInf_greatest, auto)

lemma translation_length_le [mono_intros]:
  "translation_length f \<le> dist x (f x)"
unfolding translation_length_def apply (rule cInf_lower) by (auto intro: bdd_belowI[of _ 0])

definition stable_translation_length::"(('a::metric_space) \<Rightarrow> 'a) \<Rightarrow> real"
  where "stable_translation_length f = Inf {translation_length (f^^n)/n |n. n > 0}"

lemma stable_translation_length_nonneg [simp]:
  "stable_translation_length f \<ge> 0"
unfolding stable_translation_length_def by (rule cInf_greatest, auto)

lemma stable_translation_length_le_translation_length [mono_intros]:
  "n * stable_translation_length f \<le> translation_length (f^^n)"
proof -
  have *: "stable_translation_length f \<le> translation_length (f^^n)/n" if "n > 0" for n
    unfolding stable_translation_length_def apply (rule cInf_lower) using that by (auto intro: bdd_belowI[of _ 0])
  show ?thesis
    apply (cases "n = 0") using * by (auto simp add: divide_simps algebra_simps)
qed

lemma semicontraction_iterates:
  fixes f::"('a::metric_space) \<Rightarrow> 'a"
  assumes "1-lipschitz_on UNIV f"
  shows "1-lipschitz_on UNIV (f^^n)"
by (induction n, auto intro!: lipschitz_onI lipschitz_on_compose2[of 1 UNIV _ 1 f, simplified] lipschitz_on_subset[OF assms])

text \<open>If $f$ is a semicontraction, then its stable translation length is the limit of $d(x, f^n x)/n$
for any $n$. While it is obvious that the liminf of this quantity is at least the stable translation
length (which is defined as an inf over all points and all times), the opposite inequality is more
interesting. One may find a point $y$ and a time $k$ for which $d(y, f^k y)/k$ is very close to the
stable translation length. By subadditivity of the sequence $n \mapsto f(y, f^n y)$ and Fekete's
Lemma, it follows that, for any large $n$, then $d(y, f^n y)/n$ is also very close to the stable
translation length. Since this is equal to $d(x, f^n x)/n$ up to $\pm 2 d(x,y)/n$, the result
follows.\<close>

proposition stable_translation_length_as_pointwise_limit:
  assumes "1-lipschitz_on UNIV f"
  shows "(\<lambda>n. dist x ((f^^n) x)/n) \<longlonglongrightarrow> stable_translation_length f"
proof -
  have *: "subadditive (\<lambda>n. dist y ((f^^n) y))" for y
  proof (rule subadditiveI)
    fix m n::nat
    have "dist y ((f ^^ (m + n)) y) \<le> dist y ((f^^m) y) + dist ((f^^m) y) ((f^^(m+n)) y)"
      by (rule dist_triangle)
    also have "... = dist y ((f^^m) y) + dist ((f^^m) y) ((f^^m) ((f^^n) y))"
      by (auto simp add: funpow_add)
    also have "... \<le> dist y ((f^^m) y) + dist y ((f^^n) y)"
      using semicontraction_iterates[OF assms, of m] unfolding lipschitz_on_def by auto
    finally show "dist y ((f ^^ (m + n)) y) \<le> dist y ((f ^^ m) y) + dist y ((f ^^ n) y)"
      by simp
  qed
  have Ly: "(\<lambda>n. dist y ((f^^n) y) / n) \<longlonglongrightarrow> Inf {dist y ((f^^n) y) / n |n. n > 0}" for y
    by (auto intro!: bdd_belowI[of _ 0] subadditive_converges_bounded'[OF subadditive_imp_eventually_subadditive[OF *]])
  have "eventually (\<lambda>n. dist x ((f^^n) x)/n < l) sequentially" if "stable_translation_length f < l" for l
  proof -
    obtain m where m: "stable_translation_length f < m" "m < l"
      using \<open>stable_translation_length f < l\<close> dense by auto
    have "\<exists>t \<in> {translation_length (f^^n)/n |n. n > 0}. t < m"
      apply (subst cInf_less_iff[symmetric])
      using m unfolding stable_translation_length_def by (auto intro!: bdd_belowI[of _ 0])
    then obtain k where k: "k > 0" "translation_length (f^^k)/k < m"
      by auto
    have "translation_length (f^^k) < k * m"
      using k by (simp add: divide_simps algebra_simps)
    then have "\<exists>t \<in> {dist y ((f^^k) y) |y. True}. t < k * m"
      apply (subst cInf_less_iff[symmetric])
      unfolding translation_length_def by (auto intro!: bdd_belowI[of _ 0])
    then obtain y where y: "dist y ((f^^k) y) < k * m"
      by auto
    have A: "eventually (\<lambda>n. dist y ((f^^n) y)/n < m) sequentially"
      apply (auto intro!: order_tendstoD[OF Ly] iffD2[OF cInf_less_iff] bdd_belowI[of _ 0] exI[of _ "dist y ((f^^k) y)/k"])
      using y k by (auto simp add: algebra_simps divide_simps)
    have B: "eventually (\<lambda>n. dist x y * (1/n) < (l-m)/2) sequentially"
      apply (intro order_tendstoD[of _ "dist x y * 0"] tendsto_intros)
      using \<open>m < l\<close> by simp
    have C: "dist x ((f^^n) x)/n < l" if "n > 0" "dist y ((f^^n) y)/n < m" "dist x y * (1/n) < (l-m)/2" for n
    proof -
      have "dist x ((f^^n) x) \<le> dist x y + dist y ((f^^n) y) + dist ((f^^n) y) ((f^^n) x)"
        by (intro mono_intros)
      also have "... \<le> dist x y + dist y ((f^^n) y) + dist y x"
        using semicontraction_iterates[OF assms, of n] unfolding lipschitz_on_def by auto
      also have "... = 2 * dist x y + dist y ((f^^n) y)"
        by (simp add: dist_commute)
      also have "... < 2 * real n * (l-m)/2 + n * m"
        apply (intro mono_intros) using that by (auto simp add: algebra_simps divide_simps)
      also have "... = n * l"
        by (simp add: algebra_simps divide_simps)
      finally show ?thesis
        using that by (simp add: algebra_simps divide_simps)
    qed
    show "eventually (\<lambda>n. dist x ((f^^n) x)/n < l) sequentially"
      by (rule eventually_mono[OF eventually_conj[OF eventually_conj[OF A B] eventually_gt_at_top[of 0]] C], auto)
  qed
  moreover have "eventually (\<lambda>n. dist x ((f^^n) x)/n > l) sequentially" if "stable_translation_length f > l" for l
  proof -
    have *: "dist x ((f^^n) x)/n > l" if "n > 0" for n
    proof -
      have "n * l < n * stable_translation_length f"
        using \<open>stable_translation_length f > l\<close> \<open>n > 0\<close> by auto
      also have "... \<le> translation_length (f^^n)"
        by (intro mono_intros)
      also have "... \<le> dist x ((f^^n) x)"
        by (intro mono_intros)
      finally show ?thesis
        using \<open>n > 0\<close> by (auto simp add: algebra_simps divide_simps)
    qed
    then show ?thesis
      by (rule eventually_mono[rotated], auto)
  qed
  ultimately show ?thesis
    by (rule order_tendstoI[rotated])
qed

text \<open>It follows from the previous proposition that the stable translation length is also the limit
of the renormalized translation length of $f^n$.\<close>

proposition stable_translation_length_as_limit:
  assumes "1-lipschitz_on UNIV f"
  shows "(\<lambda>n. translation_length (f^^n) / n) \<longlonglongrightarrow> stable_translation_length f"
proof -
  obtain x::'a where True by auto
  show ?thesis
  proof (rule tendsto_sandwich[of "\<lambda>n. stable_translation_length f" _ _ "\<lambda>n. dist x ((f^^n) x)/n"])
    have "stable_translation_length f \<le> translation_length (f ^^ n) / real n" if "n > 0" for n
      using stable_translation_length_le_translation_length[of n f] that by (simp add: divide_simps algebra_simps)
    then show "eventually (\<lambda>n. stable_translation_length f \<le> translation_length (f ^^ n) / real n) sequentially"
      by (rule eventually_mono[rotated], auto)
    have "translation_length (f ^^ n) / real n \<le> dist x ((f ^^ n) x) / real n" for n
      using translation_length_le[of "f^^n" x] by (auto simp add: divide_simps)
    then show "eventually (\<lambda>n. translation_length (f ^^ n) / real n \<le> dist x ((f ^^ n) x) / real n) sequentially"
      by auto
  qed (auto simp add: stable_translation_length_as_pointwise_limit[OF assms])
qed

lemma stable_translation_length_inv:
  assumes "isometry f"
  shows "stable_translation_length (inv f) = stable_translation_length f"
proof -
  have *: "dist basepoint (((inv f)^^n) basepoint) = dist basepoint ((f^^n) basepoint)" for n
  proof -
    have "basepoint = (f^^n) (((inv f)^^n) basepoint)"
      by (metis assms comp_apply fn_o_inv_fn_is_id isometry_inverse(2))
    then have "dist basepoint ((f^^n) basepoint) = dist ((f^^n) (((inv f)^^n) basepoint)) ((f^^n) basepoint)"
      by auto
    also have "... = dist (((inv f)^^n) basepoint) basepoint"
      unfolding isometryD(2)[OF isometry_iterates[OF assms]] by simp
    finally show ?thesis by (simp add: dist_commute)
  qed

  have "(\<lambda>n. dist basepoint ((f^^n) basepoint)/n) \<longlonglongrightarrow> stable_translation_length f"
    using stable_translation_length_as_pointwise_limit[OF isometryD(4)[OF assms]] by simp
  moreover have "(\<lambda>n. dist basepoint ((f^^n) basepoint)/n) \<longlonglongrightarrow> stable_translation_length (inv f)"
    unfolding *[symmetric]
    using stable_translation_length_as_pointwise_limit[OF isometryD(4)[OF isometry_inverse(1)[OF assms]]] by simp
  ultimately show ?thesis
    using LIMSEQ_unique by auto
qed

subsection \<open>The strength of an isometry at a fixed point at infinity\<close>

text \<open>The additive strength of an isometry at a fixed point at infinity is the asymptotic average
every point is moved towards the fixed point at each step. It is measured using the Busemann
function.\<close>

definition additive_strength::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> ('a Gromov_completion) \<Rightarrow> real"
  where "additive_strength f xi = lim (\<lambda>n. (Busemann_function_at xi ((f^^n) basepoint) basepoint)/n)"

text \<open>For additivity reasons, as the Busemann function is a quasi-morphism, the additive strength
measures the deplacement even at finite times. It is also uniform in terms of the basepoint. This
shows that an isometry sends horoballs centered at a fixed point to horoballs, up to a uniformly
bounded error depending only on $\delta$.\<close>

lemma Busemann_function_eq_additive_strength:
  assumes "isometry f" "Gromov_extension f xi = xi"
  shows "\<bar>Busemann_function_at xi ((f^^n) x) (x::'a::Gromov_hyperbolic_space) - real n * additive_strength f xi\<bar> \<le> 2 * deltaG(TYPE('a))"
proof -
  define u where "u = (\<lambda>y n. Busemann_function_at xi ((f^^n) y) y)"
  have *: "abs(u y (m+n) - u y m - u y n) \<le> 2 * deltaG(TYPE('a))" for n m y
  proof -
    have P: "Gromov_extension (f^^m) xi = xi"
      unfolding Gromov_extension_isometry_iterates[OF assms(1)] apply (induction m) using assms by auto
    have *: "u y n = Busemann_function_at xi ((f^^m) ((f^^n) y)) ((f^^m) y)"
      apply (subst P[symmetric]) unfolding Busemann_function_isometry[OF isometry_iterates[OF \<open>isometry f\<close>]] u_def by auto
    show ?thesis
      unfolding * unfolding u_def using Busemann_function_quasi_morphism[of xi "(f^^(m+n)) y" "(f^^m) y" y]
      unfolding funpow_add comp_def by auto
  qed
  define l where "l = (\<lambda>y. lim (\<lambda>n. u y n/n))"
  have A: "abs(u y k - k * l y) \<le> 2 * deltaG(TYPE('a))" for y k
    unfolding l_def using almost_additive_converges(2) * by auto
  then have *: "abs(Busemann_function_at xi ((f^^k) y) y - k * l y) \<le> 2 * deltaG(TYPE('a))" for y k
    unfolding u_def by auto
  have "l basepoint = additive_strength f xi"
    unfolding l_def u_def additive_strength_def by auto

  have "abs(k * l basepoint - k * l x) \<le> 4 * deltaG(TYPE('a)) + 2 * dist basepoint x" for k::nat
  proof -
    have "abs(k * l basepoint - k * l x) = abs((Busemann_function_at xi ((f^^k) x) x - k * l x) - (Busemann_function_at xi ((f^^k) basepoint) basepoint - k * l basepoint)
                                                + (Busemann_function_at xi ((f^^k) basepoint) basepoint - Busemann_function_at xi ((f^^k) x) x))"
      by auto
    also have "... \<le> abs (Busemann_function_at xi ((f^^k) x) x - k * l x) + abs (Busemann_function_at xi ((f^^k) basepoint) basepoint - k * l basepoint)
                      + abs (Busemann_function_at xi ((f^^k) basepoint) basepoint - Busemann_function_at xi ((f^^k) x) x)"
      by auto
    also have "... \<le> 2 * deltaG(TYPE('a)) + 2 * deltaG(TYPE('a)) + (dist ((f^^k) basepoint) ((f^^k) x) + dist basepoint x)"
      by (intro mono_intros *)
    also have "... = 4 * deltaG(TYPE('a)) + 2 * dist basepoint x"
      unfolding isometryD[OF isometry_iterates[OF assms(1)]] by auto
    finally show ?thesis by auto
  qed
  moreover have "u = v" if H: "\<And>k::nat. abs(k * u - k * v) \<le> C" for u v C::real
  proof -
    have "(\<lambda>n. abs(u - v)) \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n::nat. C/n"], auto)
      have "(\<lambda>n. C*(1/n)) \<longlonglongrightarrow> C * 0" by (intro tendsto_intros)
      then show "(\<lambda>n. C/n) \<longlonglongrightarrow> 0" by auto
      have "\<bar>u - v\<bar> \<le> C / real n" if "n \<ge> 1" for n
        using H[of n] that apply (simp add: divide_simps algebra_simps)
        by (metis H abs_mult abs_of_nat right_diff_distrib')
      then show "\<forall>\<^sub>F n in sequentially. \<bar>u - v\<bar> \<le> C / real n"
        unfolding eventually_sequentially by auto
    qed
    then show ?thesis
      by (metis LIMSEQ_const_iff abs_0_eq eq_iff_diff_eq_0)
  qed
  ultimately have "l basepoint = l x" by auto
  show ?thesis
    using A[of x n] unfolding u_def \<open>l basepoint = l x\<close>[symmetric] \<open>l basepoint = additive_strength f xi\<close> by auto
qed

lemma additive_strength_as_limit [tendsto_intros]:
  assumes "isometry f" "Gromov_extension f xi = xi"
  shows "(\<lambda>n. Busemann_function_at xi ((f^^n) x) x/n) \<longlonglongrightarrow> additive_strength f xi"
proof -
  have "(\<lambda>n. abs(Busemann_function_at xi ((f^^n) x) x/n - additive_strength f xi)) \<longlonglongrightarrow> 0"
    apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. (2 * deltaG(TYPE('a))) * (1/real n)"], auto)
    unfolding eventually_sequentially apply (rule exI[of _ 1])
    using Busemann_function_eq_additive_strength[OF assms] apply (simp add: divide_simps algebra_simps)
    using tendsto_mult[OF _ lim_1_over_n] by auto
  then show ?thesis
    using LIM_zero_iff tendsto_rabs_zero_cancel by blast
qed

text \<open>The additive strength measures the amount of displacement towards a fixed point at infinity.
Therefore, the distance from $x$ to $f^n x$ is at least $n$ times the additive strength, but one
might think that it might be larger, if there is displacement along the horospheres. It turns out
that this is not the case: the displacement along the horospheres is at most logarithmic (this is
a classical property of parabolic isometries in hyperbolic spaces), and in fact it is bounded for
loxodromic elements.
We prove here that the growth is at most logarithmic in all cases, using a small computation based
on the hyperbolicity inequality, expressed in Lemma \verb+dist_minus_Busemann_max_ineq+ above.
This lemma will be used below to show that the translation length is the absolute value of the
additive strength.\<close>

lemma dist_le_additive_strength:
  assumes "isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "Gromov_extension f xi = xi" "additive_strength f xi \<ge> 0" "n \<ge> 1"
  shows "dist x ((f^^n) x) \<le> dist x (f x) + real n * additive_strength f xi + ceiling (log 2 n) * 16 * deltaG(TYPE('a))"
proof -
  have A: "\<And>n. n \<in> {1..2^k} \<Longrightarrow> dist x ((f^^n) x) - real n * additive_strength f xi \<le> dist x (f x) + k * 16 * deltaG(TYPE('a))" for k
  proof (induction k)
    case 0
    fix n::nat assume "n \<in> {1..2^0}"
    then have "n = 1" by auto
    then show "dist x ((f^^n) x) - real n * additive_strength f xi \<le> dist x (f x) + real 0 * 16 * deltaG(TYPE('a))"
      using assms(3) by auto
  next
    case (Suc k)
    fix N::nat assume "N \<in> {1..2^(Suc k)}"
    then consider "N \<in> {1..2^k}" | "N \<in> {2^k<..2^(Suc k)}" using not_le by auto
    then show "dist x ((f ^^ N) x) - real N * additive_strength f xi \<le> dist x (f x) + real (Suc k) * 16 * deltaG TYPE('a)"
    proof (cases)
      case 1
      show ?thesis by (rule order_trans[OF Suc.IH[OF 1]], auto simp add: algebra_simps)
    next
      case 2
      define m::nat where "m = N - 2^k"
      define n::nat where "n = 2^k"
      have nm: "N = n+m" "m \<in> {1..2^k}" "n \<in> {1..2^k}"unfolding m_def n_def using 2 by auto
      have *: "(f^^(n+m)) x = (f^^n) ((f^^m) x)"
        unfolding funpow_add comp_def by auto
      have **: "(f^^(n+m)) x = (f^^m) ((f^^n) x)"
        apply (subst add.commute) unfolding funpow_add comp_def by auto

      have "dist x ((f^^N) x) - N * additive_strength f xi - 2 * deltaG(TYPE('a)) \<le> dist x ((f^^(n+m)) x) - Busemann_function_at xi ((f^^(n+m)) x) x"
        unfolding nm(1) using Busemann_function_eq_additive_strength[OF assms(1) assms(2), of "n+m" x] by auto
      also have "... \<le> max (dist x ((f^^n) x) - Busemann_function_at xi ((f^^n) x) x) (dist ((f^^n) x) ((f^^(n+m)) x) - Busemann_function_at xi ((f^^(n+m)) x) ((f^^n) x) - 2 * Busemann_function_at xi ((f^^n) x) x) + 8 * deltaG(TYPE('a))"
        using dist_minus_Busemann_max_ineq by auto
      also have "... \<le> max (dist x ((f^^n) x) - (n * additive_strength f xi - 2 * deltaG(TYPE('a)))) (dist ((f^^n) x) ((f^^(n+m)) x) - (m * additive_strength f xi - 2 * deltaG(TYPE('a))) - 2 * (n * additive_strength f xi - 2 * deltaG(TYPE('a)))) + 8 * deltaG(TYPE('a))"
        unfolding ** apply (intro mono_intros)
        using Busemann_function_eq_additive_strength[OF assms(1) assms(2), of n x] Busemann_function_eq_additive_strength[OF assms(1) assms(2), of m "(f^^n) x"] by auto
      also have "... \<le> max (dist x ((f^^n) x) - n * additive_strength f xi + 6 * deltaG(TYPE('a))) (dist x ((f^^m) x) - m * additive_strength f xi + 6 * deltaG(TYPE('a))) + 8 * deltaG(TYPE('a))"
        unfolding * isometryD(2)[OF isometry_iterates[OF assms(1)], of n] using assms(3) by (intro mono_intros, auto)
      also have "... = max (dist x ((f^^n) x) - n * additive_strength f xi) (dist x ((f^^m) x) - m * additive_strength f xi) + 14 * deltaG(TYPE('a))"
        unfolding max_add_distrib_left[symmetric] by auto
      also have "... \<le> dist x (f x) + k * 16 * deltaG(TYPE('a)) + 14 * deltaG(TYPE('a))"
        using nm by (auto intro!: Suc.IH)
      finally show ?thesis by (auto simp add: algebra_simps)
    qed
  qed
  define k::nat where "k = nat(ceiling (log 2 n))"
  have "n \<le> 2^k" unfolding k_def
    by (meson less_log2_of_power not_le real_nat_ceiling_ge)
  then have "dist x ((f^^n) x) - real n * additive_strength f xi \<le> dist x (f x) + k * 16 * deltaG(TYPE('a))"
    using A[of n k] \<open>n \<ge> 1\<close> by auto
  moreover have "real (nat \<lceil>log 2 (real n)\<rceil>) = real_of_int \<lceil>log 2 (real n)\<rceil>"
    by (metis Transcendental.log_one \<open>n \<le> 2 ^ k\<close> assms(4) ceiling_zero int_ops(2) k_def le_antisym nat_eq_iff2 of_int_1 of_int_of_nat_eq order_refl power_0)
  ultimately show ?thesis unfolding k_def by (auto simp add: algebra_simps)
qed

text \<open>The strength of the inverse of a map is the opposite of the strength of the map.\<close>

lemma additive_strength_inv:
  assumes "isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "Gromov_extension f xi = xi"
  shows "additive_strength (inv f) xi = - additive_strength f xi"
proof -
  have *: "(inv f ^^ n) ((f ^^ n) x) = x" for n x
    by (metis assms(1) comp_apply funpow_code_def inv_fn_o_fn_is_id isometry_inverse(2))
  have A: "abs(real n * additive_strength f xi + real n * additive_strength (inv f) xi) \<le> 6 * deltaG (TYPE('a))" for n::nat and x::'a
    using Busemann_function_quasi_morphism[of xi x "(f^^n) x" x] Busemann_function_eq_additive_strength[OF assms, of n x] Busemann_function_eq_additive_strength[OF isometry_inverse(1)[OF assms(1)]
    Gromov_extension_inv_fixed_point[OF assms], of n "(f^^n) x"] unfolding * by auto
  have B: "abs(additive_strength f xi + additive_strength (inv f) xi) \<le> 6 * deltaG(TYPE('a)) * (1/n)" if "n \<ge> 1" for n::nat
    using that A[of n] apply (simp add: divide_simps algebra_simps) unfolding distrib_left[symmetric] by auto
  have "(\<lambda>n. abs(additive_strength f xi + additive_strength (inv f) xi)) \<longlonglongrightarrow> 6 * deltaG(TYPE('a)) * 0"
    apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. 6 * deltaG(TYPE('a)) * (1/real n)"], simp)
    unfolding eventually_sequentially apply (rule exI[of _ 1]) using B apply simp
    by (simp, intro tendsto_intros)
  then show ?thesis
    using LIMSEQ_unique mult_zero_right tendsto_const by fastforce
qed

text \<open>We will now prove that the stable translation length of an isometry is given by the absolute
value of its strength at any fixed point. We start with the case where the strength is nonnegative,
and then reduce to this case by considering the map or its inverse.\<close>

lemma stable_translation_length_eq_additive_strength_aux:
  assumes "isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "Gromov_extension f xi = xi" "additive_strength f xi \<ge> 0"
  shows "stable_translation_length f = additive_strength f xi"
proof -
  have "(\<lambda>n. dist x ((f^^n) x)/n) \<longlonglongrightarrow> additive_strength f xi" for x
  proof (rule tendsto_sandwich[of "\<lambda>n. (n * additive_strength f xi - 2 * deltaG(TYPE('a)))/real n" _ _ "\<lambda>n. (dist x (f x) + n * additive_strength f xi + ceiling (log 2 n) * 16 * deltaG(TYPE('a)))/ n"])
    have "n * additive_strength f xi - 2 * deltaG TYPE('a) \<le> dist x ((f ^^ n) x)" for n
      using Busemann_function_eq_additive_strength[OF assms(1) assms(2), of n x] Busemann_function_le_dist[of xi "(f^^n) x" x]
      by (simp add: dist_commute)
    then have "(n * additive_strength f xi - 2 * deltaG TYPE('a)) / n \<le> dist x ((f ^^ n) x) / n" if "n \<ge> 1" for n
      using that by (simp add: divide_simps)
    then show "\<forall>\<^sub>F n in sequentially. (real n * additive_strength f xi - 2 * deltaG TYPE('a)) / real n \<le> dist x ((f ^^ n) x) / real n"
      unfolding eventually_sequentially by auto

    have A: "eventually (\<lambda>n. additive_strength f xi - (2 * deltaG(TYPE('a))) * (1/n) = (real n * additive_strength f xi - 2 * deltaG TYPE('a)) / real n) sequentially"
      unfolding eventually_sequentially apply (rule exI[of _ 1]) by (simp add: divide_simps)
    have B: "(\<lambda>n. additive_strength f xi - (2 * deltaG(TYPE('a))) * (1/n)) \<longlonglongrightarrow> additive_strength f xi - (2 * deltaG(TYPE('a))) * 0"
      by (intro tendsto_intros)
    show "(\<lambda>n. (real n * additive_strength f xi - 2 * deltaG TYPE('a)) / real n) \<longlonglongrightarrow> additive_strength f xi"
      using Lim_transform_eventually[OF A B] by simp

    have "dist x ((f^^n) x) \<le> dist x (f x) + n * additive_strength f xi + ceiling (log 2 n) * 16 * deltaG(TYPE('a))" if "n \<ge> 1" for n
      using dist_le_additive_strength[OF assms that] by simp
    then have "(dist x ((f^^n) x))/n \<le> (dist x (f x) + n * additive_strength f xi + ceiling (log 2 n) * 16 * deltaG(TYPE('a)))/n" if "n \<ge> 1" for n
      using that by (simp add: divide_simps)
    then show "\<forall>\<^sub>F n in sequentially. dist x ((f ^^ n) x) / real n \<le> (dist x (f x) + real n * additive_strength f xi + real_of_int (\<lceil>log 2 (real n)\<rceil> * 16) * deltaG TYPE('a)) / real n"
      unfolding eventually_sequentially by auto

    have A: "eventually (\<lambda>n. dist x (f x) * (1/n) + additive_strength f xi + 16 * deltaG TYPE('a) * (\<lceil>log 2 n\<rceil> / n) = (dist x (f x) + real n * additive_strength f xi + real_of_int (\<lceil>log 2 (real n)\<rceil> * 16) * deltaG TYPE('a)) / real n) sequentially"
      unfolding eventually_sequentially apply (rule exI[of _ 1]) by (simp add: algebra_simps divide_simps)
    have B: "(\<lambda>n. dist x (f x) * (1/n) + additive_strength f xi + 16 * deltaG TYPE('a) * (\<lceil>log 2 n\<rceil> / n)) \<longlonglongrightarrow> dist x (f x) * 0 + additive_strength f xi + 16 * deltaG TYPE('a) * 0"
      by (intro tendsto_intros)
    show "(\<lambda>n. (dist x (f x) + n * additive_strength f xi + real_of_int (\<lceil>log 2 n\<rceil> * 16) * deltaG TYPE('a)) / real n) \<longlonglongrightarrow> additive_strength f xi"
      using Lim_transform_eventually[OF A B] by simp
  qed
  then show ?thesis
    using LIMSEQ_unique stable_translation_length_as_pointwise_limit[OF isometryD(4)[OF assms(1)]] by blast
qed

lemma stable_translation_length_eq_additive_strength:
  assumes "isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "Gromov_extension f xi = xi"
  shows "stable_translation_length f = abs(additive_strength f xi)"
proof (cases "additive_strength f xi \<ge> 0")
  case True
  then show ?thesis using stable_translation_length_eq_additive_strength_aux[OF assms] by auto
next
  case False
  then have *: "abs(additive_strength f xi) = additive_strength (inv f) xi"
    unfolding additive_strength_inv[OF assms] by auto
  show ?thesis
    unfolding * stable_translation_length_inv[OF assms(1), symmetric]
    using stable_translation_length_eq_additive_strength_aux[OF isometry_inverse(1)[OF assms(1)] Gromov_extension_inv_fixed_point[OF assms]] * by auto
qed


subsection \<open>Elliptic isometries\<close>

text \<open>Elliptic isometries are the simplest ones: they have bounded orbits.\<close>

definition elliptic_isometry::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> bool"
  where "elliptic_isometry f = (isometry f \<and> (\<forall>x. bounded {(f^^n) x|n. True}))"

lemma elliptic_isometryD:
  assumes "elliptic_isometry f"
  shows "bounded {(f^^n) x |n. True}"
        "isometry f"
using assms unfolding elliptic_isometry_def by auto

lemma elliptic_isometryI [intro]:
  assumes "bounded {(f^^n) x |n. True}"
          "isometry f"
  shows "elliptic_isometry f"
proof -
  have "bounded {(f^^n) y |n. True}" for y
  proof -
    obtain c e where c: "\<And>n. dist c ((f^^n) x) \<le> e"
      using assms(1) unfolding bounded_def by auto
    have "dist c ((f^^n) y) \<le> e + dist x y" for n
    proof -
      have "dist c ((f^^n) y) \<le> dist c ((f^^n) x) + dist ((f^^n) x) ((f^^n) y)"
        by (intro mono_intros)
      also have "... \<le> e + dist x y"
        using c[of n] isometry_iterates[OF assms(2), of n] by (intro mono_intros, auto simp add: isometryD)
      finally show ?thesis by simp
    qed
    then show ?thesis
      unfolding bounded_def by auto
  qed
  then show ?thesis unfolding elliptic_isometry_def using assms by auto
qed

text \<open>The inverse of an elliptic isometry is an elliptic isometry.\<close>

lemma elliptic_isometry_inv:
  assumes "elliptic_isometry f"
  shows "elliptic_isometry (inv f)"
proof -
  obtain c e where A: "\<And>n. dist c ((f^^n) basepoint) \<le> e"
    using elliptic_isometryD(1)[OF assms, of basepoint] unfolding bounded_def by auto
  have "c = (f^^n) (((inv f)^^n) c)" for n
    using fn_o_inv_fn_is_id[OF isometry_inverse(2)[OF elliptic_isometryD(2)[OF assms]], of n]
    unfolding comp_def by metis
  then have "dist ((f^^n) (((inv f)^^n) c)) ((f^^n) basepoint) \<le> e" for n
    using A by auto
  then have B: "dist basepoint (((inv f)^^n) c) \<le> e" for n
    unfolding isometryD(2)[OF isometry_iterates[OF elliptic_isometryD(2)[OF assms]]] by (auto simp add: dist_commute)
  show ?thesis
    apply (rule elliptic_isometryI[of _ c])
    using isometry_inverse(1)[OF elliptic_isometryD(2)[OF assms]] B unfolding bounded_def by auto
qed

text \<open>The inverse of a bijective map is an elliptic isometry if and only if the original map is.\<close>

lemma elliptic_isometry_inv_iff:
  assumes "bij f"
  shows "elliptic_isometry (inv f) \<longleftrightarrow> elliptic_isometry f"
using elliptic_isometry_inv[of f] elliptic_isometry_inv[of "inv f"] inv_inv_eq[OF assms] by auto

text \<open>The identity is an elliptic isometry.\<close>

lemma elliptic_isometry_id:
  "elliptic_isometry id"
by (intro elliptic_isometryI isometryI, auto)

text \<open>The translation length of an elliptic isometry is $0$.\<close>

lemma elliptic_isometry_stable_translation_length:
  assumes "elliptic_isometry f"
  shows "stable_translation_length f = 0"
proof -
  obtain x::'a where True by auto
  have "bounded {(f^^n) x|n. True}"
    using elliptic_isometryD[OF assms] by auto
  then obtain c C where cC: "\<And>n. dist c ((f^^n) x) \<le> C"
    unfolding bounded_def by auto
  have "(\<lambda>n. dist x ((f^^n) x)/n) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ sequentially "\<lambda>n. 2 * C / n"])
    have "(\<lambda>n. 2 * C * (1 / real n)) \<longlonglongrightarrow> 2 * C * 0" by (intro tendsto_intros)
    then show "(\<lambda>n. 2 * C / real n) \<longlonglongrightarrow> 0" by auto
    have "dist x ((f ^^ n) x) / real n \<le> 2 * C / real n" for n
      using cC[of 0] cC[of n] dist_triangle[of x "(f^^n) x" c] by (auto simp add: algebra_simps divide_simps dist_commute)
    then show "eventually (\<lambda>n. dist x ((f ^^ n) x) / real n \<le> 2 * C / real n) sequentially"
      by auto
  qed (auto)
  moreover have "(\<lambda>n. dist x ((f^^n) x)/n) \<longlonglongrightarrow> stable_translation_length f"
    by (rule stable_translation_length_as_pointwise_limit[OF isometry_on_lipschitz[OF isometryD(1)[OF elliptic_isometryD(2)[OF assms]]]])
  ultimately show ?thesis
    using LIMSEQ_unique by auto
qed

text \<open>If an isometry has a fixed point, then it is elliptic.\<close>

lemma isometry_with_fixed_point_is_elliptic:
  assumes "isometry f" "f x = x"
  shows "elliptic_isometry f"
proof -
  have *: "(f^^n) x = x" for n
    apply (induction n) using assms(2) by auto
  show ?thesis
    apply (rule elliptic_isometryI[of _ x, OF _ assms(1)]) unfolding * by auto
qed


subsection \<open>Parabolic and loxodromic isometries\<close>

text \<open>An isometry is parabolic if it is not elliptic and if its translation length vanishes.\<close>

definition parabolic_isometry::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> bool"
  where "parabolic_isometry f = (isometry f \<and> \<not>elliptic_isometry f \<and> stable_translation_length f = 0)"

text \<open>An isometry is loxodromic if it is not elliptic and if its translation length is nonzero.\<close>

definition loxodromic_isometry::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> bool"
  where "loxodromic_isometry f = (isometry f \<and> \<not>elliptic_isometry f \<and> stable_translation_length f \<noteq> 0)"

text \<open>The main features of such isometries are expressed in terms of their fixed points at infinity.
We define them now, but proving that the definitions make sense will take some work.\<close>

definition neutral_fixed_point::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> 'a Gromov_completion"
  where "neutral_fixed_point f = (SOME xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi = 0)"

definition attracting_fixed_point::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> 'a Gromov_completion"
  where "attracting_fixed_point f = (SOME xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi < 0)"

definition repelling_fixed_point::"('a::Gromov_hyperbolic_space \<Rightarrow> 'a) \<Rightarrow> 'a Gromov_completion"
  where "repelling_fixed_point f = (SOME xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi > 0)"


lemma parabolic_isometryD:
  assumes "parabolic_isometry f"
  shows "isometry f"
        "\<not>bounded {(f^^n) x|n. True}"
        "stable_translation_length f = 0"
        "\<not>elliptic_isometry f"
using assms unfolding parabolic_isometry_def by auto

lemma parabolic_isometryI:
  assumes "isometry f"
          "\<not>bounded {(f^^n) x|n. True}"
          "stable_translation_length f = 0"
  shows "parabolic_isometry f"
using assms unfolding parabolic_isometry_def elliptic_isometry_def by auto

lemma loxodromic_isometryD:
  assumes "loxodromic_isometry f"
  shows "isometry f"
        "\<not>bounded {(f^^n) x|n. True}"
        "stable_translation_length f > 0"
        "\<not>elliptic_isometry f"
using assms unfolding loxodromic_isometry_def
by (auto, meson dual_order.antisym not_le stable_translation_length_nonneg)

text \<open>To have a loxodromic isometry, it suffices to know that the stable translation length is
nonzero, as elliptic isometries have zero translation length.\<close>

lemma loxodromic_isometryI:
  assumes "isometry f"
          "stable_translation_length f \<noteq> 0"
  shows "loxodromic_isometry f"
using assms elliptic_isometry_stable_translation_length unfolding loxodromic_isometry_def by auto

text \<open>Any isometry is elliptic, or parabolic, or loxodromic, and these possibilities are mutually
exclusive.\<close>

lemma elliptic_or_parabolic_or_loxodromic:
  assumes "isometry f"
  shows "elliptic_isometry f \<or> parabolic_isometry f \<or> loxodromic_isometry f"
using assms unfolding parabolic_isometry_def loxodromic_isometry_def by auto

lemma elliptic_imp_not_parabolic_loxodromic:
  assumes "elliptic_isometry f"
  shows "\<not>parabolic_isometry f"
        "\<not>loxodromic_isometry f"
using assms unfolding parabolic_isometry_def loxodromic_isometry_def by auto

lemma parabolic_imp_not_elliptic_loxodromic:
  assumes "parabolic_isometry f"
  shows "\<not>elliptic_isometry f"
        "\<not>loxodromic_isometry f"
using assms unfolding parabolic_isometry_def loxodromic_isometry_def by auto

lemma loxodromic_imp_not_elliptic_parabolic:
  assumes "loxodromic_isometry f"
  shows "\<not>elliptic_isometry f"
        "\<not>parabolic_isometry f"
using assms unfolding parabolic_isometry_def loxodromic_isometry_def by auto

text \<open>The inverse of a parabolic isometry is parabolic.\<close>

lemma parabolic_isometry_inv:
  assumes "parabolic_isometry f"
  shows "parabolic_isometry (inv f)"
unfolding parabolic_isometry_def using isometry_inverse[of f] elliptic_isometry_inv_iff[of f]
parabolic_isometryD[OF assms] stable_translation_length_inv[of f] by auto

text \<open>The inverse of a loxodromic isometry is loxodromic.\<close>

lemma loxodromic_isometry_inv:
  assumes "loxodromic_isometry f"
  shows "loxodromic_isometry (inv f)"
unfolding loxodromic_isometry_def using isometry_inverse[of f] elliptic_isometry_inv_iff[of f]
loxodromic_isometryD[OF assms] stable_translation_length_inv[of f] by auto

text \<open>We will now prove that an isometry which is not elliptic has a fixed point at infinity. This
is very easy if the space is proper (ensuring that the Gromov completion is compact), but in fact
this holds in general. One constructs it by considering a sequence $r_n$ such that $f^{r_n} 0$ tends
to infinity, and additionally $d(f^l 0, 0) < d(f^{r_n} 0, 0)$ for $l < r_n$: this implies the
convergence at infinity of $f^{r_n} 0$, by an argument based on a Gromov product computation -- and
the limit is a fixed point. Moreover, it has nonpositive additive strength, essentially by
construction.\<close>

lemma high_scores:
  fixes u::"nat \<Rightarrow> real" and i::nat and C::real
  assumes "\<not>(bdd_above (range u))"
  shows "\<exists>n. (\<forall>l \<le> n. u l \<le> u n) \<and> u n \<ge> C \<and> n \<ge> i"
proof -
  define M where "M = max C (Max {u l|l. l < i})"
  define n where "n = Inf {m. u m > M}"
  have "\<not>(range u \<subseteq> {..M})"
    using assms by (meson bdd_above_Iic bdd_above_mono)
  then have "{m. u m > M} \<noteq> {}"
    using assms by (simp add: image_subset_iff not_less)
  then have "n \<in> {m. u m > M}" unfolding n_def using Inf_nat_def1 by metis
  then have "u n > M" by simp
  have "n \<ge> i"
  proof (rule ccontr)
    assume "\<not> i \<le> n"
    then have *: "n < i" by simp
    have "u n \<le> Max {u l|l. l < i}" apply (rule Max_ge) using * by auto
    then show False using \<open>u n > M\<close> M_def by auto
  qed
  moreover have "u l \<le> u n" if "l \<le> n" for l
  proof (cases "l = n")
    case True
    then show ?thesis by simp
  next
    case False
    then have "l < n" using \<open>l \<le> n\<close> by auto
    then have "l \<notin> {m. u m > M}"
      unfolding n_def by (meson bdd_below_def cInf_lower not_le zero_le)
    then show ?thesis using \<open>u n > M\<close> by auto
  qed
  ultimately show ?thesis
    using \<open>u n > M\<close> M_def less_eq_real_def by auto
qed

lemma isometry_not_elliptic_has_attracting_fixed_point:
  assumes "isometry f"
          "\<not>(elliptic_isometry f)"
  shows "\<exists>xi \<in> Gromov_boundary. Gromov_extension f xi = xi \<and> additive_strength f xi \<le> 0"
proof -
  define u where "u = (\<lambda>n. dist basepoint ((f^^n) basepoint))"
  have NB: "\<not>(bdd_above (range u))"
  proof
    assume "bdd_above (range u)"
    then obtain C where *: "\<And>n. u n \<le> C" unfolding bdd_above_def by auto
    have "bounded {(f^^n) basepoint|n. True}"
      unfolding bounded_def apply (rule exI[of _ basepoint], rule exI[of _ C])
      using * unfolding u_def by auto
    then show False
      using elliptic_isometryI assms by auto
  qed
  have "\<exists>r. \<forall>n. ((\<forall>l \<le> r n. u l \<le> u (r n)) \<and> u (r n) \<ge> 2 * n) \<and> r (Suc n) \<ge> r n + 1"
    apply (rule dependent_nat_choice) using high_scores[OF NB] by (auto) blast
  then obtain r::"nat \<Rightarrow> nat" where r: "\<And>n l. l \<le> r n \<Longrightarrow> u l \<le> u (r n)"
                                       "\<And>n. u (r n) \<ge> 2 * n" "\<And>n. r (Suc n) \<ge> r n + 1"
    by auto
  then have "strict_mono r"
    by (metis Suc_eq_plus1 Suc_le_lessD strict_monoI_Suc)
  then have "r n \<ge> n" for n
    by (simp add: seq_suble)

  have A: "dist ((f^^(r p)) basepoint) ((f^^(r n)) basepoint) \<le> dist basepoint ((f^^(r n)) basepoint)" if "n \<ge> p" for n p
  proof -
    have "r n \<ge> r p" using \<open>n \<ge> p\<close> \<open>strict_mono r\<close> by (simp add: strict_mono_less_eq)
    then have *: "f^^((r n)) = (f^^(r p)) o (f^^(r n - r p))"
      unfolding funpow_add[symmetric] by auto
    have "dist ((f^^(r p)) basepoint) ((f^^(r n)) basepoint) = dist ((f^^(r p)) basepoint) ((f^^(r p)) ((f^^(r n - r p)) basepoint))"
      unfolding * comp_def by auto
    also have "... = dist basepoint ((f^^(r n - r p)) basepoint)"
      using isometry_iterates[OF assms(1), of "r p"] isometryD by auto
    also have "... \<le> dist basepoint ((f^^(r n)) basepoint)"
      using r(1)[of "r n - r p" n] unfolding u_def by auto
    finally show ?thesis
      by simp
  qed

  have *: "Gromov_product_at basepoint ((f^^(r p)) basepoint) ((f^^(r n)) basepoint) \<ge> p" if "n \<ge> p" for n p
  proof -
    have "2 * Gromov_product_at basepoint ((f^^(r p)) basepoint) ((f^^(r n)) basepoint)
            = dist basepoint ((f^^(r p)) basepoint) + dist basepoint ((f^^(r n)) basepoint)
              - dist ((f^^(r p)) basepoint) ((f^^(r n)) basepoint)"
      unfolding Gromov_product_at_def by auto
    also have "... \<ge> dist basepoint ((f^^(r p)) basepoint)"
      using A[OF that] by auto
    finally show "Gromov_product_at basepoint ((f^^(r p)) basepoint) ((f^^(r n)) basepoint) \<ge> p"
      using r(2)[of p] unfolding u_def by auto
  qed
  have *: "Gromov_product_at basepoint ((f^^(r p)) basepoint) ((f^^(r n)) basepoint) \<ge> N" if "n \<ge> N" "p \<ge> N" for n p N
    using *[of n p] *[of p n] that by (auto simp add: Gromov_product_commute intro: le_cases[of n p])
  have "Gromov_converging_at_boundary (\<lambda>n. (f^^(r n)) basepoint)"
    apply (rule Gromov_converging_at_boundaryI[of basepoint]) using * by (meson dual_order.trans real_arch_simple)
  with Gromov_converging_at_boundary_converges[OF this]
  obtain xi where xi: "(\<lambda>n. to_Gromov_completion ((f^^(r n)) basepoint)) \<longlonglongrightarrow> xi" "xi \<in> Gromov_boundary"
    by auto
  then have *: "(\<lambda>n. Gromov_extension f (to_Gromov_completion ((f^^(r n)) basepoint))) \<longlonglongrightarrow> xi"
    apply (simp, rule Gromov_converging_at_boundary_bounded_perturbation[of _ _ _ "dist basepoint (f basepoint)"])
    by (simp add: assms(1) funpow_swap1 isometryD(2) isometry_iterates)
  moreover have "(\<lambda>n. Gromov_extension f (to_Gromov_completion ((f^^(r n)) basepoint))) \<longlonglongrightarrow> Gromov_extension f xi"
    using continuous_on_tendsto_compose[OF Gromov_extension_isometry(2)[OF assms(1)] xi(1)] by auto
  ultimately have fxi: "Gromov_extension f xi = xi"
    using LIMSEQ_unique by auto

  have "Busemann_function_at (to_Gromov_completion ((f^^(r n)) basepoint)) ((f^^(r p)) basepoint) basepoint \<le> 0" if "n \<ge> p" for n p
    unfolding Busemann_function_inner using A[OF that] by auto
  then have A: "eventually (\<lambda>n. Busemann_function_at (to_Gromov_completion ((f^^(r n)) basepoint)) ((f^^(r p)) basepoint) basepoint \<le> 0) sequentially" for p
    unfolding eventually_sequentially by auto
  have B: "eventually (\<lambda>n. Busemann_function_at (to_Gromov_completion ((f^^(r n)) basepoint)) ((f^^(r p)) basepoint) basepoint \<ge> Busemann_function_at xi ((f^^(r p)) basepoint) basepoint - 2 * deltaG(TYPE('a)) - 1) sequentially" for p
    by (rule eventually_mono[OF Busemann_function_inside_approx[OF _ xi(1), of 1 "((f^^(r p)) basepoint)" basepoint, simplified]], simp)
  have "eventually (\<lambda>n. Busemann_function_at xi ((f^^(r p)) basepoint) basepoint - 2 * deltaG(TYPE('a)) - 1 \<le> 0) sequentially" for p
    by (rule eventually_mono[OF eventually_conj[OF A[of p] B[of p]]], simp)
  then have *: "Busemann_function_at xi ((f^^(r p)) basepoint) basepoint - 2 * deltaG(TYPE('a)) - 1 \<le> 0" for p
    by auto
  then have A: "Busemann_function_at xi ((f^^(r p)) basepoint) basepoint / (r p) - (2 * deltaG(TYPE('a)) + 1) * (1/r p) \<le> 0" if "p \<ge> 1" for p
    using order_trans[OF that \<open>p \<le> r p\<close>] by (auto simp add: algebra_simps divide_simps)
  have B: "(\<lambda>p. Busemann_function_at xi ((f^^(p)) basepoint) basepoint / p - (2 * deltaG(TYPE('a)) + 1) * (1/p)) \<longlonglongrightarrow> additive_strength f xi - (2 * deltaG(TYPE('a)) + 1) * 0"
    by (intro tendsto_intros assms fxi)
  have "additive_strength f xi - (2 * deltaG TYPE('a) + 1) * 0 \<le> 0"
    apply (rule LIMSEQ_le_const2[OF LIMSEQ_subseq_LIMSEQ[OF B \<open>strict_mono r\<close>]]) using A unfolding comp_def by auto
  then show ?thesis using xi fxi by auto
qed

text \<open>Applying the previous result to the inverse map, we deduce that there is also a fixed point
with nonnegative strength.\<close>

lemma isometry_not_elliptic_has_repelling_fixed_point:
  assumes "isometry f"
          "\<not>(elliptic_isometry f)"
  shows "\<exists>xi \<in> Gromov_boundary. Gromov_extension f xi = xi \<and> additive_strength f xi \<ge> 0"
proof -
  have *: "\<not>elliptic_isometry (inv f)"
    using elliptic_isometry_inv_iff isometry_inverse(2)[OF assms(1)] assms(2) by auto
  obtain xi where xi: "xi \<in> Gromov_boundary" "Gromov_extension (inv f) xi = xi" "additive_strength (inv f) xi \<le> 0"
    using isometry_not_elliptic_has_attracting_fixed_point[OF isometry_inverse(1)[OF assms(1)] *] by auto
  have *: "Gromov_extension f xi = xi"
    using Gromov_extension_inv_fixed_point[OF isometry_inverse(1)[OF assms(1)] xi(2)] inv_inv_eq[OF isometry_inverse(2)[OF assms(1)]] by auto
  moreover have "additive_strength f xi \<ge> 0"
    using additive_strength_inv[OF assms(1) *] xi(3) by auto
  ultimately show ?thesis
    using xi(1) by auto
qed

subsubsection \<open>Parabolic isometries\<close>

text \<open>We show that a parabolic isometry has (at least) one neutral fixed point at infinity.\<close>

lemma parabolic_fixed_point:
  assumes "parabolic_isometry f"
  shows "neutral_fixed_point f \<in> Gromov_boundary"
        "Gromov_extension f (neutral_fixed_point f) = neutral_fixed_point f"
        "additive_strength f (neutral_fixed_point f) = 0"
proof -
  obtain xi where xi: "xi \<in> Gromov_boundary" "Gromov_extension f xi = xi"
    using isometry_not_elliptic_has_attracting_fixed_point parabolic_isometryD[OF assms] by blast
  moreover have "additive_strength f xi = 0"
    using stable_translation_length_eq_additive_strength[OF parabolic_isometryD(1)[OF assms] xi(2)]
    parabolic_isometryD(3)[OF assms] by auto
  ultimately have A: "\<exists>xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi = 0"
    by auto
  show "neutral_fixed_point f \<in> Gromov_boundary"
        "Gromov_extension f (neutral_fixed_point f) = neutral_fixed_point f"
        "additive_strength f (neutral_fixed_point f) = 0"
    unfolding neutral_fixed_point_def using someI_ex[OF A] by auto
qed

text \<open>Parabolic isometries have exactly one fixed point, the neutral fixed point at infinity. The
proof goes as follows: if it has another fixed point, then the orbit of a basepoint would stay
on the horospheres centered at both fixed points. But the intersection of two horospheres based
at different points is a a bounded set. Hence, the map has a bounded orbit, and is therefore
elliptic.\<close>

theorem parabolic_unique_fixed_point:
  assumes "parabolic_isometry f"
  shows "Gromov_extension f xi = xi \<longleftrightarrow> xi = neutral_fixed_point f"
proof (auto simp add: parabolic_fixed_point[OF assms])
  assume H: "Gromov_extension f xi = xi"
  have *: "additive_strength f xi = 0"
    using stable_translation_length_eq_additive_strength[OF parabolic_isometryD(1)[OF assms] H]
    parabolic_isometryD(3)[OF assms] by auto
  show "xi = neutral_fixed_point f"
  proof (rule ccontr)
    assume N: "xi \<noteq> neutral_fixed_point f"
    define C where "C = 2 * real_of_ereal (extended_Gromov_product_at basepoint xi (neutral_fixed_point f)) + 4 * deltaG(TYPE('a))"
    have A: "dist basepoint ((f^^n) basepoint) \<le> C" for n
    proof -
      have "dist ((f^^n) basepoint) basepoint - 2 * real_of_ereal (extended_Gromov_product_at basepoint xi (neutral_fixed_point f)) - 2 * deltaG(TYPE('a))
            \<le> max (Busemann_function_at xi ((f^^n) basepoint) basepoint) (Busemann_function_at (neutral_fixed_point f) ((f^^n) basepoint) basepoint)"
        using dist_le_max_Busemann_functions[OF N] by (simp add: algebra_simps)
      also have "... \<le> max (n * additive_strength f xi + 2 * deltaG(TYPE('a))) (n * additive_strength f (neutral_fixed_point f) + 2 * deltaG(TYPE('a)))"
        apply (intro mono_intros)
        using Busemann_function_eq_additive_strength[OF parabolic_isometryD(1)[OF assms] H, of n basepoint]
        Busemann_function_eq_additive_strength[OF parabolic_isometryD(1)[OF assms] parabolic_fixed_point(2)[OF assms], of n basepoint]
        by auto
      also have "... = 2 * deltaG(TYPE('a))"
        unfolding * parabolic_fixed_point[OF assms] by auto
      finally show ?thesis
        unfolding C_def by (simp add: algebra_simps dist_commute)
    qed
    have "elliptic_isometry f"
      apply (rule elliptic_isometryI[of _ basepoint])
      using parabolic_isometryD(1)[OF assms] A unfolding bounded_def by auto
    then show False
      using elliptic_imp_not_parabolic_loxodromic assms by auto
  qed
qed

text \<open>When one iterates a parabolic isometry, the distance to the starting point can grow at most
logarithmically.\<close>

lemma parabolic_logarithmic_growth:
  assumes "parabolic_isometry (f::'a::Gromov_hyperbolic_space \<Rightarrow> 'a)" "n \<ge> 1"
  shows "dist x ((f^^n) x) \<le> dist x (f x) + ceiling (log 2 n) * 16 * deltaG(TYPE('a))"
using dist_le_additive_strength[OF parabolic_isometryD(1)[OF assms(1)] parabolic_fixed_point(2)[OF assms(1)] _ assms(2)]
parabolic_isometryD(3)[OF assms(1)] stable_translation_length_eq_additive_strength[OF parabolic_isometryD(1)[OF assms(1)] parabolic_fixed_point(2)[OF assms(1)]]
by auto

text \<open>It follows that there is no parabolic isometry in trees, since the formula in the previous
lemma shows that there is no orbit growth as $\delta = 0$, and therefore orbits are bounded,
contradicting the parabolicity of the isometry.\<close>

lemma tree_no_parabolic_isometry:
  assumes "isometry (f::'a::Gromov_hyperbolic_space_0 \<Rightarrow> 'a)"
  shows "elliptic_isometry f \<or> loxodromic_isometry f"
proof -
  have "\<not>parabolic_isometry f"
  proof
    assume P: "parabolic_isometry f"
    have "dist basepoint ((f^^n) basepoint) \<le> dist basepoint (f basepoint)" if "n \<ge> 1" for n
      using parabolic_logarithmic_growth[OF P that, of basepoint] by auto
    then have *: "dist basepoint ((f^^n) basepoint) \<le> dist basepoint (f basepoint)" for n
      by (cases "n \<ge> 1", auto simp add: not_less_eq_eq)
    have "elliptic_isometry f"
      apply (rule elliptic_isometryI[OF _ assms, of basepoint]) using * unfolding bounded_def by auto
    then show False
      using elliptic_imp_not_parabolic_loxodromic P by auto
  qed
  then show ?thesis
    using elliptic_or_parabolic_or_loxodromic[OF assms] by auto
qed


subsubsection \<open>Loxodromic isometries\<close>

text \<open>A loxodromic isometry has (at least) two fixed points at infinity, one attracting
and one repelling. We have already constructed fixed points with nonnegative and nonpositive
strengths. Since the strength is nonzero (its absolute value is the stable translation length),
then these fixed points correspond to what we want.\<close>

lemma loxodromic_attracting_fixed_point:
  assumes "loxodromic_isometry f"
  shows "attracting_fixed_point f \<in> Gromov_boundary"
        "Gromov_extension f (attracting_fixed_point f) = attracting_fixed_point f"
        "additive_strength f (attracting_fixed_point f) < 0"
proof -
  obtain xi where xi: "xi \<in> Gromov_boundary" "Gromov_extension f xi = xi" "additive_strength f xi \<le> 0"
    using isometry_not_elliptic_has_attracting_fixed_point loxodromic_isometryD[OF assms] by blast
  moreover have "additive_strength f xi < 0"
    using stable_translation_length_eq_additive_strength[OF loxodromic_isometryD(1)[OF assms] xi(2)]
    loxodromic_isometryD(3)[OF assms] xi(3) by auto
  ultimately have A: "\<exists>xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi < 0"
    by auto
  show "attracting_fixed_point f \<in> Gromov_boundary"
       "Gromov_extension f (attracting_fixed_point f) = attracting_fixed_point f"
       "additive_strength f (attracting_fixed_point f) < 0"
    unfolding attracting_fixed_point_def using someI_ex[OF A] by auto
qed

lemma loxodromic_repelling_fixed_point:
  assumes "loxodromic_isometry f"
  shows "repelling_fixed_point f \<in> Gromov_boundary"
        "Gromov_extension f (repelling_fixed_point f) = repelling_fixed_point f"
        "additive_strength f (repelling_fixed_point f) > 0"
proof -
  obtain xi where xi: "xi \<in> Gromov_boundary" "Gromov_extension f xi = xi" "additive_strength f xi \<ge> 0"
    using isometry_not_elliptic_has_repelling_fixed_point loxodromic_isometryD[OF assms] by blast
  moreover have "additive_strength f xi > 0"
    using stable_translation_length_eq_additive_strength[OF loxodromic_isometryD(1)[OF assms] xi(2)]
    loxodromic_isometryD(3)[OF assms] xi(3) by auto
  ultimately have A: "\<exists>xi. xi \<in> Gromov_boundary \<and> Gromov_extension f xi = xi \<and> additive_strength f xi > 0"
    by auto
  show "repelling_fixed_point f \<in> Gromov_boundary"
       "Gromov_extension f (repelling_fixed_point f) = repelling_fixed_point f"
       "additive_strength f (repelling_fixed_point f) > 0"
    unfolding repelling_fixed_point_def using someI_ex[OF A] by auto
qed

text \<open>The attracting and repelling fixed points of a loxodromic isometry are distinct -- precisely
since one is attracting and the other is repelling.\<close>

lemma attracting_fixed_point_neq_repelling_fixed_point:
  assumes "loxodromic_isometry f"
  shows "attracting_fixed_point f \<noteq> repelling_fixed_point f"
using loxodromic_repelling_fixed_point[OF assms] loxodromic_attracting_fixed_point[OF assms] by auto

text \<open>The attracting fixed point of a loxodromic isometry is indeed attracting. Moreover, the
convergence is uniform away from the repelling fixed point. This is expressed in the following
proposition, where neighborhoods of the repelling and attracting fixed points are given by the property
that the Gromov product with the fixed point is large.

The proof goes as follows. First, the Busemann function with respect to the fixed points at infinity
evolves like the strength. Therefore, $f^n e$ tends to the repulsive fixed point in negative time,
and to the attracting one in positive time. Consider now a general point $x$ with
$(\xi^-, x)_e \leq K$. This means that the geodesics from $e$ to $x$ and $\xi^-$ diverge before
time $K$. For large $n$, since $f^{-n} e$ is close to $\xi^-$, we also get the inequality
$(f^{-n} e, x)_e \leq K$. Applying $f^n$ and using the invariance of the Gromov product under
isometries yields $(e, f^n x)_{f^n e} \leq K$. But this Gromov product is equal to
$d(e, f^n e) - (f^n e, f^n x)_e$ (this is a general property of Gromov products). In particular,
$(f^n e, f^n x) \geq d(e, f^n e) - K$, and moreover $d(e, f^n e)$ is large.
Since $f^n e$ is close to $\xi^+$, it follows that $f^n x$
is also close to $\xi^+$, as desired.

The real proof requires some more care as everything should be done in ereal, and moreover every
inequality is only true up to some multiple of $\delta$. But everything works in the way just
described above.
\<close>

proposition loxodromic_attracting_fixed_point_attracts_uniformly:
  assumes "loxodromic_isometry f"
  shows "\<exists>N. \<forall>n \<ge> N. \<forall>x. extended_Gromov_product_at basepoint x (repelling_fixed_point f) \<le> ereal K
          \<longrightarrow> extended_Gromov_product_at basepoint (((Gromov_extension f)^^n) x) (attracting_fixed_point f) \<ge> ereal M"
proof -
  have I: "isometry f"
    using loxodromic_isometryD(1)[OF assms] by simp
  have J: "\<bar>ereal r\<bar> \<noteq> \<infinity>" for r by auto

  text \<open>We show that $f^n e$ tends to the repelling fixed point in negative time.\<close>
  have "(\<lambda>n. ereal (Busemann_function_at (repelling_fixed_point f) ((inv f ^^ n) basepoint) basepoint)) \<longlonglongrightarrow> - \<infinity>"
  proof (rule tendsto_sandwich[of "\<lambda>n. -\<infinity>" _ _ "\<lambda>n. ereal(- real n * additive_strength f (repelling_fixed_point f) + 2 * deltaG(TYPE('a)))", OF _ always_eventually], auto)
    fix n
    have "Busemann_function_at (repelling_fixed_point f) ((inv f ^^ n) basepoint) basepoint \<le> real n * additive_strength (inv f) (repelling_fixed_point f) + 2 * deltaG(TYPE('a))"
      using Busemann_function_eq_additive_strength[OF isometry_inverse(1)[OF I]
      Gromov_extension_inv_fixed_point[OF I loxodromic_repelling_fixed_point(2)[OF assms]], of n basepoint] by auto
    then show "Busemann_function_at (repelling_fixed_point f) ((inv f ^^ n) basepoint) basepoint \<le> 2 * deltaG(TYPE('a)) - real n * additive_strength f (repelling_fixed_point f)"
      by (simp add: I additive_strength_inv assms loxodromic_repelling_fixed_point(2))
  next
    have "(\<lambda>n. ereal (2 * deltaG TYPE('a)) + ereal (- real n) * additive_strength f (repelling_fixed_point f)) \<longlonglongrightarrow> ereal (2 * deltaG (TYPE('a))) + (- \<infinity>) * additive_strength f (repelling_fixed_point f)"
      apply (intro tendsto_intros) using loxodromic_repelling_fixed_point(3)[OF assms] by auto
    then show "(\<lambda>n. ereal (2 * deltaG TYPE('a) - real n * additive_strength f (repelling_fixed_point f))) \<longlonglongrightarrow> - \<infinity>"
      using loxodromic_repelling_fixed_point(3)[OF assms] by auto
  qed
  then have "(\<lambda>n. to_Gromov_completion (((inv f)^^n) basepoint)) \<longlonglongrightarrow> repelling_fixed_point f"
    by (rule Busemann_function_minus_infinity_imp_convergent[of _ _ basepoint])
  then have "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (((inv f)^^n) basepoint)) (repelling_fixed_point f)) \<longlonglongrightarrow> \<infinity>"
    unfolding Gromov_completion_boundary_limit[OF loxodromic_repelling_fixed_point(1)[OF assms]] by simp
  then obtain Nr where Nr: "\<And>n. n \<ge> Nr \<Longrightarrow> extended_Gromov_product_at basepoint (to_Gromov_completion (((inv f)^^n) basepoint)) (repelling_fixed_point f) \<ge> ereal (K + deltaG(TYPE('a)) + 1)"
    unfolding Lim_PInfty by auto

  text \<open>We show that $f^n e$ tends to the attracting fixed point in positive time.\<close>
  have "(\<lambda>n. ereal (Busemann_function_at (attracting_fixed_point f) ((f ^^ n) basepoint) basepoint)) \<longlonglongrightarrow> - \<infinity>"
  proof (rule tendsto_sandwich[of "\<lambda>n. -\<infinity>" _ _ "\<lambda>n. ereal(real n * additive_strength f (attracting_fixed_point f) + 2 * deltaG(TYPE('a)))", OF _ always_eventually], auto)
    fix n
    show "Busemann_function_at (attracting_fixed_point f) ((f ^^ n) basepoint) basepoint \<le> real n * additive_strength f (attracting_fixed_point f) + 2 * deltaG(TYPE('a))"
      using Busemann_function_eq_additive_strength[OF I loxodromic_attracting_fixed_point(2)[OF assms], of n basepoint] by auto
  next
    have "(\<lambda>n. ereal (2 * deltaG TYPE('a)) + ereal (real n) * additive_strength f (attracting_fixed_point f)) \<longlonglongrightarrow> ereal (2 * deltaG (TYPE('a))) + (\<infinity>) * additive_strength f (attracting_fixed_point f)"
      apply (intro tendsto_intros) using loxodromic_attracting_fixed_point(3)[OF assms] by auto
    then show "(\<lambda>n. ereal (real n * additive_strength f (attracting_fixed_point f) + 2 * deltaG TYPE('a))) \<longlonglongrightarrow> - \<infinity>"
      using loxodromic_attracting_fixed_point(3)[OF assms] by (auto simp add: algebra_simps)
  qed
  then have *: "(\<lambda>n. to_Gromov_completion (((f)^^n) basepoint)) \<longlonglongrightarrow> attracting_fixed_point f"
    by (rule Busemann_function_minus_infinity_imp_convergent[of _ _ basepoint])
  then have "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (((f)^^n) basepoint)) (attracting_fixed_point f)) \<longlonglongrightarrow> \<infinity>"
    unfolding Gromov_completion_boundary_limit[OF loxodromic_attracting_fixed_point(1)[OF assms]] by simp
  then obtain Na where Na: "\<And>n. n \<ge> Na \<Longrightarrow> extended_Gromov_product_at basepoint (to_Gromov_completion (((f)^^n) basepoint)) (attracting_fixed_point f) \<ge> ereal (M + deltaG(TYPE('a)))"
    unfolding Lim_PInfty by auto

  text \<open>We show that the distance between $e$ and $f^n e$ tends to infinity.\<close>
  have "(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (to_Gromov_completion ((f^^n) basepoint))) \<longlonglongrightarrow>
          extended_Gromov_distance (to_Gromov_completion basepoint) (attracting_fixed_point f)"
    using * extended_Gromov_distance_continuous[of "to_Gromov_completion basepoint"]
    by (metis UNIV_I continuous_on filterlim_compose tendsto_at_iff_tendsto_nhds)
  then have "(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (to_Gromov_completion ((f^^n) basepoint))) \<longlonglongrightarrow> \<infinity>"
    using loxodromic_attracting_fixed_point(1)[OF assms] by simp
  then obtain Nd where Nd: "\<And>n. n \<ge> Nd \<Longrightarrow> dist basepoint ((f^^n) basepoint) \<ge> M + K + 3 * deltaG(TYPE('a))"
    unfolding Lim_PInfty by auto

  text \<open>Now, if $n$ is large enough so that all the convergences to infinity above are almost
  realized, we show that a point $x$ which is not too close to $\xi^-$ is sent by $f^n$ to a point
  close to $\xi^+$, uniformly.\<close>
  define N where "N = Nr + Na + Nd"
  have "extended_Gromov_product_at basepoint (((Gromov_extension f)^^n) x) (attracting_fixed_point f) \<ge> ereal M" if H: "extended_Gromov_product_at basepoint x (repelling_fixed_point f) \<le> K" "n \<ge> N" for n x
  proof -
    have n: "n \<ge> Nr" "n \<ge> Na" "n \<ge> Nd" using that unfolding N_def by auto
    have "min (extended_Gromov_product_at basepoint x (to_Gromov_completion (((inv f)^^n) basepoint)))
              (extended_Gromov_product_at basepoint (to_Gromov_completion (((inv f)^^n) basepoint)) (repelling_fixed_point f))
          \<le> extended_Gromov_product_at basepoint x (repelling_fixed_point f) + deltaG(TYPE('a))"
      by (intro mono_intros)
    also have "... \<le> ereal K + deltaG(TYPE('a))"
      apply (intro mono_intros) using H by auto
    finally have "min (extended_Gromov_product_at basepoint x (to_Gromov_completion (((inv f)^^n) basepoint)))
              (extended_Gromov_product_at basepoint (to_Gromov_completion (((inv f)^^n) basepoint)) (repelling_fixed_point f))
                \<le> ereal K + deltaG(TYPE('a))"
      by simp
    moreover have "extended_Gromov_product_at basepoint (to_Gromov_completion (((inv f)^^n) basepoint)) (repelling_fixed_point f) > ereal K + deltaG(TYPE('a))"
      using Nr[OF n(1)] ereal_le_less by auto
    ultimately have A: "extended_Gromov_product_at basepoint x (to_Gromov_completion (((inv f)^^n) basepoint)) \<le> ereal K + deltaG(TYPE('a))"
      using not_le by fastforce
    have *: "((inv f)^^n) ((f^^n) z) = z" for z
      by (metis I bij_is_inj inj_fn inv_f_f inv_fn isometry_inverse(2))
    have **: "x = Gromov_extension ((inv f)^^n) (Gromov_extension (f^^n) x)"
      using Gromov_extension_isometry_composition[OF isometry_iterates[OF I] isometry_iterates[OF isometry_inverse(1)[OF I]], of n n]
      unfolding comp_def * apply auto by meson
    have "extended_Gromov_product_at (((inv f)^^n) ((f^^n) basepoint)) (Gromov_extension ((inv f)^^n) (Gromov_extension (f^^n) x)) (Gromov_extension (((inv f)^^n)) (to_Gromov_completion basepoint)) \<le> ereal K + deltaG(TYPE('a))"
      using A by (simp add: * **[symmetric])
    then have B: "extended_Gromov_product_at ((f^^n) basepoint) (Gromov_extension (f^^n) x) (to_Gromov_completion basepoint) \<le> ereal K + deltaG(TYPE('a))"
      unfolding Gromov_extension_preserves_extended_Gromov_product[OF isometry_iterates[OF isometry_inverse(1)[OF I]]] by simp

    have "dist basepoint ((f^^n) basepoint) - deltaG(TYPE('a)) \<le>
        extended_Gromov_product_at ((f^^n) basepoint) (Gromov_extension (f^^n) x) (to_Gromov_completion basepoint) + extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (to_Gromov_completion ((f^^n) basepoint))"
      using extended_Gromov_product_add_ge[of basepoint "(f^^n) basepoint" "Gromov_extension (f^^n) x"] by (auto simp add: algebra_simps)
    also have "... \<le> (ereal K + deltaG(TYPE('a))) + extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (to_Gromov_completion ((f^^n) basepoint))"
      by (intro mono_intros B)
    finally have "extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (to_Gromov_completion ((f^^n) basepoint)) \<ge> dist basepoint ((f^^n) basepoint) - (2 * deltaG(TYPE('a)) + K)"
      unfolding ereal_minus(1)[symmetric] apply (simp only: ereal_minus_le[OF J]) apply (auto simp add: algebra_simps)
      by (metis (no_types, hide_lams) linordered_field_class.sign_simps(1) linordered_field_class.sign_simps(3) mult_2_right plus_ereal.simps(1))
    moreover have "dist basepoint ((f ^^ n) basepoint) - (2 * deltaG TYPE('a) + K) \<ge> M + deltaG(TYPE('a))"
      using Nd[OF n(3)] by auto
    ultimately have "extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (to_Gromov_completion ((f^^n) basepoint)) \<ge> ereal (M + deltaG(TYPE('a)))"
      using order_trans ereal_le_le by auto
    then have "ereal (M + deltaG(TYPE('a))) \<le> min (extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (to_Gromov_completion ((f^^n) basepoint)))
                                                  (extended_Gromov_product_at basepoint (to_Gromov_completion ((f^^n) basepoint)) (attracting_fixed_point f))"
      using Na[OF n(2)] by (simp add: extended_Gromov_product_at_commute)
    also have "... \<le> extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (attracting_fixed_point f) + deltaG(TYPE('a))"
      by (intro mono_intros)
    finally have "ereal M \<le> extended_Gromov_product_at basepoint (Gromov_extension (f^^n) x) (attracting_fixed_point f)"
      unfolding plus_ereal.simps(1)[symmetric] ereal_add_le_add_iff2 by auto
    then show ?thesis
      by (simp add: Gromov_extension_isometry_iterates I)
  qed
  then show ?thesis
    by auto
qed

text \<open>We deduce pointwise convergence from the previous result.\<close>

lemma loxodromic_attracting_fixed_point_attracts:
  assumes "loxodromic_isometry f"
          "xi \<noteq> repelling_fixed_point f"
  shows "(\<lambda>n. ((Gromov_extension f)^^n) xi) \<longlonglongrightarrow> attracting_fixed_point f"
proof -
  have "(\<lambda>n. extended_Gromov_product_at basepoint (((Gromov_extension f)^^n) xi) (attracting_fixed_point f)) \<longlonglongrightarrow> \<infinity>"
    unfolding Lim_PInfty using loxodromic_attracting_fixed_point_attracts_uniformly[OF assms(1)]
    by (metis Gromov_boundary_extended_product_PInf assms(2) ereal_top funpow_code_def infinity_ereal_def linear)
  then show ?thesis
    unfolding Gromov_completion_boundary_limit[OF loxodromic_attracting_fixed_point(1)[OF assms(1)]] by simp
qed

text \<open>Finally, we show that a loxodromic isometry has exactly two fixed points, its attracting and
repelling fixed points defined above. Indeed, we already know that these points are fixed. It
remains to see that there is no other fixed point. But a fixed point which is not the repelling one
is both stationary and attracted to the attracting fixed point by the previous lemma, hence it has
to coincide with the attracting fixed point.\<close>

theorem loxodromic_unique_fixed_points:
  assumes "loxodromic_isometry f"
  shows "Gromov_extension f xi = xi \<longleftrightarrow> xi = attracting_fixed_point f \<or> xi = repelling_fixed_point f"
proof -
  have "xi = attracting_fixed_point f" if H: "Gromov_extension f xi = xi" "xi \<noteq> repelling_fixed_point f" for xi
  proof -
    have "((Gromov_extension f)^^n) xi = xi" for n
      apply (induction n) using H(1) by auto
    then have "(\<lambda>n. ((Gromov_extension f)^^n) xi) \<longlonglongrightarrow> xi"
      by auto
    then show ?thesis
      using loxodromic_attracting_fixed_point_attracts[OF assms H(2)] LIMSEQ_unique by auto
  qed
  then show ?thesis
    using loxodromic_attracting_fixed_point(2)[OF assms] loxodromic_repelling_fixed_point(2)[OF assms] by auto
qed

end (*of theory Isometries_Classification*)
