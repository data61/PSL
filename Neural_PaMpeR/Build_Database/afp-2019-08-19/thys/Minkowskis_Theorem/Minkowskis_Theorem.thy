(*
  File:    Minkowskis_Theorem.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  A proof of Blichfeldt's and Minkowski's theorem about the relation between
  subsets of the Euclidean space, the Lebesgue measure, and the integer lattice.
*)
section \<open>Minkowski's theorem\<close>
theory Minkowskis_Theorem
  imports "HOL-Analysis.Analysis"
begin

(* Could be generalised to arbitrary euclidean spaces and full-dimensional lattices *)

subsection \<open>Miscellaneous material\<close>

lemma bij_betw_UN:
  assumes "bij_betw f A B"
  shows   "(\<Union>n\<in>A. g (f n)) = (\<Union>n\<in>B. g n)"
  using assms by (auto simp: bij_betw_def)

definition of_int_vec where
  "of_int_vec v = (\<chi> i. of_int (v $ i))"

lemma of_int_vec_nth [simp]: "of_int_vec v $ n = of_int (v $ n)"
  by (simp add: of_int_vec_def)

lemma of_int_vec_eq_iff [simp]:
  "(of_int_vec a :: ('a :: ring_char_0) ^ 'n) = of_int_vec b \<longleftrightarrow> a = b"
  by (simp add: of_int_vec_def vec_eq_iff)

lemma inj_axis:
  assumes "c \<noteq> 0"
  shows   "inj (\<lambda>k. axis k c :: ('a :: {zero}) ^ 'n)"
proof
  fix x y :: 'n
  assume *: "axis x c = axis y c"
  have "axis x c $ x = axis x c $ y"
    by (subst *) simp
  thus "x = y" using assms
    by (auto simp: axis_def split: if_splits)
qed

lemma compactD:
  assumes "compact (A :: 'a :: metric_space set)" "range f \<subseteq> A"
  shows   "\<exists>h l. strict_mono (h::nat\<Rightarrow>nat) \<and> (f \<circ> h) \<longlonglongrightarrow> l"
  using assms unfolding compact_def by blast

lemma closed_lattice:
  fixes A :: "(real ^ 'n) set"
  assumes "\<And>v i. v \<in> A \<Longrightarrow> v $ i \<in> \<int>"
  shows   "closed A"
proof (rule discrete_imp_closed[OF zero_less_one], safe, goal_cases)
  case (1 x y)
  have "x $ i = y $ i" for i
  proof -
    from 1 and assms have "x $ i - y $ i \<in> \<int>"
      by auto
    then obtain m where m: "of_int m = (x $ i - y $ i)"
      by (elim Ints_cases) auto
    hence "of_int (abs m) = abs ((x - y) $ i)"
      by simp
    also have "\<dots> \<le> norm (x - y)"
      by (rule component_le_norm_cart)
    also have "\<dots> < of_int 1"
      using 1 by (simp add: dist_norm norm_minus_commute)
    finally have "abs m < 1"
      by (subst (asm) of_int_less_iff)
    thus "x $ i = y $ i"
      using m by simp
  qed
  thus "y = x"
    by (simp add: vec_eq_iff)
qed


subsection \<open>Auxiliary theorems about measure theory\<close>

lemma emeasure_lborel_cbox_eq':
  "emeasure lborel (cbox a b) = ennreal (\<Prod>e\<in>Basis. max 0 ((b - a) \<bullet> e))"
proof (cases "\<forall>ba\<in>Basis. a \<bullet> ba \<le> b \<bullet> ba")
  case True
  hence "emeasure lborel (cbox a b) = ennreal (prod ((\<bullet>) (b - a)) Basis)"
    unfolding emeasure_lborel_cbox_eq by auto
  also have "prod ((\<bullet>) (b - a)) Basis = (\<Prod>e\<in>Basis. max 0 ((b - a) \<bullet> e))"
    using True by (intro prod.cong refl) (auto simp: max_def inner_simps)
  finally show ?thesis .
next
  case False
  hence "emeasure lborel (cbox a b) = ennreal 0"
    by (auto simp: emeasure_lborel_cbox_eq)
  also from False have "0 = (\<Prod>e\<in>Basis. max 0 ((b - a) \<bullet> e))"
    by (auto simp: max_def inner_simps)
  finally show ?thesis .
qed

lemma emeasure_lborel_cbox_cart_eq:
  fixes a b :: "real ^ ('n :: finite)"
  shows "emeasure lborel (cbox a b) = ennreal (\<Prod>i \<in> UNIV. max 0 ((b - a) $ i))"
proof -
  have "emeasure lborel (cbox a b) = ennreal (\<Prod>e\<in>Basis. max 0 ((b - a) \<bullet> e))"
    unfolding emeasure_lborel_cbox_eq' ..
  also have "(Basis :: (real ^ 'n) set) = range (\<lambda>k. axis k 1)"
    unfolding Basis_vec_def by auto
  also have "(\<Prod>e\<in>\<dots>. max 0 ((b - a) \<bullet> e)) = (\<Prod> i \<in> UNIV . max 0 ((b - a) $ i))"
    by (subst prod.reindex) (auto intro!: inj_axis simp: algebra_simps inner_axis)
  finally show ?thesis .
qed

lemma sum_emeasure':
  assumes [simp]: "finite A"
  assumes [measurable]: "\<And>x. x \<in> A \<Longrightarrow> B x \<in> sets M"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> emeasure M (B x \<inter> B y) = 0"
  shows   "(\<Sum>x\<in>A. emeasure M (B x)) = emeasure M (\<Union>x\<in>A. B x)"
proof -
  define C where "C = (\<Union>x\<in>A. \<Union>y\<in>(A-{x}). B x \<inter> B y)"
  have C: "C \<in> null_sets M"
    unfolding C_def using assms
    by (intro null_sets.finite_UN) (auto simp: null_sets_def)
  hence [measurable]: "C \<in> sets M" and [simp]: "emeasure M C = 0"
    by (simp_all add: null_sets_def)
  have "(\<Union>x\<in>A. B x) = (\<Union>x\<in>A. B x - C) \<union> C"
    by (auto simp: C_def)
  also have "emeasure M \<dots> = emeasure M (\<Union>x\<in>A. B x - C)"
    by (subst emeasure_Un_null_set) (auto intro!: sets.Un sets.Diff)
  also from assms have "\<dots> = (\<Sum>x\<in>A. emeasure M (B x - C))"
    by (subst sum_emeasure)
       (auto simp: disjoint_family_on_def C_def intro!: sets.Diff sets.finite_UN)
  also have "\<dots> = (\<Sum>x\<in>A. emeasure M (B x))"
    by (intro sum.cong refl emeasure_Diff_null_set) auto
  finally show ?thesis ..
qed

lemma sums_emeasure':
  assumes [measurable]: "\<And>x. B x \<in> sets M"
  assumes "\<And>x y. x \<noteq> y \<Longrightarrow> emeasure M (B x \<inter> B y) = 0"
  shows   "(\<lambda>x. emeasure M (B x)) sums emeasure M (\<Union>x. B x)"
proof -
  define C where "C = (\<Union>x. \<Union>y\<in>-{x}. B x \<inter> B y)"
  have C: "C \<in> null_sets M"
    unfolding C_def using assms
    by (intro null_sets_UN') (auto simp: null_sets_def)
  hence [measurable]: "C \<in> sets M" and [simp]: "emeasure M C = 0"
    by (simp_all add: null_sets_def)
  have "(\<Union>x. B x) = (\<Union>x. B x - C) \<union> C"
    by (auto simp: C_def)
  also have "emeasure M \<dots> = emeasure M (\<Union>x. B x - C)"
    by (subst emeasure_Un_null_set) (auto intro!: sets.Un sets.Diff)
  also from assms have "(\<lambda>x. emeasure M (B x - C)) sums \<dots>  "
    by (intro sums_emeasure)
       (auto simp: disjoint_family_on_def C_def intro!: sets.Diff sets.finite_UN)
  also have "(\<lambda>x. emeasure M (B x - C)) = (\<lambda>x. emeasure M (B x))"
    by (intro ext emeasure_Diff_null_set) auto
  finally show ?thesis .
qed


subsection \<open>Blichfeldt's theorem\<close>

text \<open>
  Blichfeldt's theorem states that, given a subset of $\mathbb{R}^n$ with $n > 0$ and a
  volume of more than 1, there exist two different points in that set whose difference
  vector has integer components.

  This will be the key ingredient in proving Minkowski's theorem.

  Note that in the HOL Light version, it is additionally required -- both for
  Blichfeldt's theorem and for Minkowski's theorem -- that the set is bounded,
  which we do not need.
\<close>
proposition blichfeldt:
  fixes S :: "(real ^ 'n) set"
  assumes [measurable]: "S \<in> sets lebesgue"
  assumes "emeasure lebesgue S > 1"
  obtains x y where "x \<noteq> y" and "x \<in> S" and "y \<in> S" and "\<And>i. (x - y) $ i \<in> \<int>"
proof -
  \<comment> \<open>We define for each lattice point in $\mathbb{Z}^n$ the corresponding cell in $\mathbb{R}^n$.\<close>
  define R :: "int ^ 'n \<Rightarrow> (real ^ 'n) set"
    where "R = (\<lambda>a. cbox (of_int_vec a) (of_int_vec (a + 1)))"

  \<comment> \<open>For each lattice point, we can intersect the cell it defines with our set @{term S}
      to obtain a partitioning of @{term S}.\<close>
  define T :: "int ^ 'n \<Rightarrow> (real ^ 'n) set"
    where "T = (\<lambda>a. S \<inter> R a)"

  \<comment> \<open>We can then translate each such partition into the cell at the origin, i.\,e. the
      unit box @{term "R 0"}.\<close>
  define T' :: "int ^ 'n \<Rightarrow> (real ^ 'n) set"
    where "T' = (\<lambda>a. (\<lambda>x. x - of_int_vec a) ` T a)"
  have T'_altdef: "T' a = (\<lambda>x. x + of_int_vec a) -` T a" for a
    unfolding T'_def by force

  \<comment> \<open>We need to show measurability of all the defined sets.\<close>
  have [measurable, simp]: "R a \<in> sets lebesgue" for a
    unfolding R_def by simp
  have [measurable, simp]: "T a \<in> sets lebesgue" for a
    unfolding T_def by auto
  have "(\<lambda>x::real^'n. x + of_int_vec a) \<in> lebesgue \<rightarrow>\<^sub>M lebesgue" for a
    using lebesgue_affine_measurable[of "\<lambda>_. 1" "of_int_vec a"]
    by (auto simp: euclidean_representation add_ac)
  from measurable_sets[OF this, of "T a" a for a]
    have [measurable, simp]: "T' a \<in> sets lebesgue" for a
      unfolding T'_altdef by simp

  \<comment> \<open>Obviously, the original set @{term S} is the union of all the lattice
      point cell partitions.\<close>
  have S_decompose: "S = (\<Union>a. T a)" unfolding T_def
  proof safe
    fix x assume x: "x \<in> S"
    define a where "a = (\<chi> i. \<lfloor>x $ i\<rfloor>)"
    have "x \<in> R a"
      unfolding R_def
      by (auto simp: cbox_interval less_eq_vec_def of_int_vec_def a_def)
    with x show "x \<in> (\<Union>a. S \<inter> R a)" by auto
  qed

  \<comment> \<open>Translating the partitioned subsets does not change their volume.\<close>
  have emeasure_T': "emeasure lebesgue (T' a) = emeasure lebesgue (T a)" for a
  proof -
    have "T' a = (\<lambda>x. 1 *\<^sub>R x + (- of_int_vec a)) ` T a"
      by (simp add: T'_def)
    also have "emeasure lebesgue \<dots> = emeasure lebesgue (T a)"
      by (subst emeasure_lebesgue_affine) auto
    finally show ?thesis
      by simp
  qed

  \<comment> \<open>Each translated partition of @{term S} is a subset of the unit cell at the origin.\<close>
  have T'_subset: "T' a \<subseteq> cbox 0 1" for a
    unfolding T'_def T_def R_def
    by (auto simp: algebra_simps cbox_interval of_int_vec_def less_eq_vec_def)

  \<comment> \<open>It is clear that the intersection of two different lattice point cells is a null set.\<close>
  have R_Int: "R a \<inter> R b \<in> null_sets lebesgue" if "a \<noteq> b" for a b
  proof -
    from that obtain i where i: "a $ i \<noteq> b $ i"
      by (auto simp: vec_eq_iff)
    have "R a \<inter> R b = cbox (\<chi> i. max (a $ i) (b $ i)) (\<chi> i. min (a $ i + 1) (b $ i + 1))"
      unfolding Int_interval_cart R_def interval_cbox
      by (simp add: of_int_vec_def max_def min_def if_distrib cong: if_cong)
    hence "emeasure lebesgue (R a \<inter> R b) = emeasure lborel \<dots>"
      by simp
    also have "\<dots> = ennreal (\<Prod>i\<in>UNIV. max 0 (((\<chi> x. real_of_int (min (a $ x + 1) (b $ x + 1))) -
                                  (\<chi> x. real_of_int (max (a $ x) (b $ x)))) $ i))"
      (is "_ = ennreal ?P")
      unfolding emeasure_lborel_cbox_cart_eq by simp
    also have "?P = 0"
      using i by (auto simp: max_def intro!: exI[of _ i])
    finally show ?thesis
      by (auto simp: null_sets_def R_def)
  qed

  \<comment> \<open>Therefore, the intersection of two lattice point cell partitionings of @{term S} is
      also a null set.\<close>
  have T_Int: "T a \<inter> T b \<in> null_sets lebesgue" if "a \<noteq> b" for a b
  proof -
    have "T a \<inter> T b = (R a \<inter> R b) \<inter> S"
      by (auto simp: T_def)
    also have "\<dots> \<in> null_sets lebesgue"
      by (rule null_set_Int2) (insert that, auto intro: R_Int assms)
    finally show ?thesis .
  qed
  have emeasure_T_Int: "emeasure lebesgue (T a \<inter> T b) = 0" if "a \<noteq> b" for a b
    using T_Int[OF that] unfolding null_sets_def by blast

  \<comment> \<open>The set of lattice points $\mathbb{Z}^n$ is countably infinite, so there exists
      a bijection $f: \mathbb{N} \to \mathbb{Z}^n$. We need this for summing over all
      lattice points.\<close>
  define f :: "nat \<Rightarrow> int ^ 'n" where "f = from_nat_into UNIV"
  have "countable (UNIV :: (int ^ 'n) set)" "infinite (UNIV :: (int ^ 'n) set)"
    using infinite_UNIV_char_0 by simp_all
  from bij_betw_from_nat_into [OF this] have f: "bij f"
    by (simp add: f_def)

  \<comment> \<open>Suppose all the translated cell partitions @{term T'} are disjoint.\<close>
  {
    assume disjoint: "\<And>a b. a \<noteq> b \<Longrightarrow> T' a \<inter> T' b = {}"
    \<comment> \<open>We know by assumption that the volume of @{term S} is greater than 1.\<close>
    have "1 < emeasure lebesgue S" by fact
    also have "emeasure lebesgue S = emeasure lebesgue (\<Union>n. T' (f n))"
    proof -
      \<comment> \<open>The sum of the volumes of all the @{term T'} is precisely the volume
          of their union, which is @{term "S"}.\<close>
      have "S = (\<Union>a. T a)" by (rule S_decompose)
      also have "\<dots> = (\<Union>n. T (f n))"
        by (rule bij_betw_UN [OF f, symmetric])
      also have "(\<lambda>n. emeasure lebesgue (T (f n))) sums emeasure lebesgue \<dots>"
        by (intro sums_emeasure' emeasure_T_Int) (insert f, auto simp: bij_betw_def inj_on_def)
      also have "(\<lambda>n. emeasure lebesgue (T (f n))) = (\<lambda>n. emeasure lebesgue (T' (f n)))"
        by (simp add: emeasure_T')
      finally have "(\<lambda>n. emeasure lebesgue (T' (f n))) sums emeasure lebesgue S" .
      moreover have "(\<lambda>n. emeasure lebesgue (T' (f n))) sums emeasure lebesgue (\<Union>n. T' (f n))"
        using disjoint by (intro sums_emeasure)
                          (insert f, auto simp: disjoint_family_on_def bij_betw_def inj_on_def)
      ultimately show ?thesis
        by (auto simp: sums_iff)
    qed
    \<comment> \<open>On the other hand, all the translated partitions lie in the unit cell
        @{term "cbox (0 :: real ^ 'n) 1"}, so their combined volume cannot be
        greater than 1.\<close>
    also have "emeasure lebesgue (\<Union>n. T' (f n)) \<le> emeasure lebesgue (cbox 0 (1 :: real ^ 'n))"
      using T'_subset by (intro emeasure_mono) auto
    also have "\<dots> = 1"
      by (simp add: emeasure_lborel_cbox_cart_eq)
    \<comment> \<open>This leads to a contradiction.\<close>
    finally have False by simp
  }
  \<comment> \<open>Therefore, there exists a point that lies in two different translated partitions,
      which obviously corresponds two two points in the non-translated partitions
      whose difference is the difference between two lattice points and therefore
      has integer components.\<close>
  then obtain a b x where "a \<noteq> b" "x \<in> T' a" "x \<in> T' b"
    by auto
  thus ?thesis
    by (intro that[of "x + of_int_vec a" "x + of_int_vec b"])
       (auto simp: T'_def T_def algebra_simps)
qed


subsection \<open>Minkowski's theorem\<close>

text \<open>
  Minkowski's theorem now states that, given a convex subset of $\mathbb{R}^n$ that is
  symmetric around the origin and has a volume greater than $2^n$, that set must contain
  a non-zero point with integer coordinates.
\<close>
theorem minkowski:
  fixes B :: "(real ^ 'n) set"
  assumes "convex B" and symmetric: "uminus ` B \<subseteq> B"
  assumes meas_B [measurable]: "B \<in> sets lebesgue"
  assumes measure_B: "emeasure lebesgue B > 2 ^ CARD('n)"
  obtains x where "x \<in> B" and "x \<noteq> 0" and "\<And>i. x $ i \<in> \<int>"
proof -
  \<comment> \<open>We scale @{term B} with $\frac{1}{2}$.\<close>
  define B' where "B' = (\<lambda>x. 2 *\<^sub>R x) -` B"
  have meas_B' [measurable]: "B' \<in> sets lebesgue"
    using measurable_sets[OF lebesgue_measurable_scaling[of 2] meas_B]
    by (simp add: B'_def)
  have B'_altdef: "B' = (\<lambda>x. (1/2) *\<^sub>R x) ` B"
    unfolding B'_def by force

  \<comment> \<open>The volume of the scaled set is $2^n$ times smaller than the original set, and
      therefore still has a volume greater than 1.\<close>
  have "1 < ennreal ((1 / 2) ^ CARD('n)) * emeasure lebesgue B"
  proof (cases "emeasure lebesgue B")
    case (real x)
    have "ennreal (2 ^ CARD('n)) = 2 ^ CARD('n)"
      by (subst ennreal_power [symmetric]) auto
    also from measure_B and real have "\<dots> < ennreal x" by simp
    finally have "(2 ^ CARD('n)) < x"
      by (subst (asm) ennreal_less_iff) auto
    thus ?thesis
      using real by (simp add: ennreal_1 [symmetric] ennreal_mult' [symmetric]
                       ennreal_less_iff field_simps del: ennreal_1)
  qed (simp_all add: ennreal_mult_top)
  also have "\<dots> = emeasure lebesgue B'"
    unfolding B'_altdef using emeasure_lebesgue_affine[of "1/2" 0 B] by simp
  finally have *: "emeasure lebesgue B' > 1" .

  \<comment> \<open>We apply Blichfeldt's theorem to get two points whose difference vector has
      integer coefficients. It only remains to show that that difference vector is
      itself a point in the original set.\<close>
  obtain x y
    where xy: "x \<noteq> y" "x \<in> B'" "y \<in> B'" "\<And>i. (x - y) $ i \<in> \<int>"
    by (erule blichfeldt [OF meas_B' *])
  hence "2 *\<^sub>R x \<in> B" "2 *\<^sub>R y \<in> B" by (auto simp: B'_def)
  \<comment> \<open>Exploiting the symmetric of @{term B}, the reflection of @{term "2 *\<^sub>R y"} is
      also in @{term B}.\<close>
  moreover from this and symmetric have "-(2 *\<^sub>R y) \<in> B" by blast
  \<comment> \<open>Since @{term B} is convex, the mid-point between @{term "2 *\<^sub>R x"} and @{term "-2 *\<^sub>R y"}
      is also in @{term B}, and that point is simply @{term "x - y"} as desired.\<close>
  ultimately have "(1 / 2) *\<^sub>R 2 *\<^sub>R x + (1 / 2) *\<^sub>R (- 2 *\<^sub>R y) \<in> B"
    using \<open>convex B\<close> by (intro convexD) auto
  also have "(1 / 2) *\<^sub>R 2 *\<^sub>R x + (1 / 2) *\<^sub>R (- 2 *\<^sub>R y) = x - y"
    by simp
  finally show ?thesis using xy
    by (intro that[of "x - y"]) auto
qed

text \<open>
  If the set in question is compact, the restriction to the volume can be weakened
  to ``at least 1'' from ``greater than 1''.
\<close>
theorem minkowski_compact:
  fixes B :: "(real ^ 'n) set"
  assumes "convex B" and "compact B" and symmetric: "uminus ` B \<subseteq> B"
  assumes measure_B: "emeasure lebesgue B \<ge> 2 ^ CARD('n)"
  obtains x where "x \<in> B" and "x \<noteq> 0" and "\<And>i. x $ i \<in> \<int>"
proof (cases "emeasure lebesgue B = 2 ^ CARD('n)")
  \<comment> \<open>If the volume is greater than 1, we can just apply the theorem from before.\<close>
  case False
  with measure_B have less: "emeasure lebesgue B > 2 ^ CARD('n)"
    by simp
  from \<open>compact B\<close> have meas: "B \<in> sets lebesgue"
    by (intro sets_completionI_sets lborelD borel_closed compact_imp_closed)
  from minkowski[OF assms(1) symmetric meas less] and that
    show ?thesis by blast
next
  case True
  \<comment> \<open>If the volume is precisely one, we look at what happens when @{term B} is
      scaled with a factor of $1 + \varepsilon$.\<close>
  define B' where "B' = (\<lambda>\<epsilon>. (*\<^sub>R) (1 + \<epsilon>) ` B)"
  from \<open>compact B\<close> have compact': "compact (B' \<epsilon>)" for \<epsilon>
    unfolding B'_def by (intro compact_scaling)
  have B'_altdef: "B' \<epsilon> = (*\<^sub>R) (inverse (1 + \<epsilon>)) -` B" if \<epsilon>: "\<epsilon> > 0" for \<epsilon>
    using \<epsilon> unfolding B'_def by force

  \<comment> \<open>Since the scaled sets are convex, they are stable under scaling.\<close>
  have B_scale: "a *\<^sub>R x \<in> B" if "x \<in> B" "a \<in> {0..1}" for a x
  proof -
    have "((a + 1) / 2) *\<^sub>R x + (1 - ((a + 1) / 2)) *\<^sub>R (-x) \<in> B"
      using that and \<open>convex B\<close> and symmetric by (intro convexD) auto
    also have "((a + 1) / 2) *\<^sub>R x + (1 - ((a + 1) / 2)) *\<^sub>R (-x) =
                 (1 + a) *\<^sub>R ((1/2) *\<^sub>R (x + x)) - x"
      by (simp add: algebra_simps del: scaleR_half_double)
    also have "\<dots> = a *\<^sub>R x"
      by (subst scaleR_half_double) (simp add: algebra_simps)
    finally show "\<dots> \<in> B" .
  qed

  \<comment> \<open>This means that @{term B'} is monotonic.\<close>
  have B'_subset: "B' a \<subseteq> B' b" if "0 \<le> a" "a \<le> b" for a b
  proof
    fix x assume "x \<in> B' a"
    then obtain y where "x = (1 + a) *\<^sub>R y" "y \<in> B"
      by (auto simp: B'_def)
    moreover then have "(inverse (1 + b) * (1 + a)) *\<^sub>R y \<in> B"
      using that by (intro B_scale) (auto simp: field_simps)
    ultimately show "x \<in> B' b"
      using that by (force simp: B'_def)
  qed

  \<comment> \<open>We obtain some upper bound on the norm of @{term B}.\<close>
  from \<open>compact B\<close> have "bounded B"
    by (rule compact_imp_bounded)
  then obtain C where C: "norm x \<le> C" if "x \<in> B" for x
    unfolding bounded_iff by blast

  \<comment> \<open>We can then bound the distance of any point in a scaled set to the original set.\<close>
  have setdist_le: "setdist {x} B \<le> \<epsilon> * C" if "x \<in> B' \<epsilon>" and "\<epsilon> \<ge> 0" for x \<epsilon>
  proof -
    from that obtain y where y: "y \<in> B" and [simp]: "x = (1 + \<epsilon>) *\<^sub>R y"
      by (auto simp: B'_def)
    from y have "setdist {x} B \<le> dist x y"
      by (intro setdist_le_dist) auto
    also from that have "dist x y = \<epsilon> * norm y"
      by (simp add: dist_norm algebra_simps)
    also from y have "norm y \<le> C"
      by (rule C)
    finally show "setdist {x} B \<le> \<epsilon> * C"
      using that by (simp add: mult_left_mono)
  qed

  \<comment> \<open>By applying the standard Minkowski theorem to the a scaled set, we can see that
      any scaled set contains a non-zero point with integer coordinates.\<close>
  have "\<exists>v. v \<in> B' \<epsilon> - {0} \<and> (\<forall>i. v $ i \<in> \<int>)" if \<epsilon>: "\<epsilon> > 0" for \<epsilon>
  proof -
    from \<open>convex B\<close> have convex': "convex (B' \<epsilon>)"
      unfolding B'_def by (rule convex_scaling)
    from \<open>compact B\<close> have meas: "B' \<epsilon> \<in> sets lebesgue" unfolding B'_def
      by (intro sets_completionI_sets lborelD borel_closed compact_imp_closed compact_scaling)
    from symmetric have symmetric': "uminus ` B' \<epsilon> \<subseteq> B' \<epsilon>"
      by (auto simp: B'_altdef[OF \<epsilon>])

    have "2 ^ CARD('n) = ennreal (2 ^ CARD('n))"
      by (subst ennreal_power [symmetric]) auto
    hence "1 * emeasure lebesgue B < ennreal ((1 + \<epsilon>) ^ CARD('n)) * emeasure lebesgue B"
      using True and \<epsilon> by (intro ennreal_mult_strict_right_mono) (auto)
    also have "\<dots> = emeasure lebesgue (B' \<epsilon>)"
      using emeasure_lebesgue_affine[of "1+\<epsilon>" 0 B] and \<epsilon> by (simp add: B'_def)
    finally have measure_B': "emeasure lebesgue (B' \<epsilon>) > 2 ^ CARD('n)"
      using True by simp
   
    obtain v where "v \<in> B' \<epsilon>" "v \<noteq> 0" "\<And>i. v $ i \<in> \<int>"
      by (erule minkowski[OF convex' symmetric' meas measure_B'])
    thus ?thesis
      by blast
  qed
  hence "\<forall>n. \<exists>v. v \<in> B' (1/Suc n) - {0} \<and> (\<forall>i. v $ i \<in> \<int>)"
    by auto
  \<comment> \<open>In particular, this means we can choose some sequence tending to zero
      -- say $\frac{1}{n+1}$ -- and always find a lattice point in the scaled set.\<close>
  hence "\<exists>v. \<forall>n. v n \<in> B' (1/Suc n) - {0} \<and> (\<forall>i. v n $ i \<in> \<int>)"
    by (subst (asm) choice_iff)
  then obtain v where v: "v n \<in> B' (1/Suc n) - {0}" "v n $ i \<in> \<int>" for i n
    by blast

  \<comment> \<open>By the Bolzano--Weierstraß theorem, there exists a convergent subsequence of @{term v}.\<close>
  have "\<exists>h l. strict_mono (h::nat\<Rightarrow>nat) \<and> (v \<circ> h) \<longlonglongrightarrow> l"
  proof (rule compactD)
    show "compact (B' 1)" by (rule compact')
    show "range v \<subseteq> B' 1"
      using B'_subset[of "1/Suc n" 1 for n] and v by auto
  qed
  then obtain h l where h: "strict_mono h" and l: "(v \<circ> h) \<longlonglongrightarrow> l"
    by blast

  \<comment> \<open>Since the convergent subsequence tends to @{term l}, the distance of the
      sequence elements to @{term B} tends to the distance of @{term l} and @{term B}.
      Furthermore, the distance of the sequence elements is bounded by $(1+\varepsilon)C$,
      which tends to 0, so the distance of @{term l} to @{term B} must be 0.\<close>
  have "setdist {l} B \<le> 0"
  proof (rule tendsto_le)
    show "((\<lambda>x. setdist {x} B) \<circ> (v \<circ> h)) \<longlonglongrightarrow> setdist {l} B"
      by (intro continuous_imp_tendsto l continuous_at_setdist)
    show "(\<lambda>n. inverse (Suc (h n)) * C) \<longlonglongrightarrow> 0"
      by (intro tendsto_mult_left_zero filterlim_compose[OF _ filterlim_subseq[OF h]]
                LIMSEQ_inverse_real_of_nat)
    show "\<forall>\<^sub>F x in sequentially. ((\<lambda>x. setdist {x} B) \<circ> (v \<circ> h)) x
                                  \<le> inverse (real (Suc (h x))) * C"
      using setdist_le and v unfolding o_def
      by (intro always_eventually allI setdist_le) (auto simp: field_simps)
  qed auto
  hence "setdist {l} B = 0"
    by (intro antisym setdist_pos_le)
  with assms and \<open>compact B\<close> have "l \<in> B"
    by (subst (asm) setdist_eq_0_closed) (auto intro: compact_imp_closed)

  \<comment> \<open>It is also easy to see that, since the lattice is a closed set and all sequence
      elements lie on it, the limit @{term l} also lies on it.\<close>
  moreover have "l \<in> {l. \<forall>i. l $ i \<in> \<int>} - {0}"
    using v by (intro closed_sequentially[OF closed_lattice _ l]) auto
  ultimately show ?thesis using that by blast
qed

end
