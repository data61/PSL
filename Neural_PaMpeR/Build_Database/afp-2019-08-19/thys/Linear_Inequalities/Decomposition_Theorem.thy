section \<open>The Decomposition Theorem\<close>

text \<open>This theory contains a proof of the fact, that every polyhedron can be decomposed
  into a convex hull of a finite set of points + a finitely generated cone, including bounds
  on the numbers that are required in the decomposition.
  We further prove the inverse direction of this theorem (without bounds) and
  as a corollary, we derive that a polyhedron is bounded iff it is the convex hull
  of finitely many points, i.e., a polytope.\<close>

theory Decomposition_Theorem
  imports
    Farkas_Minkowsky_Weyl
    Convex_Hull
begin

context gram_schmidt
begin

definition "polytope P = (\<exists> V. V \<subseteq> carrier_vec n \<and> finite V \<and> P = convex_hull V)"

definition "polyhedron A b = {x \<in> carrier_vec n. A *\<^sub>v x \<le> b}"

lemma polyhedra_are_convex:
  assumes A: "A \<in> carrier_mat nr n"
    and b: "b \<in> carrier_vec nr"
    and P: "P = polyhedron A b"
  shows "convex P"
proof (intro convexI)
  show Pcarr: "P \<subseteq> carrier_vec n" using assms unfolding polyhedron_def by auto
  fix a :: 'a and x y
  assume xy: "x \<in> P" "y \<in> P" and a: "0 \<le> a" "a \<le> 1"
  from xy[unfolded P polyhedron_def]
  have x: "x \<in> carrier_vec n" and y: "y \<in> carrier_vec n" and le: "A *\<^sub>v x \<le> b" "A *\<^sub>v y \<le> b" by auto
  show "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> P" unfolding P polyhedron_def
  proof (intro CollectI conjI)
    from x have ax: "a \<cdot>\<^sub>v x \<in> carrier_vec n" by auto
    from y have ay: "(1 - a) \<cdot>\<^sub>v y \<in> carrier_vec n" by auto
    show "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> carrier_vec n" using ax ay by auto
    show "A *\<^sub>v (a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y) \<le> b"
    proof (intro lesseq_vecI[OF _ b])
      show "A *\<^sub>v (a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y) \<in> carrier_vec nr" using A x y by auto
      fix i
      assume i: "i < nr"
      from lesseq_vecD[OF b le(1) i] lesseq_vecD[OF b le(2) i]
      have le: "(A *\<^sub>v x) $ i \<le> b $ i" "(A *\<^sub>v y) $ i \<le> b $ i" by auto
      have "(A *\<^sub>v (a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y)) $ i = a * (A *\<^sub>v x) $ i + (1 - a) * (A *\<^sub>v y) $ i"
        using A x y i by (auto simp: scalar_prod_add_distrib[of _ n])
      also have "\<dots> \<le> a * b $ i + (1 - a) * b $ i"
        by (rule add_mono; rule mult_left_mono, insert le a, auto)
      also have "\<dots> = b $ i" by (auto simp: field_simps)
      finally show "(A *\<^sub>v (a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y)) $ i \<le> b $ i" .
    qed
  qed
qed

end



locale gram_schmidt_m = n: gram_schmidt n f_ty + m: gram_schmidt m f_ty
  for n m :: nat and f_ty
begin

lemma vec_first_lincomb_list:
  assumes Xs: "set Xs \<subseteq> carrier_vec n"
    and nm: "m \<le> n"
  shows "vec_first (n.lincomb_list c Xs) m =
       m.lincomb_list c (map (\<lambda> v. vec_first v m) Xs)"
  using Xs
proof (induction Xs arbitrary: c)
  case Nil
  show ?case by (simp add: nm)
next
  case (Cons x Xs)
  from Cons.prems have x: "x \<in> carrier_vec n" and Xs: "set Xs \<subseteq> carrier_vec n" by auto

  have "vec_first (n.lincomb_list c (x # Xs)) m =
          vec_first (c 0 \<cdot>\<^sub>v x + n.lincomb_list (c \<circ> Suc) Xs) m" by auto
  also have "\<dots> = vec_first (c 0 \<cdot>\<^sub>v x) m + vec_first (n.lincomb_list (c \<circ> Suc) Xs) m"
    using vec_first_add[of m "c 0 \<cdot>\<^sub>v x"] x n.lincomb_list_carrier[OF Xs, of "c \<circ> Suc"] nm
    by simp
  also have "vec_first (c 0 \<cdot>\<^sub>v x) m = c 0 \<cdot>\<^sub>v vec_first x m"
    using vec_first_smult[OF nm, of x "c 0"] Cons.prems by auto
  also have "vec_first (n.lincomb_list (c \<circ> Suc) Xs) m =
               m.lincomb_list (c \<circ> Suc) (map (\<lambda> v. vec_first v m) Xs)"
    using Cons by simp
  also have "c 0 \<cdot>\<^sub>v vec_first x m + \<dots> =
               m.lincomb_list c (map (\<lambda> v. vec_first v m) (x # Xs))"
    by simp
  finally show ?case by auto
qed

lemma convex_hull_next_dim:
  assumes "n = m + 1"
    and X: "X \<subseteq> carrier_vec n"
    and "finite X"
    and Xm1: "\<forall> y \<in> X. y $ m = 1"
    and y_dim: "y \<in> carrier_vec n"
    and y: "y $ m = 1"
  shows "(vec_first y m \<in> m.convex_hull {vec_first y m | y. y \<in> X}) = (y \<in> n.cone X)"
proof -
  from `finite X` obtain Xs where Xs: "X = set Xs" using finite_list by auto
  let ?Y = "{vec_first y m | y. y \<in> X}"
  let ?Ys = "map (\<lambda> y. vec_first y m) Xs"
  have Ys: "?Y = set ?Ys" using Xs by auto

  define x where "x = vec_first y m"
  {
    have "y = vec_first y m @\<^sub>v vec_last y 1"
      using `n = m + 1` vec_first_last_append y_dim by auto
    also have "vec_last y 1 = vec_of_scal (vec_last y 1 $ 0)"
      using vec_of_scal_dim_1[of "vec_last y 1"] by simp
    also have "vec_last y 1 $ 0 = y $ m"
      using y_dim `n = m + 1` vec_last_index[of y m 1 0] by auto
    finally have "y = x @\<^sub>v vec_of_scal 1" unfolding x_def using y by simp
  } note xy = this
  {
    assume "y \<in> n.cone X"
    then obtain c where x: "n.nonneg_lincomb c X y"
      using n.cone_iff_finite_cone[OF X] `finite X`
      unfolding n.finite_cone_def by auto

    have "1 = y $ m" by (simp add: y)
    also have "y = n.lincomb c X"
      using x unfolding n.nonneg_lincomb_def by simp
    also have "\<dots> $ m = (\<Sum>x\<in>X. c x * x $ m)"
      using n.lincomb_index[OF _ X] `n = m + 1` by simp
    also have "\<dots> = sum c X"
      by (rule n.R.finsum_restrict, auto, rule restrict_ext, simp add: Xm1)
    finally have "y \<in> n.convex_hull X"
      unfolding n.convex_hull_def n.convex_lincomb_def
      using `finite X` x by auto
  }
  moreover have "n.convex_hull X \<subseteq> n.cone X"
    unfolding n.convex_hull_def n.convex_lincomb_def n.finite_cone_def n.cone_def
    using `finite X` by auto
  moreover have "n.convex_hull X = n.convex_hull_list Xs"
    by (rule n.finite_convex_hull_iff_convex_hull_list[OF X Xs])
  moreover {
    assume "y \<in> n.convex_hull_list Xs"
    then obtain c where c: "n.lincomb_list c Xs = y"
      and c0: "\<forall> i < length Xs. c i \<ge> 0" and c1: "sum c {0..<length Xs} = 1"
      unfolding n.convex_hull_list_def n.convex_lincomb_list_def
        n.nonneg_lincomb_list_def by fast
    have "m.lincomb_list c ?Ys = vec_first y m"
      using c vec_first_lincomb_list[of Xs c] X Xs `n = m + 1` by simp
    hence "x \<in> m.convex_hull_list ?Ys"
      unfolding m.convex_hull_list_def m.convex_lincomb_list_def
        m.nonneg_lincomb_list_def
      using x_def c0 c1 x_def by auto
  } moreover {
    assume "x \<in> m.convex_hull_list ?Ys"
    then obtain c where x: "m.lincomb_list c ?Ys = x"
      and c0: "\<forall> i < length Xs. c i \<ge> 0"
      and c1: "sum c {0..<length Xs} = 1"
      unfolding m.convex_hull_list_def m.convex_lincomb_list_def
        m.nonneg_lincomb_list_def by auto

    have "n.lincomb_list c Xs $ m = (\<Sum>j = 0..<length Xs. c j * Xs ! j $ m)"
      using n.lincomb_list_index[of m Xs c] `n = m + 1` Xs X by fastforce
    also have "\<dots> = sum c {0..<length Xs}"
      apply(rule n.R.finsum_restrict, auto, rule restrict_ext)
      by (simp add: Xm1 Xs)
    also have "\<dots> = 1" by (rule c1)
    finally have "vec_last (n.lincomb_list c Xs) 1 $ 0 = 1"
      using vec_of_scal_dim_1 vec_last_index[of "n.lincomb_list c Xs" m 1 0]
        n.lincomb_list_carrier Xs X `n = m + 1` by simp
    hence "vec_last (n.lincomb_list c Xs) 1 = vec_of_scal 1"
      using vec_of_scal_dim_1 by auto

    moreover have "vec_first (n.lincomb_list c Xs) m = x"
      using vec_first_lincomb_list `n = m + 1` Xs X x by auto

    moreover have "n.lincomb_list c Xs =
                   vec_first (n.lincomb_list c Xs) m @\<^sub>v vec_last (n.lincomb_list c Xs) 1"
      using vec_first_last_append Xs X n.lincomb_list_carrier `n = m + 1` by auto

    ultimately have "n.lincomb_list c Xs = y" using xy by simp

    hence "y \<in> n.convex_hull_list Xs"
      unfolding n.convex_hull_list_def n.convex_lincomb_list_def
        n.nonneg_lincomb_list_def using c0 c1 by blast
  }
  moreover have "m.convex_hull ?Y = m.convex_hull_list ?Ys"
    using m.finite_convex_hull_iff_convex_hull_list[OF _ Ys] by fastforce
  ultimately show ?thesis unfolding x_def by blast
qed

lemma cone_next_dim:
  assumes "n = m + 1"
    and X: "X \<subseteq> carrier_vec n"
    and "finite X"
    and Xm0: "\<forall> y \<in> X. y $ m = 0"
    and y_dim: "y \<in> carrier_vec n"
    and y: "y $ m = 0"
  shows "(vec_first y m \<in> m.cone {vec_first y m | y. y \<in> X}) = (y \<in> n.cone X)"
proof -
  from `finite X` obtain Xs where Xs: "X = set Xs" using finite_list by auto
  let ?Y = "{vec_first y m | y. y \<in> X}"
  let ?Ys = "map (\<lambda> y. vec_first y m) Xs"
  have Ys: "?Y = set ?Ys" using Xs by auto

  define x where "x = vec_first y m"
  {
    have "y = vec_first y m @\<^sub>v vec_last y 1"
      using `n = m + 1` vec_first_last_append y_dim by auto
    also have "vec_last y 1 = vec_of_scal (vec_last y 1 $ 0)"
      using vec_of_scal_dim_1[of "vec_last y 1"] by simp
    also have "vec_last y 1 $ 0 = y $ m"
      using y_dim `n = m + 1` vec_last_index[of y m 1 0] by auto
    finally have "y = x @\<^sub>v vec_of_scal 0" unfolding x_def using y by simp
  } note xy = this

  have "n.cone X = n.cone_list Xs"
    using n.cone_iff_finite_cone[OF X `finite X`] n.finite_cone_iff_cone_list[OF X Xs]
    by simp
  moreover {
    assume "y \<in> n.cone_list Xs"
    then obtain c where y: "n.lincomb_list c Xs = y" and c: "\<forall> i < length Xs. c i \<ge> 0"
      unfolding n.cone_list_def n.nonneg_lincomb_list_def by blast
    from y have "m.lincomb_list c ?Ys = x"
      unfolding x_def
      using vec_first_lincomb_list Xs X `n = m + 1` by auto
    hence "x \<in> m.cone_list ?Ys" using c
      unfolding m.cone_list_def m.nonneg_lincomb_list_def by auto
  } moreover {
    assume "x \<in> m.cone_list ?Ys"
    then obtain c where x: "m.lincomb_list c ?Ys = x" and c: "\<forall> i < length Xs. c i \<ge> 0"
      unfolding m.cone_list_def m.nonneg_lincomb_list_def by auto

    have "vec_last (n.lincomb_list c Xs) 1 $ 0 = n.lincomb_list c Xs $ m"
      using `n = m + 1` n.lincomb_list_carrier X Xs vec_last_index[of _ m 1 0]
      by auto
    also have "\<dots> = 0"
      using n.lincomb_list_index[of m Xs c] Xs X `n = m + 1` Xm0 by simp
    also have "\<dots> = vec_last y 1 $ 0"
      using y y_dim `n = m + 1` vec_last_index[of y m 1 0] by auto
    finally have "vec_last (n.lincomb_list c Xs) 1 = vec_last y 1" by fastforce

    moreover have "vec_first (n.lincomb_list c Xs) m = x"
      using vec_first_lincomb_list[of Xs c] x X Xs `n = m + 1`
      unfolding x_def by simp

    ultimately have "n.lincomb_list c Xs = y" unfolding x_def
      using vec_first_last_append[of _ m 1] `n = m + 1` y_dim
        n.lincomb_list_carrier[of Xs c] Xs X
      by metis
    hence "y \<in> n.cone_list Xs"
      unfolding n.cone_list_def n.nonneg_lincomb_list_def using c by blast
  }
  moreover have "m.cone_list ?Ys = m.cone ?Y"
    using m.finite_cone_iff_cone_list[OF _ Ys] m.cone_iff_finite_cone[of ?Y]
      `finite X` by force
  ultimately show ?thesis unfolding x_def by blast
qed

end

context gram_schmidt
begin

lemma decomposition_theorem_polyhedra_1:
  assumes A: "A \<in> carrier_mat nr n"
    and b: "b \<in> carrier_vec nr"
    and P: "P = polyhedron A b"
  shows "\<exists> Q X. X \<subseteq> carrier_vec n \<and> finite X \<and>
    Q \<subseteq> carrier_vec n \<and> finite Q \<and>
    P = convex_hull Q + cone X \<and>
    (A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd \<longrightarrow> b \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<longrightarrow>
      X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound n (max 1 Bnd))
    \<and> Q \<subseteq> Bounded_vec (det_bound n (max 1 Bnd)))"
proof -
  interpret next_dim: gram_schmidt "n + 1" "TYPE ('a)".
  interpret gram_schmidt_m "n + 1" n "TYPE('a)".

  from P[unfolded polyhedron_def] have "P \<subseteq> carrier_vec n" by auto

  have mcb: "mat_of_col (-b) \<in> carrier_mat nr 1" using b by auto
  define M where "M = (A @\<^sub>c mat_of_col (-b)) @\<^sub>r (0\<^sub>m 1 n @\<^sub>c -1\<^sub>m 1)"
  have M_top: "A @\<^sub>c mat_of_col (- b) \<in> carrier_mat nr (n + 1)"
    by (rule carrier_append_cols[OF A mcb])
  have M_bottom: "(0\<^sub>m 1 n @\<^sub>c -1\<^sub>m 1) \<in> carrier_mat 1 (n + 1)"
    by (rule carrier_append_cols, auto)
  have M_dim: "M \<in> carrier_mat (nr + 1) (n + 1)"
    unfolding M_def
    by (rule carrier_append_rows[OF M_top M_bottom])

  {
    fix x :: "'a vec" fix t assume x: "x \<in> carrier_vec n"
    have "x @\<^sub>v vec_of_scal t \<in> next_dim.polyhedral_cone M =
          (A *\<^sub>v x - t \<cdot>\<^sub>v b \<le> 0\<^sub>v nr \<and> t \<ge> 0)"
    proof -
      let ?y = "x @\<^sub>v vec_of_scal t"
      have y: "?y \<in> carrier_vec (n + 1)" using x by(simp del: One_nat_def)
      have "?y \<in> next_dim.polyhedral_cone M =
            (M *\<^sub>v ?y \<le> 0\<^sub>v (nr + 1))"
        unfolding next_dim.polyhedral_cone_def using y M_dim by auto
      also have "0\<^sub>v (nr + 1) = 0\<^sub>v nr @\<^sub>v 0\<^sub>v 1" by auto
      also have "M *\<^sub>v ?y \<le> 0\<^sub>v nr @\<^sub>v 0\<^sub>v 1 =
                   ((A @\<^sub>c mat_of_col (-b)) *\<^sub>v ?y \<le> 0\<^sub>v nr \<and>
                   (0\<^sub>m 1 n @\<^sub>c -1\<^sub>m 1) *\<^sub>v ?y \<le> 0\<^sub>v 1)"
        unfolding M_def
        by (intro append_rows_le[OF M_top M_bottom _ y], auto)
      also have "(A @\<^sub>c mat_of_col(-b)) *\<^sub>v ?y =
                 A *\<^sub>v x + mat_of_col(-b) *\<^sub>v vec_of_scal t"
        by (rule mat_mult_append_cols[OF A _ x],
            auto simp add: b simp del: One_nat_def)
      also have "mat_of_col(-b) *\<^sub>v vec_of_scal t = t \<cdot>\<^sub>v (-b)"
        by(rule mult_mat_of_row_vec_of_scal)
      also have "A *\<^sub>v x + t \<cdot>\<^sub>v (-b) = A *\<^sub>v x - t \<cdot>\<^sub>v b" by auto
      also have "(0\<^sub>m 1 n @\<^sub>c - 1\<^sub>m 1) *\<^sub>v (x @\<^sub>v vec_of_scal t) =
                 0\<^sub>m 1 n *\<^sub>v x + - 1\<^sub>m 1 *\<^sub>v vec_of_scal t"
        by(rule mat_mult_append_cols, auto simp add: x simp del: One_nat_def)
      also have "\<dots> = - vec_of_scal t" using x by (auto simp del: One_nat_def)
      also have "(\<dots> \<le> 0\<^sub>v 1) = (t \<ge> 0)" unfolding less_eq_vec_def by auto
      finally show "(?y \<in> next_dim.polyhedral_cone M) =
                    (A *\<^sub>v x - t \<cdot>\<^sub>v b \<le> 0\<^sub>v nr \<and> t \<ge> 0)" by auto
    qed
  } note M_cone_car = this
  from next_dim.farkas_minkowsky_weyl_theorem_2[OF M_dim, of "max 1 Bnd"]
  obtain X where X: "next_dim.polyhedral_cone M = next_dim.cone X" and
    fin_X: "finite X" and X_carrier: "X \<subseteq> carrier_vec (n+1)"
    and Bnd: "M \<in> \<int>\<^sub>m \<inter> Bounded_mat (max 1 Bnd) \<Longrightarrow>
          X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound n (max 1 Bnd))"
    by auto
  let ?f = "\<lambda> x. if x $ n = 0 then 1 else 1 / (x $ n)"
  define Y where "Y = {?f x \<cdot>\<^sub>v x | x. x \<in> X}"
  have "finite Y" unfolding Y_def using fin_X by auto
  have Y_carrier: "Y \<subseteq> carrier_vec (n+1)" unfolding Y_def using X_carrier by auto
  have "?f ` X \<subseteq> {y. y > 0}"
  proof
    fix y
    assume "y \<in> ?f ` X"
    then obtain x where x: "x \<in> X" and y: "y = ?f x" by auto
    show "y \<in> {y. y > 0}"
    proof cases
      assume "x $ n = 0"
      thus "y \<in> {y. y > 0}" using y by auto
    next
      assume P: "x $ n \<noteq> 0"
      have "x = vec_first x n @\<^sub>v vec_last x 1"
        using x X_carrier vec_first_last_append by auto
      also have "vec_last x 1 = vec_of_scal (vec_last x 1 $ 0)" by auto
      also have "vec_last x 1 $ 0 = x $ n"
        using x X_carrier unfolding vec_last_def by auto
      finally have "x = vec_first x n @\<^sub>v vec_of_scal (x $ n)" by auto
      moreover have "x \<in> next_dim.polyhedral_cone M"
        using x X X_carrier next_dim.set_in_cone by auto
      ultimately have "x $ n \<ge> 0" using M_cone_car vec_first_carrier by metis
      hence "x $ n > 0" using P by auto
      thus "y \<in> {y. y > 0}" using y by auto
    qed
  qed
  hence Y: "next_dim.cone Y = next_dim.polyhedral_cone M" unfolding Y_def
    using next_dim.cone_smult_basis[OF X_carrier] X by auto
  define Y0 where "Y0 = {v \<in> Y. v $ n = 0}"
  define Y1 where "Y1 = Y - Y0"
  have Y0_carrier: "Y0 \<subseteq> carrier_vec (n + 1)" and Y1_carrier: "Y1 \<subseteq> carrier_vec (n + 1)"
    unfolding Y0_def Y1_def using Y_carrier by auto
  have "finite Y0" and "finite Y1"
    unfolding Y0_def Y1_def using `finite Y` by auto

  have Y1: "\<And> y. y \<in> Y1 \<Longrightarrow> y $ n = 1"
  proof -
    fix y assume y: "y \<in> Y1"
    hence "y \<in> Y" unfolding Y1_def by auto
    then obtain x where "x \<in> X" and x: "y = ?f x \<cdot>\<^sub>v x" unfolding Y_def by auto
    then have "x $ n \<noteq> 0" using x y Y1_def Y0_def by auto
    then have "y = 1 / (x $ n) \<cdot>\<^sub>v x" using x by auto
    then have "y $ n = 1 / (x $ n) * x $ n" using X_carrier `x \<in> X` by auto
    thus "y $ n = 1" using `x $ n \<noteq> 0` by auto
  qed

  let ?Z0 = "{vec_first y n | y. y \<in> Y0}"
  let ?Z1 = "{vec_first y n | y. y \<in> Y1}"
  show ?thesis
  proof (intro exI conjI impI)
    show "?Z0 \<subseteq> carrier_vec n" by auto
    show "?Z1 \<subseteq> carrier_vec n" by auto
    show "finite ?Z0" using `finite Y0` by auto
    show "finite ?Z1" using `finite Y1` by auto
    show "P = convex_hull ?Z1 + cone ?Z0"
    proof -
      {
        fix x
        assume "x \<in> P"
        hence xn: "x \<in> carrier_vec n" and "A *\<^sub>v x \<le> b"
          using P unfolding polyhedron_def by auto
        hence "A *\<^sub>v x - 1 \<cdot>\<^sub>v b \<le> 0\<^sub>v nr"
          using vec_le_iff_diff_le_0 A b carrier_vecD mult_mat_vec_carrier one_smult_vec
          by metis
        hence "x @\<^sub>v vec_of_scal 1 \<in> next_dim.polyhedral_cone M"
          using M_cone_car[OF xn] by auto
        hence "x @\<^sub>v vec_of_scal 1 \<in> next_dim.cone Y" using Y by auto
        hence "x @\<^sub>v vec_of_scal 1 \<in> next_dim.finite_cone Y"
          using next_dim.cone_iff_finite_cone[OF Y_carrier `finite Y`] by auto
        then obtain c where c: "next_dim.nonneg_lincomb c Y (x @\<^sub>v vec_of_scal 1)"
          unfolding next_dim.finite_cone_def using `finite Y` by auto
        let ?y = "next_dim.lincomb c Y1"
        let ?z = "next_dim.lincomb c Y0"
        have y_dim: "?y \<in> carrier_vec (n + 1)" and z_dim: "?z \<in> carrier_vec (n + 1)"
          unfolding next_dim.nonneg_lincomb_def
          using Y0_carrier Y1_carrier next_dim.lincomb_closed by simp_all
        hence yz_dim: "?y + ?z \<in> carrier_vec (n + 1)" by auto
        have "x @\<^sub>v vec_of_scal 1 = next_dim.lincomb c Y"
          using c unfolding next_dim.nonneg_lincomb_def by auto
        also have "Y = Y1 \<union> Y0" unfolding Y1_def using Y0_def by blast
        also have "next_dim.lincomb c (Y1 \<union> Y0) = ?y + ?z"
          using next_dim.lincomb_union2[of Y1 Y0]
            `finite Y0` `finite Y` Y0_carrier Y_carrier
          unfolding Y1_def by fastforce
        also have "?y + ?z = vec_first (?y + ?z) n @\<^sub>v vec_last (?y + ?z) 1"
          using vec_first_last_append[of "?y + ?z" n 1] add_carrier_vec yz_dim
          by simp
        also have "vec_last (?y + ?z) 1 = vec_of_scal ((?y + ?z) $ n)"
          using vec_of_scal_dim_1 vec_last_index[OF yz_dim, of 0] by auto
        finally have "x @\<^sub>v vec_of_scal 1 =
                     vec_first (?y + ?z) n @\<^sub>v vec_of_scal ((?y + ?z) $ n)" by auto
        hence "x = vec_first (?y + ?z) n" and
          yz_last: "vec_of_scal 1 = vec_of_scal ((?y + ?z) $ n)"
          using append_vec_eq yz_dim xn by auto
        hence xyz: "x = vec_first ?y n + vec_first ?z n"
          using vec_first_add[of n ?y ?z] y_dim z_dim by simp

        have "1 = ((?y + ?z) $ n)" using yz_last index_vec_of_scal
          by (metis (no_types, lifting))
        hence "1 = ?y $ n + ?z $ n" using y_dim z_dim by auto
        moreover have zn0: "?z $ n = 0"
          using next_dim.lincomb_index[OF _ Y0_carrier] Y0_def by auto
        ultimately have yn1: "1 = ?y $ n" by auto
        have "next_dim.nonneg_lincomb c Y1 ?y"
          using c Y1_def
          unfolding next_dim.nonneg_lincomb_def by auto
        hence "?y \<in> next_dim.cone Y1"
          using next_dim.cone_iff_finite_cone[OF Y1_carrier] `finite Y1`
          unfolding next_dim.finite_cone_def by auto
        hence y: "vec_first ?y n \<in> convex_hull ?Z1"
          using convex_hull_next_dim[OF _ Y1_carrier `finite Y1` _ y_dim] Y1 yn1
          by simp

        have "next_dim.nonneg_lincomb c Y0 ?z" using c Y0_def
          unfolding next_dim.nonneg_lincomb_def by blast
        hence "?z \<in> next_dim.cone Y0"
          using `finite Y0` next_dim.cone_iff_finite_cone[OF Y0_carrier `finite Y0`]
          unfolding next_dim.finite_cone_def
          by fastforce
        hence z: "vec_first ?z n \<in> cone ?Z0"
          using cone_next_dim[OF _ Y0_carrier `finite Y0` _ _ zn0] Y0_def
            next_dim.lincomb_closed[OF Y0_carrier] by blast

        from xyz y z have "x \<in> convex_hull ?Z1 + cone ?Z0" by blast
      } moreover {
        fix x
        assume "x \<in> convex_hull ?Z1 + cone ?Z0"
        then obtain y z where "x = y + z" and y: "y \<in> convex_hull ?Z1"
          and z: "z \<in> cone ?Z0" by (auto elim: set_plus_elim)

        have yn: "y \<in> carrier_vec n"
          using y convex_hull_carrier[OF `?Z1 \<subseteq> carrier_vec n`] by blast
        hence "y @\<^sub>v vec_of_scal 1 \<in> carrier_vec (n + 1)"
          using vec_of_scal_dim(2) by fast
        moreover have "vec_first (y @\<^sub>v vec_of_scal 1) n \<in> convex_hull ?Z1"
          using vec_first_append[OF yn] y by auto
        moreover have "(y @\<^sub>v vec_of_scal 1) $ n = 1" using yn by simp
        ultimately have "y @\<^sub>v vec_of_scal 1 \<in> next_dim.cone Y1"
          using convex_hull_next_dim[OF _ Y1_carrier `finite Y1`] Y1 by blast
        hence y_cone: "y @\<^sub>v vec_of_scal 1 \<in> next_dim.cone Y"
          using next_dim.cone_mono[of Y1 Y] Y1_def by blast

        have zn: "z \<in> carrier_vec n" using z cone_carrier[of ?Z0] by fastforce
        hence "z @\<^sub>v vec_of_scal 0 \<in> carrier_vec (n + 1)"
          using vec_of_scal_dim(2) by fast
        moreover have "vec_first (z @\<^sub>v vec_of_scal 0) n \<in> cone ?Z0"
          using vec_first_append[OF zn] z by auto
        moreover have "(z @\<^sub>v vec_of_scal 0) $ n = 0" using zn by simp
        ultimately have "z @\<^sub>v vec_of_scal 0 \<in> next_dim.cone Y0"
          using cone_next_dim[OF _ Y0_carrier `finite Y0`] Y0_def by blast
        hence z_cone: "z @\<^sub>v vec_of_scal 0 \<in> next_dim.cone Y"
          using Y0_def next_dim.cone_mono[of Y0 Y] by blast

        have xn: "x \<in> carrier_vec n" using `x = y + z` yn zn by blast
        have "x @\<^sub>v vec_of_scal 1 = (y @\<^sub>v vec_of_scal 1) + (z @\<^sub>v vec_of_scal 0)"
          using `x = y + z` append_vec_add[OF yn zn]
          unfolding vec_of_scal_def by auto
        hence "x @\<^sub>v vec_of_scal 1 \<in> next_dim.cone Y"
          using next_dim.cone_elem_sum[OF Y_carrier y_cone z_cone] by simp
        hence "A *\<^sub>v x - b \<le> 0\<^sub>v nr" using M_cone_car[OF xn] Y by simp
        hence "A *\<^sub>v x \<le> b" using vec_le_iff_diff_le_0[of "A *\<^sub>v x" b]
            dim_mult_mat_vec[of A x] A by simp
        hence "x \<in> P" using P xn unfolding polyhedron_def by blast
      }
      ultimately show "P = convex_hull ?Z1 + cone ?Z0" by blast
    qed

    let ?Bnd = "det_bound n (max 1 Bnd)"
    assume "A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
      "b \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    hence *: "A \<in> \<int>\<^sub>m" "A \<in> Bounded_mat Bnd" "b \<in> \<int>\<^sub>v" "b \<in> Bounded_vec Bnd" by auto
    have "elements_mat M \<subseteq> elements_mat A \<union> vec_set (-b) \<union> {0,-1}"
      unfolding M_def
      unfolding elements_mat_append_rows[OF M_top M_bottom]
      unfolding elements_mat_append_cols[OF A mcb]
      by (subst elements_mat_append_cols, auto)
    also have "\<dots> \<subseteq> \<int> \<inter> ({x. abs x \<le> Bnd} \<union> {0,-1})"
      using *[unfolded Bounded_mat_elements_mat Ints_mat_elements_mat
          Bounded_vec_vec_set Ints_vec_vec_set] by auto
    also have "\<dots> \<subseteq> \<int> \<inter> ({x. abs x \<le> max 1 Bnd})" by auto
    finally have "M \<in> \<int>\<^sub>m" "M \<in> Bounded_mat (max 1 Bnd)"
      unfolding Bounded_mat_elements_mat Ints_mat_elements_mat by auto
    hence "M \<in> \<int>\<^sub>m \<inter> Bounded_mat (max 1 Bnd)" by blast
    from Bnd[OF this]
    have XBnd: "X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec ?Bnd" .
    {
      fix y
      assume y: "y \<in> Y"
      then obtain x where y: "y = ?f x \<cdot>\<^sub>v x" and xX: "x \<in> X" unfolding Y_def by auto
      with \<open>X \<subseteq> carrier_vec (n+1)\<close> have x: "x \<in> carrier_vec (n+1)" by auto
      from XBnd xX have xI: "x \<in> \<int>\<^sub>v" and xB: "x \<in> Bounded_vec ?Bnd" by auto
      {
        assume "y $ n = 0"
        hence "y = x" unfolding y using x by auto
        hence "y \<in> \<int>\<^sub>v \<inter> Bounded_vec ?Bnd" using xI xB by auto
      } note y0 = this
      {
        assume "y $ n \<noteq> 0"
        hence x0: "x $ n \<noteq> 0" using x unfolding y by auto
        from x xI have "x $ n \<in> \<int>" unfolding Ints_vec_def by auto
        with x0 have "abs (x $ n) \<ge> 1" by (meson Ints_nonzero_abs_ge1)
        hence abs: "abs (1 / (x $ n)) \<le> 1" by simp
        {
          fix a
          have "abs ((1 / (x $ n)) * a) = abs (1 / (x $ n)) * abs a"
            by simp
          also have "\<dots> \<le> 1 * abs a"
            by (rule mult_right_mono[OF abs], auto)
          finally have "abs ((1 / (x $ n)) * a) \<le> abs a" by auto
        } note abs = this
        from x0 have y: "y = (1 / (x $ n)) \<cdot>\<^sub>v x" unfolding y by auto
        have vy: "vec_set y = (\<lambda> a. (1 / (x $ n)) * a) ` vec_set x"
          unfolding y by (auto simp: vec_set_def)
        have "y \<in> Bounded_vec ?Bnd" using xB abs
          unfolding Bounded_vec_vec_set vy
          by (smt imageE max.absorb2 max.bounded_iff)
      } note yn0 = this
      note y0 yn0
    } note BndY = this
    from \<open>Y \<subseteq> carrier_vec (n+1)\<close>
    have setvY: "y \<in> Y \<Longrightarrow> set\<^sub>v (vec_first y n) \<subseteq> set\<^sub>v y" for y
      unfolding vec_first_def vec_set_def by auto
    from BndY(1) setvY
    show "?Z0 \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound n (max 1 Bnd))"
      by (force simp: Bounded_vec_vec_set Ints_vec_vec_set Y0_def)
    from BndY(2) setvY
    show "?Z1 \<subseteq> Bounded_vec (det_bound n (max 1 Bnd))"
      by (force simp: Bounded_vec_vec_set Ints_vec_vec_set Y0_def Y1_def)
  qed
qed

lemma decomposition_theorem_polyhedra_2:
  assumes Q: "Q \<subseteq> carrier_vec n" and fin_Q: "finite Q"
    and X: "X \<subseteq> carrier_vec n" and fin_X: "finite X"
    and P: "P = convex_hull Q + cone X"
  shows "\<exists>A b nr. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b"
proof -
  interpret next_dim: gram_schmidt "n + 1" "TYPE ('a)".
  interpret gram_schmidt_m "n + 1" n "TYPE('a)".

  from fin_Q obtain Qs where Qs: "Q = set Qs" using finite_list by auto
  from fin_X obtain Xs where Xs: "X = set Xs" using finite_list by auto
  define Y where "Y = {x @\<^sub>v vec_of_scal 1 | x. x \<in> Q}"
  define Z where "Z = {x @\<^sub>v vec_of_scal 0 | x. x \<in> X}"
  have fin_Y: "finite Y" unfolding Y_def using fin_Q by simp
  have fin_Z: "finite Z" unfolding Z_def using fin_X by simp
  have Y_dim: "Y \<subseteq> carrier_vec (n + 1)"
    unfolding Y_def using Q append_carrier_vec[OF _ vec_of_scal_dim(2)[of 1]]
    by blast
  have Z_dim: "Z \<subseteq> carrier_vec (n + 1)"
    unfolding Z_def using X append_carrier_vec[OF _ vec_of_scal_dim(2)[of 0]]
    by blast
  have Y_car: "Q = {vec_first x n | x. x \<in> Y}"
  proof (intro equalityI subsetI)
    fix x assume x: "x \<in> Q"
    hence "x @\<^sub>v vec_of_scal 1 \<in> Y" unfolding Y_def by blast
    thus "x \<in> {vec_first x n | x. x \<in> Y}"
      using Q vec_first_append[of x n "vec_of_scal 1"] x by force
  next
    fix x assume "x \<in> {vec_first x n | x. x \<in> Y}"
    then obtain y where "y \<in> Q" and "x = vec_first (y @\<^sub>v vec_of_scal 1) n"
      unfolding Y_def by blast
    thus "x \<in> Q" using Q vec_first_append[of y] by auto
  qed
  have Z_car: "X = {vec_first x n | x. x \<in> Z}"
  proof (intro equalityI subsetI)
    fix x assume x: "x \<in> X"
    hence "x @\<^sub>v vec_of_scal 0 \<in> Z" unfolding Z_def by blast
    thus "x \<in> {vec_first x n | x. x \<in> Z}"
      using X vec_first_append[of x n "vec_of_scal 0"] x by force
  next
    fix x assume "x \<in> {vec_first x n | x. x \<in> Z}"
    then obtain y where "y \<in> X" and "x = vec_first (y @\<^sub>v vec_of_scal 0) n"
      unfolding Z_def by blast
    thus "x \<in> X" using X vec_first_append[of y] by auto
  qed
  have Y_last: "\<forall> x \<in> Y. x $ n = 1" unfolding Y_def using Q by auto
  have Z_last: "\<forall> x \<in> Z. x $ n = 0" unfolding Z_def using X by auto

  have "finite (Y \<union> Z)" using fin_Y fin_Z by blast
  moreover have "Y \<union> Z \<subseteq> carrier_vec (n + 1)" using Y_dim Z_dim by blast
  ultimately obtain B nr
    where B: "next_dim.cone (Y \<union> Z) = next_dim.polyhedral_cone B"
      and B_carrier: "B \<in> carrier_mat nr (n + 1)"
    using next_dim.farkas_minkowsky_weyl_theorem[of "next_dim.cone (Y \<union> Z)"]
    by blast
  define A where "A = mat_col_first B n"
  define b where "b = col B n"
  have B_blocks: "B = A @\<^sub>c mat_of_col b"
    unfolding A_def b_def
    using mat_col_first_last_append[of B n 1] B_carrier
      mat_of_col_dim_col_1[of "mat_col_last B 1"] by auto
  have A_carrier: "A \<in> carrier_mat nr n" unfolding A_def using B_carrier by force
  have b_carrier: "b \<in> carrier_vec nr" unfolding b_def using B_carrier by force

  {
    fix x assume "x \<in> P"
    then obtain y z where x: "x = y + z" and y: "y \<in> convex_hull Q" and z: "z \<in> cone X"
      using P by (auto elim: set_plus_elim)

    have yn: "y \<in> carrier_vec n" using y convex_hull_carrier[OF Q] by blast
    moreover have zn: "z \<in> carrier_vec n" using z cone_carrier[OF X] by blast
    ultimately have xn: "x \<in> carrier_vec n" using x by blast

    have yn1: "y @\<^sub>v vec_of_scal 1 \<in> carrier_vec (n + 1)"
      using append_carrier_vec[OF yn] vec_of_scal_dim by fast
    have y_last: "(y @\<^sub>v vec_of_scal 1) $ n = 1" using yn by force
    have "vec_first (y @\<^sub>v vec_of_scal 1) n = y"
      using vec_first_append[OF yn] by simp
    hence "y @\<^sub>v vec_of_scal 1 \<in> next_dim.cone Y"
      using convex_hull_next_dim[OF _ Y_dim fin_Y Y_last yn1 y_last] Y_car y by argo
    hence y_cone: "y @\<^sub>v vec_of_scal 1 \<in> next_dim.cone (Y \<union> Z)"
      using next_dim.cone_mono[of Y "Y \<union> Z"] by blast

    have zn1: "z @\<^sub>v vec_of_scal 0 \<in> carrier_vec (n + 1)"
      using append_carrier_vec[OF zn] vec_of_scal_dim by fast
    have z_last: "(z @\<^sub>v vec_of_scal 0) $ n = 0" using zn by force
    have "vec_first (z @\<^sub>v vec_of_scal 0) n = z"
      using vec_first_append[OF zn] by simp
    hence "z @\<^sub>v vec_of_scal 0 \<in> next_dim.cone Z"
      using cone_next_dim[OF _ Z_dim fin_Z Z_last zn1 z_last] Z_car z by argo
    hence z_cone: "z @\<^sub>v vec_of_scal 0 \<in> next_dim.cone (Y \<union> Z)"
      using next_dim.cone_mono[of Z "Y \<union> Z"] by blast

    from `x = y + z`
    have "x @\<^sub>v vec_of_scal 1 = (y @\<^sub>v vec_of_scal 1) + (z @\<^sub>v vec_of_scal 0)"
      using append_vec_add[OF yn zn] vec_of_scal_dim_1
      unfolding vec_of_scal_def by auto
    hence "x @\<^sub>v vec_of_scal 1 \<in> next_dim.cone (Y \<union> Z) \<and> x \<in> carrier_vec n"
      using next_dim.cone_elem_sum[OF _ y_cone z_cone] Y_dim Z_dim xn by auto
  } moreover {
    fix x assume "x @\<^sub>v vec_of_scal 1 \<in> next_dim.cone (Y \<union> Z)"
    then obtain c where x: "next_dim.lincomb c (Y \<union> Z) = x @\<^sub>v vec_of_scal 1"
      and c: "c ` (Y \<union> Z) \<subseteq> {t. t \<ge> 0}"
      using next_dim.cone_iff_finite_cone Y_dim Z_dim fin_Y fin_Z
      unfolding next_dim.finite_cone_def next_dim.nonneg_lincomb_def by auto

    let ?y = "next_dim.lincomb c Y"
    let ?z = "next_dim.lincomb c Z"
    have xyz: "x @\<^sub>v vec_of_scal 1 = ?y + ?z"
      using x next_dim.lincomb_union[OF Y_dim Z_dim _ fin_Y fin_Z] Y_last Z_last
      by fastforce

    have y_dim: "?y \<in> carrier_vec (n + 1)" using next_dim.lincomb_closed[OF Y_dim]
      by blast
    have z_dim: "?z \<in> carrier_vec (n + 1)" using next_dim.lincomb_closed[OF Z_dim]
      by blast
    have "x @\<^sub>v vec_of_scal 1 \<in> carrier_vec (n + 1)"
      using xyz add_carrier_vec[OF y_dim z_dim] by argo
    hence x_dim: "x \<in> carrier_vec n"
      using carrier_dim_vec[of x n] carrier_dim_vec[of _ "n + 1"]
      by force

    have z_last: "?z $ n = 0" using Z_last next_dim.lincomb_index[OF _ Z_dim, of n]
      by force
    have "?y $ n + ?z $ n = (x @\<^sub>v vec_of_scal 1) $ n"
      using xyz index_add_vec(1) z_dim by simp
    also have "\<dots> = 1" using x_dim by auto
    finally have y_last: "?y $ n = 1" using z_last by algebra

    have "?y \<in> next_dim.cone Y"
      using next_dim.cone_iff_finite_cone[OF Y_dim] fin_Y c
      unfolding next_dim.finite_cone_def next_dim.nonneg_lincomb_def by auto
    hence y_cone: "vec_first ?y n \<in> convex_hull Q"
      using convex_hull_next_dim[OF _ Y_dim fin_Y Y_last y_dim y_last] Y_car
      by blast

    have "?z \<in> next_dim.cone Z"
      using next_dim.cone_iff_finite_cone[OF Z_dim] fin_Z c
      unfolding next_dim.finite_cone_def next_dim.nonneg_lincomb_def by auto
    hence z_cone: "vec_first ?z n \<in> cone X"
      using cone_next_dim[OF _ Z_dim fin_Z Z_last z_dim z_last] Z_car
      by blast

    have "x = vec_first (x @\<^sub>v vec_of_scal 1) n" using vec_first_append[OF x_dim] by simp
    also have "\<dots> = vec_first ?y n + vec_first ?z n"
      using xyz vec_first_add[of n ?y ?z] y_dim z_dim carrier_dim_vec by auto
    finally have "x \<in> P"
      using y_cone z_cone P by blast
  } moreover {
    fix x :: "'a vec"
    assume xn: "x \<in> carrier_vec n"
    hence "(x @\<^sub>v vec_of_scal 1 \<in> next_dim.polyhedral_cone B) =
          (B *\<^sub>v (x @\<^sub>v vec_of_scal 1) \<le> 0\<^sub>v nr)"
      unfolding next_dim.polyhedral_cone_def using B_carrier
      using append_carrier_vec[OF _ vec_of_scal_dim(2)[of 1]] by auto
    also have "\<dots> = ((A @\<^sub>c mat_of_col b) *\<^sub>v (x @\<^sub>v vec_of_scal 1) \<le> 0\<^sub>v nr)"
      using B_blocks by blast
    also have "(A @\<^sub>c mat_of_col b) *\<^sub>v (x @\<^sub>v vec_of_scal 1) =
               A *\<^sub>v x + mat_of_col b *\<^sub>v vec_of_scal 1"
      by (rule mat_mult_append_cols, insert A_carrier b_carrier xn, auto simp del: One_nat_def)
    also have "mat_of_col b *\<^sub>v vec_of_scal 1 = b"
      using mult_mat_of_row_vec_of_scal[of b 1] by simp
    also have "A *\<^sub>v x + b = A *\<^sub>v x - -b" by auto
    finally have "(x @\<^sub>v vec_of_scal 1 \<in> next_dim.polyhedral_cone B) = (A *\<^sub>v x \<le> -b)"
      using vec_le_iff_diff_le_0[of "A *\<^sub>v x" "-b"] A_carrier by simp
  }
  ultimately have "P = polyhedron A (-b)"
    unfolding polyhedron_def using B by blast
  moreover have "-b \<in> carrier_vec nr" using b_carrier by simp
  ultimately show ?thesis using A_carrier by blast
qed

lemma decomposition_theorem_polyhedra:
  "(\<exists> A b nr. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b) \<longleftrightarrow>
   (\<exists> Q X. Q \<union> X \<subseteq> carrier_vec n \<and> finite (Q \<union> X) \<and> P = convex_hull Q + cone X)" (is "?l = ?r")
proof
  assume ?l
  then obtain A b nr where A: "A \<in> carrier_mat nr n"
    and b: "b \<in> carrier_vec nr" and P: "P = polyhedron A b" by auto
  from decomposition_theorem_polyhedra_1[OF this] obtain Q X
    where *: "X \<subseteq> carrier_vec n" "finite X" "Q \<subseteq> carrier_vec n" "finite Q" "P = convex_hull Q + cone X"
    by meson
  show ?r
    by (rule exI[of _ Q], rule exI[of _ X], insert *, auto simp: polytope_def)
next
  assume ?r
  then obtain Q X where QX_carrier: "Q \<union> X \<subseteq> carrier_vec n"
    and QX_fin: "finite (Q \<union> X)"
    and P: "P = convex_hull Q + cone X" by blast
  from QX_carrier have Q: "Q \<subseteq> carrier_vec n" and X: "X \<subseteq> carrier_vec n" by simp_all
  from QX_fin have fin_Q: "finite Q" and fin_X: "finite X" by simp_all
  show ?l using decomposition_theorem_polyhedra_2[OF Q fin_Q X fin_X P] by blast
qed

lemma polytope_equiv_bounded_polyhedron:
  "polytope P \<longleftrightarrow>
  (\<exists>A b nr bnd. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b \<and> P \<subseteq> Bounded_vec bnd)"
proof
  assume polyP: "polytope P"
  from this obtain Q where Qcarr: "Q \<subseteq> carrier_vec n" and finQ: "finite Q"
    and PconvhQ: "P = convex_hull Q" unfolding polytope_def by auto
  let ?X = "{}"
  have "convex_hull Q + {0\<^sub>v n} = convex_hull Q" using Qcarr add_0_right_vecset[of "convex_hull Q"]
    by (simp add: convex_hull_carrier)
  hence "P = convex_hull Q + cone ?X" using PconvhQ by simp
  hence "Q \<union> ?X \<subseteq> carrier_vec n \<and> finite (Q \<union> ?X) \<and> P = convex_hull Q + cone ?X"
    using Qcarr finQ PconvhQ by simp
  hence "\<exists> A b nr. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b"
    using decomposition_theorem_polyhedra by blast
  hence Ppolyh: "\<exists>A b nr. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b" by blast
  from finite_Bounded_vec_Max[OF Qcarr finQ] obtain bnd where "Q \<subseteq> Bounded_vec bnd" by auto
  hence Pbnd: "P \<subseteq> Bounded_vec bnd" using convex_hull_bound PconvhQ Qcarr by auto
  from Ppolyh Pbnd show "\<exists>A b nr bnd. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr
    \<and> P = polyhedron A b \<and> P \<subseteq> Bounded_vec bnd" by auto
next
  assume "\<exists>A b nr bnd. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b
    \<and> P \<subseteq> Bounded_vec bnd"
  from this obtain A b nr bnd where Adim: "A \<in> carrier_mat nr n" and bdim: "b \<in> carrier_vec nr"
    and Ppolyh: "P = polyhedron A b" and Pbnd: "P \<subseteq> Bounded_vec bnd" by auto
  have "\<exists> A b nr. A \<in> carrier_mat nr n \<and> b \<in> carrier_vec nr \<and> P = polyhedron A b"
    using Adim bdim Ppolyh by blast
  hence "\<exists> Q X. Q \<union> X \<subseteq> carrier_vec n \<and> finite (Q \<union> X) \<and> P = convex_hull Q + cone X"
    using decomposition_theorem_polyhedra by simp
  from this obtain Q X where QXcarr: "Q \<union> X \<subseteq> carrier_vec n"
    and finQX: "finite (Q \<union> X)" and Psum: "P = convex_hull Q + cone X" by auto
  from QXcarr have Qcarr: "convex_hull Q \<subseteq> carrier_vec n" by (simp add: convex_hull_carrier)
  from QXcarr have Xcarr: "cone X \<subseteq> carrier_vec n" by (simp add: gram_schmidt.cone_carrier)
  from Pbnd have Pcarr: "P \<subseteq> carrier_vec n" using Ppolyh unfolding polyhedron_def by simp
  have "P = convex_hull Q"
  proof(cases "Q = {}")
    case True
    then show "P = convex_hull Q" unfolding Psum by (auto simp: set_plus_def)
  next
    case False
    hence convnotempty: "convex_hull Q \<noteq> {}" using QXcarr by simp
    have Pbndex: "\<exists>bnd. P \<subseteq> Bounded_vec bnd" using Pbnd
      using QXcarr by auto
    from False have "(\<exists> bndc. cone X \<subseteq> Bounded_vec bndc)"
      using bounded_vecset_sum[OF Qcarr Xcarr Psum Pbndex] False convnotempty by blast
    hence "cone X = {0\<^sub>v n}" using bounded_cone_is_zero QXcarr by auto
    thus ?thesis unfolding Psum using Qcarr by (auto simp: add_0_right_vecset)
  qed
  thus "polytope P" using finQX QXcarr unfolding polytope_def by auto
qed
end

end