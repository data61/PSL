section \<open>Integer Hull\<close>

text \<open>We define the integer hull of a polyhedron, i.e., the convex hull of all integer solutions.
  Moreover, we prove the result of Meyer that the integer hull of a polyhedron defined by an
  integer matrix is again a polyhedron, and give bounds for a corresponding decomposition theorem.\<close>

theory Integer_Hull
  imports
    Decomposition_Theorem
    Mixed_Integer_Solutions (* for gram-schmidt-floor *)
begin

context gram_schmidt
begin
definition "integer_hull P = convex_hull (P \<inter> \<int>\<^sub>v)"

lemma integer_hull_mono: "P \<subseteq> Q \<Longrightarrow> integer_hull P \<subseteq> integer_hull Q"
  unfolding integer_hull_def
  by (intro convex_hull_mono, auto)

end

lemma abs_neg_floor: "\<bar>of_int b\<bar> \<le> Bnd \<Longrightarrow> - (floor Bnd) \<le> b"
  using abs_le_D2 floor_mono by fastforce

lemma abs_pos_floor: "\<bar>of_int b\<bar> \<le> Bnd \<Longrightarrow> b \<le> floor Bnd"
  using abs_le_D1 le_floor_iff by auto

context gram_schmidt_floor
begin

lemma integer_hull_integer_cone: assumes C: "C \<subseteq> carrier_vec n" 
  and CI: "C \<subseteq> \<int>\<^sub>v"
  shows "integer_hull (cone C) = cone C"
proof
  have "cone C \<inter> \<int>\<^sub>v \<subseteq> cone C" by blast
  thus "integer_hull (cone C) \<subseteq> cone C"
    using cone_cone[OF C] convex_cone[OF C] convex_hull_mono
    unfolding integer_hull_def convex_def by metis
  {
    fix x
    assume "x \<in> cone C"
    then obtain D where finD: "finite D" and DC: "D \<subseteq> C" and x: "x \<in> finite_cone D" 
      unfolding cone_def by auto    
    from DC C CI have D: "D \<subseteq> carrier_vec n" and DI: "D \<subseteq> \<int>\<^sub>v" by auto
    from D x finD have "x \<in> finite_cone (D \<union> {0\<^sub>v n})" using finite_cone_mono[of "D \<union> {0\<^sub>v n}" D] by auto
    then obtain l where x: "lincomb l (D \<union> {0\<^sub>v n}) = x"
                  and l: "l ` (D \<union> {0\<^sub>v n}) \<subseteq> {t. t \<ge> 0}"
      using finD unfolding finite_cone_def nonneg_lincomb_def by auto
    define L where "L = sum l (D \<union> {0\<^sub>v n})"
    define L_sup :: 'a where "L_sup = of_int (floor L + 1)" 
    have "L_sup \<ge> L" using floor_correct[of L] unfolding L_sup_def by linarith
    have "L \<ge> 0" unfolding L_def using sum_nonneg[of _ l] l by blast
    hence "L_sup \<ge> 1" unfolding L_sup_def by simp
    hence "L_sup > 0" by fastforce

    let ?f = "\<lambda> y. if y = 0\<^sub>v n then L_sup - L else 0"
    have "lincomb ?f {0\<^sub>v n} = 0\<^sub>v n"
      using already_in_span[of "{}" "0\<^sub>v n"] lincomb_in_span local.span_empty
      by auto
    moreover have "lincomb ?f (D - {0\<^sub>v n}) = 0\<^sub>v n"
      by(rule lincomb_zero, insert D, auto)
    ultimately have "lincomb ?f (D \<union> {0\<^sub>v n}) = 0\<^sub>v n"
      using lincomb_vec_diff_add[of "D \<union> {0\<^sub>v n}" "{0\<^sub>v n}"] D finD by simp
    hence lcomb_f: "lincomb (\<lambda> y. l y + ?f y) (D \<union> {0\<^sub>v n}) = x"
      using lincomb_sum[of "D \<union> {0\<^sub>v n}" l ?f] finD D x by simp
    have "sum ?f (D \<union> {0\<^sub>v n}) = L_sup - L"
      by (simp add: sum.subset_diff[of "{0\<^sub>v n}" "D \<union> {0\<^sub>v n}" ?f] finD)
    hence "sum (\<lambda> y. l y + ?f y) (D \<union> {0\<^sub>v n}) = L_sup"
      using l L_def by auto
    moreover have "(\<lambda> y. l y + ?f y) ` (D \<union> {0\<^sub>v n}) \<subseteq> {t. t \<ge> 0}"
      using `L \<le> L_sup` l by force
    ultimately obtain l' where x: "lincomb l' (D \<union> {0\<^sub>v n}) = x"
                          and l': "l' ` (D \<union> {0\<^sub>v n}) \<subseteq> {t. t \<ge> 0}"
                          and sum_l': "sum l' (D \<union> {0\<^sub>v n}) = L_sup"
      using lcomb_f by blast
    
    let ?D' = "{L_sup \<cdot>\<^sub>v v | v. v \<in> D \<union> {0\<^sub>v n}}"
    have Did: "?D' = (\<lambda> v. L_sup \<cdot>\<^sub>v v) ` (D \<union> {0\<^sub>v n})" by force
    define l'' where "l'' = (\<lambda> y. l' ((1 / L_sup) \<cdot>\<^sub>v y) / L_sup)"
    obtain lD where dist: "distinct lD" and lD: "D \<union> {0\<^sub>v n} = set lD"
      using finite_distinct_list[of "D \<union> {0\<^sub>v n}"] finD by auto
    let ?lD' = "map ((\<cdot>\<^sub>v) L_sup) lD"
    have dist': "distinct ?lD'"
      using distinct_smult_nonneg[OF _ dist] `L_sup > 0` by fastforce

    have x': "lincomb l'' ?D' = x" unfolding x[symmetric] l''_def
      unfolding lincomb_def Did 
    proof (subst finsum_reindex)
      from `L_sup > 0` smult_vec_nonneg_eq[of L_sup] show "inj_on ((\<cdot>\<^sub>v) L_sup) (D \<union> {0\<^sub>v n})" 
        by (auto simp: inj_on_def)
      show "(\<lambda>v. l' (1 / L_sup \<cdot>\<^sub>v v) / L_sup \<cdot>\<^sub>v v) \<in> (\<cdot>\<^sub>v) L_sup ` (D \<union> {0\<^sub>v n}) \<rightarrow> carrier_vec n" 
        using D by auto
      from `L_sup > 0` have "L_sup \<noteq> 0" by auto
      then show "(\<Oplus>\<^bsub>V\<^esub>x\<in>D \<union> {0\<^sub>v n}. l' (1 / L_sup \<cdot>\<^sub>v (L_sup \<cdot>\<^sub>v x)) / L_sup \<cdot>\<^sub>v (L_sup \<cdot>\<^sub>v x)) =
        (\<Oplus>\<^bsub>V\<^esub>v\<in>D \<union> {0\<^sub>v n}. l' v \<cdot>\<^sub>v v)" 
        by (intro finsum_cong, insert D, auto simp: smult_smult_assoc)
    qed
    have "D \<union> {0\<^sub>v n} \<subseteq> cone C" using set_in_cone[OF C] DC zero_in_cone by blast
    hence D': "?D' \<subseteq> cone C" using cone_smult[of L_sup, OF _ C] `L_sup > 0` by auto
    have "D \<union> {0\<^sub>v n} \<subseteq> \<int>\<^sub>v" unfolding zero_vec_def using DI Ints_vec_def by auto
    moreover have "L_sup \<in> \<int>" unfolding L_sup_def by auto
    ultimately have D'I: "?D' \<subseteq> \<int>\<^sub>v" unfolding Ints_vec_def by force

    have "1 = sum l' (D \<union> {0\<^sub>v n}) * (1 / L_sup)" using sum_l' `L_sup > 0` by auto
    also have "sum l' (D \<union> {0\<^sub>v n}) = sum_list (map l' lD)"
      using sum.distinct_set_conv_list[OF dist] lD by auto
    also have "map l' lD = map (l' \<circ> ((\<cdot>\<^sub>v) (1 / L_sup))) ?lD'"
      using smult_smult_assoc[of "1 / L_sup" L_sup] `L_sup > 0`
      by (simp add: comp_assoc)
    also have "l' \<circ> ((\<cdot>\<^sub>v) (1 / L_sup)) = (\<lambda> x. l' ((1 / L_sup) \<cdot>\<^sub>v x))" by (rule comp_def)
    also have "sum_list (map \<dots> ?lD') * (1 / L_sup) =
               sum_list (map (\<lambda>y. l' (1 / L_sup \<cdot>\<^sub>v y) * (1 / L_sup)) ?lD')"
      using sum_list_mult_const[of _ "1 / L_sup" ?lD'] by presburger
    also have "\<dots> = sum_list (map l'' ?lD')"
      unfolding l''_def using `L_sup > 0` by simp
    also have "\<dots> = sum l'' (set ?lD')" using sum.distinct_set_conv_list[OF dist'] by metis
    also have "set ?lD' = ?D'" using lD by auto
    finally have sum_l': "sum l'' ?D' = 1" by auto

    moreover have "l'' ` ?D' \<subseteq> {t. t \<ge> 0}"
    proof
      fix y
      assume "y \<in> l'' ` ?D'"
      then obtain x where y: "y = l'' x" and "x \<in> ?D'" by blast
      then obtain v where "v \<in> D \<union> {0\<^sub>v n}" and x: "x = L_sup \<cdot>\<^sub>v v" by blast
      hence "0 \<le> l' v / L_sup" using l' `L_sup > 0` by fastforce
      also have "\<dots> = l'' x" unfolding x l''_def
        using smult_smult_assoc[of "1 / L_sup" "L_sup" v] `L_sup > 0` by simp
      finally show "y \<in> {t. t \<ge> 0}" using y by blast
      qed
    moreover have "finite ?D'" using finD by simp

    ultimately have "x \<in> integer_hull (cone C)"
      unfolding integer_hull_def convex_hull_def
      using x' D' D'I convex_lincomb_def[of l'' ?D' x]
                      nonneg_lincomb_def[of l'' ?D' x] by fast
  }
  thus "cone C \<subseteq> integer_hull (cone C)" by blast
qed

theorem decomposition_theorem_integer_hull_of_polyhedron: assumes A: "A \<in> carrier_mat nr n"
  and b: "b \<in> carrier_vec nr"
  and AI: "A \<in> \<int>\<^sub>m"
  and bI: "b \<in> \<int>\<^sub>v"
  and P: "P = polyhedron A b"
  and Bnd: "Bnd = Max (abs ` (elements_mat A \<union> vec_set b))"
shows "\<exists> H C. H \<union> C \<subseteq> carrier_vec n \<inter> \<int>\<^sub>v 
  \<and> H \<subseteq> Bounded_vec (fact (n+1) * (max 1 Bnd)^n)
  \<and> C \<subseteq> Bounded_vec (fact n * (max 1 Bnd)^n)
  \<and> finite (H \<union> C) 
  \<and> integer_hull P = convex_hull H + cone C"
proof -
  define DBnd where "DBnd = det_bound n (max 1 Bnd)" 
  define nBnd where "nBnd = of_nat (n+1) * DBnd" 
  have DBnd: "DBnd = fact n * (max 1 Bnd)^n" unfolding DBnd_def det_bound_def by auto
  have nBnd: "nBnd = fact (n+1) * (max 1 Bnd)^n" unfolding nBnd_def DBnd
    by auto
  have DBnd0: "DBnd \<ge> 0" unfolding DBnd_def det_bound_def by auto
  have Pn: "P \<subseteq> carrier_vec n" unfolding P polyhedron_def by auto
  have "A \<in> Bounded_mat Bnd \<and> b \<in> Bounded_vec Bnd"
    unfolding Bnd Bounded_mat_elements_mat Bounded_vec_vec_set
    by (intro ballI conjI Max_ge finite_imageI imageI finite_UnI, auto)
  from decomposition_theorem_polyhedra_1[OF A b P, of Bnd] AI bI this
  obtain QQ Q C where C: "C \<subseteq> carrier_vec n" and finC: "finite C"
    and QQ: "QQ \<subseteq> carrier_vec n" and finQ: "finite QQ" and BndQQ: "QQ \<subseteq> Bounded_vec DBnd"
    and P: "P = Q + cone C"
    and Q_def: "Q = convex_hull QQ"
    and CI: "C \<subseteq> \<int>\<^sub>v" and BndC: "C \<subseteq> Bounded_vec DBnd"
    by (auto simp: DBnd_def)
  define Bnd' where "Bnd' = of_nat n * DBnd" 
  note coneC = cone_iff_finite_cone[OF C finC]
  have Q: "Q \<subseteq> carrier_vec n" unfolding Q_def using convex_hull_carrier[OF QQ] .
  define B where "B = {x. \<exists> a D. nonneg_lincomb a D x \<and> D \<subseteq> C \<and> lin_indpt D \<and> (\<forall> d \<in> D. a d \<le> 1)}"
  {
    fix b
    assume "b \<in> B" 
    then obtain a D where b: "b = lincomb a D" and DC: "D \<subseteq> C" 
      and linD: "lin_indpt D" and bnd_a: "\<forall> d \<in> D. 0 \<le> a d \<and> a d \<le> 1" 
      by (force simp: B_def nonneg_lincomb_def)
    from DC C have D: "D \<subseteq> carrier_vec n" by auto
    from DC finC have finD: "finite D" by (metis finite_subset)
    from D linD finD have cardD: "card D \<le> n" using dim_is_n li_le_dim(2) by auto
    from BndC DC have BndD: "D \<subseteq> Bounded_vec DBnd" by auto
    from lincomb_card_bound[OF this D DBnd0 _ cardD, of a, folded b] bnd_a 
    have "b \<in> Bounded_vec Bnd'" unfolding Bnd'_def by force
  }
  hence BndB: "B \<subseteq> Bounded_vec Bnd'" ..
  from BndQQ have BndQ: "Q \<subseteq> Bounded_vec DBnd" unfolding Q_def using QQ by (metis convex_hull_bound)
  have B: "B \<subseteq> carrier_vec n"
    unfolding B_def nonneg_lincomb_def using C by auto
  from Q B have QB: "Q + B \<subseteq> carrier_vec n" by (auto elim!: set_plus_elim)
  from sum_in_Bounded_vecI[of _ DBnd _ Bnd' n] BndQ BndB B Q
  have "Q + B \<subseteq> Bounded_vec (DBnd + Bnd')" by (auto elim!: set_plus_elim)
  also have "DBnd + Bnd' = nBnd" unfolding nBnd_def Bnd'_def by (simp add: algebra_simps)
  finally have QB_Bnd: "Q + B \<subseteq> Bounded_vec nBnd" by blast
  have finQBZ: "finite ((Q + B) \<inter> \<int>\<^sub>v)"
  proof (rule finite_subset[OF subsetI])
    define ZBnd where "ZBnd = floor nBnd"
    let ?vecs = "set (map vec_of_list (concat_lists (map (\<lambda> i. map (of_int :: _ \<Rightarrow> 'a) [-ZBnd..ZBnd]) [0..<n])))"
    have id: "?vecs = vec_of_list `
      {as. length as = n \<and> (\<forall>i<n. \<exists> b. as ! i = of_int b \<and> b \<in> {- ZBnd..ZBnd})}"
      unfolding set_map by (rule image_cong, auto)
    show "finite ?vecs" by (rule finite_set)
    fix x
    assume "x \<in> (Q + B) \<inter> \<int>\<^sub>v"
    hence xQB: "x \<in> Q + B" and xI: "x \<in> \<int>\<^sub>v" by auto
    from xQB QB_Bnd QB have xBnd: "x \<in> Bounded_vec nBnd" and x: "x \<in> carrier_vec n" by auto
    have xid: "x = vec_of_list (list_of_vec x)" by auto
    show "x \<in> ?vecs" unfolding id
    proof (subst xid, intro imageI CollectI conjI allI impI)
      show "length (list_of_vec x) = n" using x by auto
      fix i
      assume i: "i < n"
      have id: "list_of_vec x ! i = x $ i" using i x by auto
      from xBnd[unfolded Bounded_vec_def] i x have xiBnd: "abs (x $ i) \<le> nBnd" by auto
      from xI[unfolded Ints_vec_def] i x have "x $ i \<in> \<int>" by auto
      then obtain b where b: "x $ i = of_int b" unfolding Ints_def by blast
      show "\<exists>b. list_of_vec x ! i = of_int b \<and> b \<in> {- ZBnd..ZBnd}" unfolding id ZBnd_def
        using xiBnd unfolding b by (intro exI[of _ b], auto intro!: abs_neg_floor abs_pos_floor)
    qed
  qed
  have QBZ: "(Q + B) \<inter> \<int>\<^sub>v \<subseteq> carrier_vec n" using QB by auto
  from decomposition_theorem_polyhedra_2[OF QBZ finQBZ, folded integer_hull_def, OF C finC refl]
  obtain A' b' nr' where A': "A' \<in> carrier_mat nr' n" and b': "b' \<in> carrier_vec nr'"
    and IH: "integer_hull (Q + B) + cone C = polyhedron A' b'"
    by auto
  {
    fix p
    assume "p \<in> P \<inter> \<int>\<^sub>v"
    hence pI: "p \<in> \<int>\<^sub>v" and p: "p \<in> Q + cone C" unfolding P by auto
    from set_plus_elim[OF p] obtain q c where
      pqc: "p = q + c" and qQ: "q \<in> Q" and cC: "c \<in> cone C" by auto
    from qQ Q have q: "q \<in> carrier_vec n" by auto
    from Caratheodory_theorem[OF C] cC
    obtain D where cD: "c \<in> finite_cone D" and DC: "D \<subseteq> C" and linD: "lin_indpt D" by auto
    from DC C have D: "D \<subseteq> carrier_vec n" by auto
    from DC finC have finD: "finite D" by (metis finite_subset)
    from cD finD
    obtain a where "nonneg_lincomb a D c" unfolding finite_cone_def by auto
    hence caD: "c = lincomb a D" and a0: "\<And> d. d \<in> D \<Longrightarrow> a d \<ge> 0"
      unfolding nonneg_lincomb_def by auto
    define a1 where "a1 = (\<lambda> c. a c - of_int (floor (a c)))"
    define a2 where "a2 = (\<lambda> c. of_int (floor (a c)) :: 'a)"
    define d where "d = lincomb a2 D"
    define b where "b = lincomb a1 D"
    have b: "b \<in> carrier_vec n" and d: "d \<in> carrier_vec n" unfolding d_def b_def using D by auto
    have bB: "b \<in> B" unfolding B_def b_def nonneg_lincomb_def
    proof (intro CollectI exI[of _ a1] exI[of _ D] conjI ballI refl subsetI linD)
      show "x \<in> a1 ` D \<Longrightarrow> 0 \<le> x" for x using a0 unfolding a1_def by auto
      show "a1 c \<le> 1" for c unfolding a1_def by linarith
    qed (insert DC, auto)
    have cbd: "c = b + d" unfolding b_def d_def caD lincomb_sum[OF finD D, symmetric]
      by (rule lincomb_cong[OF refl D], auto simp: a1_def a2_def)
    have "nonneg_lincomb a2 D d" unfolding d_def nonneg_lincomb_def
      by (intro allI conjI refl subsetI, insert a0, auto simp: a2_def)
    hence dC: "d \<in> cone C" unfolding cone_def finite_cone_def using finC finD DC by auto
    have p: "p = (q + b) + d" unfolding pqc cbd using q b d by auto
    have dI: "d \<in> \<int>\<^sub>v" using CI DC C unfolding d_def indexed_Ints_vec_UNIV
      by (intro lincomb_indexed_Ints_vec, auto simp: a2_def)
    from diff_indexed_Ints_vec[of _ _ _ UNIV, folded indexed_Ints_vec_UNIV, OF _ d pI dI, unfolded p]
    have "q + b + d - d \<in> \<int>\<^sub>v" using q b d by auto
    also have "q + b + d - d = q + b" using q b d by auto
    finally have qbI: "q + b \<in> \<int>\<^sub>v" by auto
    have "p \<in> integer_hull (Q + B) + cone C" unfolding p integer_hull_def
      by (intro set_plus_intro dC set_mp[OF set_in_convex_hull] IntI qQ bB qbI, insert Q B,
          auto elim!: set_plus_elim)
  }
  hence "P \<inter> \<int>\<^sub>v \<subseteq> integer_hull (Q + B) + cone C" by auto
  hence one_dir: "integer_hull P \<subseteq> integer_hull (Q + B) + cone C" unfolding IH
    unfolding integer_hull_def using convex_convex_hull[OF polyhedra_are_convex[OF A' b' refl]]
      convex_hull_mono by blast
  have "integer_hull (Q + B) + cone C \<subseteq> integer_hull P + cone C" unfolding P
  proof (intro set_plus_mono2 subset_refl integer_hull_mono)
    show "B \<subseteq> cone C" unfolding B_def cone_def finite_cone_def using finite_subset[OF _ finC] by auto
  qed
  also have "\<dots> = integer_hull P + integer_hull (cone C)"
    using integer_hull_integer_cone[OF C CI] by simp
  also have "\<dots> = convex_hull (P \<inter> \<int>\<^sub>v) + convex_hull (cone C \<inter> \<int>\<^sub>v)"
    unfolding integer_hull_def by simp
  also have "\<dots> = convex_hull ((P \<inter> \<int>\<^sub>v) + (cone C \<inter> \<int>\<^sub>v))"
    by (rule convex_hull_sum[symmetric], insert Pn cone_carrier[OF C], auto)
  also have "\<dots> \<subseteq> convex_hull ((P + cone C) \<inter> \<int>\<^sub>v)"
  proof (rule convex_hull_mono)
    show "P \<inter> \<int>\<^sub>v + cone C \<inter> \<int>\<^sub>v \<subseteq> (P + cone C) \<inter> \<int>\<^sub>v"
      using add_indexed_Ints_vec[of _ n _ UNIV, folded indexed_Ints_vec_UNIV] cone_carrier[OF C] Pn
      by (auto elim!: set_plus_elim)
  qed
  also have "\<dots> = integer_hull (P + cone C)" unfolding integer_hull_def ..
  also have "P + cone C = P"
  proof -
    have CC: "cone C \<subseteq> carrier_vec n" using C by (rule cone_carrier)
    have "P + cone C = Q + (cone C + cone C)" unfolding P
      by (rule assoc_add_vecset[symmetric, OF Q CC CC])
    also have "cone C + cone C = cone C" by (rule cone_add_cone[OF C])
    finally show ?thesis unfolding P .
  qed
  finally have "integer_hull (Q + B) + cone C \<subseteq> integer_hull P" .
  with one_dir have id: "integer_hull P = integer_hull (Q + B) + cone C" by auto
  show ?thesis unfolding id unfolding integer_hull_def nBnd[symmetric] DBnd[symmetric]
  proof (rule exI[of _ "(Q + B) \<inter> \<int>\<^sub>v"], intro exI[of _ C] conjI refl BndC)
    from QB_Bnd show "(Q + B) \<inter> \<int>\<^sub>v \<subseteq> Bounded_vec nBnd" by auto
    show "(Q + B) \<inter> \<int>\<^sub>v \<union> C \<subseteq> carrier_vec n \<inter> \<int>\<^sub>v" 
      using QB C CI by auto
    show "finite ((Q + B) \<inter> \<int>\<^sub>v \<union> C)" using finQBZ finC by auto
  qed
qed

corollary integer_hull_of_polyhedron: assumes A: "A \<in> carrier_mat nr n"
  and b: "b \<in> carrier_vec nr"
  and AI: "A \<in> \<int>\<^sub>m"
  and bI: "b \<in> \<int>\<^sub>v"
  and P: "P = polyhedron A b"
shows "\<exists> A' b' nr'. A' \<in> carrier_mat nr' n \<and> b' \<in> carrier_vec nr' \<and> integer_hull P = polyhedron A' b'"
proof -
  from decomposition_theorem_integer_hull_of_polyhedron[OF A b AI bI P refl]
  obtain H C
    where HC: "H \<union> C \<subseteq> carrier_vec n \<inter> \<int>\<^sub>v" "finite (H \<union> C)" 
      and decomp: "integer_hull P = convex_hull H + cone C" by auto
  show ?thesis
    by (rule decomposition_theorem_polyhedra_2[OF _ _ _ _ decomp], insert HC, auto)
qed

corollary small_integer_solution_nonstrict_via_decomp: fixes A :: "'a mat"
  assumes A: "A \<in> carrier_mat nr n"
    and b: "b \<in> carrier_vec nr"
    and AI: "A \<in> \<int>\<^sub>m"
    and bI: "b \<in> \<int>\<^sub>v"
    and Bnd: "Bnd = Max (abs ` (elements_mat A \<union> vec_set b))"
    and x: "x \<in> carrier_vec n"
    and xI: "x \<in> \<int>\<^sub>v"
    and sol: "A *\<^sub>v x \<le> b"
  shows "\<exists> y.
  y \<in> carrier_vec n \<and>
  y \<in> \<int>\<^sub>v \<and>
  A *\<^sub>v y \<le> b \<and>
  y \<in> Bounded_vec (fact (n+1) * (max 1 Bnd)^n)"
proof -
  from x sol have "x \<in> polyhedron A b" unfolding polyhedron_def by auto
  with xI x have xsol: "x \<in> integer_hull (polyhedron A b)" unfolding integer_hull_def
    by (meson IntI convex_hull_mono in_mono inf_sup_ord(1) inf_sup_ord(2) set_in_convex_hull)
  from decomposition_theorem_integer_hull_of_polyhedron[OF A b AI bI refl Bnd]
  obtain H C where HC: "H \<union> C \<subseteq> carrier_vec n \<inter> \<int>\<^sub>v" 
    "H \<subseteq> Bounded_vec (fact (n + 1) * max 1 Bnd ^ n)" 
    "finite (H \<union> C)" and
    id: "integer_hull (polyhedron A b) = convex_hull H + cone C" 
    by auto
  from xsol[unfolded id] have "H \<noteq> {}" unfolding set_plus_def by auto
  then obtain h where hH: "h \<in> H" by auto
  with set_in_convex_hull have "h \<in> convex_hull H" using HC by auto
  moreover have "0\<^sub>v n \<in> cone C" by (intro zero_in_cone)
  ultimately have "h + 0\<^sub>v n \<in> integer_hull (polyhedron A b)" unfolding id by auto
  also have "h + 0\<^sub>v n = h" using hH HC by auto
  also have "integer_hull (polyhedron A b) \<subseteq> convex_hull (polyhedron A b)" 
    unfolding integer_hull_def by (rule convex_hull_mono, auto)
  also have "convex_hull (polyhedron A b) = polyhedron A b" using A b
    using convex_convex_hull polyhedra_are_convex by blast
  finally have h: "h \<in> carrier_vec n" "A *\<^sub>v h \<le> b" unfolding polyhedron_def by auto
  show ?thesis
    by (intro exI[of _ h] conjI h, insert HC hH, auto)
qed

end
end