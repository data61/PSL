section \<open>Mixed Integer Solutions\<close>

text \<open>We prove that if an integral system of linear inequalities
$Ax \leq b \wedge A'x < b'$ has a (mixed)integer solution, there there is also
a small (mixed)integer solution, where the numbers are bounded by
$(n+1)! \cdot m^n$ where $n$ is the number of variables and $m$ is a bound on
the absolute values of numbers occurring in $A,A',b,b'$.\<close>

theory Mixed_Integer_Solutions
  imports Decomposition_Theorem
begin


definition less_vec :: "'a vec \<Rightarrow> ('a :: ord) vec \<Rightarrow> bool" (infix "<\<^sub>v" 50) where
  "v <\<^sub>v w = (dim_vec v = dim_vec w \<and> (\<forall> i < dim_vec w. v $ i < w $ i))"

lemma less_vecD: assumes "v <\<^sub>v w" and "w \<in> carrier_vec n"
  shows "i < n \<Longrightarrow> v $ i < w $ i"
  using assms unfolding less_vec_def by auto

lemma less_vecI: assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  "\<And> i. i < n \<Longrightarrow> v $ i < w $ i"
shows "v <\<^sub>v w"
  using assms unfolding less_vec_def by auto

lemma less_vec_lesseq_vec: "v <\<^sub>v (w :: 'a :: preorder vec) \<Longrightarrow> v \<le> w"
  unfolding less_vec_def less_eq_vec_def
  by (auto simp: less_le_not_le)

lemma floor_less: "x \<notin> \<int> \<Longrightarrow> of_int \<lfloor>x\<rfloor> < x"
  using le_less by fastforce

lemma floor_of_int_eq[simp]: "x \<in> \<int> \<Longrightarrow> of_int \<lfloor>x\<rfloor> = x"
  by (metis Ints_cases of_int_floor_cancel)


locale gram_schmidt_floor = gram_schmidt n f_ty
  for n :: nat and f_ty :: "'a :: {floor_ceiling,
    trivial_conjugatable_linordered_field} itself"
begin

lemma small_mixed_integer_solution_main: fixes A\<^sub>1 :: "'a mat"
  assumes A1: "A\<^sub>1 \<in> carrier_mat nr\<^sub>1 n"
    and A2: "A\<^sub>2 \<in> carrier_mat nr\<^sub>2 n"
    and b1: "b\<^sub>1 \<in> carrier_vec nr\<^sub>1"
    and b2: "b\<^sub>2 \<in> carrier_vec nr\<^sub>2"
    and A1Bnd: "A\<^sub>1 \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    and b1Bnd: "b\<^sub>1 \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    and A2Bnd: "A\<^sub>2 \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    and b2Bnd: "b\<^sub>2 \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    and x: "x \<in> carrier_vec n"
    and xI: "x \<in> indexed_Ints_vec I"
    and sol_nonstrict: "A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1"
    and sol_strict: "A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2"
  shows "\<exists> x.
  x \<in> carrier_vec n \<and>
  x \<in> indexed_Ints_vec I \<and>
  A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1 \<and>
  A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2 \<and>
  x \<in> Bounded_vec (fact (n+1) * (max 1 Bnd)^n)"
proof -
  define B where "B = det_bound n (max 1 Bnd)"
  define A where "A = A\<^sub>1 @\<^sub>r A\<^sub>2"
  define b where "b = b\<^sub>1 @\<^sub>v b\<^sub>2"
  define nr where "nr = nr\<^sub>1 + nr\<^sub>2"
  have B0: "B \<ge> 0" unfolding B_def det_bound_def by auto
  note defs = A_def b_def nr_def
  from A1 A2 have A: "A \<in> carrier_mat nr n" unfolding defs by auto
  from b1 b2 have b: "b \<in> carrier_vec nr" unfolding defs by auto
  from A1Bnd A2Bnd A1 A2 have ABnd: "A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd" unfolding defs
    by (auto simp: Ints_mat_elements_mat Bounded_mat_elements_mat elements_mat_append_rows)
  from b1Bnd b2Bnd b1 b2 have bBnd: "b \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd" unfolding defs
    by (auto simp: Ints_vec_vec_set Bounded_vec_vec_set)
  from decomposition_theorem_polyhedra_1[OF A b refl, of Bnd] ABnd bBnd
  obtain Y Z where Z: "Z \<subseteq> carrier_vec n"
    and finX: "finite Z"
    and Y: "Y \<subseteq> carrier_vec n"
    and finY: "finite Y"
    and poly: "polyhedron A b = convex_hull Y + cone Z"
    and ZBnd: "Z \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec B"
    and YBnd: "Y \<subseteq> Bounded_vec B" unfolding B_def by blast
  let ?P = "{x \<in> carrier_vec n. A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1 \<and> A\<^sub>2 *\<^sub>v x \<le> b\<^sub>2}"
  let ?L = "?P \<inter> {x. A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2} \<inter> indexed_Ints_vec I"
  have "polyhedron A b = {x \<in> carrier_vec n. A *\<^sub>v x \<le> b}" unfolding polyhedron_def by auto
  also have "\<dots> = ?P" unfolding defs
    by (intro Collect_cong conj_cong refl append_rows_le[OF A1 A2 b1])
  finally have poly: "?P = convex_hull Y + cone Z" unfolding poly ..
  have "x \<in> ?P" using x sol_nonstrict less_vec_lesseq_vec[OF sol_strict] by blast
  note sol = this[unfolded poly]
  from set_plus_elim[OF sol] obtain y z where xyz: "x = y + z" and
    yY: "y \<in> convex_hull Y" and zZ: "z \<in> cone Z" by auto
  from convex_hull_carrier[OF Y] yY have y: "y \<in> carrier_vec n" by auto
  from Caratheodory_theorem[OF Z] zZ
  obtain C where zC: "z \<in> finite_cone C" and CZ: "C \<subseteq> Z" and lin: "lin_indpt C" by auto
  from subset_trans[OF CZ Z] lin have card: "card C \<le> n"
    using dim_is_n li_le_dim(2) by auto
  from finite_subset[OF CZ finX] have finC: "finite C" .
  from zC[unfolded finite_cone_def nonneg_lincomb_def] finC obtain a
    where za: "z = lincomb a C" and nonneg: "\<And> u. u \<in> C \<Longrightarrow> a u \<ge> 0" by auto
  from CZ Z have C: "C \<subseteq> carrier_vec n" by auto
  have z: "z \<in> carrier_vec n" using C unfolding za by auto
  have yB: "y \<in> Bounded_vec B" using yY convex_hull_bound[OF YBnd Y] by auto
  {
    fix D
    assume DC: "D \<subseteq> C"
    from finite_subset[OF this finC] have "finite D" .
    hence "\<exists> a. y + lincomb a C \<in> ?L \<and> (\<forall> c \<in> C. a c \<ge> 0) \<and> (\<forall> c \<in> D. a c \<le> 1)"
      using DC
    proof (induct D)
      case empty
      show ?case by (intro exI[of _ a], fold za xyz, insert sol_strict x xI nonneg \<open>x \<in> ?P\<close>, auto)
    next
      case (insert c D)
      then obtain a where sol: "y + lincomb a C \<in> ?L"
        and a: "(\<forall> c \<in> C. a c \<ge> 0)" and D: "(\<forall> c \<in> D. a c \<le> 1)" by auto
      from insert(4) C have c: "c \<in> carrier_vec n" and cC: "c \<in> C" by auto
      show ?case
      proof (cases "a c > 1")
        case False
        thus ?thesis by (intro exI[of _ a], insert sol a D, auto)
      next
        case True (* this is the core reasoning step where a\<^sub>c is large *)
        let ?z = "\<lambda> d. lincomb a C - d \<cdot>\<^sub>v c"
        let ?x = "\<lambda> d. y + ?z d"
        {
          fix d
          have lin: "lincomb a (C - {c}) \<in> carrier_vec n" using C by auto
          have id: "?z d = lincomb (\<lambda> e. if e = c then (a c - d) else a e) C"
            unfolding lincomb_del2[OF finC C TrueI cC]
            by (subst (2) lincomb_cong[OF refl, of _ _ a], insert C c lin, auto simp: diff_smult_distrib_vec)
          {
            assume le: "d \<le> a c"
            have "?z d \<in> finite_cone C"
            proof -
              have "\<forall>f\<in>C. 0 \<le> (\<lambda>e. if e = c then a c - d else a e) f" using le a finC by simp
              then show ?thesis unfolding id using le a finC
                by (simp add: C lincomb_in_finite_cone)
            qed
            hence "?z d \<in> cone Z" using CZ
              using finC local.cone_def by blast
            hence "?x d \<in> ?P" unfolding poly
              by (intro set_plus_intro[OF yY], auto)
          } note sol = this
          {
            fix w :: "'a vec"
            assume w: "w \<in> carrier_vec n"
            have "w \<bullet> (?x d) = w \<bullet> y + w \<bullet> lincomb a C - d * (w \<bullet> c)"
              by (subst scalar_prod_add_distrib[OF w y], (insert C c, force),
                  subst scalar_prod_minus_distrib[OF w], insert w c C, auto)
          } note scalar = this
          note id sol scalar
        } note generic = this
        let ?fl = "(of_int (floor (a c)) :: 'a)"
        define p where "p = (if ?fl  = a c then a c - 1 else ?fl)"
        have p_lt_ac: "p < a c" unfolding p_def
          using floor_less floor_of_int_eq by auto
        have p1_ge_ac: "p + 1 \<ge> a c" unfolding p_def
          using floor_correct le_less by auto
        have p1: "p \<ge> 1" using True unfolding p_def by auto
        define a' where "a' = (\<lambda>e. if e = c then a c - p else a e)"
        have lin_id: "lincomb a' C = lincomb a C - p \<cdot>\<^sub>v c" unfolding a'_def using id
          by (simp add: generic(1))
        hence 1: "y + lincomb a' C \<in> {x \<in> carrier_vec n. A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1 \<and> A\<^sub>2 *\<^sub>v x \<le> b\<^sub>2}"
          using p_lt_ac generic(2)[of p] by auto
        have pInt: "p \<in> \<int>" unfolding p_def using sol by auto
        have "C \<subseteq> indexed_Ints_vec I" using CZ ZBnd
          using indexed_Ints_vec_subset by force
        hence "c \<in> indexed_Ints_vec I" using cC by auto
        hence pvindInts: "p \<cdot>\<^sub>v c \<in> indexed_Ints_vec I" unfolding indexed_Ints_vec_def using pInt by simp
        have prod: "A\<^sub>2 *\<^sub>v (?x b) \<in> carrier_vec nr\<^sub>2" for b using A2 C c y by auto
        have 2: "y + lincomb a' C \<in> {x. A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2}" unfolding lin_id
        proof (intro less_vecI[OF prod b2] CollectI)
          fix i
          assume i: "i < nr\<^sub>2"
          from sol have "A\<^sub>2 *\<^sub>v (?x 0) <\<^sub>v b\<^sub>2" using y C c by auto
          from less_vecD[OF this b2 i]
          have lt: "row A\<^sub>2 i \<bullet> ?x 0 < b\<^sub>2 $ i" using A2 i by auto
          from generic(2)[of "a c"] i A2
          have le: "row A\<^sub>2 i \<bullet> ?x (a c) \<le> b\<^sub>2 $ i"
            unfolding less_eq_vec_def by auto
          from A2 i have A2icarr: "row A\<^sub>2 i \<in> carrier_vec n" by auto
          have "row A\<^sub>2 i \<bullet> ?x p < b\<^sub>2 $ i"
          proof -
            define lhs where "lhs = row A\<^sub>2 i \<bullet> y + row A\<^sub>2 i \<bullet> lincomb a C - b\<^sub>2 $ i"
            define mult where "mult = row A\<^sub>2 i \<bullet> c"
            have le2: "lhs \<le> a c * mult" using le unfolding generic(3)[OF A2icarr] lhs_def mult_def by auto
            have lt2: "lhs < 0 * mult" using lt unfolding generic(3)[OF A2icarr] lhs_def by auto
            from le2 lt2 have "lhs < p * mult" using p_lt_ac p1 True
              by (smt dual_order.strict_trans linorder_neqE_linordered_idom
                  mult_less_cancel_right not_less zero_less_one_class.zero_less_one)
            then show ?thesis unfolding generic(3)[OF A2icarr] lhs_def mult_def by auto
          qed
          thus "(A\<^sub>2 *\<^sub>v ?x p) $ i < b\<^sub>2 $ i" using i A2 by auto
        qed
        have "y + lincomb a' C = y + lincomb a C - p \<cdot>\<^sub>v c"
          by (subst lin_id, insert y C c, auto simp: add_diff_eq_vec)
        also have "\<dots> \<in> indexed_Ints_vec I" using sol
          by(intro diff_indexed_Ints_vec[OF _ _ _ pvindInts, of _ n ], insert c C, auto)
        finally have 3: "y + lincomb a' C \<in> indexed_Ints_vec I" by auto
        have 4: "\<forall>c\<in>C. 0 \<le> a' c" unfolding a'_def p_def using p_lt_ac a by auto
        have 5: "\<forall>c\<in>insert c D. a' c \<le> 1" unfolding a'_def using p1_ge_ac D p_def by auto
        show ?thesis
          by (intro exI[of _ a'], intro conjI IntI 1 2 3 4 5)
      qed
    qed
  }
  from this[of C] obtain a where
    sol: "y + lincomb a C \<in> ?L" and bnds: "(\<forall> c \<in> C. a c \<ge> 0)" "(\<forall> c \<in> C. a c \<le> 1)" by auto
  show ?thesis
  proof (intro exI[of _ "y + lincomb a C"] conjI)
    from ZBnd CZ have BndC: "C \<subseteq> Bounded_vec B" and IntC: "C \<subseteq> \<int>\<^sub>v" by auto
    have "lincomb a C \<in> Bounded_vec (of_nat n * B)"
      using lincomb_card_bound[OF BndC C B0 _ card] bnds by auto
    from sum_in_Bounded_vecI[OF yB this y] C
    have "y + lincomb a C \<in> Bounded_vec (B + of_nat n * B)" by auto
    also have "B + of_nat n * B = of_nat (n+1) * B" by (auto simp: field_simps)
    also have "\<dots> = fact (n + 1) * (max 1 Bnd)^n" unfolding B_def det_bound_def by simp
    finally show "y + lincomb a C \<in> Bounded_vec (fact (n + 1) * max 1 Bnd ^ n)" by auto
  qed (insert sol, auto)
qed

text \<open>We get rid of the max-1 operation, by showing that a smaller value of Bnd 
  can only occur in very special cases where the theorem is trivially satisfied.\<close>

lemma small_mixed_integer_solution: fixes A\<^sub>1 :: "'a mat"
  assumes A1: "A\<^sub>1 \<in> carrier_mat nr\<^sub>1 n"
    and A2: "A\<^sub>2 \<in> carrier_mat nr\<^sub>2 n"
    and b1: "b\<^sub>1 \<in> carrier_vec nr\<^sub>1"
    and b2: "b\<^sub>2 \<in> carrier_vec nr\<^sub>2"
    and A1Bnd: "A\<^sub>1 \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    and b1Bnd: "b\<^sub>1 \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    and A2Bnd: "A\<^sub>2 \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    and b2Bnd: "b\<^sub>2 \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    and x: "x \<in> carrier_vec n"
    and xI: "x \<in> indexed_Ints_vec I"
    and sol_nonstrict: "A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1"
    and sol_strict: "A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2"
    and non_degenerate: "nr\<^sub>1 \<noteq> 0 \<or> nr\<^sub>2 \<noteq> 0 \<or> Bnd \<ge> 0" 
  shows "\<exists> x.
  x \<in> carrier_vec n \<and>
  x \<in> indexed_Ints_vec I \<and>
  A\<^sub>1 *\<^sub>v x \<le> b\<^sub>1 \<and>
  A\<^sub>2 *\<^sub>v x <\<^sub>v b\<^sub>2 \<and>
  x \<in> Bounded_vec (fact (n+1) * Bnd^n)"
proof (cases "Bnd \<ge> 1")
  case True
  hence "max 1 Bnd = Bnd" by auto
  with small_mixed_integer_solution_main[OF assms(1-12)] True show ?thesis by auto
next
  case trivial: False
  show ?thesis 
  proof (cases "n = 0")
    case True
    with x have "x \<in> Bounded_vec (fact (n+1) * Bnd^n)" unfolding Bounded_vec_def by auto
    with xI x sol_nonstrict sol_strict show ?thesis by blast
  next
    case n: False
    {
      fix A nr
      assume A: "A \<in> carrier_mat nr n" and Bnd: "A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
      {
        fix i j
        assume "i < nr" "j < n" 
        with Bnd A have *: "A $$ (i,j) \<in> \<int>" "abs (A $$ (i,j)) \<le> Bnd" 
          unfolding Bounded_mat_def Ints_mat_def by auto
        with trivial have "Bnd \<ge> 0" "A $$ (i,j) = 0" by (auto simp: Ints_nonzero_abs_less1)
      } note main = this      
      have A0: "A = 0\<^sub>m nr n" 
        by (intro eq_matI, insert main A, auto)
      have "nr \<noteq> 0 \<Longrightarrow> Bnd \<ge> 0" using main[of 0 0] n by auto
      note A0 this
    } note main = this
    from main[OF A1 A1Bnd] have A1: "A\<^sub>1 = 0\<^sub>m nr\<^sub>1 n" and nr1: "nr\<^sub>1 \<noteq> 0 \<Longrightarrow> Bnd \<ge> 0" 
      by auto
    from main[OF A2 A2Bnd] have A2: "A\<^sub>2 = 0\<^sub>m nr\<^sub>2 n" and nr2: "nr\<^sub>2 \<noteq> 0 \<Longrightarrow> Bnd \<ge> 0" 
      by auto
    let ?x = "0\<^sub>v n" 
    show ?thesis
    proof (intro exI[of _ ?x] conjI)
      show "A\<^sub>1 *\<^sub>v ?x \<le> b\<^sub>1" using sol_nonstrict x unfolding A1 by auto
      show "A\<^sub>2 *\<^sub>v ?x <\<^sub>v b\<^sub>2" using sol_strict x unfolding A2 by auto
      show "?x \<in> carrier_vec n" by auto
      show "?x \<in> indexed_Ints_vec I" unfolding indexed_Ints_vec_def by auto
      from nr1 nr2 non_degenerate have Bnd: "Bnd \<ge> 0" by auto
      hence "fact (n + 1) * Bnd ^ n \<ge> 0" by simp
      thus "?x \<in> Bounded_vec (fact (n + 1) * Bnd ^ n)" by (auto simp: Bounded_vec_def)
    qed
  qed
qed      

corollary small_integer_solution_nonstrict: fixes A :: "'a mat"
  assumes A: "A \<in> carrier_mat nr n"
    and b: "b \<in> carrier_vec nr"
    and ABnd: "A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    and bBnd: "b \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    and x: "x \<in> carrier_vec n"
    and xI: "x \<in> \<int>\<^sub>v"
    and sol: "A *\<^sub>v x \<le> b"
    and non_degenerate: "nr \<noteq> 0 \<or> Bnd \<ge> 0" 
  shows "\<exists> y.
  y \<in> carrier_vec n \<and>
  y \<in> \<int>\<^sub>v \<and>
  A *\<^sub>v y \<le> b \<and>
  y \<in> Bounded_vec (fact (n+1) * Bnd^n)"
proof -
  let ?A2 = "0\<^sub>m 0 n :: 'a mat"
  let ?b2 = "0\<^sub>v 0 :: 'a vec"
  from non_degenerate have degen: "nr \<noteq> 0 \<or> (0 :: nat) \<noteq> 0 \<or> Bnd \<ge> 0" by auto
  have "\<exists>y. y \<in> carrier_vec n \<and> y \<in> \<int>\<^sub>v \<and> A *\<^sub>v y \<le> b \<and> ?A2 *\<^sub>v y <\<^sub>v ?b2
  \<and> y \<in> Bounded_vec (fact (n + 1) * Bnd ^ n)"
    by (rule small_mixed_integer_solution[OF A _ b _ ABnd bBnd _ _ x _ sol, of ?A2 0 ?b2 UNIV,
          folded indexed_Ints_vec_UNIV], insert xI degen,
        auto simp: Ints_vec_def Ints_mat_def Bounded_mat_def Bounded_vec_def less_vec_def)
  thus ?thesis by blast
qed

end
end