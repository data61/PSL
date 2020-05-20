section \<open>The Theorem of Farkas, Minkowsky and Weyl\<close>

text \<open>We prove the theorem of Farkas, Minkowsky and Weyl that a cone is finitely generated
  iff it is polyhedral. Moreover, we provide quantative bounds.\<close>

theory Farkas_Minkowsky_Weyl
  imports Fundamental_Theorem_Linear_Inequalities
begin

context gram_schmidt
begin

text \<open>We first prove the one direction of the theorem
  for the case that the span of the vectors is the full n-dimensional space.\<close>

lemma farkas_minkowsky_weyl_theorem_1_full_dim:
  assumes X: "X \<subseteq> carrier_vec n"
    and fin: "finite X"
    and span: "span X = carrier_vec n"
  shows "\<exists> nr A. A \<in> carrier_mat nr n \<and> cone X = polyhedral_cone A
  \<and> (X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<longrightarrow> A \<in> \<int>\<^sub>m \<inter> Bounded_mat (det_bound (n-1) Bnd))"
proof -
  define cond where "cond = (\<lambda> W. Suc (card W) = n \<and> lin_indpt W \<and> W \<subseteq> X)"
  {
    fix W
    assume "cond W"
    hence *: "finite W" "Suc (card W) = n" "lin_indpt W" "W \<subseteq> carrier_vec n" and WX: "W \<subseteq> X" unfolding cond_def
      using finite_subset[OF _ fin] X by auto
    note nv = normal_vector[OF *]
    hence "normal_vector W \<in> carrier_vec n" "\<And> w. w \<in> W \<Longrightarrow> normal_vector W \<bullet> w = 0"
      "normal_vector W \<noteq> 0\<^sub>v n" "X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<Longrightarrow> normal_vector W \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) Bnd)"
      using WX by blast+
  } note condD = this
  define Ns where "Ns = { normal_vector W | W. cond W \<and> (\<forall> w \<in> X. normal_vector W \<bullet> w \<ge> 0) }
       \<union> { - normal_vector W | W. cond W \<and> (\<forall> w \<in> X. (- normal_vector W) \<bullet> w \<ge> 0)}"
  have "Ns \<subseteq> normal_vector ` {W . W \<subseteq> X} \<union> (\<lambda> W. - normal_vector W) ` {W. W \<subseteq> X}" unfolding Ns_def cond_def by blast
  moreover have "finite \<dots>" using \<open>finite X\<close> by auto
  ultimately have "finite Ns" by (metis finite_subset)
  from finite_list[OF this] obtain ns where ns: "set ns = Ns" by auto
  have Ns: "Ns \<subseteq> carrier_vec n" unfolding Ns_def using condD by auto
  define A where "A = mat_of_rows n ns"
  define nr where "nr = length ns"
  have A: "- A \<in> carrier_mat nr n" unfolding A_def nr_def by auto
  show ?thesis
  proof (intro exI conjI impI, rule A)
    have not_conj: "\<not> (a \<and> b) \<longleftrightarrow> (a \<longrightarrow> \<not> b)" for a b by auto
    have id: "Ns = { nv . \<exists> W. W \<subseteq> X \<and> nv \<in> {normal_vector W, - normal_vector W} \<and>
             Suc (card W) = n \<and> lin_indpt W \<and> (\<forall>a\<^sub>i\<in>X. 0 \<le> nv \<bullet> a\<^sub>i)}"
      unfolding Ns_def cond_def by auto
    have "polyhedral_cone (- A) = { b. b \<in> carrier_vec n \<and> (- A) *\<^sub>v b \<le> 0\<^sub>v nr}" unfolding polyhedral_cone_def
      using A by auto
    also have "\<dots> = {b. b \<in> carrier_vec n \<and> (\<forall> i < nr. row (- A) i \<bullet> b \<le> 0)}"
      unfolding less_eq_vec_def using A by auto
    also have "\<dots> = {b. b \<in> carrier_vec n \<and> (\<forall> i < nr. - (ns ! i) \<bullet> b \<le> 0)}" using A Ns[folded ns]
      by (intro Collect_cong conj_cong refl all_cong arg_cong[of _ _ "\<lambda> x. x \<bullet> _ \<le> _"],
          force simp: A_def mat_of_rows_def nr_def set_conv_nth)
    also have "\<dots> = {b. b \<in> carrier_vec n \<and> (\<forall> n \<in> Ns. - n \<bullet> b \<le> 0)}"
      unfolding ns[symmetric] nr_def by (auto simp: set_conv_nth)
    also have "\<dots> = {b. b \<in> carrier_vec n \<and> (\<forall> n \<in> Ns. n \<bullet> b \<ge> 0)}"
      by (intro Collect_cong conj_cong refl ball_cong, insert Ns, auto)
    also have "\<dots> = cone X"
      unfolding fundamental_theorem_of_linear_inequalities_full_dim(2)[OF X fin span]
      by (intro Collect_cong conj_cong refl, unfold not_le[symmetric] not_ex not_conj not_not id, blast)
    finally show "cone X = polyhedral_cone (- A)" ..
    {
      assume XI: "X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
      {
        fix v
        assume "v \<in> set (rows (- A))"
        hence "-v \<in> set (rows A)" unfolding rows_def by auto
        hence "-v \<in> Ns" unfolding A_def using ns Ns by auto
        from this[unfolded Ns_def] obtain W where cW: "cond W"
          and v: "-v = normal_vector W \<or> v = normal_vector W" by auto
        from cW[unfolded cond_def] have WX: "W \<subseteq> X" by auto
        from v have v: "v = normal_vector W \<or> v = - normal_vector W"
          by (metis uminus_uminus_vec)
        from condD(4)[OF cW XI]
        have "normal_vector W \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) Bnd)" by auto
        hence "v \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) Bnd)" using v by auto
      }
      hence "set (rows (- A)) \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) Bnd)" by blast
      thus "- A \<in> \<int>\<^sub>m \<inter> Bounded_mat (det_bound (n - 1) Bnd)" by simp
    }
  qed
qed

text \<open>We next generalize the theorem to the case where X does not span the full space.
  To this end, we extend X by unit-vectors until the full space is spanned, and then
  add the normal-vectors of these unit-vectors which are orthogonal to span X as additional
  constraints to the resulting matrix.\<close>
lemma farkas_minkowsky_weyl_theorem_1:
  assumes X: "X \<subseteq> carrier_vec n"
    and finX: "finite X"
  shows "\<exists> nr A. A \<in> carrier_mat nr n \<and> cone X = polyhedral_cone A \<and>
    (X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<longrightarrow> A \<in> \<int>\<^sub>m \<inter> Bounded_mat (det_bound (n-1) (max 1 Bnd)))"
proof -
  from exists_lin_indpt_sublist[OF X]
  obtain Ls where lin_Ls: "lin_indpt_list Ls" and
    spanL: "span (set Ls) = span X" and LX: "set Ls \<subseteq> X" by auto
  define Ns where "Ns = normal_vectors Ls"
  define Bs where "Bs = basis_extension Ls"
  from basis_extension[OF lin_Ls, folded Bs_def]
  have BU: "set Bs \<subseteq> set (unit_vecs n)"
    and lin_Ls_Bs: "lin_indpt_list (Ls @ Bs)"
    and len_Ls_Bs: "length (Ls @ Bs) = n"
    by auto
  note nv = normal_vectors[OF lin_Ls, folded Ns_def]
  from nv(1-6) nv(7)[of Bnd]
  have N: "set Ns \<subseteq> carrier_vec n"
    and LN': "lin_indpt_list (Ls @ Ns)" "length (Ls @ Ns) = n"
    and ortho: "\<And> l w. l \<in> set Ls \<Longrightarrow> w \<in> set Ns \<Longrightarrow> w \<bullet> l = 0"
    and Ns_bnd: "set Ls \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd
     \<Longrightarrow> set Ns \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n-1) (max 1 Bnd))"
    by auto
  from lin_indpt_list_length_eq_n[OF LN']
  have spanLN: "span (set Ls \<union> set Ns) = carrier_vec n" by auto
  let ?Bnd = "Bounded_vec (det_bound (n-1) (max 1 Bnd))"
  let ?Bndm = "Bounded_mat (det_bound (n-1) (max 1 Bnd))"
  define Y where "Y = X \<union> set Bs"
  from lin_Ls_Bs[unfolded lin_indpt_list_def] have
    Ls: "set Ls \<subseteq> carrier_vec n" and
    Bs: "set Bs \<subseteq> carrier_vec n" and
    distLsBs: "distinct (Ls @ Bs)" and
    lin': "lin_indpt (set (Ls @ Bs))" by auto
  have LN: "set Ls \<inter> set Ns = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where xX: "x \<in> set Ls" and xW: "x \<in> set Ns" by auto
    from ortho[OF xX xW] have "x \<bullet> x = 0" by auto
    hence "sq_norm x = 0" by (auto simp: sq_norm_vec_as_cscalar_prod)
    with xX LX X have "x = 0\<^sub>v n" by auto
    with vs_zero_lin_dep[OF _ lin'] Ls Bs xX show False by auto
  qed
  have Y: "Y \<subseteq> carrier_vec n" using X Bs unfolding Y_def by auto
  have CLB: "carrier_vec n = span (set (Ls @ Bs))"
    using lin_Ls_Bs len_Ls_Bs lin_indpt_list_length_eq_n by blast
  also have "\<dots> \<subseteq> span Y"
    by (rule span_is_monotone, insert LX, auto simp: Y_def)
  finally have span: "span Y = carrier_vec n" using Y by auto
  have finY: "finite Y" using finX unfolding Y_def by auto
  from farkas_minkowsky_weyl_theorem_1_full_dim[OF Y finY span]
  obtain A nr where A: "A \<in> carrier_mat nr n" and YA: "cone Y = polyhedral_cone A"
    and Y_Ints: "Y \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (max 1 Bnd) \<Longrightarrow> A \<in> \<int>\<^sub>m \<inter> ?Bndm" by blast
  have fin: "finite ({row A i | i. i < nr} \<union> set Ns \<union> uminus ` set Ns)" by auto
  from finite_list[OF this] obtain rs where rs_def: "set rs = {row A i |i. i < nr} \<union> set Ns \<union> uminus ` set Ns" by auto
  from A N have rs: "set rs \<subseteq> carrier_vec n" unfolding rs_def by auto
  let ?m = "length rs"
  define B where "B = mat_of_rows n rs"
  have B: "B \<in> carrier_mat ?m n" unfolding B_def by auto
  show ?thesis
  proof (intro exI conjI impI, rule B)
    have id: "(\<forall>r\<in>{rs ! i |i. i < ?m}. P r) = (\<forall> r < ?m. P (rs ! r))" for P by auto
    have "polyhedral_cone B = { x \<in> carrier_vec n. B *\<^sub>v x \<le> 0\<^sub>v ?m}" unfolding polyhedral_cone_def
      using B by auto
    also have "\<dots> = { x \<in> carrier_vec n. \<forall> i < ?m. row B i \<bullet> x \<le> 0}"
      unfolding less_eq_vec_def using B by auto
    also have "\<dots> = { x \<in> carrier_vec n. \<forall> r \<in> set rs. r \<bullet> x \<le> 0}" using rs unfolding set_conv_nth id
      by (intro Collect_cong conj_cong refl all_cong arg_cong[of _ _ "\<lambda> x. x \<bullet> _ \<le> 0"], auto simp: B_def)
    also have "\<dots> = {x \<in> carrier_vec n. \<forall> i < nr. row A i \<bullet> x \<le> 0}
           \<inter> {x \<in> carrier_vec n. \<forall> w \<in> set Ns \<union> uminus ` set Ns. w \<bullet> x \<le> 0}"
      unfolding rs_def by blast
    also have "{x \<in> carrier_vec n. \<forall> i < nr. row A i \<bullet> x \<le> 0} = polyhedral_cone A"
      unfolding polyhedral_cone_def using A by (auto simp: less_eq_vec_def)
    also have "\<dots> = cone Y" unfolding YA ..
    also have "{x \<in> carrier_vec n. \<forall> w \<in> set Ns \<union> uminus ` set Ns. w \<bullet> x \<le> 0}
      = {x \<in> carrier_vec n. \<forall> w \<in> set Ns. w \<bullet> x = 0}"
      (is "?l = ?r")
    proof
      show "?r \<subseteq> ?l" using N by auto
      {
        fix x w
        assume "x \<in> ?l" "w \<in> set Ns"
        with N have x: "x \<in> carrier_vec n" and w: "w \<in> carrier_vec n"
          and one: "w \<bullet> x \<le> 0" and two: "(-w) \<bullet> x \<le> 0" by auto
        from two have "w \<bullet> x \<ge> 0"
          by (subst (asm) scalar_prod_uminus_left, insert w x, auto)
        with one have "w \<bullet> x = 0" by auto
      }
      thus "?l \<subseteq> ?r" by blast
    qed
    finally have "polyhedral_cone B = cone Y \<inter> {x \<in> carrier_vec n. \<forall>w\<in>set Ns. w \<bullet> x = 0}" .
    also have "\<dots> = cone X" unfolding Y_def
      by (rule orthogonal_cone(1)[OF X N finX spanLN ortho refl spanL LX lin_Ls_Bs len_Ls_Bs])
    finally show "cone X = polyhedral_cone B" ..
    assume X_I: "X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    with LX have "set Ls \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd" by auto
    from Ns_bnd[OF this] have N_I_Bnd: "set Ns \<subseteq> \<int>\<^sub>v \<inter> ?Bnd" by auto
    from lin_Ls_Bs have linLs: "lin_indpt_list Ls" unfolding lin_indpt_list_def
      using subset_li_is_li[of _ "set Ls"] by auto
    from X_I LX have L_I: "set Ls \<subseteq> \<int>\<^sub>v" by auto
    have Y_I: "Y \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (max 1 Bnd)" unfolding Y_def using X_I BU
        Bounded_vec_mono[of Bnd "max 1 Bnd"] by (auto simp: unit_vecs_def Ints_vec_def)
    from Y_Ints[OF Y_I]
    have A_I_Bnd: "set (rows A) \<subseteq> \<int>\<^sub>v \<inter> ?Bnd" by auto
    have "set (rows B) = set (rows (mat_of_rows n rs))" unfolding B_def by auto
    also have "\<dots> = set rs" using rs by auto
    also have "\<dots> = set (rows A) \<union> set Ns \<union> uminus ` set Ns" unfolding rs_def rows_def using A by auto
    also have "\<dots> \<subseteq> \<int>\<^sub>v \<inter> ?Bnd" using A_I_Bnd N_I_Bnd by auto
    finally show "B \<in> \<int>\<^sub>m \<inter> ?Bndm" by simp
  qed
qed

text \<open>Now for the other direction.\<close>

lemma farkas_minkowsky_weyl_theorem_2:
  assumes A: "A \<in> carrier_mat nr n"
  shows "\<exists> X. X \<subseteq> carrier_vec n \<and> finite X \<and> polyhedral_cone A = cone X
    \<and> (A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd \<longrightarrow> X \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n-1) (max 1 Bnd)))"
proof -
  let ?rows_A = "{row A i | i. i < nr}"
  let ?Bnd = "Bounded_vec (det_bound (n-1) (max 1 Bnd))"
  have rows_A_n: "?rows_A \<subseteq> carrier_vec n" using row_carrier_vec A by auto
  hence "\<exists> mr B. B \<in> carrier_mat mr n \<and> cone ?rows_A = polyhedral_cone B
    \<and> (?rows_A \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<longrightarrow> set (rows B) \<subseteq> \<int>\<^sub>v \<inter> ?Bnd)"
    using farkas_minkowsky_weyl_theorem_1[of ?rows_A] by auto
  then obtain mr B
    where mr: "B \<in> carrier_mat mr n" and B: "cone ?rows_A = polyhedral_cone B"
      and Bnd: "?rows_A \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<Longrightarrow> set (rows B) \<subseteq> \<int>\<^sub>v \<inter> ?Bnd"
    by blast
  let ?rows_B = "{row B i | i. i < mr}"
  have rows_B: "?rows_B \<subseteq> carrier_vec n" using mr by auto
  have "cone ?rows_B = polyhedral_cone A"
  proof
    have "?rows_B \<subseteq> polyhedral_cone A"
    proof
      fix r
      assume "r \<in> ?rows_B"
      then obtain j where r: "r = row B j" and j: "j < mr" by auto
      then have rn: "r \<in> carrier_vec n" using mr row_carrier by auto
      moreover have "A *\<^sub>v r \<le> 0\<^sub>v nr" unfolding less_eq_vec_def
      proof (standard, unfold index_zero_vec)
        show "dim_vec (A *\<^sub>v r) = nr" using A by auto
      next
        show "\<forall>i< nr. (A *\<^sub>v r) $ i \<le> 0\<^sub>v nr $ i"
        proof (standard, rule impI)
          fix i
          assume i: "i < nr"
          then have "row A i \<in> ?rows_A" by auto
          then have "row A i \<in> cone ?rows_A"
            using set_in_cone rows_A_n by blast
          then have "row A i \<in> polyhedral_cone B" using B by auto
          then have Br: "B *\<^sub>v (row A i) \<le> 0\<^sub>v mr"
            unfolding polyhedral_cone_def using rows_A_n mr by auto

          then have "(A *\<^sub>v r) $ i = (row A i) \<bullet> r" using A i index_mult_mat_vec by auto
          also have "\<dots> = r \<bullet> (row A i)"
            using comm_scalar_prod[OF _ rn] row_carrier A by auto
          also have "\<dots> = (row B j) \<bullet> (row A i)" using r by auto
          also have "\<dots> = (B *\<^sub>v (row A i)) $ j" using index_mult_mat_vec mr j by auto
          also have "\<dots> \<le> 0" using Br j unfolding less_eq_vec_def by auto
          also have "\<dots> = 0\<^sub>v nr $ i" using i by auto
          finally show "(A *\<^sub>v r) $ i \<le> 0\<^sub>v nr $ i" by auto
        qed
      qed
      then show "r \<in> polyhedral_cone A"
        unfolding polyhedral_cone_def
        using A rn by auto
    qed
    then show "cone ?rows_B \<subseteq> polyhedral_cone A"
      using cone_in_polyhedral_cone A by auto

  next

    show "polyhedral_cone A \<subseteq> cone ?rows_B"
    proof (rule ccontr)
      assume "\<not> polyhedral_cone A \<subseteq> cone ?rows_B"
      then obtain y where yA: "y \<in> polyhedral_cone A"
        and yB: "y \<notin> cone ?rows_B" by auto
      then have yn: "y \<in> carrier_vec n" unfolding polyhedral_cone_def by auto
      have finRB: "finite ?rows_B" by auto
      from farkas_minkowsky_weyl_theorem_1[OF rows_B finRB]
      obtain nr' A' where A': "A' \<in> carrier_mat nr' n" and cone: "cone ?rows_B = polyhedral_cone A'"
        by blast
      from yB[unfolded cone polyhedral_cone_def] yn A'
      have "\<not> (A' *\<^sub>v y \<le> 0\<^sub>v nr')" by auto
      then obtain i where i: "i < nr'" and "row A' i \<bullet> y > 0"
        unfolding less_eq_vec_def using A' yn by auto
      define w where "w = row A' i"
      have w: "w \<in> carrier_vec n" using i A' yn unfolding w_def by auto
      from \<open>row A' i \<bullet> y > 0\<close> comm_scalar_prod[OF w yn] have wy: "w \<bullet> y > 0" "y \<bullet> w > 0" unfolding w_def by auto
      {
        fix b
        assume "b \<in> ?rows_B"
        hence "b \<in> cone ?rows_B" using set_in_cone[OF rows_B] by auto
        from this[unfolded cone polyhedral_cone_def] A'
        have b: "b \<in> carrier_vec n" and "A' *\<^sub>v b \<le> 0\<^sub>v nr'" by auto
        from this(2)[unfolded less_eq_vec_def, THEN conjunct2, rule_format, of i]
        have "w \<bullet> b \<le> 0" unfolding w_def using i A' by auto
        hence "b \<bullet> w \<le> 0" using comm_scalar_prod[OF b w] by auto
      }
      hence wA: "w \<in> cone ?rows_A" unfolding B polyhedral_cone_def using mr w
        by (auto simp: less_eq_vec_def)
      from wy have yw: "-y \<bullet> w < 0"
        by (subst scalar_prod_uminus_left, insert yn w, auto)
      have "?rows_A \<subseteq> carrier_vec n" "finite ?rows_A" using assms by auto
      from fundamental_theorem_of_linear_inequalities_A_imp_D[OF this wA, unfolded not_ex,
          rule_format, of "-y" ] yn yw
      obtain i where i: "i < nr" and "- y \<bullet> row A i < 0" by auto
      hence "y \<bullet> row A i > 0" by (subst (asm) scalar_prod_uminus_left, insert i assms yn, auto)
      hence "row A i \<bullet> y > 0" using comm_scalar_prod[OF _ yn, of "row A i"] i assms yn by auto
      with yA show False unfolding polyhedral_cone_def less_eq_vec_def using i assms by auto
    qed
  qed
  moreover have "?rows_B \<subseteq> carrier_vec n"
    using row_carrier_vec mr by auto
  moreover have "finite ?rows_B" by auto
  moreover {
    have rA: "set (rows A) = ?rows_A" using A unfolding rows_def by auto
    have rB: "set (rows B) = ?rows_B" using mr unfolding rows_def by auto
    assume "A \<in> \<int>\<^sub>m \<inter> Bounded_mat Bnd"
    hence "set (rows A) \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd" by simp
    from Bnd[OF this[unfolded rA]]
    have "?rows_B \<subseteq> \<int>\<^sub>v \<inter> ?Bnd" unfolding rA rB .
  }
  ultimately show ?thesis by blast
qed

lemma farkas_minkowsky_weyl_theorem:
  "(\<exists> X. X \<subseteq> carrier_vec n \<and> finite X \<and> P = cone X)
  \<longleftrightarrow> (\<exists> A nr. A \<in> carrier_mat nr n \<and> P = polyhedral_cone A)"
  using farkas_minkowsky_weyl_theorem_1 farkas_minkowsky_weyl_theorem_2 by metis
end
end