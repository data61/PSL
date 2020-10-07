section \<open>Normal Vectors\<close>

text \<open>We provide a function for the normal vector of a half-space (given as n-1 linearly
  independent vectors).
  We further provide a function that returns a list of normal vectors that span the
  orthogonal complement of some subspace of $R^n$.
  Bounds for all normal vectors are provided.\<close>

theory Normal_Vector
  imports
    Integral_Bounded_Vectors
    Basis_Extension
begin

context gram_schmidt
begin
  (* TODO move *)
lemma ortho_sum_in_span:
  assumes W: "W \<subseteq> carrier_vec n"
    and X: "X \<subseteq> carrier_vec n"
    and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> X \<Longrightarrow> x \<bullet> w = 0"
    and inspan: "lincomb l1 X + lincomb l2 W \<in> span X"
  shows "lincomb l2 W = 0\<^sub>v n"
proof (rule ccontr)
  let ?v = "lincomb l2 W"
  have vcarr: "?v \<in> carrier_vec n" using W by auto
  have vspan: "?v \<in> span W" using W by auto
  assume "\<not>?thesis"
  from this have vnz: "?v \<noteq> 0\<^sub>v n" by auto
  let ?x = "lincomb l1 X"
  have xcarr: "?x \<in> carrier_vec n" using X by auto
  have xspan: "?x \<in> span X" using X xcarr by auto
  have "0 \<noteq> sq_norm ?v" using vnz vcarr by simp
  also have "sq_norm ?v = 0 + ?v \<bullet> ?v" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "\<dots> = ?x \<bullet> ?v + ?v \<bullet> ?v"
    by (subst (2) ortho_span_span[OF X W ortho], insert X W, auto)
  also have "\<dots> = (?x + ?v ) \<bullet> ?v" using xcarr vcarr
    using add_scalar_prod_distrib by force
  also have "\<dots> = 0"
    by (rule ortho_span_span[OF X W ortho inspan vspan])
  finally show False by simp
qed

(* TODO move *)
lemma ortho_lin_indpt: assumes W: "W \<subseteq> carrier_vec n"
  and X: "X \<subseteq> carrier_vec n"
  and ortho: "\<And> w x. w \<in> W \<Longrightarrow> x \<in> X \<Longrightarrow> x \<bullet> w = 0"
  and linW: "lin_indpt W"
  and linX: "lin_indpt X"
shows "lin_indpt (W \<union> X)"
proof (rule ccontr)
  assume "\<not>?thesis"
  from this obtain c where zerocomb:"lincomb c (W \<union> X) = 0\<^sub>v n"
    and notallz: "\<exists>v \<in> (W \<union> X). c v \<noteq> 0"
    using assms fin_dim fin_dim_li_fin finite_lin_indpt2 infinite_Un le_sup_iff
    by metis
  have zero_nin_W: "0\<^sub>v n \<notin> W" using assms by (metis vs_zero_lin_dep)
  have WXinters: "W \<inter> X = {}"
  proof (rule ccontr)
    assume "\<not>?thesis"
    from this obtain v where v: "v\<in> W \<inter> X" by auto
    hence "v\<bullet>v=0" using ortho by auto
    moreover have "v \<in> carrier_vec n" using assms v by auto
    ultimately have "v=0\<^sub>v n" using sq_norm_vec_as_cscalar_prod[of v] by auto
    then show False using zero_nin_W v by auto
  qed
  have finX: "finite X" using X linX by (simp add: fin_dim_li_fin)
  have finW: "finite W" using W linW by (simp add: fin_dim_li_fin)
  have split: "lincomb c (W \<union> X) = lincomb c X + lincomb c W"
    using lincomb_union[OF W X WXinters finW finX]
    by (simp add: M.add.m_comm W X)
  hence "lincomb c X + lincomb c W  \<in> span X" using zerocomb
    using local.span_zero by auto
  hence z1: "lincomb c W = 0\<^sub>v n"
    using ortho_sum_in_span[OF W X ortho] by simp
  hence z2: "lincomb c X = 0\<^sub>v n" using split zerocomb X by simp
  have or: "(\<exists>v \<in> W. c v \<noteq> 0) \<or> (\<exists> v\<in> X. c v \<noteq> 0)" using notallz by auto
  have ex1: "\<exists>v \<in> W. c v \<noteq> 0 \<Longrightarrow> False" using linW
    using finW lin_dep_def z1 by blast
  have ex2: "\<exists> v\<in> X. c v \<noteq> 0 \<Longrightarrow> False" using linX
    using finX lin_dep_def z2 by blast
  show False using ex1 ex2 or by auto
qed

definition normal_vector :: "'a vec set \<Rightarrow> 'a vec" where
  "normal_vector W = (let ws = (SOME ws. set ws = W \<and> distinct ws);
     m = length ws;
     B = (\<lambda> j. mat m m (\<lambda>(i, j'). ws ! i $ (if j' < j then j' else Suc j')))
     in vec n (\<lambda> j. (-1)^(m+j) * det (B j)))"

lemma normal_vector: assumes fin: "finite W"
  and card: "Suc (card W) = n"
  and lin: "lin_indpt W"
  and W: "W \<subseteq> carrier_vec n"
shows "normal_vector W \<in> carrier_vec n"
  "normal_vector W \<noteq> 0\<^sub>v n"
  "w \<in> W \<Longrightarrow> w \<bullet> normal_vector W = 0"
  "w \<in> W \<Longrightarrow> normal_vector W \<bullet> w = 0"
  "lin_indpt (insert (normal_vector W) W)"
  "normal_vector W \<notin> W"
  "W \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<Longrightarrow> normal_vector W \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n-1) Bnd)"
proof -
  define ws where "ws = (SOME ws. set ws = W \<and> distinct ws)"
  from finite_distinct_list[OF fin]
  have "\<exists> ws. set ws = W \<and> distinct ws" by auto
  from someI_ex[OF this, folded ws_def] have id: "set ws = W" and dist: "distinct ws" by auto
  have len: "length ws = card W" using distinct_card[OF dist] id by auto
  let ?n = "length ws"
  define B where "B = (\<lambda> j. mat ?n ?n (\<lambda>(i, j'). ws ! i $ (if j' < j then j' else Suc j')))"
  define nv where "nv = vec n (\<lambda> j. (-1)^(?n+j) * det (B j))"
  have nv2: "normal_vector W = nv" unfolding normal_vector_def Let_def
      ws_def[symmetric] B_def nv_def ..
  define A where "A = (\<lambda> w. mat_of_rows n (ws @ [w]))"
  from len id card have len: "Suc ?n = n" by auto
  have A: "A w \<in> carrier_mat n n" for w using id W len unfolding A_def by auto
  {
    fix w :: "'a vec"
    assume w: "w \<in> carrier_vec n"
    from len have n1[simp]: "n - Suc 0 = ?n" by auto
    {
      fix j
      assume j: "j < n"
      have "mat_delete (A w) ?n j = B j"
        unfolding mat_delete_def A_def mat_of_rows_def B_def
        by (rule eq_matI, insert j len, auto simp: nth_append)
    } note B = this
    have "det (A w) = (\<Sum>j<n. (A w) $$ (length ws, j) * cofactor (A w) ?n j)"
      by (subst laplace_expansion_row[OF A, of ?n], insert len, auto)
    also have "\<dots> = (\<Sum>j<n. w $ j * (-1)^(?n+j) * det (mat_delete (A w) ?n j))"
      by (rule sum.cong, auto simp: A_def mat_of_rows_def cofactor_def)
    also have "\<dots> = (\<Sum>j<n. w $ j * (-1)^(?n+j) * det (B j))"
      by (rule sum.cong[OF refl], subst B, auto)
    also have "\<dots> = (\<Sum>j<n. w $ j * nv $ j)"
      by (rule sum.cong[OF refl], auto simp: nv_def)
    also have "\<dots> = w \<bullet> nv" unfolding scalar_prod_def unfolding nv_def
      by (rule sum.cong, auto)
    finally have "det (A w) = w \<bullet> nv" .
  } note det_scalar = this
  have nv: "nv \<in> carrier_vec n" unfolding nv_def by auto
  {
    fix w
    assume wW: "w \<in> W"
    with W have w: "w \<in> carrier_vec n" by auto
    from wW id obtain i where i: "i < ?n" and ws: "ws ! i = w" unfolding set_conv_nth by auto
    from det_scalar[OF w] have "det (A w) = w \<bullet> nv" .
    also have "det (A w) = 0"
      by (subst det_identical_rows[OF A, of i ?n], insert i ws len, auto simp: A_def mat_of_rows_def nth_append)
    finally have "w \<bullet> nv = 0" ..
    note this this[unfolded comm_scalar_prod[OF w nv]]
  } note ortho = this
  have nv0: "nv \<noteq> 0\<^sub>v n"
  proof
    assume nv: "nv = 0\<^sub>v n"
    define bs where "bs = basis_extension ws"
    define w where "w = hd bs"
    have "lin_indpt_list ws" using dist lin W unfolding lin_indpt_list_def id by auto
    from basis_extension[OF this, folded bs_def] len
    have lin: "lin_indpt_list (ws @ bs)" and "length bs = 1" and bsc: "set bs \<subseteq> carrier_vec n"
      by (auto simp: unit_vecs_def)
    hence bs: "bs = [w]" unfolding w_def by (cases bs, auto)
    with bsc have w: "w \<in> carrier_vec n" by auto
    note lin = lin[unfolded bs]
    from lin_indpt_list_length_eq_n[OF lin] len
    have basis: "basis (set (ws @ [w]))" by auto
    from w det_scalar nv have det0: "det (A w) = 0" by auto
    with basis_det_nonzero[OF basis] len show False
      unfolding A_def by auto
  qed
  let ?nv = "normal_vector W"
  from ortho nv nv0
  show nv: "?nv \<in> carrier_vec n"
    and ortho: "\<And> w. w \<in> W \<Longrightarrow> w \<bullet> ?nv = 0"
    "\<And> w. w \<in> W \<Longrightarrow> ?nv \<bullet> w = 0"
    and n0: "?nv \<noteq> 0\<^sub>v n" unfolding nv2 by auto
  from n0 nv have "sq_norm ?nv \<noteq> 0" by auto
  hence nvnv: "?nv \<bullet> ?nv \<noteq> 0" by (auto simp: sq_norm_vec_as_cscalar_prod)
  show nvW: "?nv \<notin> W" using nvnv ortho by blast
  have "?nv \<notin> span W" using W ortho nvnv nv
    using orthocompl_span by blast
  with lin_dep_iff_in_span[OF W lin nv nvW]
  show "lin_indpt (insert ?nv W)" by auto
  {
    assume "W \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    hence wsI: "set ws \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd" unfolding id by auto
    have ws: "set ws \<subseteq> carrier_vec n" using W unfolding id by auto
    from wsI ws have wsI: "i < ?n \<Longrightarrow> ws ! i \<in> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<inter> carrier_vec n" for i
      using len wsI unfolding set_conv_nth by auto
    have ints: "i < ?n \<Longrightarrow> j < n \<Longrightarrow> ws ! i $ j \<in> \<int>" for i j
      using wsI[of i, unfolded Ints_vec_def] by force
    have bnd: "i < ?n \<Longrightarrow> j < n \<Longrightarrow> abs (ws ! i $ j) \<le> Bnd" for i j
      using wsI[unfolded Bounded_vec_def, of i] by auto
    {
      fix i
      assume i: "i < n"
      have ints: "nv $ i \<in> \<int>" unfolding nv_def using wsI len ws
        by (auto simp: i B_def set_conv_nth intro!: Ints_mult Ints_det ints)
      have "\<bar>nv $ i\<bar> \<le> det_bound (n - 1) Bnd" unfolding nv_def using wsI len ws i
        by (auto simp: B_def Bounded_mat_def abs_mult intro!: det_bound bnd)
      note ints this
    }
    with nv nv2 show "?nv \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) Bnd)"
      unfolding Ints_vec_def Bounded_vec_def by auto
  }
qed

lemma normal_vector_span:
  assumes card: "Suc (card D) = n"
    and D: "D \<subseteq> carrier_vec n" and fin: "finite D" and lin: "lin_indpt D"
  shows "span D = { x. x \<in> carrier_vec n \<and> x \<bullet> normal_vector D = 0}"
proof -
  note nv = normal_vector[OF fin card lin D]
  {
    fix x
    assume xspan: "x \<in> span D"
    from finite_in_span[OF fin D xspan] obtain c where
      "x \<bullet> normal_vector D = lincomb c D \<bullet> normal_vector D" by auto
    also have "\<dots> = (\<Sum>w\<in>D. c w * (w \<bullet> normal_vector D))"
      by (rule lincomb_scalar_prod_left, insert D nv, auto)
    also have "\<dots> = 0"
      apply (rule sum.neutral) using nv(1,2,3) D comm_scalar_prod[of "normal_vector D"] by fastforce
    finally have "x \<in> carrier_vec n"  "x \<bullet> normal_vector D = 0" using xspan D by auto
  }
  moreover
  {
    let ?n = "normal_vector D"
    fix x
    assume x: "x \<in> carrier_vec n" and xscal: "x \<bullet> normal_vector D = 0"
    let ?B = "(insert (normal_vector D) D)"
    have "card ?B = n" using card card_insert_disjoint[OF fin nv(6)] by auto
    moreover have B: "?B \<subseteq> carrier_vec n" using D nv by auto
    ultimately have "span ?B = carrier_vec n"
      by (intro span_carrier_lin_indpt_card_n, insert nv(5), auto)
    hence xspan: "x \<in> span ?B" using x by auto
    obtain c where "x = lincomb c ?B" using finite_in_span[OF _ B xspan] fin by auto
    hence "0 = lincomb c ?B \<bullet> normal_vector D" using xscal by auto
    also have "\<dots> = (\<Sum>w\<in> ?B. c w * (w \<bullet> normal_vector D))"
      by (subst lincomb_scalar_prod_left, insert B, auto)
    also have "\<dots> = (\<Sum>w\<in> D. c w * (w \<bullet> normal_vector D)) + c ?n * (?n \<bullet> ?n)"
      by (subst sum.insert[OF fin nv(6)], auto)
    also have "(\<Sum>w\<in> D. c w * (w \<bullet> normal_vector D)) = 0"
      apply(rule sum.neutral) using nv(1,3) comm_scalar_prod[OF nv(1)] D by fastforce
    also have "?n \<bullet> ?n = sq_norm ?n" using sq_norm_vec_as_cscalar_prod[of ?n] by simp
    finally have "c ?n * sq_norm ?n = 0" by simp
    hence ncoord: "c ?n = 0" using nv(1-5) by auto
    have "x = lincomb c ?B" by fact
    also have "\<dots> = lincomb c D"
      apply (subst lincomb_insert2[OF fin D _ nv(6,1)]) using ncoord nv(1) D by auto
    finally have "x \<in> span D" using fin by auto
  }
  ultimately show ?thesis by auto
qed

definition normal_vectors :: "'a vec list \<Rightarrow> 'a vec list" where
  "normal_vectors ws = (let us = basis_extension ws
    in map (\<lambda> i. normal_vector (set (ws @ us) - {us ! i})) [0..<length us])"

lemma normal_vectors:
  assumes lin: "lin_indpt_list ws"
  shows "set (normal_vectors ws) \<subseteq> carrier_vec n"
    "w \<in> set ws \<Longrightarrow> nv \<in> set (normal_vectors ws) \<Longrightarrow> nv \<bullet> w = 0"
    "w \<in> set ws \<Longrightarrow> nv \<in> set (normal_vectors ws) \<Longrightarrow> w \<bullet> nv = 0"
    "lin_indpt_list (ws @ normal_vectors ws)"
    "length ws + length (normal_vectors ws) = n"
    "set ws \<inter> set (normal_vectors ws) = {}"
    "set ws \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd \<Longrightarrow>
       set (normal_vectors ws) \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n-1) (max 1 Bnd))"
proof -
  define us where "us = basis_extension ws"
  from basis_extension[OF assms, folded us_def]
  have units: "set us \<subseteq> set (unit_vecs n)"
    and lin: "lin_indpt_list (ws @ us)"
    and len: "length (ws @ us) = n"
    by auto
  from lin_indpt_list_length_eq_n[OF lin len]
  have span: "span (set (ws @ us)) = carrier_vec n" by auto
  from lin[unfolded lin_indpt_list_def]
  have wsus: "set (ws @ us) \<subseteq> carrier_vec n"
    and dist: "distinct (ws @ us)"
    and lin': "lin_indpt (set (ws @ us))" by auto
  let ?nv = "normal_vectors ws"
  note nv_def = normal_vectors_def[of ws, unfolded Let_def, folded us_def]
  let ?m = "length ws"
  let ?n = "length us"
  have lnv[simp]: "length ?nv = length us" unfolding nv_def by auto
  {
    fix i
    let ?V = "set (ws @ us) - {us ! i}"
    assume i: "i < ?n"
    hence nvi: "?nv ! i = normal_vector ?V" unfolding nv_def by auto
    from i have "us ! i \<in> set us" by auto
    with wsus have u: "us ! i \<in> carrier_vec n" by auto
    have id: "?V \<union> {us ! i} = set (ws @ us)" using i by auto
    have V: "?V \<subseteq> carrier_vec n" using wsus by auto
    have finV: "finite ?V" by auto
    have "Suc (card ?V) = card (insert (us ! i) ?V)"
      by (subst card_insert_disjoint[OF finV], auto)
    also have "insert (us ! i) ?V = set (ws @ us)" using i by auto
    finally have cardV: "Suc (card ?V) = n"
      using len distinct_card[OF dist] by auto
    from subset_li_is_li[OF lin'] have linV: "lin_indpt ?V" by auto
    from lin_dep_iff_in_span[OF _ linV u, unfolded id] wsus lin'
    have usV: "us ! i \<notin> span ?V" by auto
    note nv = normal_vector[OF finV cardV linV V, folded nvi]
    from normal_vector_span[OF cardV V _ linV, folded nvi] comm_scalar_prod[OF _ nv(1)]
    have span: "span ?V = {x \<in> carrier_vec n. ?nv ! i \<bullet> x = 0}"
      by auto
    from nv(1,2) have "sq_norm (?nv ! i) \<noteq> 0" by auto
    hence nvi: "?nv ! i \<bullet> ?nv ! i \<noteq> 0"
      by (auto simp: sq_norm_vec_as_cscalar_prod)
    from span nvi have nvspan: "?nv ! i \<notin> span ?V" by auto
    from u usV[unfolded span] have "?nv ! i \<bullet> us ! i \<noteq> 0" by blast
    note nv nvi this span usV nvspan
  } note nvi = this
  show nv: "set ?nv \<subseteq> carrier_vec n"
    unfolding set_conv_nth using nvi(1) by auto
  {
    fix w nv
    assume w: "w \<in> set ws"
    with dist have wus: "w \<notin> set us" by auto
    assume n: "nv \<in> set ?nv"
    with w wus show "nv \<bullet> w = 0"
      unfolding set_conv_nth[of "normal_vectors _"] by (auto intro!: nvi(4)[of _ w])
    thus "w \<bullet> nv = 0" using comm_scalar_prod[of w n nv] w nv n wsus by auto
  } note scalar_0 = this
  show "length ws + length ?nv = n" using len by simp
  {
    assume wsI: "set ws \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec Bnd"
    {
      fix nv
      assume "nv \<in> set ?nv"
      then obtain i where nv: "nv = ?nv ! i" and i: "i < ?n" unfolding set_conv_nth by auto
      from wsI have "set (ws @ us) - {us ! i} \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (max 1 Bnd)" using units
          Bounded_vec_mono[of Bnd "max 1 Bnd"]
        by (auto simp: unit_vecs_def)
      from nvi(7)[OF i this] nv
      have "nv \<in> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) (max 1 Bnd))"
        by auto
    }
    thus "set ?nv \<subseteq> \<int>\<^sub>v \<inter> Bounded_vec (det_bound (n - 1) (max 1 Bnd))" by auto
  }
  have dist_nv: "distinct ?nv" unfolding distinct_conv_nth lnv
  proof (intro allI impI)
    fix i j
    assume i: "i < ?n" and j: "j < ?n" and ij: "i \<noteq> j"
    with dist have usj: "us ! j \<in> set (ws @ us) - {us ! i}"
      by (simp, auto simp: distinct_conv_nth set_conv_nth)
    from nvi(4)[OF i this] nvi(9)[OF j]
    show "?nv ! i \<noteq> ?nv ! j" by auto
  qed
  show disj: "set ws \<inter> set ?nv = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain w where w: "w \<in> set ws" "w \<in> set ?nv" by auto
    from scalar_0[OF this] this(1) have "sq_norm w = 0"
      by (auto simp: sq_norm_vec_as_cscalar_prod)
    with w wsus have "w = 0\<^sub>v n" by auto
    with vs_zero_lin_dep[OF wsus lin'] w(1) show False by auto
  qed
  have dist': "distinct (ws @ ?nv)" using dist disj dist_nv by auto
  show "lin_indpt_list (ws @ ?nv)" unfolding lin_indpt_list_def
  proof (intro conjI dist')
    show set: "set (ws @ ?nv) \<subseteq> carrier_vec n" using nv wsus by auto
    hence ws: "set ws \<subseteq> carrier_vec n" by auto
    have lin_nv: "lin_indpt (set ?nv)"
    proof
      assume "lin_dep (set ?nv)"
      from finite_lin_dep[OF finite_set this nv]
      obtain a v where comb: "lincomb a (set ?nv) = 0\<^sub>v n" and vnv: "v \<in> set ?nv" and av0: "a v \<noteq> 0" by auto
      from vnv[unfolded set_conv_nth] obtain i where i: "i < ?n" and vi: "v = ?nv ! i" by auto
      define b where "b = (\<lambda> w. a w / a v)"
      define c where "c = (\<lambda> w. -1 * b w)"
      define x where "x = lincomb b (set ?nv - {v})"
      define w where "w = lincomb c (set ?nv - {v})"
      have w: "w \<in> carrier_vec n" unfolding w_def using nv by auto
      have x: "x \<in> carrier_vec n" unfolding x_def using nv by auto
      from arg_cong[OF comb, of "\<lambda> x. (1/ a v) \<cdot>\<^sub>v x"]
      have "0\<^sub>v n = 1 / a v \<cdot>\<^sub>v lincomb a (set ?nv)" by auto
      also have "\<dots> = lincomb b (set ?nv)"
        by (subst lincomb_smult[symmetric, OF nv], auto simp: b_def)
      also have "\<dots> = b v \<cdot>\<^sub>v v + lincomb b (set ?nv - {v})"
        by (subst lincomb_del2[OF _ nv _ vnv], auto)
      also have "b v \<cdot>\<^sub>v v = v" using av0 unfolding b_def by auto
      finally have "v + lincomb b (set ?nv - {v}) - lincomb b (set ?nv - {v}) =
         0\<^sub>v n - lincomb b (set ?nv - {v})" (is "?l = ?r") by simp
      also have "?l = v"
        by (rule add_diff_cancel_right_vec, insert vnv nv, auto)
      also have "?r = w" unfolding w_def c_def
        by (subst lincomb_smult, unfold x_def[symmetric], insert nv x, auto)
      finally have vw: "v = w" .
      have u: "us ! i \<in> carrier_vec n" using i wsus by auto
      have nv': "set ?nv - {?nv ! i} \<subseteq> carrier_vec n" using nv by auto
      have "?nv ! i \<bullet> us ! i = 0"
        unfolding vi[symmetric] vw unfolding w_def vi
        unfolding lincomb_scalar_prod_left[OF nv' u]
      proof (rule sum.neutral, intro ballI)
        fix x
        assume "x \<in> set ?nv - {?nv ! i}"
        then obtain j where j: "j < ?n" and x: "x = ?nv ! j" and ij: "i \<noteq> j" unfolding set_conv_nth by auto
        from dist[simplified] ij i j have "us ! i \<noteq> us ! j" unfolding distinct_conv_nth by auto
        with i have "us ! i \<in> set (ws @ us) - {us ! j}" by auto
        from nvi(3-4)[OF j this]
        show "c x * (x \<bullet> us ! i) = 0" unfolding x by auto
      qed
      with nvi(9)[OF i] show False ..
    qed
    from subset_li_is_li[OF lin'] have "lin_indpt (set ws)" by auto
    from ortho_lin_indpt[OF nv ws scalar_0 lin_nv this]
    have "lin_indpt (set ?nv \<union> set ws)" .
    also have "set ?nv \<union> set ws = set (ws @ ?nv)" by auto
    finally show "lin_indpt (set (ws @ ?nv))" .
  qed
qed

definition pos_norm_vec :: "'a vec set \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "pos_norm_vec D x = (let c' = normal_vector D;
     c = (if c' \<bullet> x > 0 then c' else -c') in c)"

lemma pos_norm_vec:
  assumes D: "D \<subseteq> carrier_vec n" and fin: "finite D" and lin: "lin_indpt D"
    and card: "Suc (card D) = n"
    and c_def: "c = pos_norm_vec D x"
  shows "c \<in> carrier_vec n" "span D = { x. x \<in> carrier_vec n \<and> x \<bullet> c = 0}"
    "x \<notin> span D \<Longrightarrow> x \<in> carrier_vec n \<Longrightarrow> c \<bullet> x > 0"
    "c \<in> {normal_vector D, -normal_vector D}"
proof -
  have n: "normal_vector D \<in> carrier_vec n" using normal_vector assms by auto
  show cnorm: "c \<in> {normal_vector D, -normal_vector D}" unfolding c_def pos_norm_vec_def Let_def by auto
  then show c: "c \<in> carrier_vec n" using assms normal_vector by auto
  have "span D = { x. x \<in> carrier_vec n \<and> x \<bullet> normal_vector D = 0}"
    using normal_vector_span[OF card D fin lin] by auto
  also have "\<dots> = { x. x \<in> carrier_vec n \<and> x \<bullet> c = 0}" using cnorm c by auto
  finally show span_char: "span D = { x. x \<in> carrier_vec n \<and> x \<bullet> c = 0}" by auto
  {
    assume x: "x \<notin> span D" "x \<in> carrier_vec n"
    hence "c \<bullet> x \<noteq> 0" using comm_scalar_prod[OF c] unfolding span_char by auto
    hence "normal_vector D \<bullet> x \<noteq> 0" using cnorm n x by auto
    with x have b: "\<not> (normal_vector D \<bullet> x > 0) \<Longrightarrow> (-normal_vector D) \<bullet> x > 0"
      using assms n by auto
    then show "c \<bullet> x > 0"  unfolding c_def pos_norm_vec_def Let_def
      by (auto split: if_splits)
  }
qed

end

end