(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Matrix Kernel\<close>

text \<open>We define the kernel of a matrix $A$ and prove the following properties.

\begin{itemize}
\item The kernel stays invariant when multiplying $A$ with an invertible matrix from the left.
\item The dimension of the kernel stays invariant when 
  multiplying $A$ with an invertible matrix from the right.
\item The function find-base-vectors returns a basis of the kernel if $A$ is in row-echelon form.
\item The dimension of the kernel of a block-diagonal matrix is the sum of the dimensions of
  the kernels of the blocks.
\item There is an executable algorithm which computes the dimension of the kernel of a matrix
  (which just invokes Gauss-Jordan and then counts the number of pivot elements).
\end{itemize}
\<close>

theory Matrix_Kernel
imports 
  VS_Connect
  Missing_VectorSpace
  Determinant
begin

hide_const real_vector.span
hide_const (open) Real_Vector_Spaces.span
hide_const real_vector.dim
hide_const (open) Real_Vector_Spaces.dim

definition mat_kernel :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec set" where
  "mat_kernel A = { v . v \<in> carrier_vec (dim_col A) \<and> A *\<^sub>v v = 0\<^sub>v (dim_row A)}"

lemma mat_kernelI: assumes "A \<in> carrier_mat nr nc" "v \<in> carrier_vec nc" "A *\<^sub>v v = 0\<^sub>v nr"
  shows "v \<in> mat_kernel A"
  using assms unfolding mat_kernel_def by auto

lemma mat_kernelD: assumes "A \<in> carrier_mat nr nc" "v \<in> mat_kernel A"
  shows "v \<in> carrier_vec nc" "A *\<^sub>v v = 0\<^sub>v nr"
  using assms unfolding mat_kernel_def by auto

lemma mat_kernel: assumes "A \<in> carrier_mat nr nc" 
  shows "mat_kernel A = {v. v \<in> carrier_vec nc \<and> A *\<^sub>v v = 0\<^sub>v nr}"
  unfolding mat_kernel_def using assms by auto

lemma mat_kernel_carrier:
  assumes "A \<in> carrier_mat nr nc" shows "mat_kernel A \<subseteq> carrier_vec nc"
  using assms mat_kernel by auto

lemma mat_kernel_mult_subset: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat n nr"
  shows "mat_kernel A \<subseteq> mat_kernel (B * A)"
proof -
  from A B have BA: "B * A \<in> carrier_mat n nc" by auto
  show ?thesis unfolding mat_kernel[OF BA] mat_kernel[OF A] using A B by auto
qed

lemma mat_kernel_smult: assumes A: "A \<in> carrier_mat nr nc"
  and v: "v \<in> mat_kernel A"
  shows "a \<cdot>\<^sub>v v \<in>  mat_kernel A"
proof -
  from mat_kernelD[OF A v] have v: "v \<in> carrier_vec nc"
    and z: "A *\<^sub>v v = 0\<^sub>v nr" by auto
  from arg_cong[OF z, of "\<lambda> v. a \<cdot>\<^sub>v v"] v 
  have "a \<cdot>\<^sub>v (A *\<^sub>v v) = 0\<^sub>v nr" by auto
  also have "a \<cdot>\<^sub>v (A *\<^sub>v v) = A *\<^sub>v (a \<cdot>\<^sub>v v)" using A v by auto
  finally show ?thesis using v A
    by (intro mat_kernelI, auto)
qed

lemma mat_kernel_mult_eq: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nr"
  and C: "C \<in> carrier_mat nr nr"
  and inv: "C * B = 1\<^sub>m nr"
  shows "mat_kernel (B * A) = mat_kernel A"
proof 
  from B A have BA: "B * A \<in> carrier_mat nr nc" by auto
  show "mat_kernel A \<subseteq> mat_kernel (B * A)" by (rule mat_kernel_mult_subset[OF A B])
  {
    fix v
    assume v: "v \<in> mat_kernel (B * A)"
    from mat_kernelD[OF BA this] have v: "v \<in> carrier_vec nc" and z: "B * A *\<^sub>v v = 0\<^sub>v nr" by auto
    from arg_cong[OF z, of "\<lambda> v. C *\<^sub>v v"] 
    have "C *\<^sub>v (B * A *\<^sub>v v) = 0\<^sub>v nr" using C v by auto
    also have "C *\<^sub>v (B * A *\<^sub>v v) = ((C * B) * A) *\<^sub>v v" 
      unfolding assoc_mult_mat_vec[symmetric, OF C BA v]    
      unfolding assoc_mult_mat[OF C B A] by simp
    also have "\<dots> = A *\<^sub>v v" unfolding inv using A v by auto
    finally have "v \<in> mat_kernel A"
      by (intro mat_kernelI[OF A v])
  }
  thus "mat_kernel (B * A) \<subseteq> mat_kernel A" by auto
qed

locale kernel =
  fixes nr :: nat
    and nc :: nat
    and A :: "'a :: field mat"
  assumes A: "A \<in> carrier_mat nr nc"
begin

sublocale NC: vec_space "TYPE('a)" nc .

abbreviation "VK \<equiv> NC.V\<lparr>carrier := mat_kernel A\<rparr>"

sublocale Ker: vectorspace class_ring VK 
  rewrites "carrier VK = mat_kernel A"
    and [simp]: "add VK = (+)"
    and [simp]: "zero VK = 0\<^sub>v nc"
    and [simp]: "module.smult VK = (\<cdot>\<^sub>v)"
    and "carrier class_ring = UNIV"
    and "monoid.mult class_ring = (*)"
    and "add class_ring = (+)"
    and "one class_ring = 1"
    and "zero class_ring = 0"
    and "a_inv (class_ring :: 'a ring) = uminus"
    and "a_minus (class_ring :: 'a ring) = minus"
    and "pow (class_ring :: 'a ring) = (^)"
    and "finsum (class_ring :: 'a ring) = sum"
    and "finprod (class_ring :: 'a ring) = prod"
    and "m_inv (class_ring :: 'a ring) x = (if x = 0 then div0 else inverse x)"
  apply (intro vectorspace.intro)
  apply (rule NC.submodule_is_module)
  apply (unfold_locales)
  by (insert A mult_add_distrib_mat_vec[OF A] mult_mat_vec[OF A] mat_kernel[OF A], auto simp: class_ring_simps)

abbreviation "basis \<equiv> Ker.basis"
abbreviation "span \<equiv> Ker.span"
abbreviation "lincomb \<equiv> Ker.lincomb"
abbreviation "dim \<equiv> Ker.dim"
abbreviation "lin_dep \<equiv> Ker.lin_dep"
abbreviation "lin_indpt \<equiv> Ker.lin_indpt"
abbreviation "gen_set \<equiv> Ker.gen_set"

lemma finsum_same:
  assumes "f : S \<rightarrow> mat_kernel A"
  shows "finsum VK f S = finsum NC.V f S"
  using assms
proof (induct S rule: infinite_finite_induct)
  case (insert s S)
    hence base: "finite S" "s \<notin> S"
      and f_VK: "f : S \<rightarrow> mat_kernel A" "f s : mat_kernel A" by auto
    hence f_NC: "f : S \<rightarrow> carrier_vec nc" "f s : carrier_vec nc" using mat_kernel[OF A] by auto
    have IH: "finsum VK f S = finsum NC.V f S" using insert f_VK by auto
    thus ?case
      unfolding NC.M.finsum_insert[OF base f_NC]
      unfolding Ker.finsum_insert[OF base f_VK]
      by simp
qed auto

lemma lincomb_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "lincomb a S = NC.lincomb a S"
  unfolding Ker.lincomb_def
  unfolding NC.lincomb_def
  apply(subst finsum_same)
  using S_kernel Ker.smult_closed[unfolded module_vec_simps class_ring_simps] by auto

lemma span_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "span S = NC.span S"
proof (rule;rule)
  fix v assume L: "v : span S" show "v : NC.span S"
  proof -
    obtain a U where know: "finite U" "U \<subseteq> S" "a : U \<rightarrow> UNIV" "v = lincomb a U"
      using L unfolding Ker.span_def by auto
    hence v: "v = NC.lincomb a U" using lincomb_same S_kernel by auto
    show ?thesis
      unfolding NC.span_def by (rule,intro exI conjI;fact)
  qed
  next fix v assume R: "v : NC.span S" show "v : span S"
  proof -
    obtain a U where know: "finite U" "U \<subseteq> S" "v = NC.lincomb a U"
      using R unfolding NC.span_def by auto
    hence v: "v = lincomb a U" using lincomb_same S_kernel by auto
    show ?thesis unfolding Ker.span_def by (rule, intro exI conjI, insert v know, auto)
  qed
qed

lemma lindep_same:
  assumes S_kernel: "S \<subseteq> mat_kernel A"
  shows "Ker.lin_dep S = NC.lin_dep S"
proof
  note [simp] = module_vec_simps class_ring_simps
  { assume L: "Ker.lin_dep S"
    then obtain v a U
    where finU: "finite U" and US: "U \<subseteq> S"
      and lc: "lincomb a U = 0\<^sub>v nc"
      and vU: "v \<in> U"
      and av0: "a v \<noteq> 0"
      unfolding Ker.lin_dep_def by auto
    have lc': "NC.lincomb a U = 0\<^sub>v nc"
      using lc lincomb_same US S_kernel by auto
    show "NC.lin_dep S" unfolding NC.lin_dep_def
      by (intro exI conjI, insert finU US lc' vU av0, auto)
  }
  assume R: "NC.lin_dep S"
  then obtain v a U
  where finU: "finite U" and US: "U \<subseteq> S"
    and lc: "NC.lincomb a U = 0\<^sub>v nc"
    and vU: "v : U"
    and av0: "a v \<noteq> 0"
    unfolding NC.lin_dep_def by auto
  have lc': "lincomb a U = zero VK"
    using lc lincomb_same US S_kernel by auto
  show "Ker.lin_dep S" unfolding Ker.lin_dep_def
    by (intro exI conjI,insert finU US lc' vU av0, auto)
qed

lemma lincomb_index:
  assumes i: "i < nc"
    and Xk: "X \<subseteq> mat_kernel A"
  shows "lincomb a X $ i = sum (\<lambda>x. a x * x $ i) X"
proof -
  have X: "X \<subseteq> carrier_vec nc" using Xk mat_kernel_def A by auto
  show ?thesis
    using vec_space.lincomb_index[OF i X]
    using lincomb_same[OF Xk] by auto
qed

end

lemma find_base_vectors: assumes ref: "row_echelon_form A" 
  and A: "A \<in> carrier_mat nr nc" shows
  "set (find_base_vectors A) \<subseteq> mat_kernel A"
  "0\<^sub>v nc \<notin> set (find_base_vectors A)"
  "kernel.basis nc A (set (find_base_vectors A))"
  "card (set (find_base_vectors A)) = nc - card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
  "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
  "kernel.dim nc A = nc - card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
proof -
  note non_pivot_base = non_pivot_base[OF ref A]
  let ?B = "set (find_base_vectors A)"
  let ?pp = "set (pivot_positions A)"
  from A have dim: "dim_row A = nr" "dim_col A = nc" by auto
  from ref[unfolded row_echelon_form_def] obtain p 
  where pivot: "pivot_fun A p nc" using dim by auto
  note piv = pivot_funD[OF dim(1) pivot]
  {
    fix v
    assume "v \<in> ?B"
    from this[unfolded find_base_vectors_def Let_def dim]
      obtain c where c: "c < nc" "c \<notin> snd ` ?pp"
      and res: "v = non_pivot_base A (pivot_positions A) c" by auto
    from non_pivot_base[OF c, folded res] c
    have "v \<in> mat_kernel A" "v \<noteq> 0\<^sub>v nc" 
      by (intro mat_kernelI[OF A], auto)
  }
  thus sub: "?B \<subseteq> mat_kernel A" and
    "0\<^sub>v nc \<notin> ?B" by auto
  {
    fix j j'
    assume j: "j < nc" "j \<notin> snd ` ?pp" and j': "j' < nc" "j' \<notin> snd ` ?pp" and neq: "j' \<noteq> j"
    from non_pivot_base(2)[OF j] non_pivot_base(4)[OF j' j neq]
    have "non_pivot_base A (pivot_positions A) j \<noteq> non_pivot_base A (pivot_positions A) j'" by auto
  }
  hence inj: "inj_on (non_pivot_base A (pivot_positions A))
     (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` ?pp])" unfolding inj_on_def by auto
    note pp = pivot_positions[OF A pivot]
  have lc: "length (pivot_positions A) = card (snd ` ?pp)"
    using distinct_card[OF pp(3)] by auto
  show card: "card ?B = nc - card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
    "length (pivot_positions A) = card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
    unfolding find_base_vectors_def Let_def dim set_map  card_image[OF inj] pp(4)[symmetric]
    unfolding pp(1) lc
  proof -
    have "nc - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})
      = card {0 ..< nc} - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})" by auto
    also have "\<dots> = card ({0 ..< nc} - snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})"
      by (rule card_Diff_subset[symmetric], insert piv(1), force+)
    also have "{0 ..< nc} - snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc} = (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc}])"
      by auto
    finally show "card (set [j\<leftarrow>[0..<nc] . j \<notin> snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc}]) =
      nc - card (snd ` {(i, p i) |i. i < nr \<and> p i \<noteq> nc})" by simp
  qed auto
  interpret kernel nr nc A by (unfold_locales, rule A)
  show basis: "basis ?B"
    unfolding Ker.basis_def
  proof (intro conjI)
    show "span ?B = mat_kernel A"
    proof
      show "span ?B \<subseteq> mat_kernel A"
        using sub by (rule Ker.span_is_subset2)
      show "mat_kernel A \<subseteq> Ker.span ?B"
      proof
        fix v
        assume "v \<in> mat_kernel A" 
        from mat_kernelD[OF A this]
        have v: "v \<in> carrier_vec nc" and Av: "A *\<^sub>v v = 0\<^sub>v nr" by auto
        let ?bi = "non_pivot_base A (pivot_positions A)"
        let ?ran = "set [j\<leftarrow>[0..<nc] . j \<notin> snd ` ?pp]"
        let ?ran' = "set [j\<leftarrow>[0..<nc] . j \<in> snd ` ?pp]"
        have dimv: "dim_vec v = nc" using v by auto
        define I where "I = (\<lambda> b. SOME i. i \<in> ?ran \<and> ?bi i = b)"
        {
          fix j
          assume j: "j \<in> ?ran"
          hence "\<exists> i. i \<in> ?ran \<and> ?bi i = ?bi j" unfolding find_base_vectors_def Let_def dim by auto
          from someI_ex[OF this] have I: "I (?bi j) \<in> ?ran" and id: "?bi (I (?bi j)) = ?bi j" unfolding I_def by blast+
          from inj_onD[OF inj id I j] have "I (?bi j) = j" .
        } note I = this        
        define a where "a = (\<lambda> b. v $ (I b))"
        from Ker.lincomb_closed[OF sub] have diml: "dim_vec (lincomb a ?B) = nc"
          unfolding mat_kernel_def using dim lincomb_same by auto
        have "v = lincomb a ?B"
        proof (rule eq_vecI; unfold diml dimv)
          fix j
          assume j: "j < nc"
          have "Ker.lincomb a ?B $ j = (\<Sum>b\<in> ?B. a b * b $ j)" by (rule lincomb_index[OF j sub])
          also have "\<dots> = (\<Sum> i\<in> ?ran. v $ i * ?bi i $ j)"
          proof (subst sum.reindex_cong[OF inj])
            show "?B = ?bi ` ?ran"  unfolding find_base_vectors_def Let_def dim by auto
            fix i
            assume "i \<in> ?ran"
            hence "I (?bi i) = i" by (rule I)
            hence "a (?bi i) = v $ i" unfolding a_def by simp
            thus "a (?bi i) * ?bi i $ j = v $ i * ?bi i $ j" by simp
          qed auto
          also have "\<dots> = v $ j"
          proof (cases "j \<in> ?ran")
            case True
            hence nmem: "j \<notin> snd ` set (pivot_positions A)" by auto 
            note npb = non_pivot_base[OF j nmem]
            have "(\<Sum> i\<in> ?ran. v $ i * (?bi i) $ j) =
              v $ j * ?bi j $ j + (\<Sum> i\<in> ?ran - {j}. v $ i * ?bi i $ j)"
              by (subst sum.remove[OF _ True], auto)
            also have "?bi j $ j = 1" using npb by simp
            also have "(\<Sum> i \<in> ?ran - {j}. v $ i * ?bi i $ j) = 0"
              using insert non_pivot_base(4)[OF _ _ j nmem] by (intro sum.neutral, auto)
            finally show ?thesis by simp
          next
            case False
            with j have jpp: "j \<in> snd ` ?pp" by auto
            with j pp obtain i where i: "i < nr" and ji: "j = p i" and pi: "p i < nc" by auto
            from arg_cong[OF Av, of "\<lambda> u. u $ i"] i A
            have "v $ j = v $ j - row A i \<bullet> v" by auto
            also have "row A i \<bullet> v = (\<Sum> j = 0 ..< nc. A $$ (i,j) * v $ j)" unfolding scalar_prod_def using v A i by auto
            also have "\<dots> = (\<Sum> j \<in> ?ran. A $$ (i,j) * v $ j) +  (\<Sum> j \<in> ?ran'. A $$ (i,j) * v $ j)"
              by (subst sum.union_disjoint[symmetric], auto intro: sum.cong)
            also have "(\<Sum> j \<in> ?ran'. A $$ (i,j) * v $ j) =
              A $$ (i,p i) * v $ j + (\<Sum> j \<in> ?ran' - {p i}. A $$ (i,j) * v $ j)"
              using jpp by (subst sum.remove, auto simp: ji i pi)
            also have "A $$ (i, p i) = 1" using piv(4)[OF i] pi ji by auto
            also have "(\<Sum> j \<in> ?ran' - {p i}. A $$ (i,j) * v $ j) = 0"
            proof (rule sum.neutral, intro ballI)
              fix j'
              assume "j' \<in> ?ran' - {p i}"
              then obtain i' where i': "i' < nr" and j': "j' = p i'" and pi': "p i' \<noteq> nc" and neq: "p i' \<noteq> p i"
                unfolding pp by auto
              from pi' piv[OF i'] have pi': "p i' < nc" by auto
              from pp pi' neq j i' i have "i \<noteq> i'" by auto
              from piv(5)[OF i' pi' i this]
              show "A $$ (i,j') * v $ j' = 0" unfolding j' by simp
            qed
            also have "(\<Sum> j \<in> ?ran. A $$ (i,j) * v $ j) = - (\<Sum> j \<in> ?ran. v $ j * - A $$ (i,j))" 
              unfolding sum_negf[symmetric] by (rule sum.cong, auto)
            finally have vj: "v $ j = (\<Sum> j \<in> ?ran. v $ j * - A $$ (i,j))" by simp
            show ?thesis unfolding vj j
            proof (rule sum.cong[OF refl])
              fix j'
              assume j': "j' \<in> ?ran"
              from jpp j' have jj': "j \<noteq> j'" by auto
              let ?map = "map prod.swap (pivot_positions A)"
              from ji i j have "(i,j) \<in> set (pivot_positions A)" unfolding pp by auto
              hence mem: "(j,i) \<in> set ?map" by auto
              from pp have "distinct (map fst ?map)" unfolding map_map o_def prod.swap_def fst_conv by auto
              from map_of_is_SomeI[OF this mem] have "map_of ?map j = Some i" by auto
              hence "?bi j' $ j = - A $$ (i, j')" 
                unfolding non_pivot_base_def Let_def dim using j jj' by auto
              thus "v $ j' * ?bi j' $ j = v $ j' * - A $$ (i,j')" by simp
            qed
          qed
          finally show "v $ j = lincomb a ?B $ j" ..
        qed auto
        thus "v \<in> span ?B" unfolding Ker.span_def by auto
      qed
    qed
    show "?B \<subseteq> mat_kernel A" by (rule sub)
    {
      fix a v
      assume lc: "lincomb a ?B = 0\<^sub>v nc" and vB: "v \<in> ?B"
      from vB[unfolded find_base_vectors_def Let_def dim]
        obtain j where j: "j < nc" "j \<notin> snd ` ?pp" and v: "v = non_pivot_base A (pivot_positions A) j"
        by auto         
      from arg_cong[OF lc, of "\<lambda> v. v $ j"] j
      have "0 = lincomb a ?B $ j" by auto
      also have "\<dots> = (\<Sum>v\<in>?B. a v * v $ j)" 
        by (subst lincomb_index[OF j(1) sub], simp)
      also have "\<dots> = a v * v $ j + (\<Sum>w\<in>?B - {v}. a w * w $ j)"
        by (subst sum.remove[OF _ vB], auto)
      also have "a v * v $ j = a v" using non_pivot_base[OF j, folded v] by simp
      also have "(\<Sum>w\<in>?B - {v}. a w * w $ j) = 0"
      proof (rule sum.neutral, intro ballI)
        fix w
        assume wB: "w \<in> ?B - {v}"
        from this[unfolded find_base_vectors_def Let_def dim]
        obtain j' where j': "j' < nc" "j' \<notin> snd ` ?pp" and w: "w = non_pivot_base A (pivot_positions A) j'"
          by auto    
        with wB v have "j' \<noteq> j" by auto
        from non_pivot_base(4)[OF j' j this]
        show "a w * w $ j = 0" unfolding w by simp
      qed
      finally have "a v = 0" by simp
    }
    thus "\<not> lin_dep ?B"
      by (intro Ker.finite_lin_indpt2[OF finite_set sub], auto simp: class_field_def)
  qed
  show "dim = nc - card { i. i < nr \<and> row A i \<noteq> 0\<^sub>v nc}"
    using Ker.dim_basis[OF finite_set basis] card by simp
qed


definition kernel_dim :: "'a :: field mat \<Rightarrow> nat" where
  [code del]: "kernel_dim A = kernel.dim (dim_col A) A"

lemma (in kernel) kernel_dim [simp]: "kernel_dim A = dim" unfolding kernel_dim_def
  using A by simp

lemma kernel_dim_code[code]: 
  "kernel_dim A = dim_col A - length (pivot_positions (gauss_jordan_single A))"
proof -
  define nr where "nr = dim_row A" 
  define nc where "nc = dim_col A"
  let ?B = "gauss_jordan_single A"
  have A: "A \<in> carrier_mat nr nc" unfolding nr_def nc_def by auto
  from gauss_jordan_single[OF A refl]
    obtain P Q where AB: "?B = P * A" and QP: "Q * P = 1\<^sub>m nr" and
    P: "P \<in> carrier_mat nr nr" and Q: "Q \<in> carrier_mat nr nr" and B: "?B \<in> carrier_mat nr nc" 
    and row: "row_echelon_form ?B" by auto
  interpret K: kernel nr nc ?B
    by (unfold_locales, rule B)
  from mat_kernel_mult_eq[OF A P Q QP, folded AB]
  have "kernel_dim A = K.dim" unfolding kernel_dim_def using A by simp
  also have "\<dots> = nc - length (pivot_positions ?B)" using find_base_vectors[OF row B] by auto
  also have "\<dots> = dim_col A - length (pivot_positions ?B)"
    unfolding nc_def by simp
  finally show ?thesis .
qed


lemma kernel_one_mat: fixes A :: "'a :: field mat" and n :: nat
  defines A: "A \<equiv> 1\<^sub>m n"
  shows 
    "kernel.dim n A = 0"
    "kernel.basis n A {}"
proof -
  have Ac: "A \<in> carrier_mat n n" unfolding A by auto
  have "pivot_fun A id n"
    unfolding A by (rule pivot_funI, auto)
  hence row: "row_echelon_form A" unfolding row_echelon_form_def A by auto
  have "{i. i < n \<and> row A i \<noteq> 0\<^sub>v n} = {0 ..< n}" unfolding A by auto
  hence id: "card {i. i < n \<and> row A i \<noteq> 0\<^sub>v n} = n" by auto
  interpret kernel n n A by (unfold_locales, rule Ac)
  from find_base_vectors[OF row Ac, unfolded id]
  show "dim = 0" "basis {}" by auto
qed

lemma kernel_upper_triangular: assumes A: "A \<in> carrier_mat n n"
  and ut: "upper_triangular A" and 0: "0 \<notin> set (diag_mat A)"
  shows "kernel.dim n A = 0" "kernel.basis n A {}"
proof -
  define ma where "ma = diag_mat A"
  from det_upper_triangular[OF ut A] have "det A = prod_list (diag_mat A)" .
  also have "\<dots> \<noteq> 0" using 0 unfolding ma_def[symmetric]
    by (induct ma, auto)
  finally have "det A \<noteq> 0" .
  from det_non_zero_imp_unit[OF A this, unfolded Units_def, of "()"]
    obtain B where B: "B \<in> carrier_mat n n" and BA: "B * A = 1\<^sub>m n" and AB: "A * B = 1\<^sub>m n"
    by (auto simp: ring_mat_def)
  from mat_kernel_mult_eq[OF A B A AB, unfolded BA]
  have id: "mat_kernel A = mat_kernel (1\<^sub>m n)" ..
  show "kernel.dim n A = 0" "kernel.basis n A {}"
    unfolding id by (rule kernel_one_mat)+
qed

lemma kernel_basis_exists: assumes A: "A \<in> carrier_mat nr nc"
  shows "\<exists> B. finite B \<and> kernel.basis nc A B"
proof -
  obtain C where gj: "gauss_jordan_single A = C" by auto
  from gauss_jordan_single[OF A gj]
  obtain P Q where CPA: "C = P * A" and QP: "Q * P = 1\<^sub>m nr"
    and P: "P \<in> carrier_mat nr nr" and Q: "Q \<in> carrier_mat nr nr"   
    and C: "C \<in> carrier_mat nr nc" and row: "row_echelon_form C"
    by auto
  from find_base_vectors[OF row C] have "\<exists> B. finite B \<and> kernel.basis nc C B" by blast
  also have "mat_kernel C = mat_kernel A" unfolding CPA
    by (rule mat_kernel_mult_eq[OF A P Q QP])
  finally show ?thesis .
qed


lemma mat_kernel_mult_right_gen_set: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nc nc"
  and C: "C \<in> carrier_mat nc nc"
  and inv: "B * C = 1\<^sub>m nc"
  and gen_set: "kernel.gen_set nc (A * B) gen" and gen: "gen \<subseteq> mat_kernel (A * B)"
  shows "kernel.gen_set nc A (((*\<^sub>v) B) ` gen)" "(*\<^sub>v) B ` gen \<subseteq> mat_kernel A" "card (((*\<^sub>v) B) ` gen) = card gen"
proof -
  let ?AB = "A * B"
  let ?gen = "((*\<^sub>v) B) ` gen"
  from A B have AB: "A * B \<in> carrier_mat nr nc" by auto
  from B have dimB: "dim_row B = nc" by auto
  from inv B C have CB: "C * B = 1\<^sub>m nc" by (metis mat_mult_left_right_inverse)
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  {
    fix w
    assume "w \<in> ?gen"
    then obtain v where w: "w = B *\<^sub>v v" and v: "v \<in> gen" by auto
    from v have "v \<in> mat_kernel ?AB" using gen by auto
    hence v: "v \<in> carrier_vec nc" and 0: "?AB *\<^sub>v v = 0\<^sub>v nr" unfolding mat_kernel[OF AB] by auto
    have "?AB *\<^sub>v v = A *\<^sub>v w" unfolding w using v A B by simp
    with 0 have 0: "A *\<^sub>v w = 0\<^sub>v nr" by auto
    from w B v have w: "w \<in> carrier_vec nc" by auto
    from 0 w have "w \<in> mat_kernel A" unfolding mat_kernel[OF A] by auto
  } 
  thus genn: "?gen \<subseteq> mat_kernel A" by auto
  hence one_dir: "A.span ?gen \<subseteq> mat_kernel A" by fastforce
  {
    fix v v'
    assume v: "v \<in> gen" and v': "v' \<in> gen" and id: "B *\<^sub>v v = B *\<^sub>v v'"
    from v v' have v: "v \<in> carrier_vec nc" and v': "v' \<in> carrier_vec nc" 
      using gen unfolding mat_kernel[OF AB] by auto
    from arg_cong[OF id, of "\<lambda> v. C *\<^sub>v v"]
    have "v = v'" using v v'
      unfolding assoc_mult_mat_vec[symmetric, OF C B v] 
        assoc_mult_mat_vec[symmetric, OF C B v'] CB
      by auto
  } note inj = this
  hence inj_gen: "inj_on ((*\<^sub>v) B) gen" unfolding inj_on_def by auto
  show "card ?gen = card gen" using inj_gen by (rule card_image)
  {
    fix v
    let ?Cv = "C *\<^sub>v v"
    assume "v \<in> mat_kernel A"
    from mat_kernelD[OF A this] have v: "v \<in> carrier_vec nc" and 0: "A *\<^sub>v v = 0\<^sub>v nr" by auto
    have "?AB *\<^sub>v ?Cv = (A * (B * C)) *\<^sub>v v" using A B C v 
      by (subst assoc_mult_mat_vec[symmetric, OF AB C v], subst assoc_mult_mat[OF A B C], simp)
    also have "\<dots> = 0\<^sub>v nr" unfolding inv using 0 A v by simp
    finally have 0: "?AB *\<^sub>v ?Cv = 0\<^sub>v nr" and Cv: "?Cv \<in> carrier_vec nc" using C v by auto
    hence "?Cv \<in> mat_kernel ?AB" unfolding mat_kernel[OF AB] by auto
    with gen_set have "?Cv \<in> AB.span gen" by auto
    from this[unfolded AB.Ker.span_def] obtain a gen' where 
      Cv: "?Cv = AB.lincomb a gen'" and sub: "gen' \<subseteq> gen" and fin: "finite gen'" by auto
    let ?gen' = "((*\<^sub>v) B) ` gen'"
    from sub gen have gen': "gen' \<subseteq> mat_kernel ?AB" by auto
    have lin1: "AB.lincomb a gen' \<in> carrier_vec nc"
      using AB.Ker.lincomb_closed[OF gen', of a]
      unfolding mat_kernel[OF AB] by (auto simp: class_field_def)
    hence dim1: "dim_vec (AB.lincomb a gen') = nc" by auto
    hence dim1b: "dim_vec (B *\<^sub>v (AB.Ker.lincomb a gen')) = nc" using B by auto
    from genn sub have genn': "?gen' \<subseteq> mat_kernel A" by auto
    from gen sub have gen'nc: "gen' \<subseteq> carrier_vec nc" unfolding mat_kernel[OF AB] by auto
    define a' where "a' = (\<lambda> b. a (C *\<^sub>v b))"
    from A.Ker.lincomb_closed[OF genn']
    have lin2: "A.Ker.lincomb a' ?gen' \<in> carrier_vec nc"
      unfolding mat_kernel[OF A] by (auto simp: class_field_def)
    hence dim2: "dim_vec (A.Ker.lincomb a' ?gen') = nc" by auto
    have "v = B *\<^sub>v ?Cv" 
      by (unfold assoc_mult_mat_vec[symmetric, OF B C v] inv, insert v, simp)
    hence "v = B *\<^sub>v AB.Ker.lincomb a gen'" unfolding Cv by simp
    also have "\<dots> = A.Ker.lincomb a' ?gen'"
    proof (rule eq_vecI; unfold dim1 dim1b dim2)
      fix i
      assume i: "i < nc"
      with dimB have ii: "i < dim_row B" by auto
      from sub inj have inj: "inj_on ((*\<^sub>v) B) gen'" unfolding inj_on_def by auto
      {
        fix v
        assume "v \<in> gen'"
        with gen'nc have v: "v \<in> carrier_vec nc" by auto
        hence "a' (B *\<^sub>v v) = a v" unfolding a'_def assoc_mult_mat_vec[symmetric, OF C B v] CB by auto
      } note a' = this
      have "A.Ker.lincomb a' ?gen' $ i = (\<Sum>v\<in>(*\<^sub>v) B ` gen'. a' v * v $ i)"
        unfolding A.lincomb_index[OF i genn']  by simp
      also have "\<dots> = (\<Sum>v\<in>gen'. a v * ((B *\<^sub>v v) $ i))"
        by (rule sum.reindex_cong[OF inj refl], auto simp: a')
      also have "\<dots> = (\<Sum>v\<in>gen'. (\<Sum>j = 0..< nc. a v * row B i $ j * v $ j))"
        unfolding mult_mat_vec_def dimB scalar_prod_def index_vec[OF i]
        by (rule sum.cong, insert gen'nc, auto simp: sum_distrib_left ac_simps)
      also have "\<dots> = (\<Sum>j = 0 ..< nc. (\<Sum>v \<in> gen'. a v * row B i $ j * v $ j))"
        by (rule sum.swap)
      also have "\<dots> = (\<Sum>j = 0..<nc. row B i $ j * (\<Sum>v\<in>gen'. a v * v $ j))"
        by (rule sum.cong, auto simp: sum_distrib_left ac_simps)
      also have "\<dots> = (B *\<^sub>v AB.Ker.lincomb a gen') $ i"
        unfolding index_mult_mat_vec[OF ii]
        unfolding scalar_prod_def dim1
        by (rule sum.cong[OF refl], subst AB.lincomb_index[OF _ gen'], auto)
      finally show "(B *\<^sub>v AB.Ker.lincomb a gen') $ i = A.Ker.lincomb a' ?gen' $ i" ..
    qed auto
    finally have "v \<in> A.Ker.span ?gen" using sub fin
      unfolding A.Ker.span_def by (auto simp: class_field_def intro!: exI[of _ a'] exI[of _ ?gen'])
  }
  hence other_dir: "A.Ker.span ?gen \<supseteq> mat_kernel A" by fastforce
  from one_dir other_dir show "kernel.gen_set nc A (((*\<^sub>v) B) ` gen)" by auto
qed

lemma mat_kernel_mult_right_basis: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nc nc"
  and C: "C \<in> carrier_mat nc nc"
  and inv: "B * C = 1\<^sub>m nc"
  and fin: "finite gen"
  and basis: "kernel.basis nc (A * B) gen"
  shows "kernel.basis nc A (((*\<^sub>v) B) ` gen)" 
  "card (((*\<^sub>v) B) ` gen) = card gen"
proof -
  let ?AB = "A * B"
  let ?gen = "((*\<^sub>v) B) ` gen"
  from A B have AB: "?AB \<in> carrier_mat nr nc" by auto
  from B have dimB: "dim_row B = nc" by auto
  from inv B C have CB: "C * B = 1\<^sub>m nc" by (metis mat_mult_left_right_inverse)
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  from basis[unfolded AB.Ker.basis_def] have gen_set: "AB.gen_set gen" and genAB: "gen \<subseteq> mat_kernel ?AB" by auto
  from mat_kernel_mult_right_gen_set[OF A B C inv gen_set genAB]
  have gen: "A.gen_set ?gen" and sub: "?gen \<subseteq> mat_kernel A" and card: "card ?gen = card gen" .
  from card show "card ?gen = card gen" .
  from fin have fing: "finite ?gen" by auto
  from gen have gen: "A.Ker.span ?gen = mat_kernel A" by auto
  have ABC: "A * B * C = A" using A B C inv by simp
  from kernel_basis_exists[OF A] obtain bas where finb: "finite bas" and bas: "A.basis bas" by auto
  from bas have bas': "A.gen_set bas" "bas \<subseteq> mat_kernel A" unfolding A.Ker.basis_def by auto
  let ?bas = "(*\<^sub>v) C ` bas"
  from mat_kernel_mult_right_gen_set[OF AB C B CB, unfolded ABC, OF bas']
  have bas': "?bas \<subseteq> mat_kernel ?AB" "AB.Ker.span ?bas = mat_kernel ?AB" "card ?bas = card bas" by auto
  from finb bas have cardb: "A.dim = card bas" by (rule A.Ker.dim_basis)
  from fin basis have cardg: "AB.dim = card gen" by (rule AB.Ker.dim_basis)
  from AB.Ker.gen_ge_dim[OF _ bas'(1-2)] finb bas'(3) cardb cardg
  have ineq1: "card gen \<le> A.dim" by auto
  from A.Ker.dim_gen_is_basis[OF fing sub gen, unfolded card, OF this]
  show "A.basis ?gen" .
qed  
  
  
lemma mat_kernel_dim_mult_eq_right: assumes A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nc nc"
  and C: "C \<in> carrier_mat nc nc"
  and BC: "B * C = 1\<^sub>m nc"
  shows "kernel.dim nc (A * B) = kernel.dim nc A"
proof -
  let ?AB = "A * B"
  from A B have AB: "?AB \<in> carrier_mat nr nc" by auto
  interpret AB: kernel nr nc ?AB 
    by (unfold_locales, rule AB)
  interpret A: kernel nr nc A
    by (unfold_locales, rule A)
  from kernel_basis_exists[OF AB] obtain bas where finb: "finite bas" and bas: "AB.basis bas" by auto
  let ?bas = "((*\<^sub>v) B) ` bas"
  from mat_kernel_mult_right_basis[OF A B C BC finb bas] finb
  have bas': "A.basis ?bas" and finb': "finite ?bas" and card: "card ?bas = card bas" by auto
  show "AB.dim = A.dim" unfolding A.Ker.dim_basis[OF finb' bas'] AB.Ker.dim_basis[OF finb bas] card ..
qed


locale vardim =
  fixes f_ty :: "'a :: field itself"
begin

abbreviation "M == \<lambda>k. module_vec TYPE('a) k"

abbreviation "span == \<lambda>k. LinearCombinations.module.span class_ring (M k)"
abbreviation "lincomb == \<lambda>k. module.lincomb (M k)"
abbreviation "lin_dep == \<lambda>k. module.lin_dep class_ring (M k)"
abbreviation "padr m v == v @\<^sub>v 0\<^sub>v m"
definition "unpadr m v == vec (dim_vec v - m) (\<lambda>i. v $ i)"
abbreviation "padl m v == 0\<^sub>v m @\<^sub>v v"
definition "unpadl m v == vec (dim_vec v - m) (\<lambda>i. v $ (m+i))"

lemma unpadr_padr[simp]: "unpadr m (padr m v) = v" unfolding unpadr_def by auto
lemma unpadl_padl[simp]: "unpadl m (padl m v) = v" unfolding unpadl_def by auto

lemma padr_unpadr[simp]: "v : padr m ` U \<Longrightarrow> padr m (unpadr m v) = v" by auto
lemma padl_unpadl[simp]: "v : padl m ` U \<Longrightarrow> padl m (unpadl m v) = v" by auto

(* somehow not automatically proven *)
lemma padr_image:
  assumes "U \<subseteq> carrier_vec n" shows "padr m ` U \<subseteq> carrier_vec (n + m)"
proof(rule subsetI)
  fix v assume "v : padr m ` U"
  then obtain u where "u : U" and vmu: "v = padr m u" by auto
  hence "u : carrier_vec n" using assms by auto
  thus "v : carrier_vec (n + m)"
    unfolding vmu
    using zero_carrier_vec[of m] append_carrier_vec by metis
qed
lemma padl_image:
  assumes "U \<subseteq> carrier_vec n" shows "padl m ` U \<subseteq> carrier_vec (m + n)"
proof(rule subsetI)
  fix v assume "v : padl m ` U"
  then obtain u where "u : U" and vmu: "v = padl m u" by auto
  hence "u : carrier_vec n" using assms by auto
  thus "v : carrier_vec (m + n)"
    unfolding vmu
    using zero_carrier_vec[of m] append_carrier_vec by metis
qed

lemma padr_inj:
  shows "inj_on (padr m) (carrier_vec n :: 'a vec set)"
  apply(intro inj_onI) using append_vec_eq by auto

lemma padl_inj:
  shows "inj_on (padl m) (carrier_vec n :: 'a vec set)"
  apply(intro inj_onI)
  using append_vec_eq[OF zero_carrier_vec zero_carrier_vec] by auto

lemma lincomb_pad:
  fixes m n a
  assumes U: "(U :: 'a vec set) \<subseteq> carrier_vec n"
      and finU: "finite U"
  defines "goal pad unpad W == pad m (lincomb n a W) = lincomb (n+m) (a o unpad m) (pad m ` W)"
  shows "goal padr unpadr U" (is ?R) and "goal padl unpadl U" (is "?L")
proof -
  interpret N: vectorspace class_ring "M n" using vec_vs.
  interpret NM: vectorspace class_ring "M (n+m)" using vec_vs.
  note [simp] = module_vec_simps class_ring_simps
  have "?R \<and> ?L" using finU U
  proof (induct set:finite)
    case empty thus ?case
      unfolding goal_def unfolding N.lincomb_def NM.lincomb_def by auto next
    case (insert u U)
      hence finU: "finite U"
        and U: "U \<subseteq> carrier_vec n"
        and u[simp]: "u : carrier_vec n"
        and uU: "u \<notin> U"
        and auU: "a : insert u U \<rightarrow> UNIV"
        and aU: "a : U \<rightarrow> UNIV"
        and au: "a u : UNIV"
        by auto
      have IHr: "goal padr unpadr U" and IHl: "goal padl unpadl U"
        using insert(3) U aU by auto
      note N_lci = N.lincomb_insert2[unfolded module_vec_simps]
      note NM_lci = NM.lincomb_insert2[unfolded module_vec_simps]
      have auu[simp]: "a u \<cdot>\<^sub>v u : carrier_vec n" using au u by simp
      have laU[simp]: "lincomb n a U : carrier_vec n"
        using N.lincomb_closed[unfolded module_vec_simps class_ring_simps, OF U aU].
      let ?m0 = "0\<^sub>v m :: 'a vec"
      have m0: "?m0 : carrier_vec m" by auto
      have ins: "lincomb n a (insert u U) = a u \<cdot>\<^sub>v u + lincomb n a U"
        using N_lci[OF finU U] auU uU u by auto
      show ?case
      proof
        have "padr m (a u \<cdot>\<^sub>v u + lincomb n a U) =
          (a u \<cdot>\<^sub>v u + lincomb n a U) @\<^sub>v (?m0 + ?m0)" by auto
        also have "... = padr m (a u \<cdot>\<^sub>v u) + padr m (lincomb n a U)"
          using append_vec_add[symmetric, OF auu laU]
          using zero_carrier_vec[of m] by metis
        also have "padr m (lincomb n a U) = lincomb (n+m) (a o unpadr m) (padr m ` U)"
          using IHr unfolding goal_def.
        also have "padr m (a u \<cdot>\<^sub>v u) = a u \<cdot>\<^sub>v padr m u" by auto
        also have "... = (a o unpadr m) (padr m u) \<cdot>\<^sub>v padr m u" by auto
        also have "... + lincomb (n+m) (a o unpadr m) (padr m ` U) =
          lincomb (n+m) (a o unpadr m) (insert (padr m u) (padr m ` U))"
          apply(subst NM_lci[symmetric])
          using finU uU U append_vec_eq[OF u] by auto
        also have "insert (padr m u) (padr m ` U) = padr m ` insert u U"
          by auto
        finally show "goal padr unpadr (insert u U)" unfolding goal_def ins.
        have [simp]: "n+m = m+n" by auto
        have "padl m (a u \<cdot>\<^sub>v u + lincomb n a U) =
          (?m0 + ?m0) @\<^sub>v (a u \<cdot>\<^sub>v u + lincomb n a U)" by auto
        also have "... = padl m (a u \<cdot>\<^sub>v u) + padl m (lincomb n a U)"
          using append_vec_add[symmetric, OF _ _ auu laU]
          using zero_carrier_vec[of m] by metis
        also have "padl m (lincomb n a U) = lincomb (n+m) (a o unpadl m) (padl m ` U)"
          using IHl unfolding goal_def.
        also have "padl m (a u \<cdot>\<^sub>v u) = a u \<cdot>\<^sub>v padl m u" by auto
        also have "... = (a o unpadl m) (padl m u) \<cdot>\<^sub>v padl m u" by auto
        also have "... + lincomb (n+m) (a o unpadl m) (padl m ` U) =
          lincomb (n+m) (a o unpadl m) (insert (padl m u) (padl m ` U))"
          apply(subst NM_lci[symmetric])
          using finU uU U append_vec_eq[OF m0] by auto
        also have "insert (padl m u) (padl m ` U) = padl m ` insert u U"
          by auto
        finally show "goal padl unpadl (insert u U)" unfolding goal_def ins.
      qed
  qed
  thus ?R ?L by auto
qed

lemma span_pad:
  assumes U: "(U::'a vec set) \<subseteq> carrier_vec n"
  defines "goal pad m == pad m ` span n U = span (n+m) (pad m ` U)"
  shows "goal padr m" "goal padl m"
proof -
  interpret N: vectorspace class_ring "M n" using vec_vs.
  interpret NM: vectorspace class_ring "M (n+m)" using vec_vs.
  { fix pad :: "'a vec \<Rightarrow> 'a vec" and unpad :: "'a vec \<Rightarrow> 'a vec"
    assume main: "\<And>A a. A \<subseteq> U \<Longrightarrow> finite A \<Longrightarrow>
      pad (lincomb n a A) = lincomb (n+m) (a o unpad) (pad ` A)"
    assume [simp]: "\<And>v. unpad (pad v) = v"
    assume pU: "pad ` U \<subseteq> carrier_vec (n+m)"
    have "pad ` (span n U) = span (n+m) (pad ` U)"
    proof (intro Set.equalityI subsetI)
      fix x assume "x : pad ` (span n U)"
      then obtain v where "v : span n U" and xv: "x = pad v" by auto
      then obtain a A
        where AU: "A \<subseteq> U" and finA: "finite A" and a: "a : A \<rightarrow> UNIV"
          and vaA: "v = lincomb n a A"
        unfolding N.span_def by auto
      hence A: "A \<subseteq> carrier_vec n" using U by auto
      show "x : span (n+m) (pad ` U)" unfolding NM.span_def
      proof (intro CollectI exI conjI)
        show "x = lincomb (n+m) (a o unpad) (pad ` A)"
          using xv vaA main[OF AU finA] by auto
        show "pad ` A \<subseteq> pad ` U" using AU by auto
      qed (insert finA, auto simp: class_ring_simps)
      next
      fix x assume "x : span (n+m) (pad ` U)"
      then obtain a' A'
        where A'U: "A' \<subseteq> pad ` U" and finA': "finite A'" and a': "a' : A' \<rightarrow> UNIV"
          and xa'A': "x = lincomb (n+m) a' A'"
        unfolding NM.span_def by auto
      then obtain A where finA: "finite A" and AU: "A \<subseteq> U" and A'A: "A' = pad ` A"
        using finite_subset_image[OF finA' A'U] by auto
      hence A: "A \<subseteq> carrier_vec n" using U by auto
      have A': "A' \<subseteq> carrier_vec (n+m)" using A'U pU by auto
      define a where "a = a' o pad"
      define a'' where "a'' = (a' o pad) o unpad"
      have a: "a : A \<rightarrow> UNIV" by auto
      have restr: "restrict a' A' = restrict a'' A'"
      proof(rule restrict_ext)
        fix u' assume "u' : A'"
        then obtain u where "u : A" and "u' = pad u" unfolding A'A by auto
        thus "a' u' = a'' u'" unfolding a''_def a_def by auto
      qed
      have "x = lincomb (n+m) a' A'" using xa'A' unfolding A'A.
      also have "... = lincomb (n+m) a'' A'"
        apply (subst NM.lincomb_restrict)
        using finA' A' restr by (auto simp: module_vec_simps class_ring_simps)
      also have "... = lincomb (n+m) a'' (pad ` A)" unfolding A'A..
      also have "... = pad (lincomb n a A)"
        unfolding a''_def using main[OF AU finA] unfolding a_def by auto
      finally show "x : pad ` (span n U)" unfolding N.span_def
      apply(rule image_eqI, intro CollectI exI conjI)
        using finA AU by (auto simp: class_ring_simps)
    qed
  }
  note main = this
  have AUC: "\<And>A. A \<subseteq> U \<Longrightarrow> A \<subseteq> carrier_vec n" using U by simp
  have [simp]: "n+m = m+n" by auto
  show "goal padr m" unfolding goal_def
    apply (subst main[OF _ _ padr_image[OF U]])
    using lincomb_pad[OF AUC] unpadr_padr by auto
  show "goal padl m" unfolding goal_def
    apply (subst main)
    using lincomb_pad[OF AUC] unpadl_padl padl_image[OF U] by auto
qed

lemma kernel_padr:
  assumes aA: "a : mat_kernel (A :: 'a :: field mat)"
      and A: "A : carrier_mat nr1 nc1"
      and B: "B : carrier_mat nr1 nc2"
      and D: "D : carrier_mat nr2 nc2"
  shows "padr nc2 a : mat_kernel (four_block_mat A B (0\<^sub>m nr2 nc1) D)" (is "_ : mat_kernel ?ABCD")
  unfolding mat_kernel_def
proof (rule, intro conjI)
  have [simp]: "dim_row A = nr1" "dim_row D = nr2" "dim_row ?ABCD = nr1 + nr2" using A D by auto
  have a: "a : carrier_vec nc1" using mat_kernel_carrier[OF A] aA by auto
  show "?ABCD *\<^sub>v padr nc2 a = 0\<^sub>v (dim_row ?ABCD)" (is "?l = ?r")
  proof
    fix i assume i: "i < dim_vec ?r"
    hence "?l $ i = row ?ABCD i \<bullet> padr nc2 a" by auto
    also have "... = 0"
    proof (cases "i < nr1")
      case True
        hence rows: "row A i : carrier_vec nc1" "row B i : carrier_vec nc2"
          using A B by auto
        have "row ?ABCD i = row A i @\<^sub>v row B i"
          using row_four_block_mat(1)[OF A B _ D True] by auto
        also have "... \<bullet> padr nc2 a = row A i \<bullet> a + row B i \<bullet> 0\<^sub>v nc2"
          using scalar_prod_append[OF rows] a by auto
        also have "row A i \<bullet> a = (A *\<^sub>v a) $ i" using True A by auto
        also have "... = 0" using mat_kernelD[OF A aA] True by auto
        also have "row B i \<bullet> 0\<^sub>v nc2 = 0" using True rows by auto
        finally show ?thesis by simp
      next case False
        let ?C = "0\<^sub>m nr2 nc1"
        let ?i = "i - nr1"
        have rows:
            "row ?C ?i : carrier_vec nc1" "row D ?i : carrier_vec nc2"
          using D i False A by auto
        have "row ?ABCD i = row ?C ?i @\<^sub>v row D ?i"
          using row_four_block_mat(2)[OF A B _ D False] i A D by auto
        also have "... \<bullet> padr nc2 a = row ?C ?i \<bullet> a + row D ?i \<bullet> 0\<^sub>v nc2"
          using scalar_prod_append[OF rows] a by auto
        also have "row ?C ?i \<bullet> a = 0\<^sub>v nc1 \<bullet> a" using False A i by auto
        also have "... = 0" using a by auto
        also have "row D ?i \<bullet> 0\<^sub>v nc2 = 0" using False rows by auto
        finally show ?thesis by simp
    qed
    finally show "?l $ i = ?r $ i" using i by auto
  qed auto
  show "padr nc2 a : carrier_vec (dim_col ?ABCD)" using a A D by auto
qed

lemma kernel_padl:
  assumes dD: "d \<in> mat_kernel (D :: 'a :: field mat)"
      and A: "A \<in> carrier_mat nr1 nc1"
      and C: "C \<in> carrier_mat nr2 nc1"
      and D: "D \<in> carrier_mat nr2 nc2"
  shows "padl nc1 d \<in> mat_kernel (four_block_mat A (0\<^sub>m nr1 nc2) C D)" (is "_ \<in> mat_kernel ?ABCD")
  unfolding mat_kernel_def
proof (rule, intro conjI)
  have [simp]: "dim_row A = nr1" "dim_row D = nr2" "dim_row ?ABCD = nr1 + nr2" using A D by auto
  have d: "d : carrier_vec nc2" using mat_kernel_carrier[OF D] dD by auto
  show "?ABCD *\<^sub>v padl nc1 d = 0\<^sub>v (dim_row ?ABCD)" (is "?l = ?r")
  proof
    fix i assume i: "i < dim_vec ?r"
    hence "?l $ i = row ?ABCD i \<bullet> padl nc1 d" by auto
    also have "... = 0"
    proof (cases "i < nr1")
      case True
        let ?B = "0\<^sub>m nr1 nc2"
        have rows: "row A i : carrier_vec nc1" "row ?B i : carrier_vec nc2"
          using A True by auto
        have "row ?ABCD i = row A i @\<^sub>v row ?B i"
          using row_four_block_mat(1)[OF A _ C D True] by auto
        also have "... \<bullet> padl nc1 d = row A i \<bullet> 0\<^sub>v nc1 + row ?B i \<bullet> d"
          using scalar_prod_append[OF rows] d by auto
        also have "row A i \<bullet> 0\<^sub>v nc1 = 0" using A True by auto
        also have "row ?B i \<bullet> d = 0" using True d by auto
        finally show ?thesis by simp
      next case False
        let ?i = "i - nr1"
        have rows:
            "row C ?i : carrier_vec nc1" "row D ?i : carrier_vec nc2"
          using C D i False A by auto
        have "row ?ABCD i = row C ?i @\<^sub>v row D ?i"
          using row_four_block_mat(2)[OF A _ C D False] i A D by auto
        also have "... \<bullet> padl nc1 d = row C ?i \<bullet> 0\<^sub>v nc1 + row D ?i \<bullet> d"
          using scalar_prod_append[OF rows] d by auto
        also have "row C ?i \<bullet> 0\<^sub>v nc1 = 0" using False A C i by auto
        also have "row D ?i \<bullet> d = (D *\<^sub>v d) $ ?i" using D d False i by auto
        also have "... = 0" using mat_kernelD[OF D dD] using False i by auto
        finally show ?thesis by simp
    qed
    finally show "?l $ i = ?r $ i" using i by auto
  qed auto
  show "padl nc1 d : carrier_vec (dim_col ?ABCD)" using d A D by auto
qed

lemma mat_kernel_split:
  assumes A: "A \<in> carrier_mat n n"
      and D: "D \<in> carrier_mat m m"
      and kAD: "k \<in> mat_kernel (four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) D)"
           (is "_ \<in> mat_kernel ?A00D")
  shows "vec_first k n \<in> mat_kernel A" (is "?a \<in> _")
    and "vec_last k m \<in> mat_kernel D" (is "?d \<in> _")
proof -
  have "0\<^sub>v n @\<^sub>v 0\<^sub>v m = 0\<^sub>v (n+m)" by auto
  also
    have A00D: "?A00D : carrier_mat (n+m) (n+m)" using four_block_carrier_mat[OF A D].
    hence k: "k : carrier_vec (n+m)" using kAD mat_kernel_carrier by auto
    hence "?a @\<^sub>v ?d = k" by simp
    hence "0\<^sub>v (n+m) = ?A00D *\<^sub>v (?a @\<^sub>v ?d)" using mat_kernelD[OF A00D] kAD by auto
  also have "... = A *\<^sub>v ?a @\<^sub>v D *\<^sub>v ?d"
    using mult_mat_vec_split[OF A D] by auto
  finally have "0\<^sub>v n @\<^sub>v 0\<^sub>v m = A *\<^sub>v ?a @\<^sub>v D *\<^sub>v ?d".
  hence "0\<^sub>v n = A *\<^sub>v ?a \<and> 0\<^sub>v m = D *\<^sub>v ?d"
    apply(subst append_vec_eq[of _ n, symmetric]) using A D by auto
  thus "?a : mat_kernel A" "?d : mat_kernel D" unfolding mat_kernel_def using A D by auto
qed

lemma padr_padl_eq:
  assumes v: "v : carrier_vec n"
  shows "padr m v = padl n u \<longleftrightarrow> v = 0\<^sub>v n \<and> u = 0\<^sub>v m"
  apply (subst append_vec_eq) using v by auto


lemma pad_disjoint:
  assumes A: "A \<subseteq> carrier_vec n" and A0: "0\<^sub>v n \<notin> A" and B: "B \<subseteq> carrier_vec m"
  shows "padr m ` A \<inter> padl n ` B = {}" (is "?A \<inter> ?B = _")
proof (intro equals0I)
  fix ab assume "ab : ?A \<inter> ?B"
  then obtain a b
    where "ab = padr m a" "ab = padl n b" and dim: "a : A" "b : B" by force
  hence "padr m a = padl n b" by auto
  hence "a = 0\<^sub>v n" using dim A B by auto
  thus "False" using dim A0 by auto
qed

lemma padr_padl_lindep:
  assumes A: "A \<subseteq> carrier_vec n" and liA: "~ lin_dep n A"
      and B: "B \<subseteq> carrier_vec m" and liB: "~ lin_dep m B"
  shows "~ lin_dep (n+m) (padr m ` A \<union> padl n ` B)" (is "~ lin_dep _ (?A \<union> ?B)")
proof -
  interpret N: vectorspace class_ring "M n" using vec_vs.
  interpret M: vectorspace class_ring "M m" using vec_vs.
  interpret NM: vectorspace class_ring "M (n+m)" using vec_vs.
  note [simp] = module_vec_simps class_ring_simps
  have AB: "?A \<union> ?B \<subseteq> carrier_vec (n+m)"
    using padr_image[OF A] padl_image[OF B] by auto
  show ?thesis
    unfolding NM.lin_dep_def
    unfolding not_ex not_imp[symmetric] not_not
  proof(intro allI impI)
    fix U f u
    assume finU: "finite U"
       and UAB: "U \<subseteq> ?A \<union> ?B"
       and f: "f : U \<rightarrow> carrier class_ring"
       and 0: "lincomb (n+m) f U = \<zero>\<^bsub>M (n+m)\<^esub>"
       and uU: "u : U"
    let ?UA = "U \<inter> ?A" and ?UB = "U \<inter> ?B"
    have "?UA \<subseteq> ?A" "?UB \<subseteq> ?B" by auto
    then obtain A' B'
      where A'A: "A' \<subseteq> A" and B'B: "B' \<subseteq> B"
        and UAA': "?UA = padr m ` A'" and UBB': "?UB = padl n ` B'"
      unfolding subset_image_iff by auto
    hence A': "A' \<subseteq> carrier_vec n" and B': "B' \<subseteq> carrier_vec m" using A B by auto
    have finA': "finite A'" and finB': "finite B'"
    proof -
      have "padr m ` A' \<subseteq> U" "padl n ` B' \<subseteq> U" using UAA' UBB' by auto
      hence pre: "finite (padr m ` A')" "finite (padl n ` B')"
        using finite_subset[OF _ finU] by auto
      show "finite A'"
        apply (rule finite_imageD) using subset_inj_on[OF padr_inj A'] pre by auto
      show "finite B'"
        apply (rule finite_imageD) using subset_inj_on[OF padl_inj B'] pre by auto
    qed
    have "0\<^sub>v n \<notin> A" using N.zero_nin_lin_indpt[OF _ liA] A class_semiring.one_zeroI by auto
    hence "?A \<inter> ?B = {}" using pad_disjoint A B by auto
    hence disj: "?UA \<inter> ?UB = {}" by auto
    have split: "U = padr m ` A' \<union> padl n ` B'"
      unfolding UAA'[symmetric] UBB'[symmetric] using UAB by auto
    show "f u = \<zero>\<^bsub>(class_ring::'a ring)\<^esub>"
    proof -
      let ?a = "f \<circ> padr m"
      let ?b = "f \<circ> padl n"
      have lcA': "lincomb n ?a A' : carrier_vec n" using N.lincomb_closed A' by auto
      have lcB': "lincomb m ?b B' : carrier_vec m" using M.lincomb_closed B' by auto
  
      have "0\<^sub>v n @\<^sub>v 0\<^sub>v m = 0\<^sub>v (n+m)" by auto
      also have "... = lincomb (n+m) f U" using 0 by auto
      also have "U = ?UA \<union> ?UB" using UAB by auto
      also have "lincomb (n+m) f ... = lincomb (n+m) f ?UA + lincomb (n+m) f ?UB"
        apply(subst NM.lincomb_union) using A B finU disj by auto
      also have "lincomb (n+m) f ?UA = lincomb (n+m) (restrict f ?UA) ?UA"
        apply (subst NM.lincomb_restrict) using A finU by auto
      also have "restrict f ?UA = restrict (?a \<circ> unpadr m) ?UA"
        apply(rule restrict_ext) by auto
      also have "lincomb (n+m) ... ?UA = lincomb (n+m) (?a \<circ> unpadr m) ?UA"
        apply(subst NM.lincomb_restrict) using A finU by auto
      also have "?UA = padr m ` A'" using UAA'.
      also have "lincomb (n+m) (?a \<circ> unpadr m) ... =
        padr m (lincomb n ?a A')"
        using lincomb_pad(1)[OF A' finA',symmetric].
      also have "lincomb (n+m) f ?UB = lincomb (n+m) (restrict f ?UB) ?UB"
        apply (subst NM.lincomb_restrict) using B finU by auto
      also have "restrict f ?UB = restrict (?b \<circ> unpadl n) ?UB"
        apply(rule restrict_ext) by auto
      also have "lincomb (n+m) ... ?UB = lincomb (n+m) (?b \<circ> unpadl n) ?UB"
        apply(subst NM.lincomb_restrict) using B finU by auto
      also have "n+m = m+n" by auto
      also have "?UB = padl n ` B'" using UBB'.
      also have "lincomb (m+n) (?b \<circ> unpadl n) ... =
        padl n (lincomb m ?b B')"
        using lincomb_pad(2)[OF B' finB',symmetric].
      also have "padr m (lincomb n ?a A') + ... =
          (lincomb n ?a A' + 0\<^sub>v n) @\<^sub>v (0\<^sub>v m + lincomb m ?b B')"
        apply (rule append_vec_add) using lcA' lcB' by auto
      also have "... = lincomb n ?a A' @\<^sub>v lincomb m ?b B'" using lcA' lcB' by auto
      finally have "0\<^sub>v n @\<^sub>v 0\<^sub>v m = lincomb n ?a A' @\<^sub>v lincomb m ?b B'".
      hence "0\<^sub>v n = lincomb n ?a A' \<and> 0\<^sub>v m = lincomb m ?b B'"
        apply(subst append_vec_eq[symmetric]) using lcA' lcB' by auto
      from conjunct1[OF this] conjunct2[OF this]
      have "?a : A' \<rightarrow> {0}" "?b : B' \<rightarrow> {0}"
        using N.not_lindepD[OF liA finA' A'A]
        using M.not_lindepD[OF liB finB' B'B] by auto
      hence "f : padr m ` A' \<rightarrow> {0}" "f : padl n ` B' \<rightarrow> {0}" by auto
      hence "f : padr m ` A' \<union> padl n ` B' \<rightarrow> {0}" by auto
      hence "f : U \<rightarrow> {0}" using split by auto
      hence "f u = 0" using uU by auto
      thus ?thesis by simp
    qed
  qed
qed

end

lemma kernel_four_block_0_mat:
  assumes Adef: "(A :: 'a::field mat) = four_block_mat B (0\<^sub>m n m) (0\<^sub>m m n) D"
  and B: "B \<in> carrier_mat n n"
  and D: "D \<in> carrier_mat m m"
  shows "kernel.dim (n + m) A = kernel.dim n B + kernel.dim m D"
proof -
  have [simp]: "n + m = m + n" by auto
  have A: "A \<in> carrier_mat (n+m) (n+m)"
    using Adef four_block_carrier_mat[OF B D] by auto
  interpret vardim "TYPE('a)".
  interpret MN: vectorspace class_ring "M (n+m)" using vec_vs.
  interpret KA: kernel "n+m" "n+m" A by (unfold_locales, rule A)
  interpret KB: kernel n n B by (unfold_locales, rule B)
  interpret KD: kernel m m D by (unfold_locales, rule D)

  note [simp] = module_vec_simps

  from kernel_basis_exists[OF B]
    obtain baseB where fin_bB: "finite baseB" and bB: "KB.basis baseB" by blast
  hence bBkB: "baseB \<subseteq> mat_kernel B" unfolding KB.Ker.basis_def by auto
  hence bBc: "baseB \<subseteq> carrier_vec n" using mat_kernel_carrier[OF B] by auto
  have bB0: "0\<^sub>v n \<notin> baseB"
    using bB unfolding KB.Ker.basis_def
    using KB.Ker.vs_zero_lin_dep[OF bBkB] by auto
  have bBkA: "padr m ` baseB \<subseteq> mat_kernel A"
  proof
    fix a assume "a : padr m ` baseB"
    then obtain b where ab: "a = padr m b" and "b : baseB" by auto
    hence "b : mat_kernel B" using bB unfolding KB.Ker.basis_def by auto
    hence "padr m b : mat_kernel A"
      unfolding Adef using kernel_padr[OF _ B _ D] by auto
    thus "a : mat_kernel A" using ab by auto
  qed
  from kernel_basis_exists[OF D]
    obtain baseD where fin_bD: "finite baseD" and bD: "KD.basis baseD" by blast
  hence bDkD: "baseD \<subseteq> mat_kernel D" unfolding KD.Ker.basis_def by auto
  hence bDc: "baseD \<subseteq> carrier_vec m" using mat_kernel_carrier[OF D] by auto
  have bDkA: "padl n ` baseD \<subseteq> mat_kernel A"
  proof
    fix a assume "a : padl n ` baseD"
    then obtain d where ad: "a = padl n d" and "d : baseD" by auto
    hence "d : mat_kernel D" using bD unfolding KD.Ker.basis_def by auto
    hence "padl n d : mat_kernel A"
      unfolding Adef using kernel_padl[OF _ B _ D] by auto
    thus "a : mat_kernel A" using ad by auto
  qed
  let ?BD = "(padr m ` baseB \<union> padl n ` baseD)"
  have finBD: "finite ?BD" using fin_bB fin_bD by auto
  have "KA.basis  ?BD"
    unfolding KA.Ker.basis_def
  proof (intro conjI Set.equalityI)
    show BDk: "?BD \<subseteq> mat_kernel A" using bBkA bDkA by auto
    also have "mat_kernel A \<subseteq> carrier_vec (m+n)" using mat_kernel_carrier A by auto
    finally have BD: "?BD \<subseteq> carrier (M (n + m))" by auto
    show "mat_kernel A \<subseteq> KA.Ker.span ?BD"
      unfolding KA.span_same[OF BDk]
    proof
      have BD: "?BD \<subseteq> carrier_vec (n+m)" (is "_ \<subseteq> ?R")
      proof(rule)
        fix v assume "v : ?BD"
        moreover
        { assume "v : padr m ` baseB"
          then obtain b where "b : baseB" and vb: "v = padr m b" by auto
          hence "b : carrier_vec n" using bBc by auto
          hence "v : ?R" unfolding vb apply(subst append_carrier_vec) by auto
        }
        moreover
        { assume "v : padl n ` baseD"
          then obtain d where "d : baseD" and vd: "v = padl n d" by auto
          hence "d : carrier_vec m" using bDc by auto
          hence "v : ?R" unfolding vd apply(subst append_carrier_vec) by auto
        }
        ultimately show "v: ?R" by auto
      qed
      fix a assume a: "a : mat_kernel A"
      hence "a : carrier_vec (n+m)" using a mat_kernel_carrier[OF A] by auto
      hence "a = vec_first a n @\<^sub>v vec_last a m" (is "_ = ?b @\<^sub>v ?d") by simp
      also have "... = padr m ?b + padl n ?d" by auto
      finally have 1: "a = padr m ?b + padl n ?d".
  
      have subkernel: "?b : mat_kernel B" "?d : mat_kernel D"
        using mat_kernel_split[OF B D] a Adef by auto
      hence "?b : span n baseB"
        using bB unfolding KB.Ker.basis_def using KB.span_same by auto
      hence "padr m ?b : padr m ` span n baseB" by auto
      also have "padr m ` span n baseB = span (n+m) (padr m ` baseB)"
        using span_pad[OF bBc] by auto
      also have "... \<subseteq> span (n+m) ?BD" using MN.span_is_monotone by auto
      finally have 2: "padr m ?b : span (n+m) ?BD".
      have "?d : span m baseD"
        using subkernel bD unfolding KD.Ker.basis_def using KD.span_same by auto
      hence "padl n ?d : padl n ` span m baseD" by auto
      also have "padl n ` span m baseD = span (n+m) (padl n ` baseD)"
        using span_pad[OF bDc] by auto
      also have "... \<subseteq> span (n+m) ?BD" using MN.span_is_monotone by auto
      finally have 3: "padl n ?d : span (n+m) ?BD".
  
      have "padr m ?b + padl n ?d : span (n+m) ?BD"
        using MN.span_add1[OF _ 2 3] BD by auto
      thus "a \<in> span (n+m) ?BD" using 1 by auto
    qed
    show "KA.Ker.span ?BD \<subseteq> mat_kernel A" using KA.Ker.span_closed[OF BDk] by auto
    have li: "~ lin_dep n baseB" "~ lin_dep m baseD"
      using bB[unfolded KB.Ker.basis_def]
      unfolding KB.lindep_same[OF bBkB]
      using bD[unfolded KD.Ker.basis_def]
      unfolding KD.lindep_same[OF bDkD] by auto
    show "~ KA.Ker.lin_dep ?BD"
      unfolding KA.lindep_same[OF BDk]
      apply(rule padr_padl_lindep) using bBc bDc li by auto
  qed
  hence "KA.dim = card ?BD" using KA.Ker.dim_basis[OF finBD] by auto
  also have "card ?BD = card (padr m ` baseB) + card (padl n ` baseD)"
    apply(rule card_Un_disjoint)
    using pad_disjoint[OF bBc bB0 bDc] fin_bB fin_bD by auto
  also have "... = card baseB + card baseD"
    using card_image[OF subset_inj_on[OF padr_inj]]
    using card_image[OF subset_inj_on[OF padl_inj]] bBc bDc by auto
  also have "card baseB = KB.dim" using KB.Ker.dim_basis[OF fin_bB] bB by auto
  also have "card baseD = KD.dim" using KD.Ker.dim_basis[OF fin_bD] bD by auto
  finally show ?thesis.

qed

lemma similar_mat_wit_kernel_dim: assumes A: "A \<in> carrier_mat n n"
  and wit: "similar_mat_wit A B P Q"
  shows "kernel.dim n A = kernel.dim n B"
proof -
  from similar_mat_witD2[OF A wit]
  have QP: "Q * P = 1\<^sub>m n" and AB: "A = P * B * Q" and 
    A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and P: "P \<in> carrier_mat n n" and Q: "Q \<in> carrier_mat n n" by auto
  from P B have PB: "P * B \<in> carrier_mat n n" by auto
  show ?thesis unfolding AB mat_kernel_dim_mult_eq_right[OF PB Q P QP] mat_kernel_mult_eq[OF B P Q QP]
    by simp
qed


end
