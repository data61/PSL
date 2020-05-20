section \<open>Matrix limits\<close>

theory Matrix_Limit
  imports Complex_Matrix
begin

subsection \<open>Definition of limit of matrices\<close>

definition limit_mat :: "(nat \<Rightarrow> complex mat) \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> bool" where
  "limit_mat X A m \<longleftrightarrow> (\<forall> n. X n \<in> carrier_mat m m \<and> A \<in> carrier_mat m m \<and>
                       (\<forall> i < m. \<forall> j < m. (\<lambda> n. (X n) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))))"

lemma limit_mat_unique:
  assumes limA: "limit_mat X A m" and limB: "limit_mat X B m"
  shows "A = B"
proof -
  have dim: "A \<in> carrier_mat m m" "B \<in> carrier_mat m m" using limA limB limit_mat_def by auto
  {
    fix i j assume i: "i < m" and j: "j < m"
    have "(\<lambda> n. (X n) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))" using limit_mat_def limA i j by auto
    moreover have "(\<lambda> n. (X n) $$ (i, j)) \<longlonglongrightarrow> (B $$ (i, j))" using limit_mat_def limB i j by auto
    ultimately have "(A $$ (i, j)) = (B $$ (i, j))" using LIMSEQ_unique by auto
  }
  then show "A = B" using mat_eq_iff dim by auto
qed

lemma limit_mat_const:
  fixes A :: "complex mat"
  assumes "A \<in> carrier_mat m m"
  shows "limit_mat (\<lambda>k. A) A m"
  unfolding limit_mat_def using assms by auto

lemma limit_mat_scale:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat"
  assumes limX: "limit_mat X A m"
  shows "limit_mat (\<lambda>n. c \<cdot>\<^sub>m X n) (c \<cdot>\<^sub>m A) m"
proof -
  have dimA: "A \<in> carrier_mat m m" using limX limit_mat_def by auto
  have dimX: "\<And>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have "\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> (\<lambda>n. (c \<cdot>\<^sub>m X n) $$ (i, j)) \<longlonglongrightarrow> (c \<cdot>\<^sub>m A) $$ (i, j)"
  proof -
    fix i j assume i: "i < m" and j: "j < m"
    have "(\<lambda>n. (X n) $$ (i, j)) \<longlonglongrightarrow> A$$(i, j)" using limX limit_mat_def i j by auto
    moreover have "(\<lambda>n. c) \<longlonglongrightarrow> c" by auto
    ultimately have "(\<lambda>n. c * (X n) $$ (i, j)) \<longlonglongrightarrow> c * A$$(i, j)"
      using tendsto_mult[of "\<lambda>n. c" c] limX limit_mat_def by auto
    moreover have "(c \<cdot>\<^sub>m X n) $$ (i, j) = c * (X n) $$ (i, j)" for n
      using index_smult_mat(1)[of i "X n" j c] i j dimX[of n] by auto
    moreover have "(c \<cdot>\<^sub>m A) $$ (i, j) = c * A $$ (i, j)"
      using index_smult_mat(1)[of i "A" j c] i j dimA by auto
    ultimately show "(\<lambda>n. (c \<cdot>\<^sub>m X n) $$ (i, j)) \<longlonglongrightarrow> (c \<cdot>\<^sub>m A) $$ (i, j)" by auto
  qed
  then show ?thesis unfolding limit_mat_def using dimA dimX by auto
qed

lemma limit_mat_add:
  fixes X :: "nat \<Rightarrow> complex mat" and Y :: "nat \<Rightarrow> complex mat" and A :: "complex mat"
    and m :: nat and B :: "complex mat"
  assumes limX: "limit_mat X A m" and limY: "limit_mat Y B m"
  shows "limit_mat (\<lambda>k. X k + Y k) (A + B) m"
proof -
  have dimA: "A \<in> carrier_mat m m" using limX limit_mat_def by auto
  have dimB: "B \<in> carrier_mat m m" using limY limit_mat_def by auto
  have dimX: "\<And>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have dimY: "\<And>n. Y n \<in> carrier_mat m m" using limY unfolding limit_mat_def by auto
  then have dimXAB: "\<forall>n. X n + Y n \<in> carrier_mat m m \<and> A + B \<in> carrier_mat m m" using dimA dimB dimX dimY
    by (simp)

  have "(\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> (\<lambda>n. (X n + Y n) $$ (i, j)) \<longlonglongrightarrow> (A + B) $$ (i, j))"
  proof -
    fix i j assume i: "i < m" and j: "j < m"
    have "(\<lambda>n. (X n) $$ (i, j)) \<longlonglongrightarrow> A$$(i, j)" using limX limit_mat_def i j by auto
    moreover have "(\<lambda>n. (Y n) $$ (i, j)) \<longlonglongrightarrow> B$$(i, j)" using limY limit_mat_def i j by auto
    ultimately have "(\<lambda>n. (X n)$$(i, j) + (Y n) $$ (i, j)) \<longlonglongrightarrow> (A$$(i, j) + B$$(i, j))"
      using tendsto_add[of "\<lambda>n. (X n) $$ (i, j)" "A $$ (i, j)"] by auto
    moreover have "(X n + Y n) $$ (i, j) = (X n)$$(i, j) + (Y n) $$ (i, j)" for n
      using i j dimX dimY index_add_mat(1)[of i "Y n" j "X n"] by fastforce
    moreover have "(A + B) $$ (i, j) = A$$(i, j) + B$$(i, j)"
      using i j dimA dimB by fastforce
    ultimately show "(\<lambda>n. (X n + Y n) $$ (i, j)) \<longlonglongrightarrow> (A + B) $$ (i, j)" by auto
  qed
  then show ?thesis
    unfolding limit_mat_def using dimXAB by auto
qed

lemma limit_mat_minus:
  fixes X :: "nat \<Rightarrow> complex mat" and Y :: "nat \<Rightarrow> complex mat" and A :: "complex mat"
    and m :: nat and B :: "complex mat"
  assumes limX: "limit_mat X A m" and limY: "limit_mat Y B m"
  shows "limit_mat (\<lambda>k. X k - Y k) (A - B) m"
proof -
  have dimA: "A \<in> carrier_mat m m" using limX limit_mat_def by auto
  have dimB: "B \<in> carrier_mat m m" using limY limit_mat_def by auto
  have dimX: "\<And>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have dimY: "\<And>n. Y n \<in> carrier_mat m m" using limY unfolding limit_mat_def by auto
  have "-1 \<cdot>\<^sub>m Y n = - Y n" for n using dimY by auto
  moreover have "-1 \<cdot>\<^sub>m B = - B" using dimB by auto
  ultimately have "limit_mat (\<lambda>n. - Y n) (- B) m" using limit_mat_scale[OF limY, of "-1"] by auto
  then have "limit_mat (\<lambda>n. X n + (- Y n)) (A + (- B)) m" using limit_mat_add limX by auto
  moreover have "X n + (- Y n) = X n - Y n" for n using dimX dimY by auto
  moreover have "A + (- B) = A - B" by auto
  ultimately show ?thesis by auto
qed

lemma limit_mat_mult:
  fixes X :: "nat \<Rightarrow> complex mat" and Y :: "nat \<Rightarrow> complex mat" and A :: "complex mat"
    and m :: nat and B :: "complex mat"
  assumes limX: "limit_mat X A m" and limY: "limit_mat Y B m"
  shows "limit_mat (\<lambda>k. X k * Y k) (A * B) m"
proof -
  have dimA: "A \<in> carrier_mat m m" using limX limit_mat_def by auto
  have dimB: "B \<in> carrier_mat m m" using limY limit_mat_def by auto
  have dimX: "\<And>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have dimY: "\<And>n. Y n \<in> carrier_mat m m" using limY unfolding limit_mat_def by auto
  then have dimXAB: "\<forall>n. X n * Y n \<in> carrier_mat m m \<and> A * B \<in> carrier_mat m m" using dimA dimB dimX dimY
    by fastforce

  have "(\<And>i j. i < m \<Longrightarrow> j < m \<Longrightarrow> (\<lambda>n. (X n * Y n) $$ (i, j)) \<longlonglongrightarrow> (A * B) $$ (i, j))"
  proof -
    fix i j assume i: "i < m" and j: "j < m"
    have eqn: "(X n * Y n) $$ (i, j) = (\<Sum>k=0..<m. (X n)$$(i, k) * (Y n)$$(k, j))" for n
      using i j dimX[of n] dimY[of n] by (auto simp add: scalar_prod_def)
    have eq: "(A * B) $$ (i, j) = (\<Sum>k=0..<m. A$$(i,k) * B$$(k,j))"
      using i j dimB dimA by (auto simp add: scalar_prod_def)
    have "(\<lambda>n. (X n) $$ (i, k)) \<longlonglongrightarrow> A$$(i, k)" if "k < m" for k using limX limit_mat_def that i by auto
    moreover have "(\<lambda>n. (Y n) $$ (k, j)) \<longlonglongrightarrow> B$$(k, j)" if "k < m" for k using limY limit_mat_def that j by auto
    ultimately have "(\<lambda>n. (X n)$$(i, k) * (Y n)$$(k,j)) \<longlonglongrightarrow> A$$(i, k) * B$$(k, j)" if "k < m" for k
      using tendsto_mult[of "\<lambda>n. (X n) $$ (i, k)" "A$$(i, k)" _ "\<lambda>n. (Y n)$$(k, j)" "B$$(k, j)"] that by auto
    then have "(\<lambda>n. (\<Sum>k=0..<m. (X n)$$(i,k) * (Y n)$$(k,j))) \<longlonglongrightarrow> (\<Sum>k=0..<m. A$$(i,k) * B$$(k,j))"
      using tendsto_sum[of "{0..<m}" "\<lambda>k n. (X n)$$(i,k) * (Y n)$$(k,j)" "\<lambda>k. A$$(i, k) * B$$(k, j)"] by auto
    then show "(\<lambda>n. (X n * Y n) $$ (i, j)) \<longlonglongrightarrow> (A * B) $$ (i, j)" using eqn eq by auto
  qed
  then show ?thesis
    unfolding limit_mat_def using dimXAB by fastforce
qed

text \<open>Adding matrix A to the sequence X\<close>
definition mat_add_seq ::  "complex mat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> nat \<Rightarrow> complex mat" where
  "mat_add_seq A X = (\<lambda>n. A + X n)"

lemma mat_add_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat and B :: "complex mat"
  assumes dimB: "B \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (mat_add_seq B X) (B + A) m"
  unfolding mat_add_seq_def using limit_mat_add limit_mat_const[OF dimB] limX by auto

lemma mat_minus_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat and B :: "complex mat"
  assumes dimB: "B \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (\<lambda>n. B - X n) (B - A) m"
  using limit_mat_minus limit_mat_const[OF dimB] limX by auto

text \<open>Multiply matrix A by the sequence X\<close>
definition mat_mult_seq ::  "complex mat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> nat \<Rightarrow> complex mat" where
  "mat_mult_seq A X = (\<lambda>n. A * X n)"

lemma mat_mult_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A B :: "complex mat" and m :: nat
  assumes dimB: "B \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (mat_mult_seq B X) (B * A) m"
  unfolding mat_mult_seq_def using limit_mat_mult limit_mat_const[OF dimB] limX by auto

lemma mult_mat_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A B :: "complex mat" and m :: nat
  assumes dimB: "B \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (\<lambda>k. X k * B) (A * B) m"
  unfolding mat_mult_seq_def using limit_mat_mult limit_mat_const[OF dimB] limX by auto

lemma quadratic_form_mat:
  fixes A :: "complex mat" and v :: "complex vec" and m :: nat
  assumes dimv: "dim_vec v = m" and dimA: "A \<in> carrier_mat m m"
  shows "inner_prod v (A *\<^sub>v v) = (\<Sum>i=0..<m. (\<Sum>j=0..<m. conjugate (v$i) * A$$(i, j) * v$j))"
proof -
  have  "inner_prod v (A *\<^sub>v v) = (\<Sum>i=0..<m. (\<Sum>j=0..<m.
                conjugate (v$i) * A$$(i, j) * v$j))"
  unfolding scalar_prod_def using dimv dimA
    apply (simp add: scalar_prod_def sum_distrib_right)
    apply (rule sum.cong, auto, rule sum.cong, auto)
  done
  then show ?thesis by auto
qed

lemma sum_subtractff:
  fixes h g :: "nat \<Rightarrow> nat \<Rightarrow>'a::ab_group_add"
  shows "(\<Sum>x\<in>A. \<Sum>y\<in>B. h x y - g x y) = (\<Sum>x\<in>A. \<Sum>y\<in>B. h x y) - (\<Sum>x\<in>A. \<Sum>y\<in>B. g x y)"
proof -
  have "\<forall> x \<in> A. (\<Sum>y\<in>B. h x y - g x y) = (\<Sum>y\<in>B. h x y) - (\<Sum>y\<in>B. g x y)"
  proof -
    {
      fix x assume x: "x \<in> A"
      have "(\<Sum>y\<in>B. h x y - g x y) = (\<Sum>y\<in>B. h x y) - (\<Sum>y\<in>B. g x y)"
        using sum_subtractf by auto
     }
    then show ?thesis  using sum_subtractf by blast
  qed
  then have "(\<Sum>x\<in>A.\<Sum>y\<in>B. h x y - g x y) = (\<Sum>x\<in>A. ((\<Sum>y\<in>B. h x y) - (\<Sum>y\<in>B. g x y)))" by auto
  also have "\<dots> = (\<Sum>x\<in>A. \<Sum>y\<in>B. h x y) - (\<Sum>x\<in>A. \<Sum>y\<in>B. g x y)"
    by (simp add: sum_subtractf)
  finally have " (\<Sum>x\<in>A. \<Sum>y\<in>B. h x y - g x y) = (\<Sum>x\<in>A. sum (h x) B) - (\<Sum>x\<in>A. sum (g x) B)" by auto
  then show ?thesis by auto
qed

lemma sum_abs_complex:
  fixes h  :: "nat \<Rightarrow> nat \<Rightarrow> complex"
  shows "cmod (\<Sum>x\<in>A.\<Sum>y\<in>B. h x y) \<le> (\<Sum>x\<in>A. \<Sum>y\<in>B. cmod(h x y))"
proof -
  have B: "\<forall> x \<in> A. cmod( \<Sum>y\<in>B .h x y) \<le> (\<Sum>y\<in>B. cmod(h x y))" using sum_abs norm_sum by blast
  have "cmod (\<Sum>x\<in>A.\<Sum>y\<in>B. h x y) \<le> (\<Sum>x\<in>A.  cmod( \<Sum>y\<in>B .h x y))" using sum_abs norm_sum by blast
  also have "\<dots> \<le> (\<Sum>x\<in>A. \<Sum>y\<in>B. cmod(h x y))" using sum_abs norm_sum B
    by (simp add: sum_mono)
  finally have "cmod (\<Sum>x\<in>A. \<Sum>y\<in>B. h x y) \<le> (\<Sum>x\<in>A. \<Sum>y\<in>B. cmod (h x y))" by auto
  then show ?thesis by auto
qed

lemma hermitian_mat_lim_is_hermitian:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat
  assumes limX: "limit_mat X A m" and herX: "\<forall> n. hermitian (X n)"
  shows "hermitian A"
proof -
  have  dimX: "\<forall>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have dimA : "A \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto

  from herX have herXn: "\<forall> n. adjoint (X n) = (X n)" unfolding hermitian_def by auto
  from limX have limXn: "\<forall>i<m. \<forall>j<m. (\<lambda>n. X n $$ (i, j)) \<longlonglongrightarrow> A $$ (i, j)" unfolding limit_mat_def by auto
  have "\<forall>i<m. \<forall>j<m.(adjoint A)$$ (i, j) = A$$ (i, j)"
  proof -
    {
      fix i j assume i: "i < m" and j: "j < m"
      have aij: "(adjoint A)$$ (i, j) = conjugate (A $$ (j,i))" using adjoint_eval i j dimA by blast
      have ij: "(\<lambda>n. X n $$ (i, j)) \<longlonglongrightarrow> A $$ (i, j)" using limXn i j by auto
      have ji: "(\<lambda>n. X n $$ (j, i)) \<longlonglongrightarrow> A $$ (j, i)" using limXn i j by auto
      then have "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (conjugate (X n $$ (j, i))) (conjugate (A $$ (j, i))) < r"
      proof -
        {
          fix r :: real assume r : "r > 0"
          have "\<exists>no. \<forall>n\<ge>no. cmod (X n $$ (j, i) - A $$ (j, i)) < r" using ji r unfolding  LIMSEQ_def dist_norm by auto
          then obtain no where Xji: "\<forall>n\<ge>no. cmod (X n $$ (j, i) - A $$ (j, i)) < r" by auto
          then have "\<forall>n\<ge>no. cmod (conjugate (X n $$ (j, i) - A $$ (j, i))) < r"
            using complex_mod_cnj conjugate_complex_def by presburger
          then have "\<forall>n\<ge>no. dist (conjugate (X n $$ (j, i))) (conjugate (A $$ (j, i))) < r" unfolding dist_norm by auto
          then have "\<exists>no. \<forall>n\<ge>no. dist (conjugate (X n $$ (j, i))) (conjugate (A $$ (j, i))) < r" by auto
        }
        then show ?thesis by auto
      qed
      then have conjX: "(\<lambda>n. conjugate (X n $$ (j, i))) \<longlonglongrightarrow>  conjugate (A $$ (j, i))" unfolding LIMSEQ_def by auto

      from herXn have "\<forall> n. conjugate (X n $$ (j,i)) = X n$$ (i, j)"  using adjoint_eval i j dimX
        by (metis adjoint_dim_col carrier_matD(1))
      then have "(\<lambda>n. X n $$ (i, j)) \<longlonglongrightarrow>  conjugate (A $$ (j, i))" using conjX by auto
      then have "conjugate (A $$ (j,i)) = A$$ (i, j)" using ij by (simp add: LIMSEQ_unique)
      then have "(adjoint A)$$ (i, j) = A$$ (i, j)" using adjoint_eval i j by (simp add:aij)
    }
    then show ?thesis by auto
  qed
  then have "hermitian A" using hermitian_def dimA
    by (metis adjoint_dim carrier_matD(1) carrier_matD(2) eq_matI)
  then show ?thesis by auto
qed

lemma quantifier_change_order_once:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool" and m :: nat
  shows "\<forall>j<m. \<exists>no. \<forall>n\<ge>no. P n j \<Longrightarrow> \<exists>no. \<forall>j<m. \<forall>n\<ge>no. P n j"
proof (induct m)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    then show ?case
    proof -
      have mm: "\<exists>no. \<forall>j<m. \<forall>n\<ge>no. P n j" using Suc by auto
      then obtain M where MM: "\<forall>j<m. \<forall>n\<ge>M. P n j" by auto
      have sucm: "\<exists>no. \<forall>n\<ge>no. P n m" using Suc(2) by auto
      then obtain N where NN: "\<forall>n\<ge>N. P n m" by auto
      let ?N = "max M N"
      from MM NN have "\<forall>j<Suc m. \<forall>n\<ge>?N. P n j"
        by (metis less_antisym max.boundedE)
      then have "\<exists>no. \<forall>j<Suc m. \<forall>n\<ge>no. P n j" by blast
      then show ?thesis by auto
    qed
  qed

lemma quantifier_change_order_twice:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" and m n :: nat
  shows "\<forall>i<m. \<forall>j<n. \<exists> no. \<forall>n\<ge>no. P n i j \<Longrightarrow> \<exists>no. \<forall>i<m. \<forall>j<n. \<forall>n\<ge>no. P n i j"
proof -
  assume fact: "\<forall>i<m. \<forall>j<n. \<exists> no. \<forall>n\<ge>no. P n i j"
  have one: "\<forall>i<m. \<exists>no.\<forall>j<n. \<forall>n\<ge>no. P n i j"
    using fact quantifier_change_order_once by auto
  have two: "\<forall>i<m. \<exists>no.\<forall>j<n. \<forall>n\<ge>no. P n i j \<Longrightarrow> \<exists>no. \<forall>i<m. \<forall>j<n. \<forall>n\<ge>no. P n i j"
  proof (induct m)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    then show ?case
    proof -
      obtain M where MM: "\<forall>i<m. \<forall>j<n. \<forall>n\<ge>M. P n i j" using Suc by auto
      obtain N where NN: "\<forall>j<n. \<forall>n\<ge>N. P n m j" using Suc(2) by blast
      let ?N = "max M N"
      from MM NN have "\<forall>i<Suc m. \<forall>j<n. \<forall>n\<ge>?N. P n i j"
        by (metis less_antisym max.boundedE)
      then have "\<exists>no. \<forall>i<Suc m. \<forall>j<n. \<forall>n\<ge>no. P n i j" by blast
      then show ?thesis by auto
    qed
  qed
  with fact show ?thesis using one by auto
qed

lemma pos_mat_lim_is_pos:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat
  assumes limX: "limit_mat X A m" and posX: "\<forall>n. positive (X n)"
  shows "positive A"
proof (rule ccontr)
  have  dimX : "\<forall>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have dimA : "A \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  have herX : "\<forall> n. hermitian (X n)" using posX positive_is_hermitian by auto
  then have herA : "hermitian A"  using hermitian_mat_lim_is_hermitian limX by auto
  then have herprod: "\<forall> v. dim_vec v = dim_col A \<longrightarrow> inner_prod v (A *\<^sub>v v) \<in> Reals"
    using hermitian_inner_prod_real dimA by auto

  assume npA: " \<not> positive A"
  from npA have "\<not> (A \<in> carrier_mat (dim_col A) (dim_col A)) \<or> \<not> (\<forall>v. dim_vec v = dim_col A \<longrightarrow> 0 \<le> inner_prod v (A *\<^sub>v v))"
    unfolding positive_def by blast
  then have evA: "\<exists> v. dim_vec v = dim_col A \<and> \<not> inner_prod v (A *\<^sub>v v) \<ge> 0" using dimA by blast
  then have "\<exists> v. dim_vec v = dim_col A \<and>  inner_prod v (A *\<^sub>v v) < 0"
  proof -
    obtain v where vA: "dim_vec v = dim_col A \<and> \<not> inner_prod v (A *\<^sub>v v) \<ge> 0" using evA by auto
    from vA herprod have "\<not> 0 \<le> inner_prod v (A *\<^sub>v v) \<and> inner_prod v (A *\<^sub>v v) \<in> Reals" by auto
    then have "inner_prod v (A *\<^sub>v v) < 0"
      using complex_is_Real_iff by auto
    then have  "\<exists> v. dim_vec v = dim_col A \<and>  inner_prod v (A *\<^sub>v v) < 0" using vA by auto
    then show ?thesis by auto
  qed

  then obtain v where neg: "dim_vec v = dim_col A \<and> inner_prod v (A *\<^sub>v v) < 0" by auto

  have   nzero: "v \<noteq> 0\<^sub>v m"
  proof (rule ccontr)
    assume nega: " \<not> v \<noteq> 0\<^sub>v m"
    have zero: "v = 0\<^sub>v m" using nega by auto
    have "(A *\<^sub>v v) = 0\<^sub>v m" unfolding mult_mat_vec_def using zero
      using dimA by auto
    then have zerov: "inner_prod v (A *\<^sub>v v) = 0" by (simp add: zero)
    from neg zerov have "\<not> v \<noteq> 0\<^sub>v m \<Longrightarrow> False"  using dimA by auto
    with nega show False by auto
  qed

  have invgeq: "inner_prod v v > 0"
  proof -
    have "inner_prod v v = vec_norm v * vec_norm v" unfolding vec_norm_def
      by (metis carrier_matD(2) carrier_vec_dim_vec dimA mult_cancel_left1 neg normalized_cscalar_prod normalized_vec_norm nzero vec_norm_def)
    moreover have "vec_norm v > 0" using nzero vec_norm_ge_0 neg dimA
      by (metis carrier_matD(2) carrier_vec_dim_vec)
    ultimately have "inner_prod v v > 0" by auto
    then show ?thesis by auto
  qed

  have invv: "inner_prod v v = (\<Sum>i = 0..<m. cmod (conjugate (v $ i) * (v $ i)))"
  proof -
    {
      have "\<forall> i < m. conjugate (v $ i) * (v $ i) \<ge> 0" using conjugate_square_smaller_0 by simp
      then have vi: "\<forall> i < m. conjugate (v $ i) * (v $ i) = cmod (conjugate (v $ i) * (v $ i))" using cmod_eq_Re
        by (simp add: complex.expand)

      have "inner_prod v v= (\<Sum>i = 0..<m. ((v $ i) * conjugate (v $ i)))"
        unfolding scalar_prod_def conjugate_vec_def using neg dimA by auto
      also have "\<dots> = (\<Sum>i = 0..<m. (conjugate (v $ i) * (v $ i)))"
        by (meson mult.commute)
      also have "\<dots> = (\<Sum>i = 0..<m. cmod (conjugate (v $ i) * (v $ i)))" using vi by auto
      finally have  "inner_prod v v = (\<Sum>i = 0..<m. cmod (conjugate (v $ i) * (v $ i)))" by auto
    }
    then show ?thesis by auto
  qed

  let ?r = "inner_prod v (A *\<^sub>v v)" have rl: "?r < 0" using neg by auto
  have vAv: "inner_prod v (A *\<^sub>v v) =  (\<Sum>i=0..<m. (\<Sum>j=0..<m.
                conjugate (v$i) * A$$(i, j) * v$j))" using quadratic_form_mat dimA neg by auto
  from limX have limij: "\<forall>i<m. \<forall>j<m. (\<lambda>n. X n $$ (i, j)) \<longlonglongrightarrow> A $$ (i, j)" unfolding limit_mat_def by auto
  then have limXv: "(\<lambda> n. inner_prod v ((X n) *\<^sub>v v)) \<longlonglongrightarrow> inner_prod v (A *\<^sub>v v)"
  proof -
    have XAless: "cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) \<le>
      (\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j))" for n
    proof -
      have "\<forall> i < m. \<forall> j < m. conjugate (v$i) * X n $$(i, j) * v$j - conjugate (v$i) * A$$(i, j) * v$j =
        conjugate (v$i) * (X n $$(i, j)-A$$(i, j)) * v$j"
        by (simp add: mult.commute right_diff_distrib)
      then have ele: "\<forall> i < m.(\<Sum>j=0..<m.(conjugate (v$i) * X n $$(i, j) * v$j - conjugate (v$i) * A$$(i, j) * v$j)) = (\<Sum>j=0..<m.(
              conjugate (v$i) * (X n $$(i, j)-A$$(i, j)) * v$j))" by auto
      have "\<forall> i < m. \<forall> j < m. cmod(conjugate (v $ i) * (X n $$ (i, j) - A $$ (i, j)) * v $ j) =
                cmod(conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod(v $ j)"
        by (simp add: norm_mult)
      then have less: "\<forall> i < m.(\<Sum>j = 0..<m. cmod(conjugate (v $ i) * (X n $$ (i, j) - A $$ (i, j)) * v $ j)) =
                (\<Sum>j = 0..<m. cmod(conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod(v $ j))" by auto

      have "inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v) = (\<Sum>i=0..<m. (\<Sum>j=0..<m.
              conjugate (v$i) * X n $$(i, j) * v$j)) - (\<Sum>i=0..<m. (\<Sum>j=0..<m.
              conjugate (v$i) * A$$(i, j) * v$j))"  using quadratic_form_mat neg dimA dimX by auto
      also have "\<dots> = (\<Sum>i=0..<m. (\<Sum>j=0..<m.(
              conjugate (v$i) * X n $$(i, j) * v$j - conjugate (v$i) * A$$(i, j) * v$j)))"
        using sum_subtractff[of "\<lambda> i j. conjugate (v $ i) * X n $$ (i, j) * v $ j" "\<lambda> i j. conjugate (v $ i) * A $$ (i, j) * v $ j" "{0..<m}"] by auto
      also have "\<dots> = (\<Sum>i=0..<m. (\<Sum>j=0..<m.(
              conjugate (v$i) * (X n $$(i, j)-A$$(i, j)) * v$j)))"  using ele by auto
      finally have minusXA: "inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v) = (\<Sum>i = 0..<m. \<Sum>j = 0..<m. conjugate (v $ i) * (X n $$ (i, j) - A $$ (i, j)) * v $ j)" by auto

      from minusXA have "cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) =
              cmod (\<Sum>i = 0..<m. \<Sum>j = 0..<m. conjugate (v $ i) * (X n $$ (i, j) - A $$ (i, j)) * v $ j)" by auto
      also have "\<dots> \<le> (\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod(conjugate (v $ i) * (X n $$ (i, j) - A $$ (i, j)) * v $ j))"
        using sum_abs_complex by simp
      also have "\<dots> = (\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod(conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod(v $ j))"
        using less by auto
      finally show ?thesis by auto
    qed

    from limij have limijm: " \<forall>i<m. \<forall>j<m. \<forall>r>0. \<exists>no. \<forall>n\<ge>no. cmod (X n $$ (i, j) - A $$ (i, j)) < r"
      unfolding LIMSEQ_def dist_norm by auto
    from limX have mg: "m > 0" using limit_mat_def
      by (metis carrier_matD(1) carrier_matD(2) mat_eq_iff neq0_conv not_less0 npA posX)

    have cmoda: "\<exists>no. \<forall>n\<ge>no. (\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)) < r"
      if r: "r > 0" for r
    proof -
      let ?u = "(\<Sum>i = 0..<m. \<Sum>j = 0..<m.((cmod (conjugate (v $ i)) * cmod (v $ j))))"
      have ug: "?u > 0"
      proof -
        have ur: "?u = (\<Sum>i = 0..<m. (cmod (conjugate (v $ i)) * (\<Sum>j = 0..<m.( cmod (v $ j)))))"  by (simp add: sum_distrib_left)
        have "(\<Sum>j = 0..<m.( cmod (v $ j))) \<ge> cmod (v $ i)" if i: "i < m" for i
          using member_le_sum[of i "{0..<m}" "\<lambda> j. cmod (v$j)"] cmod_def i by simp
        then have "\<forall> i < m. (cmod (conjugate (v $ i)) * (\<Sum>j = 0..<m.( cmod (v $ j)))) \<ge> (cmod (conjugate (v $ i)) * cmod (v $ i))"
          by (simp add: mult_left_mono)
        then have "?u \<ge> (\<Sum>i = 0..<m. (cmod (conjugate (v $ i)) *cmod (v $ i)))"
          using ur sum_mono[of "{0..<m}" "\<lambda> i.  cmod (conjugate (v $ i)) * cmod (v $ i)" "\<lambda> i. cmod (conjugate (v $ i)) * (\<Sum>j = 0..<m. cmod (v $ j))"]
          by auto
        moreover have "(\<Sum>i = 0..<m. cmod (conjugate (v $ i)  *cmod (v $ i))) = (\<Sum>i = 0..<m. cmod (conjugate (v $ i) * (v $ i)))"
          using norm_ge_zero norm_mult norm_of_real by (metis (no_types, hide_lams) abs_of_nonneg)
        moreover have "(\<Sum>i = 0..<m. cmod (conjugate (v $ i) * (v $ i))) = inner_prod v v" using invv by auto
        ultimately have "?u \<ge>  inner_prod v v"
          by (metis (no_types, lifting) Im_complex_of_real Re_complex_of_real invv less_eq_complex_def norm_mult sum.cong)
        then have "?u > 0"  using invgeq by auto
        then show ?thesis by auto
      qed

      let ?s = "r / (2 * ?u)"
      have sgz: "?s > 0" using ug rl
        by (smt divide_pos_pos dual_order.strict_iff_order linordered_semiring_strict_class.mult_pos_pos zero_less_norm_iff r)
      from limijm have sij: "\<exists>no. \<forall>n\<ge>no. cmod (X n $$ (i, j) - A $$ (i, j)) < ?s" if i: "i < m" and j: "j < m" for i j
      proof -
        obtain N where Ns: "\<forall>n\<ge>N. cmod (X n $$ (i, j) - A $$ (i, j)) < ?s" using sgz limijm i j by blast
        then show ?thesis by auto
      qed
      then have "\<exists>no. \<forall>i<m. \<forall>j<m. \<forall>n\<ge>no. cmod (X n $$ (i, j) - A $$ (i, j)) < ?s"
        using quantifier_change_order_twice[of m m "\<lambda> n i j. (cmod (X n $$ (i, j) - A $$ (i, j))<?s)"] by auto
      then obtain N where Nno: "\<forall>i<m. \<forall>j<m. \<forall>n\<ge>N. cmod (X n $$ (i, j) - A $$ (i, j)) < ?s" by auto
      then have mmN: "cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)
                       \<le> ?s * (cmod (conjugate (v $ i)) * cmod (v $ j))"
        if i: "i < m" and j: "j < m" and n: "n \<ge> N" for i j n
      proof -
        have geq: "cmod (conjugate (v $ i)) \<ge> 0 \<and> cmod (v $ j)\<ge>0" by simp
        then have "cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) \<le>cmod (conjugate (v $ i)) * ?s" using Nno i j n
          by (smt mult_left_mono)
        then have "cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)
                    \<le> cmod (conjugate (v $ i)) *?s * cmod (v $ j)" using geq mult_right_mono by blast
        also have "\<dots> = ?s * (cmod (conjugate (v $ i)) * cmod (v $ j))" by simp
        finally show ?thesis by auto
      qed
      then have "(\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)) < r"
        if n: "n \<ge> N" for n
      proof -
        have mmX: "\<forall>i<m. \<forall>j<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)
                   \<le> ?s * (cmod (conjugate (v $ i)) * cmod (v $ j))" using n mmN by blast
        have "(\<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j))
                   \<le> (\<Sum>j = 0..<m.(?s * (cmod (conjugate (v $ i)) * cmod (v $ j))))" if i: "i < m" for i
        proof -
          have "\<forall>j<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)
                 \<le> ?s * (cmod (conjugate (v $ i)) * cmod (v $ j))" using mmX i by auto
          then show ?thesis
          using sum_mono[of "{0..<m}" "\<lambda> j. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)" "\<lambda> j. (?s * (cmod (conjugate (v $ i)) * cmod (v $ j)))"]
            atLeastLessThan_iff by blast
        qed
        then have "(\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j))
                  \<le> (\<Sum>i = 0..<m. \<Sum>j = 0..<m.(?s * (cmod (conjugate (v $ i)) * cmod (v $ j))))" using sum_mono atLeastLessThan_iff
          by (metis (no_types, lifting))
        also have "\<dots> = ?s * (\<Sum>i = 0..<m. \<Sum>j = 0..<m.((cmod (conjugate (v $ i)) * cmod (v $ j))))"  by (simp add: sum_distrib_left)
        also have "\<dots> = r / 2" using nonzero_mult_divide_mult_cancel_right sgz by fastforce
        finally show ?thesis using r by auto
      qed
      then show ?thesis by auto
    qed
    then have XnAv:"\<exists>no. \<forall>n\<ge>no. cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < r" if r: "r > 0" for r
    proof -
      obtain no where nno: "\<forall>n\<ge>no. (\<Sum>i = 0..<m. \<Sum>j = 0..<m. cmod (conjugate (v $ i)) * cmod (X n $$ (i, j) - A $$ (i, j)) * cmod (v $ j)) < r"
        using r cmoda neg by auto
      then have "\<forall>n\<ge>no. cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < r" using XAless neg by smt
      then show ?thesis by auto
    qed
    then have "(\<lambda>n. inner_prod v (X n *\<^sub>v v)) \<longlonglongrightarrow> inner_prod v (A *\<^sub>v v)" unfolding LIMSEQ_def dist_norm by auto
    then show ?thesis by auto
  qed

  from limXv have "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < r" unfolding LIMSEQ_def dist_norm by auto
  then have "\<exists>no. \<forall>n\<ge>no. cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < -?r" using rl by auto
  then obtain N where Ng: "\<forall>n\<ge>N. cmod (inner_prod v (X n *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < -?r" by auto
  then have XN: "cmod (inner_prod v (X N *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) < -?r" by auto

  from posX have "positive (X N)" by auto
  then have XNv:"inner_prod v (X N *\<^sub>v v) \<ge> 0"
    by (metis Complex_Matrix.positive_def carrier_matD(2) dimA dimX neg)

  from rl XNv have XX: "cmod (inner_prod v (X N *\<^sub>v v) - inner_prod v (A *\<^sub>v v)) = cmod(inner_prod v (X N *\<^sub>v v)) - cmod(inner_prod v (A *\<^sub>v v))"
    using XN cmod_eq_Re by auto
  then have YY: "cmod(inner_prod v (X N *\<^sub>v v)) - cmod(inner_prod v (A *\<^sub>v v)) < -?r" using XN by auto
  then have "cmod(inner_prod v (X N *\<^sub>v v)) - cmod(inner_prod v (A *\<^sub>v v)) < cmod(inner_prod v (A *\<^sub>v v))" using rl cmod_eq_Re by auto
  then have  "cmod(inner_prod v (X N *\<^sub>v v)) < 0"  using XNv XX YY cmod_eq_Re by auto
  then have "False" using XNv by simp
  with npA show False by auto
qed

lemma limit_mat_ignore_initial_segment:
  "limit_mat g A d \<Longrightarrow> limit_mat (\<lambda>n. g (n + k)) A d"
proof -
  assume asm: "limit_mat g A d"
  then have lim: "\<forall> i < d. \<forall> j < d. (\<lambda> n. (g n) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))" using limit_mat_def by auto
  then have limk: "\<forall> i < d. \<forall> j < d. (\<lambda> n. (g (n + k)) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))"
  proof -
    {
      fix i j assume dims: "i < d" "j < d"
      then have "(\<lambda> n. (g n) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))" using lim by auto
      then have "(\<lambda> n. (g (n + k)) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))" using LIMSEQ_ignore_initial_segment by auto
    }
    then show "\<forall> i < d. \<forall> j < d. (\<lambda> n. (g (n + k)) $$ (i, j)) \<longlonglongrightarrow> (A $$ (i, j))" by auto
  qed
  have "\<forall> n. g n \<in> carrier_mat d d" using asm unfolding limit_mat_def by auto
  then have "\<forall> n. g (n + k) \<in> carrier_mat d d" by auto
  moreover have "A \<in> carrier_mat d d" using asm limit_mat_def by auto
  ultimately show "limit_mat (\<lambda>n. g (n + k)) A d" using limit_mat_def limk by auto
qed

lemma mat_trace_limit:
  "limit_mat g A d \<Longrightarrow> (\<lambda>n. trace (g n)) \<longlonglongrightarrow> trace A"
proof -
  assume lim: "limit_mat g A d"
  then have dgn: "g n \<in> carrier_mat d d" for n using limit_mat_def by auto
  from lim have dA: "A \<in> carrier_mat d d" using limit_mat_def by auto
  have trg: "trace (g n) = (\<Sum>k=0..<d. (g n)$$(k, k))" for n unfolding trace_def using carrier_matD[OF dgn] by auto
  have "\<forall>k < d. (\<lambda>n. (g n)$$(k, k)) \<longlonglongrightarrow> A$$(k, k)" using limit_mat_def lim by auto
  then have "(\<lambda>n. (\<Sum>k=0..<d. (g n)$$(k, k))) \<longlonglongrightarrow> (\<Sum>k=0..<d. A$$(k, k))"
    using tendsto_sum[where ?I = "{0..<d}" and ?f = "(\<lambda>k n. (g n)$$(k, k))"] by auto
  then show "(\<lambda>n. trace (g n)) \<longlonglongrightarrow> trace A" unfolding trace_def
    using trg carrier_matD[OF dgn] carrier_matD[OF dA] by auto
qed

subsection \<open>Existence of least upper bound for the L\"{o}wner order\<close>

definition lowner_is_lub :: "(nat \<Rightarrow> complex mat) \<Rightarrow> complex mat \<Rightarrow> bool" where
  "lowner_is_lub f M \<longleftrightarrow> (\<forall>n. f n \<le>\<^sub>L M) \<and> (\<forall>M'. (\<forall>n. f n \<le>\<^sub>L M') \<longrightarrow> M \<le>\<^sub>L M')"

locale matrix_seq =
  fixes dim :: nat
    and f :: "nat \<Rightarrow> complex mat"
  assumes
    dim: "\<And>n. f n \<in> carrier_mat dim dim" and
    pdo: "\<And>n. partial_density_operator (f n)" and
    inc: "\<And>n. lowner_le (f n) (f (Suc n))"
begin

definition lowner_is_lub :: "complex mat \<Rightarrow> bool" where
  "lowner_is_lub M \<longleftrightarrow> (\<forall>n. f n \<le>\<^sub>L M) \<and> (\<forall>M'. (\<forall>n. f n \<le>\<^sub>L M') \<longrightarrow> M \<le>\<^sub>L M')"

lemma lowner_is_lub_dim:
  assumes "lowner_is_lub M"
  shows "M \<in> carrier_mat dim dim"
proof -
  have "f 0 \<le>\<^sub>L M" using assms lowner_is_lub_def by auto
  then have 1: "dim_row (f 0) = dim_row M \<and> dim_col (f 0) = dim_col M"
    using lowner_le_def by auto
  moreover have 2: "f 0 \<in> carrier_mat dim dim"
    using dim by auto
  ultimately show ?thesis by auto
qed

lemma trace_adjoint_eq_u:
  fixes A :: "complex mat"
  shows "trace (A * adjoint A) = (\<Sum> i \<in> {0 ..< dim_row A}. \<Sum> j \<in> {0 ..< dim_col A}. (norm(A $$ (i,j)))\<^sup>2)"
proof -
  have "trace (A * adjoint A) = (\<Sum> i \<in> {0 ..< dim_row A}. row A i \<bullet> conjugate (row A i))"
    by (simp add: trace_def cmod_def adjoint_def scalar_prod_def)
  also have "\<dots> = (\<Sum> i \<in> {0 ..< dim_row A}. \<Sum> j \<in> {0 ..< dim_col A}. (norm(A $$ (i,j)))\<^sup>2)"
    proof (simp add: scalar_prod_def cmod_def)
      have cnjmul: "\<forall> i ia. A $$ (i, ia) * cnj (A $$ (i, ia)) =
                   ((complex_of_real (Re (A $$ (i, ia))))\<^sup>2 + (complex_of_real (Im (A $$ (i, ia))))\<^sup>2)"
        by (simp add: complex_mult_cnj)
      then have "\<forall> i. (\<Sum>ia = 0..<dim_col A. A $$ (i, ia) * cnj (A $$ (i, ia))) =
                      (\<Sum>ia = 0..<dim_col A.  ((complex_of_real (Re (A $$ (i, ia))))\<^sup>2 + (complex_of_real (Im (A $$ (i, ia))))\<^sup>2))"
        by auto
      then show"(\<Sum>i = 0..<dim_row A. \<Sum>ia = 0..<dim_col A. A $$ (i, ia) * cnj (A $$ (i, ia))) =
        (\<Sum>x = 0..<dim_row A. \<Sum>xa = 0..<dim_col A. (complex_of_real (Re (A $$ (x, xa))))\<^sup>2) +
        (\<Sum>x = 0..<dim_row A. \<Sum>xa = 0..<dim_col A. (complex_of_real (Im (A $$ (x, xa))))\<^sup>2)"
        by auto
    qed
  finally show ?thesis .
qed

lemma trace_adjoint_element_ineq:
  fixes A :: "complex mat"
  assumes rindex: "i \<in> {0 ..< dim_row A}"
     and  cindex: "j \<in> {0 ..< dim_col A}"
  shows "(norm(A $$ (i,j)))\<^sup>2 \<le> trace (A * adjoint A)"
proof (simp add: trace_adjoint_eq_u)
  have ineqi: "(cmod (A $$ (i, j)))\<^sup>2 \<le> (\<Sum>xa = 0..<dim_col A. (cmod (A $$ (i, xa)))\<^sup>2)"
    using cindex member_le_sum[of j " {0 ..< dim_col A}" "\<lambda> x. (cmod (A $$ (i, x)))\<^sup>2"] by auto
  also have ineqj: "\<dots> \<le> (\<Sum>x = 0..<dim_row A. \<Sum>xa = 0..<dim_col A. (cmod (A $$ (x, xa)))\<^sup>2)"
    using rindex member_le_sum[of i " {0 ..< dim_row A}" "\<lambda> x. \<Sum>xa = 0..<dim_col A. (cmod (A $$ (x, xa)))\<^sup>2"]
    by (simp add: sum_nonneg)
  then show "(cmod (A $$ (i, j)))\<^sup>2 \<le> (\<Sum>x = 0..<dim_row A. \<Sum>xa = 0..<dim_col A. (cmod (A $$ (x, xa)))\<^sup>2)"
  using ineqi by linarith
 qed

lemma positive_is_normal:
  fixes A :: "complex mat"
  assumes pos: "positive A"
  shows "A * adjoint A = adjoint A * A"
proof -
  have hA: "hermitian A" using positive_is_hermitian pos by auto
  then show ?thesis by (simp add: hA hermitian_is_normal)
qed

lemma diag_mat_mul_diag_diag:
  fixes A B ::  "complex mat"
  assumes dimA: "A \<in> carrier_mat n n" and dimB: "B \<in> carrier_mat n n"
    and dA: "diagonal_mat A"  and dB: "diagonal_mat B"
  shows "diagonal_mat (A * B)"
proof  -
  have AB: "A * B = mat n n (\<lambda>(i,j). (if (i = j) then (A$$(i, i)) * (B$$(i, i)) else 0))"
    using diag_mat_mult_diag_mat[of A n B] dimA dimB dA dB by auto
  then have dAB: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (A*B) $$ (i,j) = 0"
  proof -
    {
      fix i j assume i: "i < n" and j: "j < n" and ij: "i \<noteq> j"
      have "(A*B) $$ (i,j) = 0" using AB i j ij by auto
    }
    then show ?thesis by auto
  qed
  then show ?thesis using diagonal_mat_def dAB dimA dimB
    by (metis carrier_matD(1) carrier_matD(2) index_mult_mat(2) index_mult_mat(3))
qed

lemma diag_mat_mul_diag_ele:
  fixes A B :: "complex mat"
  assumes dimA: "A \<in> carrier_mat n n" and dimB: "B \<in> carrier_mat n n"
    and dA: "diagonal_mat A" and dB: "diagonal_mat B"
  shows "\<forall>i<n. (A*B) $$ (i,i) = A$$(i, i) * B$$(i, i)"
proof -
  have AB: "A * B = mat n n (\<lambda>(i,j). if i = j then (A$$(i, i)) * (B$$(i, i)) else 0)"
    using diag_mat_mult_diag_mat[of A n B] dimA dimB dA dB by auto
  then show ?thesis
    using AB by auto
qed

lemma trace_square_less_square_trace:
  fixes B ::  "complex mat"
  assumes dimB: "B \<in> carrier_mat n n"
      and dB: "diagonal_mat B" and pB: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<ge> 0"
    shows "trace (B*B) \<le> (trace B)\<^sup>2"
proof -
  have tB:  "trace B = (\<Sum> i \<in> {0 ..<n}. B $$ (i,i))" using assms trace_def[of B] carrier_mat_def by auto
  then have tBtB: "(trace B)\<^sup>2 = (\<Sum> i \<in> {0 ..<n}.\<Sum> j \<in> {0 ..<n}. B $$ (i,i)*B $$ (j,j))"
  proof -
    show ?thesis
      by (metis (no_types) semiring_normalization_rules(29) sum_product tB)
  qed
  have BB: "\<And>i. i < n \<Longrightarrow> (B*B) $$ (i,i) = (B$$(i, i))\<^sup>2" using diag_mat_mul_diag_ele[of B n B] dimB dB
      by (metis numeral_1_eq_Suc_0 power_Suc0_right power_add_numeral semiring_norm(2))
  have tBB:  "trace (B*B) = (\<Sum> i \<in> {0 ..<n}. (B*B) $$ (i,i))" using assms trace_def[of "B*B"] carrier_mat_def by auto
  also have "\<dots> =  (\<Sum> i \<in> {0 ..<n}. (B$$(i, i))\<^sup>2)" using BB by auto
  finally have BBt: " trace (B * B) = (\<Sum>i = 0..<n. (B $$ (i, i))\<^sup>2)" by auto
  have lesseq: "\<forall>i \<in> {0 ..<n}. (B $$ (i, i))\<^sup>2 \<le> (\<Sum> j \<in> {0 ..<n}. B $$ (i,i)*B $$ (j,j))"
  proof -
    {
      fix i assume i: "i < n"
      have "(\<Sum>j = 0..<n. B $$ (i, i) * B $$ (j, j)) = (B $$ (i, i))\<^sup>2  + sum (\<lambda> j. (B $$ (i, i) * B $$ (j, j))) ({0 ..<n} - {i})"
        by (metis (no_types, lifting) BB atLeastLessThan_iff dB diag_mat_mul_diag_ele dimB finite_atLeastLessThan i not_le not_less_zero sum.remove)
      moreover have "(sum (\<lambda> j. (B $$ (i, i) * B $$ (j, j))) ({0 ..<n} - {i})) \<ge> 0"
      proof (cases "{0..<n} - {i} \<noteq> {}")
        case True
        then show ?thesis using pB i sum_nonneg[of "{0..<n} - {i}" "\<lambda> j. (B $$ (i, i) * B $$ (j, j))"] by auto
       next
         case False
         have "(\<Sum>j\<in>{0..<n} - {i}. B $$ (i, i) * B $$ (j, j)) = 0" using False by fastforce
       then show ?thesis by auto
     qed
     ultimately have "(\<Sum>j = 0..<n. B $$ (i, i) * B $$ (j, j)) \<ge> (B $$ (i, i))\<^sup>2" by auto
   }
   then show ?thesis by auto
 qed
  from tBtB BBt lesseq have "trace (B*B) \<le> (trace B)\<^sup>2"
    using sum_mono[of "{0..<n}" "\<lambda> i. (B $$ (i, i))\<^sup>2" "\<lambda> i. (\<Sum>j = 0..<n. B $$ (i, i) * B $$ (j, j))"]
    by (metis (no_types, lifting))
  then show ?thesis by auto
qed

lemma trace_positive_eq:
   fixes A :: "complex mat"
   assumes pos: "positive A"
   shows "trace (A * adjoint A) \<le> (trace A)\<^sup>2"
proof -
  from assms  have normal: "A * adjoint A = adjoint A * A" by (rule positive_is_normal)
  moreover
  from assms positive_dim_eq obtain n where cA: "A \<in> carrier_mat n n" by auto
  moreover
  from assms complex_mat_char_poly_factorizable cA obtain es where charpo: " char_poly A =  (\<Prod> a \<leftarrow> es. [:- a, 1:]) \<and> length es = n" by auto
  moreover
  obtain B P Q where B: "unitary_schur_decomposition A es = (B,P,Q)" by (cases "unitary_schur_decomposition A es", auto)
  ultimately have
    smw: "similar_mat_wit A B P (adjoint P)"
    and ut: "diagonal_mat B"
    and uP:  "unitary P"
    and dB: "diag_mat B = es"
    and QaP: "Q = adjoint P"
    using normal_complex_mat_has_spectral_decomposition[of A n es B P Q]  unitary_schur_decomposition by auto
  from smw cA QaP uP have cB: "B \<in> carrier_mat n n" and cP: "P \<in> carrier_mat n n" and cQ: "Q \<in> carrier_mat n n"
    unfolding  similar_mat_wit_def Let_def unitary_def by auto
  then have caP: "adjoint P \<in> carrier_mat n n" using adjoint_dim[of P n] by auto
  from smw QaP cA have A: "A = P * B * adjoint P" and traceA: "trace A = trace (P * B * Q)" and PB: "P * Q = 1\<^sub>m n \<and> Q * P = 1\<^sub>m n"
    unfolding similar_mat_wit_def by auto
  have traceAB: "trace (P * B * Q) = trace ((Q*P)*B)"
    using cQ cP cB by (mat_assoc n)
  also have traceelim: "\<dots> = trace B" using traceAB PB cA cB cP cQ left_mult_one_mat[of "P*Q" n n]
    using similar_mat_wit_sym by auto
  finally have traceAB: "trace A = trace B" using traceA by auto
  from A cB cP have aAa: "adjoint A = adjoint((P * B) * adjoint P)" by auto
  have aA: "adjoint A = P * adjoint B * adjoint P"
    unfolding aAa using cP cB by (mat_assoc n)
  have hA: "hermitian A" using pos positive_is_hermitian by auto
  then have AaA: "A = adjoint A" using hA hermitian_def[of A] by auto
  then have PBaP: "P * B * adjoint P = P * adjoint B * adjoint P" using A aA by auto
  then have BaB: "B = adjoint B" using unitary_elim[of B n "adjoint B" P] uP cP cB adjoint_dim[of B n] by auto
  have aPP: "adjoint P * P = 1\<^sub>m n" using uP PB QaP by blast
  have "A * A = P * B * (adjoint P * P) * B * adjoint P"
    unfolding A using cP cB by (mat_assoc n)
  also have "\<dots> = P * B * B * adjoint P"
    unfolding aPP using cP cB by (mat_assoc n)
  finally have AA: "A * A = P * B * B * adjoint P" by auto
  then have tAA: "trace (A*A) = trace (P * B * B * adjoint P)" by auto
  also have tBB: "\<dots> = trace (adjoint P * P * B * B)" using cP cB by (mat_assoc n)
  also have "\<dots> = trace (B * B)" using uP unitary_def[of P] inverts_mat_def[of P "adjoint P"]
    using PB QaP cB by auto
  finally have traceAABB: "trace (A * A) = trace (B * B)" by auto
  have BP: "\<And>i. i < n \<Longrightarrow> B$$(i, i) \<ge> 0"
  proof -
     {
       fix i assume i: "i < n"
       then have "B$$(i, i) \<ge> 0" using positive_eigenvalue_positive[of A n es B P Q i] cA pos charpo B by auto
       then show "B$$(i, i) \<ge> 0" by auto
     }
   qed
   have Brel: "trace (B*B) \<le> (trace B)\<^sup>2" using trace_square_less_square_trace[of B n] cB ut BP by auto
   from AaA traceAABB traceAB Brel have "trace (A*adjoint A) \<le> (trace A)\<^sup>2" by auto
   then show ?thesis by auto
 qed

lemma lowner_le_transitive:
  fixes m n :: nat
  assumes re: "n \<ge> m"
  shows "positive (f n - f m)"
proof -
  from re show "positive (f n - f m)"
  proof (induct n)
    case 0
    then show ?case using positive_zero
          by (metis dim le_0_eq minus_r_inv_mat)
  next
    case (Suc n)
    then show ?case
    proof (cases "Suc n = m")
      case True
      then show ?thesis using positive_zero
          by (metis dim minus_r_inv_mat)
    next
      case False
      then show ?thesis
      proof -
        from False Suc have nm: "n  \<ge> m" by linarith
        from Suc nm have pnm:  "positive (f n - f m)" by auto
        from inc have "positive (f (Suc n) - f n)" unfolding lowner_le_def by auto
        then have pf:  "positive ((f (Suc n) - f n) + (f n - f m))" using positive_add dim pnm
          by (meson minus_carrier_mat)
        have "(f (Suc n) - f n) + (f n - f m) = f (Suc n) + ((- f n) + f n) + (- f m)"
          using local.dim by (mat_assoc dim, auto)
        also have "\<dots> = f (Suc n) + 0\<^sub>m dim dim + (- f m)"
          using local.dim by (subst uminus_l_inv_mat[where nc=dim and nr=dim], auto)
        also have "\<dots> = f (Suc n) - f m"
          using local.dim by (mat_assoc dim, auto)
        finally have re: "f (Suc n) - f n + (f n - f m) = f (Suc n) - f m" .
        from pf re have "positive (f (Suc n) - f m)" by auto
        then show ?thesis by auto
      qed
    qed
  qed
qed

text \<open>The sequence of matrices converges pointwise.\<close>
lemma inc_partial_density_operator_converge:
  assumes  i: "i \<in> {0 ..<dim}" and j: "j \<in> {0 ..<dim}"
  shows "convergent (\<lambda>n. f n $$ (i, j))"
proof-
  have tracefn: "trace (f n) \<ge> 0 \<and> trace (f n) \<le> 1" for n
  proof -
    from pdo show ?thesis
      unfolding partial_density_operator_def using positive_trace[of "f n"]
      using dim by blast
  qed
  from tracefn have normf: "norm(trace (f n)) \<le> norm(trace (f (Suc n))) \<and> norm(trace (f n)) \<le> 1" for n
  proof -
    have trless: "trace (f n) \<le> trace (f (Suc n))"
    using pdo inc dim positive_trace[of "f(Suc n) - f n"] trace_minus_linear[of "f (Suc n)" dim "f n"]
    unfolding partial_density_operator_def lowner_le_def
    using Complex_Matrix.positive_def by force
    moreover from trless tracefn  have "norm(trace (f n)) \<le> norm(trace (f (Suc n)))" unfolding cmod_def by simp
    moreover from trless tracefn have "norm(trace (f n)) \<le> 1" using pdo partial_density_operator_def cmod_def by simp
    ultimately show ?thesis by auto
  qed
  then have inctrace: "incseq (\<lambda> n. norm(trace (f n)))" by (simp add: incseq_SucI)
  then have tr_sup: "(\<lambda> n. norm(trace (f n))) \<longlonglongrightarrow> (SUP i. norm (trace (f i)))"
    using LIMSEQ_incseq_SUP[of "\<lambda> n. norm(trace (f n))"] pdo partial_density_operator_def normf  by (meson bdd_aboveI2)
  then have tr_cauchy: "Cauchy (\<lambda> n. norm(trace (f n)))" using  Cauchy_convergent_iff convergent_def by blast
  then have tr_cauchy_def: "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist(norm(trace (f n))) (norm(trace (f m))) < e" unfolding Cauchy_def by blast
  moreover have "\<forall>m n. dist(norm(trace (f m))) (norm(trace (f n))) = norm(trace (f m) - trace (f n))"
    using tracefn cmod_eq_Re dist_real_def by auto
  ultimately have norm_trace: "\<forall>e>0.\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm((trace (f n)) - (trace (f m))) < e" by auto

  have eq_minus: "\<forall> m n. trace (f m) - trace (f n) = trace (f m - f n)" using trace_minus_linear dim by metis
  from eq_minus norm_trace have norm_trace_cauchy: "\<forall>e>0.\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm((trace (f n - f m))) < e" by auto
  then have norm_trace_cauchy_iff: "\<forall>e>0.\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. norm((trace (f n - f m))) < e"
    by (meson order_trans_rules(23))
  then have norm_square: "\<forall>e>0.\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. (norm((trace (f n - f m))))\<^sup>2 < e\<^sup>2"
    by (metis abs_of_nonneg norm_ge_zero order_less_le real_sqrt_abs real_sqrt_less_iff)

  have tr_re: "\<forall> m. \<forall> n \<ge> m. trace ((f n - f m) * adjoint (f n - f m)) \<le> ((trace (f n- f m)))\<^sup>2"
    using trace_positive_eq lowner_le_transitive by auto
  have tr_re_g: "\<forall> m. \<forall> n \<ge> m. trace ((f n - f m) * adjoint (f n - f m)) \<ge> 0"
    using lowner_le_transitive positive_trace trace_adjoint_positive by auto
  have norm_trace_fmn: "norm(trace ((f n - f m) * adjoint (f n - f m))) \<le> (norm(trace (f n - f m)))\<^sup>2" if nm: "n \<ge> m" for m n
  proof -
    have mnA: "trace ((f n - f m) * adjoint (f n - f m)) \<le> (trace (f n - f m))\<^sup>2" using tr_re nm by auto
    have mnB: "trace ((f n - f m) * adjoint (f n - f m)) \<ge> 0" using tr_re_g nm by auto
    from mnA mnB show ?thesis
      by (smt cmod_eq_Re less_eq_complex_def norm_power zero_complex.sel(1) zero_complex.sel(2))
  qed
  then have cauchy_adj: "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. norm(trace ((f n- f m) * adjoint (f n - f m))) < e\<^sup>2" if e: "e > 0" for e
  proof -
    have "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. (cmod (trace (f n - f m)))\<^sup>2 < e\<^sup>2" using norm_square e by auto
    then obtain M where " \<forall>m\<ge>M. \<forall>n\<ge>m. (cmod (trace (f n - f m)))\<^sup>2 < e\<^sup>2" by auto
    then have "\<forall>m\<ge>M. \<forall>n\<ge>m. norm(trace ((f n- f m) * adjoint (f n - f m))) < e\<^sup>2" using norm_trace_fmn  by fastforce
    then show ?thesis by auto
  qed

  have norm_minus: "\<forall> m. \<forall> n \<ge> m. (norm ((f n - f m) $$ (i, j)))\<^sup>2 \<le> trace ((f n - f m) * adjoint (f n - f m))"
    using trace_adjoint_element_ineq i j
    by (smt adjoint_dim_row carrier_matD(1) index_minus_mat(2) index_mult_mat(2) lowner_le_transitive matrix_seq_axioms matrix_seq_def positive_is_normal)
  then have norm_minus_le: "(norm ((f n - f m) $$ (i, j)))\<^sup>2 \<le> norm (trace ((f n - f m) * adjoint (f n - f m)))" if nm: "n \<ge> m" for n m
  proof -
    have "(norm ((f n - f m) $$ (i, j)))\<^sup>2 \<le> (trace ((f n - f m) * adjoint (f n - f m)))" using norm_minus nm by auto
    also have "\<dots> = norm (trace ((f n - f m) * adjoint (f n - f m)))" using tr_re_g nm
      by (smt Re_complex_of_real less_eq_complex_def matrix_seq.trace_adjoint_eq_u matrix_seq_axioms mult_cancel_left2 norm_one norm_scaleR of_real_def of_real_hom.hom_zero)
    finally show ?thesis by auto
  qed

  from norm_minus_le cauchy_adj have cauchy_ij: "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. (norm ((f n - f m) $$ (i, j)))\<^sup>2  < e\<^sup>2" if e: "e > 0" for e
  proof -
    have "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. norm(trace ((f n- f m) * adjoint (f n - f m))) < e\<^sup>2" using cauchy_adj e by auto
    then obtain M where " \<forall>m\<ge>M. \<forall>n\<ge>m. norm(trace ((f n - f m) * adjoint (f n - f m))) < e\<^sup>2" by auto
    then have "\<forall>m\<ge>M. \<forall>n\<ge>m. (norm ((f n - f m) $$ (i, j)))\<^sup>2 < e\<^sup>2" using norm_minus_le by fastforce
    then show ?thesis by auto
  qed
  then have cauchy_ij_norm: "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. (norm ((f n - f m) $$ (i, j))) < e" if e: "e > 0" for e
  proof -
    have "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>m. (norm ((f n - f m) $$ (i, j)))\<^sup>2 < e\<^sup>2" using cauchy_ij e by auto
    then obtain M where mn: "\<forall>m\<ge>M. \<forall>n\<ge>m. (norm ((f n - f m) $$ (i, j)))\<^sup>2 < e\<^sup>2" by auto
    have "(norm ((f n - f m) $$ (i, j))) < e" if m: "m \<ge> M" and n: "n \<ge> m" for m n :: nat
    proof -
      from m n mn have "(norm ((f n- f m) $$ (i, j)))\<^sup>2 < e\<^sup>2" by auto
      then show ?thesis
      using e power_less_imp_less_base by fastforce
    qed
    then show ?thesis by auto
  qed

  have cauchy_final: "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm ((f m) $$ (i, j) - (f n) $$ (i, j)) < e" if e: "e > 0" for e
  proof -
    obtain M where mnm: "\<forall>m\<ge>M. \<forall>n\<ge>m. norm ((f n - f m) $$ (i, j)) < e" using cauchy_ij_norm e by auto
    have "norm ((f m) $$ (i, j) - (f n) $$ (i, j)) < e" if m: "m \<ge> M" and n: "n \<ge> M" for m n
    proof (cases "n \<ge> m")
      case True
      then show ?thesis
      proof -
        from mnm m True have "norm ((f n) $$ (i, j) - (f m) $$ (i, j)) < e"
          by (metis atLeastLessThan_iff carrier_matD(1) carrier_matD(2) dim i index_minus_mat(1) j)
        then have "norm ((f m) $$ (i, j) - (f n) $$ (i, j)) < e" by (simp add: norm_minus_commute)
        then show ?thesis by auto
      qed
    next
      case False
      then show ?thesis
      proof -
        from False n mnm have norm: "norm ((f m - f n) $$ (i, j)) < e" by auto
        have minus: "(f m - f n) $$ (i, j)   =  f m  $$ (i, j) -f n $$ (i, j)"
          by (metis atLeastLessThan_iff carrier_matD(1) carrier_matD(2) dim i index_minus_mat(1) j)
        also have "\<dots> = - (f n - f m) $$ (i, j)" using dim
          by (metis atLeastLessThan_iff carrier_matD(1) carrier_matD(2) i index_minus_mat(1) j minus_diff_eq)
        finally have fmn: "(f m - f n) $$ (i, j) = - (f n - f m) $$ (i, j)" by auto
        then have "norm ((- (f n - f m)) $$ (i, j)) < e" using norm
          by (metis (no_types, lifting) atLeastLessThan_iff carrier_matD(1) carrier_matD(2) i
              index_minus_mat(2) index_minus_mat(3) index_uminus_mat(1) j matrix_seq_axioms matrix_seq_def)
        then have "norm (((f n - f m)) $$ (i, j)) < e" using fmn norm by auto
        then have "norm (f n $$ (i, j) - f m $$ (i, j)) < e"
          by (metis minus norm norm_minus_commute)
        then have "norm (f m $$ (i, j) - f n $$ (i, j)) < e" by (simp add: norm_minus_commute)
        then show ?thesis by auto
      qed
    qed
    then show ?thesis by auto
  qed

  from cauchy_final have "Cauchy (\<lambda> n. f n $$ (i, j))" by (simp add: Cauchy_def dist_norm)
  then show ?thesis by (simp add: Cauchy_convergent_iff)
qed


definition mat_seq_minus ::  "(nat \<Rightarrow> complex mat) \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
  "mat_seq_minus X A = (\<lambda>n. X n - A)"

definition minus_mat_seq :: "complex mat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> nat \<Rightarrow> complex mat" where
  "minus_mat_seq A X = (\<lambda>n. A - X n)"

lemma pos_mat_lim_is_pos_aux:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat
  assumes limX: "limit_mat X A m" and posX: "\<exists>k. \<forall>n\<ge>k. positive (X n)"
  shows "positive A"
proof -
  from posX obtain k where posk: "\<forall> n\<ge>k. positive (X n)" by auto
  let ?Y = "\<lambda>n. X (n + k)"
  have posY: "\<forall>n. positive (?Y n)" using posk by auto

  from limX have dimXA: "\<forall>n. X (n + k) \<in> carrier_mat m m \<and> A \<in> carrier_mat m m"
    unfolding limit_mat_def by auto

  have "(\<lambda>n. X (n + k) $$ (i, j)) \<longlonglongrightarrow> A $$ (i, j)" if i: "i < m" and j: "j < m" for i j
  proof -
    have "(\<lambda>n. X n $$ (i, j)) \<longlonglongrightarrow> A $$ (i, j)" using limX limit_mat_def i j by auto
    then have limseqX: "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r" unfolding LIMSEQ_def by auto
    then have "\<exists>no. \<forall>n\<ge>no. dist (X (n + k) $$ (i, j)) (A $$ (i, j)) < r" if r: "r > 0" for r
    proof -
      obtain no where "\<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r" using limseqX r by auto
      then have "\<forall>n\<ge>no. dist (X (n + k) $$ (i, j)) (A $$ (i, j)) < r" by auto
      then show ?thesis by auto
    qed
    then show ?thesis unfolding LIMSEQ_def by auto
  qed
  then have limXA: "limit_mat (\<lambda>n. X (n + k)) A m" unfolding limit_mat_def using dimXA by auto

  from posY limXA have "positive A" using pos_mat_lim_is_pos[of ?Y A m] by auto
  then show ?thesis by auto
qed

lemma minus_mat_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat and B :: "complex mat"
  assumes dimB: "B \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (mat_seq_minus X B) (A - B) m"
proof -
  have dimXAB: "\<forall>n. X n - B \<in> carrier_mat m m \<and> A - B \<in> carrier_mat m m" using index_minus_mat dimB by auto
  have "(\<lambda>n. (X n - B) $$ (i, j)) \<longlonglongrightarrow> (A - B) $$ (i, j)" if i: "i < m" and j: "j < m" for i j
  proof -
    from limX i j have "(\<lambda>n. (X n) $$ (i, j)) \<longlonglongrightarrow> (A) $$ (i, j)" unfolding limit_mat_def by auto
    then have X: "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r" unfolding LIMSEQ_def by auto
    then have XB: "\<exists>no. \<forall>n\<ge>no. dist ((X n - B) $$ (i, j)) ((A - B) $$ (i, j)) < r" if r: "r > 0" for r
    proof -
      obtain no where "\<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r"  using r X by auto
      then have dist:  "\<forall>n\<ge>no. norm (X n $$ (i, j) - A $$ (i, j)) < r" unfolding dist_norm  by auto
      then have "norm ((X n - B) $$ (i, j) - (A - B) $$ (i, j)) < r" if n: "n \<ge> no" for n
      proof -
        have "(X n - B) $$ (i, j) - (A - B) $$ (i, j) = (X n) $$ (i, j) -  A $$ (i, j)"
          using dimB i j by auto
        then have "norm ((X n - B) $$ (i, j) - (A - B) $$ (i, j)) = norm ((X n) $$ (i, j) -  A $$ (i, j))" by auto
        then show ?thesis using dist n by auto
      qed
      then show ?thesis using dist_norm by metis
    qed
    then show ?thesis unfolding LIMSEQ_def by auto
  qed
  then show ?thesis
    unfolding limit_mat_def mat_seq_minus_def using dimXAB by auto
qed

lemma mat_minus_limit:
  fixes X :: "nat \<Rightarrow> complex mat" and A :: "complex mat" and m :: nat and B :: "complex mat"
  assumes dimA: "A \<in> carrier_mat m m" and limX: "limit_mat X A m"
  shows "limit_mat (minus_mat_seq B X) (B - A) m"
proof-
  have dimX : "\<forall>n. X n \<in> carrier_mat m m" using limX unfolding limit_mat_def by auto
  then have dimXAB: "\<forall>n. B - X n \<in> carrier_mat m m \<and> B - A \<in> carrier_mat m m" using index_minus_mat dimA
    by (simp add: minus_carrier_mat)

  have "(\<lambda>n. (B - X n) $$ (i, j)) \<longlonglongrightarrow> (B - A) $$ (i, j)" if i: "i < m" and j: "j < m" for i j
  proof -
    from limX i j have "(\<lambda>n. (X n) $$ (i, j)) \<longlonglongrightarrow> (A) $$ (i, j)" unfolding limit_mat_def by auto
    then have X: "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r" unfolding LIMSEQ_def by auto
    then have XB: "\<exists>no. \<forall>n\<ge>no. dist ((B - X n) $$ (i, j)) ((B - A) $$ (i, j)) < r" if r: "r > 0" for r
    proof -
      obtain no where "\<forall>n\<ge>no. dist (X n $$ (i, j)) (A $$ (i, j)) < r" using r X by auto
      then have dist: "\<forall>n\<ge>no. norm (X n $$ (i, j) - A $$ (i, j)) < r" unfolding dist_norm by auto
      then have "norm ((B - X n) $$ (i, j) - (B - A) $$ (i, j)) < r" if n: "n \<ge> no" for n
      proof -
        have "(B - X n) $$ (i, j) - (B - A) $$ (i, j) = - ((X n) $$ (i, j) -  A $$ (i, j))"
          using dimA i j
          by (smt cancel_ab_semigroup_add_class.diff_right_commute cancel_comm_monoid_add_class.diff_cancel carrier_matD(1) carrier_matD(2) diff_add_cancel dimX index_minus_mat(1) minus_diff_eq)
        then have "norm ((B - X n) $$ (i, j) - (B - A) $$ (i, j)) = norm ((X n) $$ (i, j) -  A $$ (i, j))"
          by (metis norm_minus_cancel)
        then show ?thesis using dist n by auto
      qed
      then show ?thesis using dist_norm by metis
    qed
    then show ?thesis unfolding LIMSEQ_def by auto
  qed
  then have "limit_mat (minus_mat_seq B X) (B - A) m"
    unfolding limit_mat_def minus_mat_seq_def using dimXAB by auto
  then show ?thesis by auto
qed

lemma lowner_lub_form:
  "lowner_is_lub (mat dim dim (\<lambda> (i, j). (lim (\<lambda> n. (f n) $$ (i, j)))))"
proof -
  from inc_partial_density_operator_converge
  have conf: "\<forall> i \<in> {0 ..<dim}.  \<forall> j \<in> {0 ..<dim}. convergent (\<lambda> n. f n $$ (i, j))" by auto
  let ?A = "mat dim dim (\<lambda> (i, j). (lim (\<lambda> n. (f n) $$ (i, j))))"
  have dim_A: "?A \<in> carrier_mat dim dim" by auto
  have lim_A: "(\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> mat dim dim (\<lambda>(i, j). lim (\<lambda>n. f n $$ (i, j))) $$ (i, j)"
    if i: "i < dim" and j: "j < dim" for i j
  proof -
    from i j have ij: "mat dim dim (\<lambda>(i, j). lim (\<lambda>n. f n $$ (i, j))) $$ (i, j) = lim (\<lambda>n. f n $$ (i, j))"
      by (metis case_prod_conv index_mat(1))
    have "convergent (\<lambda>n. f n $$ (i, j))" using conf i j by auto
    then have "(\<lambda>n. f n $$ (i, j))  \<longlonglongrightarrow> lim (\<lambda>n. f n $$ (i, j)) " using convergent_LIMSEQ_iff by auto
    then show ?thesis using ij by auto
  qed

  from dim dim_A lim_A have lim_mat_A: "limit_mat f ?A dim" unfolding limit_mat_def by auto

  have is_ub: "f n \<le>\<^sub>L ?A" for n
  proof -
    have "\<forall> m \<ge> n. positive (f m - f n)" using lowner_le_transitive by auto
    then have le: "\<forall> m \<ge> n. f n \<le>\<^sub>L f m " unfolding lowner_le_def using dim
      by (metis carrier_matD(1) carrier_matD(2))
    have dimn: "f n \<in> carrier_mat dim dim" using dim by auto
    then have limAf: "limit_mat (mat_seq_minus f (f n)) (?A - f n) dim" using minus_mat_limit lim_mat_A by auto

    have " \<forall>m\<ge>n. positive (f m - f n)" using lowner_le_transitive by auto
    then have "\<exists>k. \<forall>m\<ge>k. positive (f m - f n)" by auto
    then have posAf: "\<exists> k. \<forall> m \<ge> k. positive ((mat_seq_minus f (f n)) m)" unfolding mat_seq_minus_def by auto

    from limAf posAf have "positive (?A - f n)" using pos_mat_lim_is_pos_aux by auto
    then have "f n \<le>\<^sub>L mat dim dim (\<lambda>(i, j). lim (\<lambda>n. f n $$ (i, j)))" unfolding lowner_le_def using dim by auto
    then show ?thesis by auto
  qed

  have is_lub: "?A \<le>\<^sub>L M'" if ub: "\<forall>n. f n \<le>\<^sub>L M'" for M'
  proof -
    have dim_M: "M' \<in> carrier_mat dim dim" using ub unfolding lowner_le_def using dim
      by (metis carrier_matD(1) carrier_matD(2) carrier_mat_triv)
    from ub have posAf: "\<forall> n. positive (minus_mat_seq M' f n)" unfolding minus_mat_seq_def lowner_le_def by auto
    have limAf: "limit_mat (minus_mat_seq M' f) (M' - ?A) dim"
      using mat_minus_limit dim_A lim_mat_A by auto
    from posAf limAf have  "positive (M' - ?A)" using pos_mat_lim_is_pos_aux by auto
    then have "?A \<le>\<^sub>L M'" unfolding lowner_le_def using dim dim_A dim_M by auto
    then show ?thesis by auto
  qed

  from is_ub is_lub show ?thesis unfolding lowner_is_lub_def by auto
qed

text \<open>Lowner partial order is a complete partial order.\<close>
lemma lowner_lub_exists: "\<exists>M. lowner_is_lub M"
  using lowner_lub_form by auto

lemma lowner_lub_unique: "\<exists>!M. lowner_is_lub M"
proof (rule HOL.ex_ex1I)
  show "\<exists>M. lowner_is_lub M"
    by (rule lowner_lub_exists)
next
  fix M N
  assume M: "lowner_is_lub M" and N: "lowner_is_lub N"
  have Md: "M \<in> carrier_mat dim dim" using M by (rule lowner_is_lub_dim)
  have Nd: "N \<in> carrier_mat dim dim" using N by (rule lowner_is_lub_dim)
  have MN: "M \<le>\<^sub>L N" using M N by (simp add: lowner_is_lub_def)
  have NM: "N \<le>\<^sub>L M" using M N by (simp add: lowner_is_lub_def)
  show "M = N" using MN NM by (auto intro: lowner_le_antisym[OF Md Nd])
qed

definition lowner_lub :: "complex mat" where
  "lowner_lub = (THE M. lowner_is_lub M)"

lemma lowner_lub_prop: "lowner_is_lub lowner_lub"
  unfolding lowner_lub_def
  apply (rule HOL.theI')
  by (rule lowner_lub_unique)

lemma lowner_lub_is_limit:
  "limit_mat f lowner_lub dim"
proof -
  define A where "A = lowner_lub"
  then have "A = (THE M. lowner_is_lub M)" using lowner_lub_def by auto
  then have Af: "A = (mat dim dim (\<lambda> (i, j). (lim (\<lambda> n.  (f n) $$ (i, j)))))"
    using lowner_lub_form lowner_lub_unique by auto
  show "limit_mat f A dim" unfolding Af limit_mat_def
    apply (auto simp add: dim)
  proof -
    fix i j assume dims: "i < dim" "j < dim"
    then have "convergent  (\<lambda>n. f n $$ (i, j))" using inc_partial_density_operator_converge by auto
    then show "(\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> lim (\<lambda>n. f n $$ (i, j))" using convergent_LIMSEQ_iff by auto
  qed
qed

lemma lowner_lub_trace:
  assumes "\<forall> n. trace (f n) \<le> x"
  shows "trace lowner_lub \<le> x"
proof -
  have "\<forall> n. trace (f n) \<ge> 0" using positive_trace pdo unfolding partial_density_operator_def
    using dim by blast
  then have Re: "\<forall> n. Re (trace (f n)) \<ge> 0 \<and> Im (trace (f n)) = 0" by auto
  then have lex: "\<forall> n. Re (trace (f n)) \<le> Re x \<and> Im x = 0" using assms by auto

  have "limit_mat f lowner_lub dim"  using lowner_lub_is_limit by auto
  then have conv: "(\<lambda>n. trace (f n)) \<longlonglongrightarrow> trace lowner_lub" using mat_trace_limit by auto
  then have "(\<lambda>n. Re (trace (f n))) \<longlonglongrightarrow> Re (trace lowner_lub)"
    by (simp add: tendsto_Re)
  then have Rell: "Re (trace lowner_lub) \<le> Re x"
    using lex Lim_bounded[of "(\<lambda>n. Re (trace (f n)))" "Re (trace lowner_lub)" 0 "Re x"] by simp

  from conv have "(\<lambda>n. Im (trace (f n))) \<longlonglongrightarrow> Im (trace lowner_lub)"
    by (simp add: tendsto_Im)
  then  have Imll: "Im (trace lowner_lub) = 0" using Re
    by (simp add: Lim_bounded Lim_bounded2 dual_order.antisym)

  from Rell Imll lex show ?thesis by simp
qed

lemma lowner_lub_is_positive:
  shows "positive lowner_lub"
  using lowner_lub_is_limit pos_mat_lim_is_pos pdo unfolding partial_density_operator_def by auto

end

subsection \<open>Finite sum of matrices\<close>

text \<open>Add f in the interval [0, n)\<close>
fun matrix_sum :: "nat \<Rightarrow> (nat \<Rightarrow> 'b::semiring_1 mat) \<Rightarrow> nat \<Rightarrow> 'b mat" where
  "matrix_sum d f 0 = 0\<^sub>m d d"
| "matrix_sum d f (Suc n) = f n + matrix_sum d f n"

definition matrix_inf_sum :: "nat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> complex mat" where
  "matrix_inf_sum d f = matrix_seq.lowner_lub (\<lambda>n. matrix_sum d f n)"

lemma matrix_sum_dim:
  fixes f :: "nat \<Rightarrow> 'b::semiring_1 mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> matrix_sum d f n \<in> carrier_mat d d"
proof (induct n)
  case 0
  show ?case by auto
next
  case (Suc n)
  then have "f n \<in> carrier_mat d d" by auto
  then show ?case using Suc by auto
qed

lemma matrix_sum_cong:
  fixes f :: "nat \<Rightarrow> 'b::semiring_1 mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k = f' k) \<Longrightarrow> matrix_sum d f n = matrix_sum d f' n"
proof (induct n)
  case 0
  show ?case by auto
next
  case (Suc n)
  then show ?case unfolding matrix_sum.simps by auto
qed

lemma matrix_sum_add:
  fixes f :: "nat \<Rightarrow> 'b::semiring_1 mat" and  g :: "nat \<Rightarrow> 'b::semiring_1 mat" and  h :: "nat \<Rightarrow> 'b::semiring_1 mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> g k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> h k \<in> carrier_mat d d) \<Longrightarrow>
     (\<And>k. k < n \<Longrightarrow> f k = g k + h k) \<Longrightarrow> matrix_sum d f n = matrix_sum d g n + matrix_sum d h n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
  proof -
    have gh: "matrix_sum d g n \<in> carrier_mat d d \<and> matrix_sum d h n \<in> carrier_mat d d"
      using matrix_sum_dim Suc(3, 4) by (simp add: matrix_sum_dim)

    have nSuc: "n < Suc n" by auto
    have sumf: "matrix_sum d f n = matrix_sum d g n + matrix_sum d h n" using Suc by auto
    have "matrix_sum d f (Suc n) = matrix_sum d g (Suc n) + matrix_sum d h (Suc n)"
      unfolding matrix_sum.simps Suc(5)[OF nSuc] sumf
      apply (mat_assoc d) using gh Suc by auto
    then show ?thesis by auto
  qed
qed

lemma matrix_sum_smult:
  fixes f :: "nat \<Rightarrow> 'b::semiring_1 mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow>
        matrix_sum d (\<lambda> k. c \<cdot>\<^sub>m f k) n = c \<cdot>\<^sub>m matrix_sum d f n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    apply auto
    using add_smult_distrib_left_mat Suc matrix_sum_dim
    by (metis lessI less_SucI)
qed

lemma matrix_sum_remove:
  fixes f :: "nat \<Rightarrow> 'b::semiring_1 mat"
  assumes j: "j < n"
    and df: "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d)"
    and f': "(\<And>k. f' k = (if k = j then 0\<^sub>m d d else f k))"
  shows "matrix_sum d f n = f j + matrix_sum d f' n"
proof -
  have df': "\<And>k. k < n \<Longrightarrow> f' k \<in> carrier_mat d d" using f' df by auto
  have dsf: "k < n \<Longrightarrow> matrix_sum d f k \<in> carrier_mat d d" for k using matrix_sum_dim[OF df] by auto
  have dsf': "k < n \<Longrightarrow> matrix_sum d f' k \<in> carrier_mat d d" for k using matrix_sum_dim[OF df'] by auto
  have flj: "\<And>k. k < j \<Longrightarrow> f' k = f k" using j f' by auto
  then have "matrix_sum d f j = matrix_sum d f' j" using matrix_sum_cong[of j f' f, OF flj] df df' j by auto
  then have eqj: "matrix_sum d f (Suc j) = f j + matrix_sum d f' (Suc j)" unfolding matrix_sum.simps
    by (subst (1) f', simp add: df dsf' j)
  have lm: "(j + 1) + l \<le> n \<Longrightarrow> matrix_sum d f ((j + 1) + l) = f j + matrix_sum d f' ((j + 1) + l)" for l
  proof (induct l)
    case 0
    show ?case using j eqj by auto
  next
    case (Suc l) then have eq: "matrix_sum d f ((j + 1) + l) = f j + matrix_sum d f' ((j + 1) + l)" by auto
    have s: "((j + 1) + Suc l) = Suc ((j + 1) + l)" by simp
    have eqf': "f' (j + 1 + l) = f (j + 1 + l)" using f' Suc by auto
    have dims: "f (j + 1 + l) \<in> carrier_mat d d" "f j \<in> carrier_mat d d" "matrix_sum d f' (j + 1 + l) \<in> carrier_mat d d" using df df' dsf' Suc by auto
    show ?case apply (subst (1 2) s) unfolding matrix_sum.simps
      apply (subst eq, subst eqf')
      apply (mat_assoc d) using dims by auto
  qed
  have p: "(j + 1) + (n - j - 1) \<le> n" using j by auto
  show ?thesis using lm[OF p] j by auto
qed

lemma matrix_sum_Suc_remove_head:
  fixes f :: "nat \<Rightarrow> complex mat"
  shows "(\<And>k. k < n + 1 \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow>
    matrix_sum d f (n + 1) = f 0 + matrix_sum d (\<lambda>k. f (k + 1)) n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have dSS: "\<And>k. k < Suc (Suc n) \<Longrightarrow> f k \<in> carrier_mat d d" by auto
  have ds: "matrix_sum d (\<lambda>k. f (k + 1)) n \<in> carrier_mat d d" using matrix_sum_dim[OF dSS, of "n" "\<lambda>k. k + 1"] by auto
  have "matrix_sum d f (Suc n + 1) = f (n + 1) + matrix_sum d f (n + 1)" by auto
  also have "\<dots> = f (n + 1) + (f 0 + matrix_sum d (\<lambda>k. f (k + 1)) n)" using Suc by auto
  also have "\<dots> = f 0 + (f (n + 1) + matrix_sum d (\<lambda>k. f (k + 1)) n)"
    using ds apply (mat_assoc d) using dSS by auto
  finally show ?case by auto
qed

lemma matrix_sum_positive:
  fixes f :: "nat \<Rightarrow> complex mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> positive (f k))
    \<Longrightarrow> positive (matrix_sum d f n)"
proof (induct n)
  case 0
  show ?case using positive_zero by auto
next
  case (Suc n)
  then have dfn: "f n \<in> carrier_mat d d" and psn: "positive (matrix_sum d f n)" and pn: "positive (f n)" and d: "k < n \<Longrightarrow> f k \<in> carrier_mat d d" for k by auto
  then have dsn: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim by auto
  show ?case unfolding matrix_sum.simps using positive_add[OF pn psn dfn dsn] by auto
qed

lemma matrix_sum_mult_right:
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> A \<in> carrier_mat d d
    \<Longrightarrow> matrix_sum d (\<lambda>k. (f k) * A) n = matrix_sum d (\<lambda>k. f k) n * A"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have "k < n \<Longrightarrow> f k \<in> carrier_mat d d" and dfn: "f n \<in> carrier_mat d d" for k by auto
  then have dsfn: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim by auto
  have "(f n + matrix_sum d f n) * A = f n * A + matrix_sum d f n * A"
    apply (mat_assoc d) using Suc dsfn by auto
  also have "\<dots> = f n * A + matrix_sum d (\<lambda>k. f k * A) n" using Suc by auto
  finally show ?case by auto
qed

lemma matrix_sum_add_distrib:
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> g k \<in> carrier_mat d d)
    \<Longrightarrow> matrix_sum d (\<lambda>k. (f k) + (g k)) n = matrix_sum d f n + matrix_sum d g n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have dfn: "f n \<in> carrier_mat d d" and dgn: "g n \<in> carrier_mat d d"
    and dfk: "k < n \<Longrightarrow> f k \<in> carrier_mat d d" and dgk: "k < n \<Longrightarrow> g k \<in> carrier_mat d d"
    and eq: "matrix_sum d (\<lambda>k. f k + g k) n = matrix_sum d f n + matrix_sum d g n" for k by auto
  have dsf: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim dfk by auto
  have dsg: "matrix_sum d g n \<in> carrier_mat d d" using matrix_sum_dim dgk by auto
  show ?case unfolding matrix_sum.simps eq
    using dfn dgn dsf dsg by (mat_assoc d)
qed

lemma matrix_sum_minus_distrib:
  fixes f g :: "nat \<Rightarrow> complex mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> g k \<in> carrier_mat d d)
    \<Longrightarrow> matrix_sum d (\<lambda>k. (f k) - (g k)) n = matrix_sum d f n - matrix_sum d g n"
proof -
  have eq: "-1 \<cdot>\<^sub>m g k = - g k" for k by auto
  assume dfk: "\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d" and dgk: "\<And>k. k < n \<Longrightarrow> (g k) \<in> carrier_mat d d"
  then have "k < n \<Longrightarrow> (f k) - (g k) = (f k) + (- (g k))" for k by auto
  then have "matrix_sum d (\<lambda>k. (f k) - (g k)) n = matrix_sum d (\<lambda>k. (f k) + (- (g k))) n"
    using matrix_sum_cong[of n "\<lambda>k. (f k) - (g k)"] dfk dgk by auto
  also have "\<dots> = matrix_sum d f n + matrix_sum d (\<lambda>k. - (g k)) n"
    using matrix_sum_add_distrib[of n "f"] dfk dgk by auto
  also have "\<dots> = matrix_sum d f n - matrix_sum d g n"
    apply (subgoal_tac "matrix_sum d (\<lambda>k. - (g k)) n = - matrix_sum d g n", auto)
    apply (subgoal_tac "- 1 \<cdot>\<^sub>m matrix_sum d g n = - matrix_sum d g n")
    by (simp add: matrix_sum_smult[of n g d "-1", OF dgk, simplified eq, simplified], auto)
  finally show ?thesis .
qed

lemma matrix_sum_shift_Suc:
  shows "(\<And>k. k < (Suc n) \<Longrightarrow> f k \<in> carrier_mat d d)
    \<Longrightarrow> matrix_sum d f (Suc n) = f 0 + matrix_sum d (\<lambda>k. f (Suc k)) n"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have dfk: "k < Suc (Suc n) \<Longrightarrow> f k \<in> carrier_mat d d" for k using Suc by auto
  have dsSk: "k < Suc n \<Longrightarrow> matrix_sum d (\<lambda>k. f (Suc k)) n \<in> carrier_mat d d" for k using matrix_sum_dim[of _ "\<lambda>k. f (Suc k)"] dfk by fastforce
  have "matrix_sum d f (Suc (Suc n)) = f (Suc n) + matrix_sum d f (Suc n)" by auto
  also have "\<dots> = f (Suc n) + f 0 + matrix_sum d (\<lambda>k. f (Suc k)) n" using Suc dsSk assoc_add_mat[of "f (Suc n)" d d "f 0"] by fastforce
  also have "\<dots> = f 0 + (f (Suc n) + matrix_sum d (\<lambda>k. f (Suc k)) n)" apply (mat_assoc d) using dsSk dfk by auto
  also have "\<dots> = f 0 + matrix_sum d (\<lambda>k. f (Suc k)) (Suc n)"  by auto
  finally show ?case .
qed

lemma lowner_le_matrix_sum:
  fixes f g :: "nat \<Rightarrow> complex mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> g k \<in> carrier_mat d d)
    \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> f k \<le>\<^sub>L g k)
    \<Longrightarrow> matrix_sum d f n \<le>\<^sub>L matrix_sum d g n"
proof (induct n)
  case 0
  show ?case unfolding matrix_sum.simps using lowner_le_refl[of "0\<^sub>m d d" d] by auto
next
  case (Suc n)
  then have dfn: "f n \<in> carrier_mat d d" and dgn: "g n \<in> carrier_mat d d" and le1: "f n \<le>\<^sub>L g n" by auto
  then have le2: "matrix_sum d f n \<le>\<^sub>L matrix_sum d g n" using Suc by auto
  have "k < n \<Longrightarrow> f k \<in> carrier_mat d d" for k using Suc by auto
  then have dsf: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim by auto
  have "k < n \<Longrightarrow> g k \<in> carrier_mat d d" for k using Suc by auto
  then have dsg: "matrix_sum d g n \<in> carrier_mat d d" using matrix_sum_dim by auto
  show ?case unfolding matrix_sum.simps using lowner_le_add dfn dsf dgn dsg le1 le2 by auto
qed

lemma lowner_lub_add:
  assumes "matrix_seq d f" "matrix_seq d g" "\<forall> n. trace (f n + g n) \<le> 1"
  shows "matrix_seq.lowner_lub (\<lambda>n. f n + g n) = matrix_seq.lowner_lub f + matrix_seq.lowner_lub g"
proof -
  have msf: "matrix_seq.lowner_is_lub f (matrix_seq.lowner_lub f)" using assms(1) matrix_seq.lowner_lub_prop by auto
  then have "limit_mat f (matrix_seq.lowner_lub f) d" using matrix_seq.lowner_lub_is_limit assms by auto
  then have lim1: "\<forall>i<d. \<forall>j<d. (\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub f) $$ (i, j)" using limit_mat_def assms by auto

  have msg: "matrix_seq.lowner_is_lub g (matrix_seq.lowner_lub g)" using assms(2) matrix_seq.lowner_lub_prop by auto
  then have "limit_mat g (matrix_seq.lowner_lub g) d" using matrix_seq.lowner_lub_is_limit assms by auto
  then have lim2: "\<forall>i<d. \<forall>j<d. (\<lambda>n. g n $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub g) $$ (i, j)" using limit_mat_def assms by auto

  have "\<forall>n. f n + g n \<in> carrier_mat d d" using assms unfolding matrix_seq_def by fastforce
  moreover have "\<forall>n. partial_density_operator (f n + g n)" using assms
    unfolding matrix_seq_def partial_density_operator_def using positive_add by blast
  moreover have "(f n + g n) \<le>\<^sub>L (f (Suc n) + g (Suc n))" for n
    using assms
    unfolding matrix_seq_def using lowner_le_add[of "f n" d  "f (Suc n)" "g n" "g (Suc n)"] by auto
  ultimately have msfg: "matrix_seq d (\<lambda>n. f n + g n)" using assms unfolding matrix_seq_def by auto
  then have mslfg: "matrix_seq.lowner_is_lub (\<lambda>n. f n + g n) (matrix_seq.lowner_lub (\<lambda>n. f n + g n))"
    using matrix_seq.lowner_lub_prop by auto
  then have "limit_mat (\<lambda>n. f n + g n) (matrix_seq.lowner_lub (\<lambda>n. f n + g n)) d" using matrix_seq.lowner_lub_is_limit msfg by auto
  then have lim3: "\<forall>i<d. \<forall>j<d. (\<lambda>n. (f n + g n) $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub (\<lambda>n. f n + g n)) $$ (i, j)" using limit_mat_def assms by auto

  have "\<forall> i<d. \<forall> j<d. \<forall> n. (f n + g n) $$ (i, j) = f n $$ (i, j) + g n $$ (i, j)" using assms unfolding matrix_seq_def
    by (metis carrier_matD(1) carrier_matD(2) index_add_mat(1))
  then have add: "\<forall>i<d. \<forall>j<d. (\<lambda>n. f n $$ (i, j) + g n $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub (\<lambda>n. f n + g n)) $$ (i, j)" using lim3 by auto
  have "matrix_seq.lowner_lub f $$ (i, j) + matrix_seq.lowner_lub g $$ (i, j) = matrix_seq.lowner_lub (\<lambda>n. f n + g n) $$ (i, j)"
    if i: "i < d" and j: "j < d" for i j
  proof -
    have "(\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> matrix_seq.lowner_lub f $$ (i, j)" using lim1 i j by auto
    moreover have "(\<lambda>n. g n $$ (i, j)) \<longlonglongrightarrow> matrix_seq.lowner_lub g $$ (i, j)" using lim2 i j by auto
    ultimately have "(\<lambda>n. f n $$ (i, j) + g n $$ (i, j)) \<longlonglongrightarrow> matrix_seq.lowner_lub f $$ (i, j) + matrix_seq.lowner_lub g $$ (i, j)"
      using tendsto_add[of "\<lambda>n. f n $$ (i, j)" "matrix_seq.lowner_lub f $$ (i, j)" sequentially "\<lambda>n. g n $$ (i, j)" "matrix_seq.lowner_lub g $$ (i, j)"] by auto
    moreover have "(\<lambda>n. f n $$ (i, j) + g n $$ (i, j)) \<longlonglongrightarrow> matrix_seq.lowner_lub (\<lambda>n. f n + g n) $$ (i, j)"  using add i j by auto
    ultimately show ?thesis using LIMSEQ_unique by auto
  qed
  moreover have "matrix_seq.lowner_lub f \<in> carrier_mat d d" using matrix_seq.lowner_is_lub_dim assms(1) msf unfolding matrix_seq_def by auto
  moreover have "matrix_seq.lowner_lub g \<in> carrier_mat d d" using matrix_seq.lowner_is_lub_dim assms(2) msg unfolding matrix_seq_def by auto
  moreover have "matrix_seq.lowner_lub (\<lambda>n. f n + g n) \<in> carrier_mat d d" using matrix_seq.lowner_is_lub_dim  msfg mslfg unfolding matrix_seq_def by auto
  ultimately show ?thesis  unfolding matrix_seq_def using mat_eq_iff by auto
qed

lemma lowner_lub_scale:
  fixes c :: real
  assumes "matrix_seq d f"  "\<forall> n. trace (c \<cdot>\<^sub>m f n) \<le> 1"  "c\<ge>0"
  shows "matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n) = c \<cdot>\<^sub>m matrix_seq.lowner_lub f"
proof -
  have msf: "matrix_seq.lowner_is_lub f (matrix_seq.lowner_lub f)"
    using assms(1) matrix_seq.lowner_lub_prop by auto
  then have "limit_mat f (matrix_seq.lowner_lub f) d"
    using matrix_seq.lowner_lub_is_limit assms by auto
  then have lim1: "\<forall>i<d. \<forall>j<d. (\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub f) $$ (i, j)"
    using limit_mat_def assms by auto

  have dimcf: "\<forall>n. c \<cdot>\<^sub>m f n \<in> carrier_mat d d" using assms unfolding matrix_seq_def by fastforce
  moreover have "\<forall>n. partial_density_operator (c \<cdot>\<^sub>m f n)" using assms
    unfolding matrix_seq_def partial_density_operator_def using positive_scale by blast
  moreover have "\<forall>n.  c \<cdot>\<^sub>m f n \<le>\<^sub>L  c \<cdot>\<^sub>m f (Suc n)" using lowner_le_smult assms(1,3)
    unfolding matrix_seq_def partial_density_operator_def by blast
  ultimately have mscf: "matrix_seq d (\<lambda>n. c \<cdot>\<^sub>m f n)"  unfolding matrix_seq_def by auto
  then have mslfg: "matrix_seq.lowner_is_lub (\<lambda>n. c \<cdot>\<^sub>m f n) (matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n))"
    using matrix_seq.lowner_lub_prop by auto
  then have "limit_mat (\<lambda>n. c \<cdot>\<^sub>m f n) (matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n)) d"
    using matrix_seq.lowner_lub_is_limit mscf by auto
  then have lim3: "\<forall>i<d. \<forall>j<d. (\<lambda>n. (c \<cdot>\<^sub>m f n) $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n)) $$ (i, j)"
    using limit_mat_def assms by auto

  from mslfg mscf have dleft: "matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n) \<in> carrier_mat d d"
    using matrix_seq.lowner_is_lub_dim by auto
  have dllf: "matrix_seq.lowner_lub f \<in> carrier_mat d d"
    using matrix_seq.lowner_is_lub_dim assms(1) msf unfolding matrix_seq_def by auto
  then  have dright: "c \<cdot>\<^sub>m matrix_seq.lowner_lub f \<in> carrier_mat d d" using index_smult_mat(2,3) by auto
  have "\<forall> i<d. \<forall> j<d. \<forall> n. (c \<cdot>\<^sub>m f n) $$ (i, j) = c * f n $$ (i, j)"
    using assms(1) unfolding matrix_seq_def using index_smult_mat(1)
    by (metis carrier_matD(1-2))
  then have smult: "\<forall>i<d. \<forall>j<d. (\<lambda>n.  c * f n $$ (i, j)) \<longlonglongrightarrow> (matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n)) $$ (i, j)"
    using lim3 by auto
  have ij: "(c \<cdot>\<^sub>m matrix_seq.lowner_lub f) $$ (i, j) = (matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m f n)) $$ (i, j)"
    if i: "i < d" and j: "j < d" for i j
  proof -
    have "(\<lambda>n. f n $$ (i, j)) \<longlonglongrightarrow> matrix_seq.lowner_lub f $$ (i, j)" using lim1 i j by auto
    moreover have "\<forall>i<d. \<forall>j<d.(c \<cdot>\<^sub>m matrix_seq.lowner_lub f) $$ (i, j) =  c *  matrix_seq.lowner_lub f $$ (i, j)"
      using index_smult_mat dllf by fastforce
    ultimately have "\<forall>i<d. \<forall>j<d. (\<lambda>n.  c * f n $$ (i, j)) \<longlonglongrightarrow>(c \<cdot>\<^sub>m matrix_seq.lowner_lub f) $$ (i, j)"
      using tendsto_intros(18)[of "\<lambda>n. c" "c" sequentially "\<lambda>n. f n $$ (i, j)" "matrix_seq.lowner_lub f $$ (i, j)"] i j
      by (simp add: lim1 tendsto_mult_left)
    then show ?thesis using smult i j LIMSEQ_unique by metis
  qed

  from dleft dright ij show ?thesis
    using mat_eq_iff[of "matrix_seq.lowner_lub  (\<lambda>n. c \<cdot>\<^sub>m f n)" "c \<cdot>\<^sub>m matrix_seq.lowner_lub f"]
    by (metis (mono_tags) carrier_matD(1) carrier_matD(2))
qed

lemma trace_matrix_sum_linear:
  fixes f :: "nat \<Rightarrow> complex mat"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> trace (matrix_sum d f n) = sum (\<lambda>k. trace (f k)) {0..<n}"
proof (induct n)
  case 0
  show ?case by auto
next
  case (Suc n)
  then have "\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d" by auto
  then have ds: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim by auto
  have "trace (matrix_sum d f (Suc n)) = trace (f n) + trace (matrix_sum d f n)"
    unfolding matrix_sum.simps apply (mat_assoc d) using ds Suc by auto
  also have "\<dots> = sum (trace \<circ> f) {0..<n} + (trace \<circ> f) n" using Suc by auto
  also have "\<dots> = sum (trace \<circ> f) {0..<Suc n}" by auto
  finally show ?case by auto
qed

lemma matrix_sum_distrib_left:
  fixes f :: "nat \<Rightarrow> complex mat"
  shows "P \<in> carrier_mat d d \<Longrightarrow> (\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d) \<Longrightarrow> matrix_sum d (\<lambda>k. P * (f k)) n = P * (matrix_sum d f n)"
proof (induct n)
  case 0
  show ?case unfolding matrix_sum.simps using 0 by auto
next
  case (Suc n)
  then have "\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d" by auto
  then have ds: "matrix_sum d f n \<in> carrier_mat d d" using matrix_sum_dim by auto
  then have dPf: "\<And>k. k < n \<Longrightarrow> P * f k \<in> carrier_mat d d" using Suc by auto
  then have "matrix_sum d (\<lambda>k. P * f k) n \<in> carrier_mat d d" using matrix_sum_dim[OF dPf] by auto
  have "matrix_sum d (\<lambda>k. P * f k) (Suc n) = P * f n + matrix_sum d (\<lambda>k. P * f k) n " unfolding matrix_sum.simps using Suc(2) by auto
  also have "\<dots> = P * f n + P * matrix_sum d f n" using Suc by auto
  also have "\<dots> = P * (f n + matrix_sum d f n)" apply (mat_assoc d) using ds dPf Suc by auto
  finally show "matrix_sum d (\<lambda>k. P * f k) (Suc n) = P * (matrix_sum d f (Suc n))" by auto
qed

subsection \<open>Measurement\<close>

definition measurement :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> bool" where
  "measurement d n M \<longleftrightarrow> (\<forall>j < n. M j \<in> carrier_mat d d)
                        \<and> matrix_sum d (\<lambda>j. (adjoint (M j)) * M j) n = 1\<^sub>m d"

lemma measurement_dim:
  assumes "measurement d n M"
  shows "\<And>k. k < n \<Longrightarrow> (M k) \<in> carrier_mat d d"
  using assms unfolding measurement_def by auto

lemma measurement_id2:
  assumes "measurement d 2 M"
  shows "adjoint (M 0) * M 0 + adjoint (M 1) * M 1 = 1\<^sub>m d"
proof -
  have ssz: "(Suc (Suc 0)) = 2" by auto
  have "M 0 \<in> carrier_mat d d" "M 1 \<in> carrier_mat d d" using assms measurement_def by auto
  then have "adjoint (M 0) * M 0 + adjoint (M 1) * M 1 = matrix_sum d (\<lambda>j. (adjoint (M j)) * M j) (Suc (Suc 0)) "
    by auto
  also have "\<dots> = matrix_sum d (\<lambda>j. (adjoint (M j)) * M j) (2::nat)" by (subst ssz, auto)
  also have "\<dots> = 1\<^sub>m d" using measurement_def[of d 2 M] assms by auto
  finally show ?thesis by auto
qed

text \<open>Result of measurement on $\rho$ by matrix M\<close>
definition measurement_res :: "complex mat \<Rightarrow> complex mat \<Rightarrow> complex mat" where
  "measurement_res M \<rho> = M * \<rho> * adjoint M"

lemma add_positive_le_reduce1:
  assumes dA: "A \<in> carrier_mat n n" and dB: "B \<in> carrier_mat n n" and dC: "C \<in> carrier_mat n n"
    and pB: "positive B" and le: "A + B \<le>\<^sub>L C"
  shows "A \<le>\<^sub>L C"
  unfolding lowner_le_def positive_def
proof (auto simp add: carrier_matD[OF dA] carrier_matD[OF dC] simp del: less_eq_complex_def)
  have eq: "C - (A + B) = (C - A + (-B))" using dA dB dC by auto
  have "positive (C - (A + B))" using le lowner_le_def dA dB dC by auto
  with eq have p: "positive (C - A + (-B))" by auto
  fix v :: "complex vec" assume " n = dim_vec v"
  then have dv: "v \<in> carrier_vec n" by auto
  have ge: "inner_prod v (B *\<^sub>v v) \<ge> 0" using pB dv dB positive_def by auto
  have "0 \<le> inner_prod v ((C - A + (-B)) *\<^sub>v v) " using p positive_def dv dA dB dC by auto
  also have "\<dots> = inner_prod v ((C - A)*\<^sub>v v + (-B) *\<^sub>v v) "
    using dv dA dB dC add_mult_distrib_mat_vec[OF minus_carrier_mat[OF dA]] by auto
  also have "\<dots> = inner_prod v ((C - A) *\<^sub>v v) + inner_prod v ((-B) *\<^sub>v v)"
    apply (subst inner_prod_distrib_right)
    by (rule dv, auto simp add: mult_mat_vec_carrier[OF minus_carrier_mat[OF dA]] mult_mat_vec_carrier[OF uminus_carrier_mat[OF dB]] dv)
  also have "\<dots> = inner_prod v ((C - A) *\<^sub>v v) - inner_prod v (B *\<^sub>v v)" using dB dv by auto
  also have "\<dots> \<le> inner_prod v ((C - A) *\<^sub>v v)" using ge by auto
  finally show "0 \<le> inner_prod v ((C - A) *\<^sub>v v)".
qed

lemma add_positive_le_reduce2:
  assumes dA: "A \<in> carrier_mat n n" and dB: "B \<in> carrier_mat n n" and dC: "C \<in> carrier_mat n n"
    and pB: "positive B" and le: "B + A \<le>\<^sub>L C"
  shows "A \<le>\<^sub>L C"
  apply (subgoal_tac "B + A = A + B") using add_positive_le_reduce1[of A n B C] assms by auto

lemma measurement_le_one_mat:
  assumes "measurement d n f"
  shows "\<And>j. j < n \<Longrightarrow> adjoint (f j) * f j \<le>\<^sub>L 1\<^sub>m d"
proof -
  fix j assume j: "j < n"
  define M where "M = adjoint (f j) * f j"
  have df: "k < n \<Longrightarrow> f k \<in> carrier_mat d d" for k using assms measurement_dim by auto
  have daf: "k < n \<Longrightarrow> adjoint (f k) * f k \<in> carrier_mat d d" for k
  proof -
    assume "k < n"
    then have "f k \<in> carrier_mat d d" "adjoint (f k) \<in> carrier_mat d d" using df adjoint_dim by auto
    then show "adjoint (f k) * f k \<in> carrier_mat d d" by auto
  qed
  have pafj: "k < n \<Longrightarrow> positive (adjoint (f k) * (f k)) "  for k
    apply (subst (2) adjoint_adjoint[of "f k", symmetric])
    by (metis adjoint_adjoint daf positive_if_decomp)
  define f' where "\<And>k. f' k = (if k = j then 0\<^sub>m d d else adjoint (f k) * f k)"
  have pf': "k < n \<Longrightarrow> positive (f' k)" for k unfolding f'_def using positive_zero pafj j by auto
  have df': "k < n \<Longrightarrow> f' k \<in> carrier_mat d d" for k using daf j zero_carrier_mat f'_def by auto
  then have dsf': "matrix_sum d f' n \<in> carrier_mat d d" using matrix_sum_dim[of n f' d] by auto
  have psf': "positive (matrix_sum d f' n)" using matrix_sum_positive pafj df' pf' by auto
  have "M + matrix_sum d f' n = matrix_sum d (\<lambda>k. adjoint (f k) * f k) n"
    using matrix_sum_remove[OF j , of "(\<lambda>k. adjoint (f k) * f k)", OF daf, of f'] f'_def unfolding M_def by auto
  also have "\<dots> = 1\<^sub>m d" using measurement_def assms by auto
  finally have "M + matrix_sum d f' n = 1\<^sub>m d".
  moreover have "1\<^sub>m d \<le>\<^sub>L 1\<^sub>m d" using lowner_le_refl[of _ d] by auto
  ultimately have "(M + matrix_sum d f' n) \<le>\<^sub>L 1\<^sub>m d" by auto
  then show "M \<le>\<^sub>L 1\<^sub>m d" unfolding M_def using add_positive_le_reduce1[OF _ dsf' one_carrier_mat psf'] daf j by auto
qed

lemma pdo_close_under_measurement:
  fixes M \<rho> :: "complex mat"
  assumes dM: "M \<in> carrier_mat n n" and dr: "\<rho> \<in> carrier_mat n n"
    and pdor: "partial_density_operator \<rho>"
    and le: "adjoint M * M \<le>\<^sub>L 1\<^sub>m n"
  shows "partial_density_operator (M * \<rho> * adjoint M)"
  unfolding partial_density_operator_def
proof
  show "positive (M * \<rho> * adjoint M)"
    using positive_close_under_left_right_mult_adjoint[OF dM dr] pdor partial_density_operator_def by auto
next
  have daM: "adjoint M \<in> carrier_mat n n" using dM by auto
  then have daMM: "adjoint M * M \<in> carrier_mat n n" using dM by auto
  have "trace (M * \<rho> * adjoint M) = trace (adjoint M * M * \<rho>)"
    using dM dr by (mat_assoc n)
  also have "\<dots> \<le> trace (1\<^sub>m n * \<rho>)"
    using lowner_le_trace[where ?B = "1\<^sub>m n" and ?A = "adjoint M * M", OF daMM one_carrier_mat] le dr pdor by auto
  also have "\<dots> = trace \<rho>" using dr by auto
  also have "\<dots> \<le> 1" using pdor partial_density_operator_def by auto
  finally show "trace (M * \<rho> * adjoint M) \<le> 1" by auto
qed

lemma trace_measurement:
  assumes m: "measurement d n M" and dA: "A \<in> carrier_mat d d"
  shows "trace (matrix_sum d (\<lambda>k. (M k) * A * adjoint (M k)) n) = trace A"
proof -
  have dMk: "k < n \<Longrightarrow> (M k) \<in> carrier_mat d d" for k using m unfolding measurement_def by auto
  then have daMk: "k < n \<Longrightarrow> adjoint (M k) \<in> carrier_mat d d" for k using m adjoint_dim unfolding measurement_def by auto
  have d1: "k < n \<Longrightarrow> M k * A * adjoint (M k) \<in> carrier_mat d d"for k using dMk daMk dA by fastforce
  then have ds1: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. M k * A * adjoint (M k)) k \<in> carrier_mat d d" for k
    using matrix_sum_dim[of k "\<lambda>k. M k * A * adjoint (M k)" d] by auto
  have d2: "k < n \<Longrightarrow> adjoint (M k) *M k * A  \<in> carrier_mat d d" for k using daMk dMk dA by fastforce
  then have ds2: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. adjoint (M k) *M k * A) k \<in> carrier_mat d d" for k
    using matrix_sum_dim[of k "\<lambda>k. adjoint (M k) *M k * A" d] by auto
  have daMMk: "k < n \<Longrightarrow> adjoint (M k) * M k \<in> carrier_mat d d" for k using dMk by fastforce
  have "k \<le> n \<Longrightarrow> trace (matrix_sum d (\<lambda>k. (M k) * A * adjoint (M k)) k) = trace (matrix_sum d (\<lambda>k. adjoint (M k) * (M k) * A) k)" for k
  proof (induct k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    then have k: "k < n" by auto
    have "trace (M k * A * adjoint (M k)) = trace (adjoint (M k) * M k * A)"
      using dA apply (mat_assoc d) using dMk k by auto
    then show ?case unfolding matrix_sum.simps using ds1 ds2 d1 d2 k Suc daMk dMk dA
      by (subst trace_add_linear[of _ d], auto)+
  qed
  then have "trace (matrix_sum d (\<lambda>k. (M k) * A * adjoint (M k)) n) = trace (matrix_sum d (\<lambda>k. adjoint (M k) * (M k) * A) n)" by auto
  also have "\<dots> = trace (matrix_sum d (\<lambda>k. adjoint (M k) * (M k)) n * A)" using matrix_sum_mult_right[OF daMMk, of n id A] dA by auto
  also have "\<dots> = trace A" using m dA unfolding measurement_def by auto
  finally show ?thesis by auto
qed

lemma mat_inc_seq_positive_transform:
  assumes dfn: "\<And>n. f n \<in> carrier_mat d d"
    and inc: "\<And>n. f n \<le>\<^sub>L f (Suc n)"
  shows "\<And>n. f n - f 0 \<in> carrier_mat d d" and "\<And>n. (f n - f 0) \<le>\<^sub>L (f (Suc n) - f 0)"
proof -
  show "\<And>n. f n - f 0 \<in> carrier_mat d d" using dfn by fastforce
  have "f 0 \<le>\<^sub>L f 0" using lowner_le_refl[of "f 0" d] dfn by auto
  then show "(f n - f 0) \<le>\<^sub>L (f (Suc n) - f 0)" for n
    using lowner_le_minus[of "f n" d "f (Suc n)" "f 0" "f 0"] dfn inc by fastforce
qed

lemma mat_inc_seq_lub:
  assumes dfn: "\<And>n. f n \<in> carrier_mat d d"
    and inc: "\<And>n. f n \<le>\<^sub>L f (Suc n)"
    and ub: "\<And>n. f n \<le>\<^sub>L A"
  shows "\<exists>B. lowner_is_lub f B \<and> limit_mat f B d"
proof -
  have dmfn0: "\<And>n. f n - f 0 \<in> carrier_mat d d" and incm0: "\<And>n. (f n - f 0) \<le>\<^sub>L (f (Suc n) - f 0)"
    using mat_inc_seq_positive_transform[OF dfn, of id] assms by auto
  define c where "c = 1 / (trace (A - f 0) + 1)"
  have "f 0 \<le>\<^sub>L A" using ub by auto
  then have dA: "A \<in> carrier_mat d d" using ub unfolding lowner_le_def using dfn[of 0] by fastforce
  then have dAmf0: "A - f 0 \<in> carrier_mat d d" using dfn[of 0] by auto
  have "positive (A - f 0)" using ub lowner_le_def by auto
  then have tgeq0: "trace (A - f 0) \<ge> 0" using positive_trace dAmf0 by auto
  then have "trace (A - f 0) + 1 > 0" by auto
  then have gtc: "c > 0" unfolding c_def using complex_is_Real_iff by auto
  then have gtci: "(1 / c) > 0" using complex_is_Real_iff by auto

  have "trace (c \<cdot>\<^sub>m (A - f 0)) = c * trace (A - f 0)"
    using trace_smult dAmf0 by auto
  also have "\<dots> = (1 / (trace (A - f 0) + 1)) * trace (A - f 0)" unfolding c_def by auto
  also have "\<dots> < 1" using tgeq0 by (simp add: complex_is_Real_iff)
  finally have lt1: "trace (c \<cdot>\<^sub>m (A - f 0)) < 1".

  have le0: "- f 0 \<le>\<^sub>L - f 0" using lowner_le_refl[of "- f 0" d] dfn by auto

  have dmf0: "- f 0 \<in> carrier_mat d d" using dfn by auto
  have mf0smcle: "(c \<cdot>\<^sub>m (X - f 0)) \<le>\<^sub>L (c \<cdot>\<^sub>m (Y - f 0))" if "X \<le>\<^sub>L Y" and "X \<in> carrier_mat d d" and "Y \<in> carrier_mat d d" for X Y
  proof -
    have "(X - f 0) \<le>\<^sub>L (Y - f 0)"
      using lowner_le_minus[of "X" d "Y" "f 0" "f 0"] that dfn lowner_le_refl by auto
    then show ?thesis using lowner_le_smultc[of c "(X - f 0)" "Y - f 0" d] using that dfn gtc by fastforce
  qed
  have "(c \<cdot>\<^sub>m (f n - f 0)) \<le>\<^sub>L (c \<cdot>\<^sub>m (A - f 0))" for n
    using mf0smcle ub dfn dA by auto
  then have "trace (c \<cdot>\<^sub>m (f n - f 0)) \<le> trace (c \<cdot>\<^sub>m (A - f 0))" for n
    using lowner_le_imp_trace_le[of "c \<cdot>\<^sub>m (f n - f 0)" d] dmfn0 dAmf0 by auto
  then have trlt1: "trace (c \<cdot>\<^sub>m (f n - f 0)) < 1" for n using lt1 by fastforce

  have "f 0 \<le>\<^sub>L f n" for n
  proof (induct n)
    case 0
    then show ?case using dfn lowner_le_refl by auto
  next
    case (Suc n)
    then show ?case using dfn lowner_le_trans[of "f 0" d "f n"] inc by auto
  qed
  then have "positive (f n - f 0)" for n using lowner_le_def by auto
  then have p: "positive (c \<cdot>\<^sub>m (f n - f 0))" for n 
    by (intro positive_smult, insert gtc dmfn0, auto)

  have inc': "c \<cdot>\<^sub>m (f n - f 0) \<le>\<^sub>L c \<cdot>\<^sub>m (f (Suc n) - f 0)" for n
    using incm0 lowner_le_smultc[of c "f n - f 0"] gtc dmfn0 by fastforce

  define g where "g n = c \<cdot>\<^sub>m (f n - f 0)" for n
  then have "positive (g n)" and "trace (g n) < 1" and "(g n) \<le>\<^sub>L (g (Suc n))" and dgn: "(g n) \<in> carrier_mat d d" for n
    unfolding g_def using p trlt1 inc' dmfn0 by auto
  then have ms: "matrix_seq d g" unfolding matrix_seq_def partial_density_operator_def by fastforce
  then have uniM: "\<exists>!M. matrix_seq.lowner_is_lub g M" using matrix_seq.lowner_lub_unique by auto
  then obtain M where M: "matrix_seq.lowner_is_lub g M" by auto
  then have leg: "g n \<le>\<^sub>L M" and lubg: "\<And>M'. (\<forall>n. g n \<le>\<^sub>L M') \<longrightarrow> M \<le>\<^sub>L M'" for n
    unfolding matrix_seq.lowner_is_lub_def[OF ms] by auto
  have "M = matrix_seq.lowner_lub g"
    using matrix_seq.lowner_lub_def[OF ms] M uniM theI_unique[of "matrix_seq.lowner_is_lub g"] by auto
  then have limg: "limit_mat g M d" using M matrix_seq.lowner_lub_is_limit[OF ms] by auto
  then have dM: "M \<in> carrier_mat d d" unfolding limit_mat_def by auto

  define B where "B = f 0 + (1 / c) \<cdot>\<^sub>m M"
  have eqinv: "f 0 + (1 / c) \<cdot>\<^sub>m (c \<cdot>\<^sub>m (X - f 0)) = X" if "X \<in> carrier_mat d d" for X
  proof -
    have "f 0 + (1 / c) \<cdot>\<^sub>m (c \<cdot>\<^sub>m (X - f 0)) = f 0 + (1 / c * c) \<cdot>\<^sub>m (X - f 0)"
      apply (subgoal_tac "(1 / c) \<cdot>\<^sub>m (c \<cdot>\<^sub>m (X - f 0)) = (1 / c * c) \<cdot>\<^sub>m (X - f 0)", simp)
      using smult_smult_mat dfn that by auto
    also have "\<dots> = f 0 + 1 \<cdot>\<^sub>m (X - f 0)" using gtc by auto
    also have "\<dots> = f 0 + (X - f 0)" by auto
    also have "\<dots> = (- f 0) + f 0 + X" apply (mat_assoc d) using that dfn by auto
    also have "\<dots> = 0\<^sub>m d d + X" using dfn uminus_l_inv_mat[of "f 0" d d] by fastforce
    also have "\<dots> = X" using that by auto
    finally show ?thesis by auto
  qed
  have "limit_mat (\<lambda>n. (1 / c) \<cdot>\<^sub>m g n) ((1 / c) \<cdot>\<^sub>m M) d" using limit_mat_scale[OF limg] gtci by auto
  then have "limit_mat (\<lambda>n. f 0 + (1 / c) \<cdot>\<^sub>m g n) (f 0 + (1 / c) \<cdot>\<^sub>m M ) d"
    using mat_add_limit[of "f 0"] limg dfn unfolding mat_add_seq_def by auto
  then have limf: "limit_mat f B d" using eqinv[OF dfn] unfolding B_def g_def by auto

  have f0acmcile: "(f 0 + (1 / c) \<cdot>\<^sub>m X) \<le>\<^sub>L (f 0 + (1 / c) \<cdot>\<^sub>m Y )" if "X \<le>\<^sub>L Y" and "X \<in> carrier_mat d d" and "Y \<in> carrier_mat d d" for X Y
  proof -
    have "((1 / c) \<cdot>\<^sub>m X) \<le>\<^sub>L ((1 / c) \<cdot>\<^sub>m Y)"
      using lowner_le_smultc[of "1/c"] that gtci by fastforce
    then show "(f 0 + (1 / c) \<cdot>\<^sub>m X) \<le>\<^sub>L (f 0 + (1 / c) \<cdot>\<^sub>m Y)"
      using lowner_le_add[of _ d _ "(1 / c) \<cdot>\<^sub>m X" "(1 / c) \<cdot>\<^sub>m Y"]
        that gtci dfn lowner_le_refl[of "f 0", OF dfn] by fastforce
  qed

  have "(f 0 + (1 / c) \<cdot>\<^sub>m g n) \<le>\<^sub>L (f 0 + (1 / c) \<cdot>\<^sub>m M )" for n
    using f0acmcile[OF leg dgn dM] by auto
  then have lubf: "f n \<le>\<^sub>L B" for n using eqinv[OF dfn] g_def B_def by auto

  {
    fix B' assume asm: "\<forall>n. f n \<le>\<^sub>L B'"
    then have "f 0 \<le>\<^sub>L B'" by auto
    then have dB': "B' \<in> carrier_mat d d" unfolding lowner_le_def using dfn[of 0] by auto
    have "f n \<le>\<^sub>L B'" for n using asm by auto
    then have "(c \<cdot>\<^sub>m (f n - f 0)) \<le>\<^sub>L (c \<cdot>\<^sub>m (B' - f 0))" for n
      using mf0smcle[of "f n" B'] dfn dB' by auto
    then have "g n \<le>\<^sub>L (c \<cdot>\<^sub>m (B' - f 0))" for n using g_def by auto
    then have "M \<le>\<^sub>L  (c \<cdot>\<^sub>m (B' - f 0))" using lubg by auto
    then have "(f 0 + (1 / c) \<cdot>\<^sub>m M) \<le>\<^sub>L (f 0 + (1 / c) \<cdot>\<^sub>m (c \<cdot>\<^sub>m (B' - f 0)))"
      using f0acmcile[of "M" "(c \<cdot>\<^sub>m (B' - f 0))", OF _ dM] using dB' dfn by fastforce
    then have "B \<le>\<^sub>L B'" unfolding B_def using eqinv[OF dB'] by auto
  }
  with limf lubf have "((\<forall>n. f n \<le>\<^sub>L B) \<and> (\<forall>M'. (\<forall>n. f n \<le>\<^sub>L M') \<longrightarrow> B \<le>\<^sub>L M')) \<and> limit_mat f B d" by auto
  then show ?thesis unfolding lowner_is_lub_def by auto
qed

end
