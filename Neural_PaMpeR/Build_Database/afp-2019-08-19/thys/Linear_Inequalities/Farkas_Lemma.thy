section \<open>Farkas' Lemma\<close>

text \<open>We prove two variants of Farkas' lemma. Note that type here is more general than in the versions
  of Farkas' Lemma which are in the AFP-entry Farkas-Lemma, which is restricted to rational matrices.
  However, there $\delta$-rationals are supported, which are not present here.\<close>

theory Farkas_Lemma
  imports Fundamental_Theorem_Linear_Inequalities
begin

context gram_schmidt
begin

lemma Farkas_Lemma: fixes A :: "'a mat" and b :: "'a vec"
  assumes A: "A \<in> carrier_mat n nr" and b: "b \<in> carrier_vec n"
  shows "(\<exists> x. x \<ge> 0\<^sub>v nr \<and> A *\<^sub>v x = b) \<longleftrightarrow> (\<forall> y. y \<in> carrier_vec n \<longrightarrow> A\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> b \<ge> 0)"
proof -
  let ?C = "set (cols A)"
  from A have C: "?C \<subseteq> carrier_vec n" and C': " \<forall>w\<in>set (cols A). dim_vec w = n"
    unfolding cols_def by auto
  have "(\<exists> x. x \<ge> 0\<^sub>v nr \<and> A *\<^sub>v x = b) = (b \<in> cone ?C)"
    using cone_of_cols[OF A b] by simp
  also have "\<dots> = (\<nexists>y. y \<in> carrier_vec n \<and> (\<forall>a\<^sub>i\<in>?C. 0 \<le> y \<bullet> a\<^sub>i) \<and> y \<bullet> b < 0)"
    unfolding fundamental_theorem_of_linear_inequalities(3)[OF C finite_set] mem_Collect_eq
    using b by auto
  also have "\<dots> = (\<forall>y. y \<in> carrier_vec n \<longrightarrow> (\<forall>a\<^sub>i\<in>?C. 0 \<le> y \<bullet> a\<^sub>i) \<longrightarrow> y \<bullet> b \<ge> 0)"
    by auto
  also have "\<dots> = (\<forall> y. y \<in> carrier_vec n \<longrightarrow> A\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v nr \<longrightarrow> y \<bullet> b \<ge> 0)"
  proof (intro all_cong imp_cong refl)
    fix y :: "'a vec"
    assume y: "y \<in> carrier_vec n"
    have "(\<forall>a\<^sub>i\<in> ?C. 0 \<le> y \<bullet> a\<^sub>i) = (\<forall>a\<^sub>i\<in> ?C. 0 \<le> a\<^sub>i \<bullet> y)"
      by (intro ball_cong[OF refl], subst comm_scalar_prod[OF y], insert C, auto)
    also have "\<dots> = (0\<^sub>v nr \<le> A\<^sup>T *\<^sub>v y)"
      unfolding less_eq_vec_def using C A y by (auto simp: cols_def)
    finally show "(\<forall>a\<^sub>i\<in>set (cols A). 0 \<le> y \<bullet> a\<^sub>i) = (0\<^sub>v nr \<le> A\<^sup>T *\<^sub>v y)" .
  qed
  finally show ?thesis .
qed

lemma Farkas_Lemma':
  fixes A :: "'a mat" and b :: "'a vec"
  assumes A: "A \<in> carrier_mat nr nc" and b: "b\<in> carrier_vec nr"
  shows "(\<exists>x. x\<in> carrier_vec nc \<and> A *\<^sub>v x \<le> b)
         \<longleftrightarrow> (\<forall>y. y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = 0\<^sub>v nc \<longrightarrow> y \<bullet> b \<ge> 0)"
proof -
  define B where "B = (1\<^sub>m nr) @\<^sub>c (A @\<^sub>c -A)"   
  define b' where "b' = 0\<^sub>v nc @\<^sub>v (b @\<^sub>v -b)" 
  define n where "n = nr + (nc + nc)" 
  have id0: "0\<^sub>v (nr + (nc + nc)) = 0\<^sub>v nr @\<^sub>v (0\<^sub>v nc @\<^sub>v 0\<^sub>v nc)" by (intro eq_vecI, auto)
  have idcarr: "(1\<^sub>m nr) \<in> carrier_mat nr nr" by auto
  have B: "B \<in> carrier_mat nr n" unfolding B_def n_def using A by auto
  have "(\<exists>x \<in> carrier_vec nc. A *\<^sub>v x \<le> b) =
        (\<exists>x1 \<in> carrier_vec nr. \<exists>x2 \<in> carrier_vec nc. \<exists>x3 \<in> carrier_vec nc. 
         x1 \<ge> 0\<^sub>v nr \<and> x2 \<ge> 0\<^sub>v nc \<and> x3 \<ge> 0\<^sub>v nc \<and> B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = b)"
  proof 
    assume "\<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> b"
    from this obtain x where Axb: "A *\<^sub>v x \<le> b" and xcarr: "x \<in> carrier_vec nc" by auto
    have bmAx: "b - A *\<^sub>v x \<in> carrier_vec nr" using A b xcarr by simp
    define x1 where "x1 = b - A *\<^sub>v x"
    have x1: "x1 \<in> carrier_vec nr" using bmAx unfolding x1_def by (simp add: xcarr)
    define x2 where "x2 = vec (dim_vec x) (\<lambda>i. if x $ i \<ge> 0 then x $ i else 0)"
    have x2: "x2 \<in> carrier_vec nc" using xcarr unfolding x2_def by simp
    define x3 where "x3 = vec (dim_vec x) (\<lambda>i. if x $ i < 0 then -x $ i else 0)"
    have x3: "x3 \<in> carrier_vec nc" using xcarr unfolding x3_def by simp
    have x2x3carr: "x2 @\<^sub>v x3 \<in> carrier_vec (nc + nc)" using x2 x3 by simp
    have x2x3x: "x2 - x3 = x" unfolding x2_def x3_def by auto
    have "A *\<^sub>v x -b \<le> 0\<^sub>v nr" using vec_le_iff_diff_le_0 b
      by (metis A Axb carrier_matD(1) dim_mult_mat_vec)
    hence x1lez: "x1 \<ge> 0\<^sub>v nr" using x1 unfolding x1_def
      by (smt A Axb carrier_matD(1) carrier_vecD diff_ge_0_iff_ge dim_mult_mat_vec 
          index_minus_vec(1) index_zero_vec(1) index_zero_vec(2) less_eq_vec_def)
    have x2lez: "x2 \<ge> 0\<^sub>v nc" using x2 less_eq_vec_def unfolding x2_def by fastforce
    have x3lez: "x3 \<ge> 0\<^sub>v nc" using x3 less_eq_vec_def unfolding x3_def by fastforce
    have B1: "(1\<^sub>m nr) *\<^sub>v x1 = b - A *\<^sub>v x" using xcarr x1 unfolding x1_def by simp
    have "A *\<^sub>v x2 + (-A) *\<^sub>v x3 = A *\<^sub>v x2 + A *\<^sub>v (-x3)" using x2 x3 A by auto
    also have "\<dots> = A *\<^sub>v (x2 + (-x3))" using A x2 x3
      by (metis mult_add_distrib_mat_vec uminus_carrier_vec)
    also have "\<dots> = A *\<^sub>v x" using x2x3x minus_add_uminus_vec x2 x3 by fastforce
    finally have B2:"A *\<^sub>v x2 + (-A) *\<^sub>v x3 = A *\<^sub>v x" by auto
    have "B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = (1\<^sub>m nr) *\<^sub>v x1 + (A *\<^sub>v x2 + (-A) *\<^sub>v x3)" (is "\<dots> = ?p1 + ?p2")
      using x1 x2 x3 A mat_mult_append_cols unfolding B_def
      by (subst mat_mult_append_cols[OF _ _ x1 x2x3carr], auto simp add: mat_mult_append_cols)
    also have "?p1 = b - A *\<^sub>v x" using B1 unfolding x1_def by auto
    also have "?p2 = A *\<^sub>v x" using B2 by simp
    finally have res: "B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = b" using A xcarr b by auto
    show "\<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> b \<Longrightarrow> \<exists>x1\<in>carrier_vec nr. \<exists>x2\<in>carrier_vec nc. \<exists>x3\<in>carrier_vec nc.
          0\<^sub>v nr \<le> x1 \<and> 0\<^sub>v nc \<le> x2 \<and> 0\<^sub>v nc \<le> x3 \<and> B *\<^sub>v (x1 @\<^sub>v x2 @\<^sub>v x3) = b"
      using x1 x2 x3 x1lez x2lez x3lez res by auto
  next
    assume "\<exists>x1 \<in> carrier_vec nr. \<exists>x2 \<in> carrier_vec nc. \<exists>x3 \<in> carrier_vec nc. 
            x1 \<ge> 0\<^sub>v nr \<and> x2 \<ge> 0\<^sub>v nc \<and> x3 \<ge> 0\<^sub>v nc \<and> B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = b"
    from this obtain x1 x2 x3 where x1: "x1 \<in> carrier_vec nr" and x1lez: "x1 \<ge> 0\<^sub>v nr" 
      and x2: "x2 \<in> carrier_vec nc" and x2lez: "x2 \<ge> 0\<^sub>v nc"
      and x3: "x3 \<in> carrier_vec nc" and x3lez: "x3 \<ge> 0\<^sub>v nc"
      and clc: "B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = b" by auto
    have x2x3carr: "x2 @\<^sub>v x3 \<in> carrier_vec (nc + nc)" using x2 x3 by simp
    define x where "x = x2 - x3"
    have xcarr: "x \<in> carrier_vec nc" using x2 x3 unfolding x_def by simp
    have "A *\<^sub>v x2 + (-A) *\<^sub>v x3 = A *\<^sub>v x2 + A *\<^sub>v (-x3)" using x2 x3 A by auto
    also have "\<dots> = A *\<^sub>v (x2 + (-x3))" using A x2 x3
      by (metis mult_add_distrib_mat_vec uminus_carrier_vec)
    also have "\<dots> = A *\<^sub>v x" using minus_add_uminus_vec x2 x3 unfolding x_def by fastforce
    finally have B2:"A *\<^sub>v x2 + (-A) *\<^sub>v x3 = A *\<^sub>v x" by auto
    have Axcarr: "A *\<^sub>v x \<in> carrier_vec nr" using A xcarr by auto
    have "b = B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3))" using clc by auto
    also have "\<dots> = (1\<^sub>m nr) *\<^sub>v x1 + (A *\<^sub>v x2 + (-A) *\<^sub>v x3)" (is "\<dots> = ?p1 + ?p2")
      using x1 x2 x3 A mat_mult_append_cols unfolding B_def
      by (subst mat_mult_append_cols[OF _ _ x1 x2x3carr], auto simp add: mat_mult_append_cols)
    also have "?p2 = A *\<^sub>v x" using B2 by simp
    finally have res: "b = (1\<^sub>m nr) *\<^sub>v x1 + A *\<^sub>v x" using A xcarr b by auto
    hence "b = x1 + A *\<^sub>v x" using x1 A b by simp
    hence "b - A *\<^sub>v x = x1" using x1 A b by auto
    hence "b - A *\<^sub>v x \<ge> 0\<^sub>v nr" using x1lez by auto
    hence "A *\<^sub>v x \<le> b" using Axcarr
      by (smt \<open>b - A *\<^sub>v x = x1\<close> \<open>b = x1 + A *\<^sub>v x\<close> carrier_vecD comm_add_vec index_zero_vec(2) 
          minus_add_minus_vec minus_cancel_vec vec_le_iff_diff_le_0 x1)
    then show "\<exists>x1\<in>carrier_vec nr. \<exists>x2\<in>carrier_vec nc. \<exists>x3\<in>carrier_vec nc.
          0\<^sub>v nr \<le> x1 \<and> 0\<^sub>v nc \<le> x2 \<and> 0\<^sub>v nc \<le> x3 \<and> B *\<^sub>v (x1 @\<^sub>v x2 @\<^sub>v x3) = b \<Longrightarrow>
          \<exists>x\<in>carrier_vec nc. A *\<^sub>v x \<le> b" using xcarr by blast
  qed
  also have "\<dots> = (\<exists>x1 \<in> carrier_vec nr. \<exists>x2 \<in> carrier_vec nc. \<exists>x3 \<in> carrier_vec nc. 
         (x1 @\<^sub>v (x2 @\<^sub>v x3)) \<ge> 0\<^sub>v n  \<and> B *\<^sub>v (x1 @\<^sub>v (x2 @\<^sub>v x3)) = b)"
    by (metis append_vec_le id0 n_def zero_carrier_vec)
  also have "\<dots> = (\<exists>x \<in> carrier_vec n. x \<ge> 0\<^sub>v n  \<and> B *\<^sub>v x = b)"
    unfolding n_def exists_vec_append by auto
  also have "\<dots> = (\<exists>x \<ge> 0\<^sub>v n. B *\<^sub>v x = b)" unfolding less_eq_vec_def by fastforce
  also have "\<dots> = (\<forall> y. y \<in> carrier_vec nr \<longrightarrow> B\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v n \<longrightarrow> y \<bullet> b \<ge> 0)"
    by (rule gram_schmidt.Farkas_Lemma[OF B b])
  also have "\<dots> = (\<forall> y. y \<in> carrier_vec nr \<longrightarrow> (y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = 0\<^sub>v nc) \<longrightarrow> y \<bullet> b \<ge> 0)" 
  proof (intro all_cong imp_cong refl)
    fix y :: "'a vec"
    assume y: "y \<in> carrier_vec nr"
    have idtcarr: "(1\<^sub>m nr)\<^sup>T \<in> carrier_mat nr nr" by auto
    have Atcarr: "A\<^sup>T \<in> carrier_mat nc nr" using A by auto
    have mAtcarr: "(-A)\<^sup>T \<in> carrier_mat nc nr" using A by auto
    have AtAtcarr: "A\<^sup>T @\<^sub>r (-A)\<^sup>T \<in> carrier_mat (nc + nc) nr" using A by auto
    have "B\<^sup>T *\<^sub>v y = ((1\<^sub>m nr)\<^sup>T @\<^sub>r A\<^sup>T @\<^sub>r (-A)\<^sup>T) *\<^sub>v y" unfolding B_def
      by (simp add: append_cols_def)
    also have "\<dots> = ((1\<^sub>m nr)\<^sup>T *\<^sub>v y) @\<^sub>v (A\<^sup>T *\<^sub>v y) @\<^sub>v ((-A)\<^sup>T *\<^sub>v y)" 
      using mat_mult_append[OF Atcarr mAtcarr y] mat_mult_append y Atcarr idtcarr mAtcarr
      by (metis AtAtcarr)
    finally have eq: "B\<^sup>T *\<^sub>v y = ((1\<^sub>m nr)\<^sup>T *\<^sub>v y) @\<^sub>v (A\<^sup>T *\<^sub>v y) @\<^sub>v ((-A)\<^sup>T *\<^sub>v y)" by auto
    have "(B\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v n) = (0\<^sub>v n \<le> (1\<^sub>m nr)\<^sup>T *\<^sub>v y @\<^sub>v A\<^sup>T *\<^sub>v y @\<^sub>v (- A)\<^sup>T *\<^sub>v y)" unfolding eq by simp
    also have "\<dots> = (((1\<^sub>m nr)\<^sup>T *\<^sub>v y) @\<^sub>v (A\<^sup>T *\<^sub>v y) @\<^sub>v ((-A)\<^sup>T *\<^sub>v y) \<ge> 0\<^sub>v nr @\<^sub>v 0\<^sub>v nc @\<^sub>v 0\<^sub>v nc)"
      using id0 by (metis eq n_def)
    also have "\<dots> = (y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v nc \<and> ((-A)\<^sup>T *\<^sub>v y) \<ge> 0\<^sub>v nc)"
      by (metis Atcarr append_vec_le mult_mat_vec_carrier one_mult_mat_vec transpose_one y zero_carrier_vec)
    also have "\<dots> = (y \<ge> 0\<^sub>v nr \<and>A\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v nc \<and> -(A\<^sup>T *\<^sub>v y) \<ge> 0\<^sub>v nc)"
      by (metis A Atcarr carrier_matD(2) carrier_vecD transpose_uminus uminus_mult_mat_vec y)
    also have "\<dots> = (y \<ge> 0\<^sub>v nr \<and>A\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v nc \<and> (A\<^sup>T *\<^sub>v y) \<le> 0\<^sub>v nc)"
      by (metis (mono_tags, lifting) A Atcarr carrier_matD(2) carrier_vecD index_zero_vec(2) 
          mAtcarr mult_mat_vec_carrier transpose_uminus uminus_mult_mat_vec uminus_uminus_vec
          vec_le_iff_diff_le_0 y zero_minus_vec)
    also have "\<dots> = (y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = 0\<^sub>v nc)" by auto
    finally show "(B\<^sup>T *\<^sub>v y \<ge> 0\<^sub>v n) = (y \<ge> 0\<^sub>v nr \<and> A\<^sup>T *\<^sub>v y = 0\<^sub>v nc)" .
  qed
  finally show ?thesis by (auto simp: less_eq_vec_def)
qed

end
end