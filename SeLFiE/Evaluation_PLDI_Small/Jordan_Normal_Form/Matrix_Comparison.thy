(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Comparison of Matrices\<close>

text \<open>We use matrices over ordered semirings to again define ordered semirings.
  There are two instances, one for ordinary semirings (where addition is monotone w.r.t. the
  strict ordering in a single argument); 
  and one for semirings like the arctic one, where addition is interpreted
  as maximum, and therefore monotonicity of the strict ordering in a single argument is no
  longer provided. 

  Both ordered semirings are used for checking termination proofs, where at the moment only
  the ordinary semirings is supported for checking complexity proofs.\<close>

theory Matrix_Comparison
imports 
  Matrix
  Matrix.Ordered_Semiring
begin

context ord
begin
definition mat_ge :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" (infix "\<ge>\<^sub>m" 50) where
  "A \<ge>\<^sub>m B = (\<forall> i < dim_row A. \<forall> j < dim_col A. A $$ (i,j) \<ge> B $$ (i,j))"

lemma mat_geI[intro]: assumes "A \<in> carrier_mat nr nc" 
  "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> A $$ (i,j) \<ge> B $$ (i,j)"
  shows "A \<ge>\<^sub>m B"
  using assms unfolding mat_ge_def by auto

lemma mat_geD[dest]: assumes "A \<ge>\<^sub>m B" and "i < dim_row A" "j < dim_col A"
  shows "A $$ (i,j) \<ge> B $$ (i,j)" 
  using assms unfolding mat_ge_def by auto

definition mat_gt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "mat_gt gt sd A B = (A \<ge>\<^sub>m B \<and> (\<exists> i < sd. \<exists> j < sd. gt (A $$ (i,j)) (B $$ (i,j))))"

lemma mat_gtI[intro]: assumes "A \<ge>\<^sub>m B"
  and "i < sd" "j < sd" "gt (A $$ (i,j)) (B $$ (i,j))"
  shows "mat_gt gt sd A B"
  using assms unfolding mat_gt_def by auto

lemma mat_gtD[dest]: assumes "mat_gt gt sd A B"
  shows "A \<ge>\<^sub>m B" "\<exists> i < sd. \<exists> j < sd. gt (A $$ (i,j)) (B $$ (i,j))"
  using assms unfolding mat_gt_def by auto

definition mat_max :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("max\<^sub>m") where
  "max\<^sub>m A B = mat (dim_row A) (dim_col A) (\<lambda> ij. max (A $$ ij) (B $$ ij))"

lemma mat_max_carrier[simp]:
  "max\<^sub>m A B \<in> carrier_mat (dim_row A) (dim_col A)"
  unfolding mat_max_def by auto

lemma mat_max_closed[intro]:
  "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> max\<^sub>m A B \<in> carrier_mat nr nc"
  unfolding mat_max_def by auto

lemma mat_max_index:
  assumes "i < dim_row A" "j < dim_col A"
  shows "(mat_max A B) $$ (i,j) = max (A $$ (i,j)) (B $$ (i,j))"
  unfolding mat_max_def using index_mat assms by auto

definition (in zero) mat_default :: "'a \<Rightarrow> nat \<Rightarrow> 'a mat" ("default\<^sub>m") where
  "default\<^sub>m d n = mat n n (\<lambda> (i,j). if i = j then d else 0)"

lemma mat_default_carrier[simp]: "default\<^sub>m d n \<in> carrier_mat n n"
  unfolding mat_default_def by auto
end


definition mat_mono :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_mono P sd A = (\<forall> j < sd. \<exists> i < sd. P (A $$ (i,j)))"

context non_strict_order
begin
lemma mat_ge_trans: assumes "A \<ge>\<^sub>m B" "B \<ge>\<^sub>m C"
  and "A \<in> carrier_mat nr nc" "B \<in> carrier_mat nr nc"
shows "A \<ge>\<^sub>m C"
  using assms ge_trans[of "B $$ (i,j)" "A $$ (i,j)" for i j] 
  unfolding mat_ge_def carrier_mat_def by auto

lemma mat_ge_refl: "A \<ge>\<^sub>m A"
  unfolding mat_ge_def by (auto simp: ge_refl)

lemma mat_max_comm: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> max\<^sub>m A B = max\<^sub>m B A"
  unfolding mat_max_def by (intro eq_matI, auto simp: max_comm)

lemma mat_max_ge: "max\<^sub>m A B \<ge>\<^sub>m A"
  unfolding mat_max_def by (intro mat_geI[of _ "dim_row A" "dim_col A"], auto)

lemma mat_max_ge_0: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> A \<ge>\<^sub>m B \<Longrightarrow> max\<^sub>m A B = A"
  unfolding mat_max_def by (intro eq_matI, auto simp: max_id)

lemma mat_max_mono: "A \<ge>\<^sub>m B \<Longrightarrow>
   A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> C \<in> carrier_mat nr nc \<Longrightarrow> 
   max\<^sub>m C A \<ge>\<^sub>m max\<^sub>m C B"
  by (intro mat_geI[of _ nr nc], auto simp: max_mono mat_max_def)
end

lemma mat_plus_left_mono: "A \<ge>\<^sub>m (B :: 'a :: ordered_ab_semigroup mat) 
  \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> C \<in> carrier_mat nr nc 
  \<Longrightarrow> A + C \<ge>\<^sub>m B + C"
  by (intro mat_geI[of _ nr nc], auto simp: plus_left_mono)

lemma mat_plus_right_mono: "B \<ge>\<^sub>m (C :: 'a :: ordered_ab_semigroup mat) 
  \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> C \<in> carrier_mat nr nc 
  \<Longrightarrow> A + B \<ge>\<^sub>m A + C"
  by (intro mat_geI[of _ nr nc], auto simp: plus_right_mono)

lemma plus_mono: "x\<^sub>1 \<ge> (x\<^sub>2 :: 'a :: ordered_ab_semigroup) \<Longrightarrow> 
  y\<^sub>1 \<ge> y\<^sub>2 \<Longrightarrow> x\<^sub>1 + y\<^sub>1 \<ge> x\<^sub>2 + y\<^sub>2"
  using ge_trans[OF plus_left_mono[of x\<^sub>2 x\<^sub>1] plus_right_mono[of y\<^sub>2 y\<^sub>1]] .

text \<open>Since one cannot use @{thm sum_mono} (it requires other 
  class constraints like @{class order}), we make our own copy of this
  fact.\<close>

lemma sum_mono_ge:
  assumes ge: "\<And>i. i\<in>K \<Longrightarrow> f (i::'a) \<ge> ((g i)::('b::ordered_semiring_0))"
  shows "(\<Sum>i\<in>K. f i) \<ge> (\<Sum>i\<in>K. g i)"
proof (cases "finite K")
  case True
  thus ?thesis using ge
  proof induct
    case empty
    show ?case by (simp add: ge_refl)
  next
    case insert
    thus ?case using plus_mono by fastforce
  qed
next
  case False then show ?thesis by (simp add: ge_refl)
qed

lemma (in one_mono_ordered_semiring_1) sum_mono_gt:
  assumes le: "\<And>i. i\<in>K \<Longrightarrow> f (i::'b) \<ge> ((g i)::'a)"
  and i: "i \<in> K"
  and gt: "f i \<succ> g i"
  and K: "finite K"
  shows "(\<Sum>i\<in>K. f i) \<succ> (\<Sum>i\<in>K. g i)"
proof -
  have id: "\<And> f. (\<Sum>i\<in>K. f i) = f i + (\<Sum>i\<in> K - {i}. f i)"
    by (rule sum.remove[OF K i])
  have ge: "(\<Sum>i\<in> K - {i}. f i) \<ge> (\<Sum>i\<in> K - {i}. g i)"
    by (rule sum_mono_ge[OF le], auto)
  show ?thesis unfolding id using compat[OF plus_right_mono[OF ge] plus_gt_left_mono[OF gt]] .
qed

lemma scalar_left_mono: assumes 
  "u \<in> carrier_vec n" "v \<in> carrier_vec n" "w \<in> carrier_vec n" 
  and "\<And> i. i < n \<Longrightarrow> u $ i \<ge> v $ i"
  and "\<And> i. i < n \<Longrightarrow> w $ i \<ge> (0 :: 'a :: ordered_semiring_0)"
  shows "u \<bullet> w \<ge> v \<bullet> w" unfolding scalar_prod_def
  by (intro sum_mono_ge times_left_mono, insert assms, auto)

lemma scalar_right_mono: assumes 
  "u \<in> carrier_vec n" "v \<in> carrier_vec n" "w \<in> carrier_vec n" 
  and "\<And> i. i < n \<Longrightarrow> v $ i \<ge> w $ i"
  and "\<And> i. i < n \<Longrightarrow> u $ i \<ge> (0 :: 'a :: ordered_semiring_0)"
  shows "u \<bullet> v \<ge> u \<bullet> w" 
proof -
  have dim: "dim_vec v = dim_vec w" using assms by auto
  show ?thesis unfolding scalar_prod_def dim
    by (intro sum_mono_ge times_right_mono, insert assms, auto)
qed

lemma mat_mult_left_mono: assumes C0: "C \<ge>\<^sub>m 0\<^sub>m n n"
  and AB: "A \<ge>\<^sub>m (B :: 'a :: ordered_semiring_0 mat)"
  and carr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A * C \<ge>\<^sub>m B * C"
proof -
  {
    fix i j
    assume i: "i < n" "j < n"
    have "row A i \<bullet> col C j \<ge> row B i \<bullet> col C j"
      by (rule scalar_left_mono[of _ n], insert C0 AB carr i, auto)
  }
  thus ?thesis 
    by (intro mat_geI[of _ n n], insert carr, auto)
qed

lemma mat_mult_right_mono: assumes A0: "A \<ge>\<^sub>m 0\<^sub>m n n" 
  and BC: "B \<ge>\<^sub>m (C :: 'a :: ordered_semiring_0 mat)"
  and carr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A * B \<ge>\<^sub>m A * C"
proof -
  {
    fix i j
    assume i: "i < n" "j < n"
    have "row A i \<bullet> col B j \<ge> row A i \<bullet> col C j"
      by (rule scalar_right_mono[of _ n], insert A0 BC carr i, auto)
  }
  thus ?thesis 
    by (intro mat_geI[of _ n n], insert carr, auto)
qed

lemma one_mat_ge_zero: "(1\<^sub>m n :: 'a :: ordered_semiring_1 mat) \<ge>\<^sub>m 0\<^sub>m n n"
  by (intro mat_geI[of _ n n], auto simp: one_ge_zero ge_refl)

context order_pair
begin
lemma mat_ge_gt_trans: assumes sd: "sd \<le> n" and AB: "A \<ge>\<^sub>m B" and BC: "mat_gt gt sd B C"
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
shows "mat_gt gt sd A C"
proof -  
  from mat_gtD[OF BC] obtain i j where ij: "i < sd" "j < sd" and gt: "B $$ (i, j) \<succ> C $$ (i, j)" 
    and BC: "B \<ge>\<^sub>m C" by auto
  from mat_ge_trans[OF AB BC A B] have AC: "A \<ge>\<^sub>m C" .
  from mat_geD[OF AB, of i j] A sd ij have ge: "A $$ (i,j) \<ge> B $$ (i,j)" by auto  
  from compat[OF ge gt] have gt: "A $$ (i, j) \<succ> C $$ (i, j)" .
  with ij AC show ?thesis by auto
qed

lemma mat_gt_ge_trans: assumes sd: "sd \<le> n" and AB: "mat_gt gt sd A B" and BC: "B \<ge>\<^sub>m C"
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
shows "mat_gt gt sd A C"
proof -  
  from mat_gtD[OF AB] obtain i j where ij: "i < sd" "j < sd" and gt: "A $$ (i, j) \<succ> B $$ (i, j)" 
    and AB: "A \<ge>\<^sub>m B" by auto
  from mat_ge_trans[OF AB BC A B] have AC: "A \<ge>\<^sub>m C" .
  from mat_geD[OF BC, of i j] B sd ij have ge: "B $$ (i,j) \<ge> C $$ (i,j)" by auto  
  from compat2[OF gt ge] have gt: "A $$ (i, j) \<succ> C $$ (i, j)" .
  with ij AC show ?thesis by auto
qed

lemma mat_gt_imp_mat_ge: "mat_gt gt sd A B \<Longrightarrow> A \<ge>\<^sub>m B"
  by (rule mat_gtD)

lemma mat_gt_trans: assumes sd: "sd \<le> n" and AB: "mat_gt gt sd A B" and BC: "mat_gt gt sd B C"
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
shows "mat_gt gt sd A C"
  using mat_ge_gt_trans[OF sd mat_gt_imp_mat_ge[OF AB] BC A B] .

lemma mat_default_ge_0: "default\<^sub>m default n \<ge>\<^sub>m 0\<^sub>m n n"
  by (intro mat_geI[of _ n n], auto simp: mat_default_def default_ge_zero ge_refl)
end

definition mat_ordered_semiring :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ordered_semiring_scheme" where
  "mat_ordered_semiring n sd gt b \<equiv> ring_mat TYPE('a) n \<lparr>
    ordered_semiring.geq = (\<ge>\<^sub>m),
    gt = mat_gt gt sd,
    max = max\<^sub>m,
    \<dots> = b\<rparr>"

lemma (in one_mono_ordered_semiring_1) mat_ordered_semiring: assumes sd_n: "sd \<le> n" 
  shows "ordered_semiring 
    (mat_ordered_semiring n sd (\<succ>) b :: ('a mat,'b) ordered_semiring_scheme)" 
  (is "ordered_semiring ?R")
proof -
  interpret semiring ?R unfolding mat_ordered_semiring_def by (rule semiring_mat)
  show ?thesis 
    by (unfold_locales, unfold ring_mat_def mat_ordered_semiring_def ordered_semiring_record_simps,
    auto intro: mat_ge_trans mat_ge_refl mat_ge_gt_trans[OF sd_n] mat_gt_ge_trans[OF sd_n] mat_max_comm
    mat_max_ge mat_max_ge_0 mat_max_mono one_mat_ge_zero mat_gt_trans[OF sd_n] mat_gt_imp_mat_ge
    mat_plus_left_mono mat_mult_left_mono mat_mult_right_mono)
qed

context weak_SN_strict_mono_ordered_semiring_1
begin

lemma weak_mat_gt_mono: assumes sd_n: "sd \<le> n" and
    orient: "\<And> A B. A \<in> carrier_mat n n \<Longrightarrow> B \<in> carrier_mat n n \<Longrightarrow> (A,B) \<in> set ABs \<Longrightarrow> mat_gt weak_gt sd A B"
   shows "\<exists> gt. SN_strict_mono_ordered_semiring_1 default gt mono \<and> 
     (\<forall> A B. A \<in> carrier_mat n n \<longrightarrow> B \<in> carrier_mat n n \<longrightarrow> (A, B) \<in> set ABs \<longrightarrow> mat_gt gt sd A B)"
proof -
  let ?n = "[0 ..< n]"
  let ?m1x = "[ A $$ (i,j) . A <- map fst ABs, i <- ?n, j <- ?n]"
  let ?m2y = "[ B $$ (i,j) . B <- map snd ABs, i <- ?n, j <- ?n]"
  let ?pairs = "concat (map (\<lambda> x. map (\<lambda> y. (x,y)) ?m2y) ?m1x)"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_mono[OF this] obtain gt where order: "SN_strict_mono_ordered_semiring_1 default gt mono" 
    and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y" by auto
  show ?thesis
  proof (intro exI allI conjI impI, rule order)
    fix A B
    assume A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
      and AB: "(A, B) \<in> set ABs"          
    from orient[OF this] have "mat_gt weak_gt sd A B" by auto
    from mat_gtD[OF this] obtain i j where
      ge: "A \<ge>\<^sub>m B" and ij: "i < sd" "j < sd" and wgt: "weak_gt (A $$ (i,j)) (B $$ (i,j))"
      by auto
    from ij \<open>sd \<le> n\<close> have ij': "i < n" "j < n" by auto
    have gt: "gt (A $$ (i,j)) (B $$ (i,j))"
      by (rule orient2, insert ij' AB wgt, force)
    show "mat_gt gt sd A B" using ij gt ge by auto
  qed
qed
end

lemma sum_mat_mono: 
  assumes A: "A \<in> carrier_mat nr nc" and B: "B \<in> carrier_mat nr nc" 
  and AB: "A \<ge>\<^sub>m (B :: 'a :: ordered_semiring_0 mat)"
  shows "sum_mat A \<ge> sum_mat B"
proof -
  from A B have id: "dim_row B = dim_row A" "dim_col B = dim_col A" by auto
  show ?thesis unfolding sum_mat_def id
    by (rule sum_mono_ge, insert mat_geD[OF AB] id, auto)
qed

context one_mono_ordered_semiring_1
begin
lemma sum_mat_mono_gt: 
  assumes "sd \<le> n"
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
  and AB: "mat_gt (\<succ>) sd A (B :: 'a mat)"
  shows "sum_mat A \<succ> sum_mat B"
proof -
  from A B have id: "dim_row B = dim_row A" "dim_col B = dim_col A" by auto
  from mat_gtD[OF AB] obtain i j where AB: "A \<ge>\<^sub>m B" and 
    ij: "i < sd" "j < sd" and gt: "A $$ (i,j) \<succ> B $$ (i,j)" by auto
  show ?thesis unfolding sum_mat_def id
    by (rule sum_mono_gt[of _ _ _ "(i,j)"], insert ij gt mat_geD[OF AB] A B \<open>sd \<le> n\<close>, auto)
qed

lemma mat_plus_gt_left_mono: assumes sd_n: "sd \<le> n" and gt: "mat_gt (\<succ>) sd A B"  
  and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and C: "C \<in> carrier_mat n n"
  shows "mat_gt (\<succ>) sd (A + C) (B + C)"
proof -
  note wf = A B C
  from mat_gtD[OF gt] obtain i j 
    where AB: "A \<ge>\<^sub>m B" and ij: "i < sd" "j < sd" and gt: "A $$ (i,j) \<succ> B $$ (i,j)" by auto
  from plus_gt_left_mono[OF gt, of "C $$ (i,j)"]
  show ?thesis
    by (intro mat_gtI[OF mat_geI[of _ n n] ij], insert mat_geD[OF AB] wf ij sd_n, auto intro: plus_left_mono)
qed

lemma mat_gt_ge_mono: "sd \<le> n \<Longrightarrow> mat_gt gt sd A B \<Longrightarrow>
   mat_gt gt sd C D \<Longrightarrow>
   A \<in> carrier_mat n n \<Longrightarrow>
   B \<in> carrier_mat n n \<Longrightarrow>
   C \<in> carrier_mat n n \<Longrightarrow>
   D \<in> carrier_mat n n \<Longrightarrow>
   mat_gt gt sd (A + C) (B + D)"
  by (rule mat_gt_ge_trans[OF _ mat_plus_gt_left_mono mat_plus_right_mono[OF mat_gt_imp_mat_ge]],
  auto)

lemma mat_default_gt_mat0: assumes sd_pos: "sd > 0" and sd_n: "sd \<le> n"
  shows "mat_gt (\<succ>) sd (default\<^sub>m default n) (0\<^sub>m n n)"
proof -
  from assms have n: "n > 0" by auto
  show ?thesis
    by (intro mat_gtI[OF mat_default_ge_0 sd_pos sd_pos], insert sd_pos sd_n, auto simp: mat_default_def default_gt_zero)
qed
end


context SN_one_mono_ordered_semiring_1
begin

abbreviation mat_s :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" ("(_ \<succ>\<^sub>m _ _ _)" [51,51,51,51] 50)
 where "A \<succ>\<^sub>m n sd B \<equiv> (A \<in> carrier_mat n n \<and> B \<in> carrier_mat n n \<and> B \<ge>\<^sub>m 0\<^sub>m n n \<and> mat_gt (\<succ>) sd A B)"

lemma mat_gt_SN: assumes sd_n: "sd \<le> n" shows "SN {(m1,m2) . m1 \<succ>\<^sub>m n sd m2}"
proof 
  fix A
  assume "\<forall> i. (A i, A (Suc i)) \<in> {(m1,m2). m1 \<succ>\<^sub>m n sd m2}"
  hence "\<And> i. (A i, A (Suc i)) \<in> {(m1,m2). m1 \<succ>\<^sub>m n sd m2}" by blast
  hence A: "\<And> i. A i \<in> carrier_mat n n" 
    and ge: "\<And> i. A (Suc i) \<ge>\<^sub>m 0\<^sub>m n n" 
    and gt: "\<And> i. mat_gt (\<succ>) sd (A i) (A (Suc i))" by auto  
  define s where "s = (\<lambda> i. sum_mat (A i))"
  {
    fix i
    from sum_mat_mono_gt[OF sd_n A A gt[of i]]
    have gt: "s i \<succ> s (Suc i)" unfolding s_def .
    from sum_mat_mono[OF A _ ge[of i]]
    have ge: "s (Suc i) \<ge> 0" unfolding s_def by auto
    note ge gt 
  }
  with SN show False by auto
qed
end

context SN_strict_mono_ordered_semiring_1
begin 

lemma mat_mono: assumes sd_n: "sd \<le> n" and A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" and C: "C \<in> carrier_mat n n" 
  and gt: "mat_gt (\<succ>) sd B C" and gez: "A \<ge>\<^sub>m 0\<^sub>m n n" and mmono: "mat_mono mono sd A"
  shows "mat_gt (\<succ>) sd (A * B) (A * C)" (is "mat_gt _ _ ?AB ?AC")
proof -
  from mat_gtD[OF gt] obtain i j where 
    i: "i < sd" and j: "j < sd" and gt: "B $$ (i,j) \<succ> C $$ (i,j)" and BC: "B \<ge>\<^sub>m C" by auto
  from mat_mult_right_mono[OF gez BC A B C] have ge: "?AB \<ge>\<^sub>m ?AC" .
  from mmono[unfolded mat_mono_def] i obtain k where k: "k < sd" and mon: "mono (A $$ (k,i))" by auto
  from mat_geD[OF gez] k i sd_n A have "A $$ (k, i) \<ge> 0" by auto
  note mono = mono[OF mon gt this]
  have id: "dim_vec (col B j) = n" "dim_vec (col C j) = n" using j sd_n B C by auto
  {
    fix i
    assume "i < n"
    hence "row A k $ i * col B j $ i \<ge> row A k $ i * col C j $ i"
      by (intro times_right_mono, insert j k sd_n A B C mat_geD[OF gez] mat_geD[OF BC], auto)
  } note sge = this
  have gt: "row A k \<bullet> col B j \<succ> row A k \<bullet> col C j" unfolding scalar_prod_def id
    by (rule sum_mono_gt[of _ _ _ i, OF sge], insert mono k i j A B C sd_n, auto)
  show ?thesis
    by (rule mat_gtI[OF ge k j], insert k j sd_n A B C gt, auto)
qed
end

definition mat_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_comp_all r A B =
   (\<forall> i < dim_row A. \<forall> j < dim_col A. r (A $$ (i,j)) (B $$ (i,j)))"

lemma mat_comp_allI:
  assumes "A \<in> carrier_mat nr nc" "B \<in> carrier_mat nr nc"
  and "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> r (A $$(i,j)) (B $$ (i,j))"
  shows "mat_comp_all r A B"
  unfolding mat_comp_all_def using assms by simp

lemma mat_comp_allE:
  assumes "mat_comp_all r A B"
  and "A \<in> carrier_mat nr nc" "B \<in> carrier_mat nr nc"
  shows "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> r (A $$ (i,j)) (B $$(i,j))"
  using assms unfolding mat_comp_all_def by auto

context weak_SN_both_mono_ordered_semiring_1
begin

abbreviation weak_mat_gt_arc :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "weak_mat_gt_arc \<equiv> mat_comp_all weak_gt"

lemma weak_mat_gt_both_mono:
   assumes ABs: "set ABs \<subseteq> carrier_mat n n \<times> carrier_mat n n"
   and orient: "\<forall>(A,B) \<in> set ABs. weak_mat_gt_arc A B"
   shows "\<exists> gt. SN_both_mono_ordered_semiring_1 default gt arc_pos \<and>
   (\<forall>(A,B) \<in> set ABs. mat_comp_all gt A B)"
proof -
  let ?pairs = "[ (fst AB $$ (i,j), snd AB $$ (i,j)) . AB <- ABs, i <- [0 ..< n], j <- [0 ..< n]]"
  let ?strict = "filter (\<lambda> (x,y). weak_gt x y) ?pairs"
  have "\<forall> x y. (x,y) \<in> set ?strict \<longrightarrow> weak_gt x y" by auto
  from weak_gt_both_mono[OF this]
  obtain gt
    where order: "SN_both_mono_ordered_semiring_1 default gt arc_pos"
    and orient2: "\<And> x y. (x, y) \<in> set ?strict \<Longrightarrow> gt x y"
    by auto
  {
    fix A B assume AB: "(A,B) \<in> set ABs"
    hence A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n"
      using AB ABs by auto
    have "mat_comp_all gt A B"
    proof (rule mat_comp_allI[OF A B])
      fix i j
      assume i: "i < n" and j: "j < n"
      from mat_comp_allE[OF _ A B this] orient AB
      have weak_gt: "weak_gt (A $$(i,j)) (B $$ (i,j))" (is "weak_gt ?x ?y") by auto
      have "(?x,?y) \<in> set ?pairs" using A AB i j by force
      with weak_gt
      have gt: "(?x,?y) \<in> set ?strict" by simp
      show "gt ?x ?y" by (rule orient2[OF gt])
    qed
  }
  hence "\<forall>(A, B)\<in>set ABs. mat_comp_all gt A B" by auto
  thus ?thesis using order by auto
qed
end

definition mat_both_ordered_semiring :: "nat \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ordered_semiring_scheme" where
  "mat_both_ordered_semiring n gt b \<equiv> ring_mat TYPE('a) n \<lparr>
    ordered_semiring.geq = mat_ge,
    gt = mat_comp_all gt,
    max = mat_max,
    \<dots> = b\<rparr>"

(* checking whether a matrix is arctic positive (first entry is arctic positive) *)
definition mat_arc_posI :: "('a \<Rightarrow> bool) \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_arc_posI ap A \<equiv> ap (A $$ (0,0))"

context both_mono_ordered_semiring_1
begin 

abbreviation mat_gt_arc :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool"
where "mat_gt_arc \<equiv> mat_comp_all gt"

abbreviation mat_arc_pos :: "'a mat \<Rightarrow> bool"
where "mat_arc_pos \<equiv> mat_arc_posI arc_pos"

lemma mat_max_id: fixes A :: "'a mat"
  assumes ge: "mat_ge A B"
  and A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  shows "mat_max A B = A"
  using mat_max_ge_0[OF A B ge] .

lemma mat_gt_arc_trans:
  assumes A_B: "mat_gt_arc A B"
  and B_C: "mat_gt_arc B C"
  and A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  and C: "C \<in> carrier_mat nr nc"
  shows "mat_gt_arc A C"
proof (rule mat_comp_allI[OF A C])
  fix i j
  assume i: "i < nr" and j: "j < nc"
  from mat_comp_allE[OF A_B A B i j] mat_comp_allE[OF B_C B C i j]
  show "A $$ (i,j) \<succ> C $$ (i,j)" by (rule gt_trans)
qed

lemma mat_gt_arc_compat:
  assumes ge: "mat_ge A B"
  and gt: "mat_gt_arc B C"
  and A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  and C: "C \<in> carrier_mat nr nc"
  shows "mat_gt_arc A C"
proof (rule mat_comp_allI[OF A C])
  fix i j assume i: "i < nr" and j: "j < nc"
  have "A $$ (i,j) \<ge> B $$ (i,j)" using ge A i j by auto
  also have "B $$ (i,j) \<succ> C $$ (i,j)"
    using mat_comp_allE[OF gt B C i j] by auto
  finally show "A $$ (i,j) \<succ> C $$ (i,j)" by auto
qed

lemma mat_gt_arc_compat2:
  assumes gt: "mat_gt_arc A B"
  and ge: "mat_ge B C"
  and A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  and C: "C \<in> carrier_mat nr nc"
  shows "mat_gt_arc A C"
proof (rule mat_comp_allI[OF A C])
  fix i j assume i: "i < nr" and j: "j < nc"
  have "A $$ (i,j) \<succ> B $$ (i,j)"
    using mat_comp_allE[OF gt] A B i j by auto
  also have "B $$ (i,j) \<ge> C $$ (i,j)"
    using ge B i j by auto
  finally show "A $$ (i,j) \<succ> C $$ (i,j)" by auto
qed

lemma mat_gt_arc_imp_mat_ge:
  assumes gt: "mat_gt_arc A B"
  and A: "A \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  shows "mat_ge A B"
  using subst mat_geI[OF A]
  using mat_comp_allE[OF gt A B] gt_imp_ge by auto

lemma (in both_mono_ordered_semiring_1) mat_both_ordered_semiring: assumes n: "n > 0" 
  shows "ordered_semiring 
    (mat_both_ordered_semiring n (\<succ>) b :: ('a mat,'b) ordered_semiring_scheme)" 
  (is "ordered_semiring ?R")
proof -
  interpret semiring ?R unfolding mat_both_ordered_semiring_def by (rule semiring_mat)
  show ?thesis 
    apply (unfold_locales)
    unfolding ring_mat_def mat_both_ordered_semiring_def ordered_semiring_record_simps
    apply(
      auto intro: mat_max_comm mat_ge_trans
      mat_plus_left_mono mat_mult_left_mono mat_mult_right_mono mat_ge_refl
      one_mat_ge_zero mat_max_mono mat_max_ge mat_max_id
      mat_gt_arc_trans mat_gt_arc_imp_mat_ge
      mat_gt_arc_compat mat_gt_arc_compat2)
    done
qed


lemma mat0_leastI:
  assumes A: "A \<in> carrier_mat nr nc"
  shows "mat_gt_arc A (0\<^sub>m nr nc)"
proof (rule mat_comp_allI[OF A])
  fix i j
  assume i: "i < nr" and j: "j < nc"
  thus "A $$ (i,j) \<succ> 0\<^sub>m nr nc $$ (i,j)" by (auto simp: zero_leastI)
qed auto

lemma mat0_leastII: 
  assumes gt: "mat_gt_arc (0\<^sub>m nr nc) A"
  and A: "A \<in> carrier_mat nr nc"
  shows "A = 0\<^sub>m nr nc"
  apply (rule eq_matI)
  unfolding index_zero_mat
  using A
proof -
  fix i j
  assume i: "i < nr" and j: "j < nc"
  show "A $$ (i,j) = 0"
    using zero_leastII mat_comp_allE[OF gt _ A] i j by auto
qed auto

lemma mat0_leastIII:
  assumes A: "A \<in> carrier_mat nr nc"
  shows "mat_ge A ((0\<^sub>m nr nc) :: 'a mat)"
proof (rule mat_geI[OF A]; unfold index_zero_mat)
  fix i j
  assume i: "i < nr" and j: "j < nc"
  show "A $$ (i,j) \<ge> 0" using zero_leastIII by simp
qed

lemma mat_max_0_id: fixes A :: "'a mat"
  assumes A: "A \<in> carrier_mat nr nc"
  shows "mat_max (0\<^sub>m nr nc) A = A"
  unfolding mat_max_comm[OF zero_carrier_mat A]
  by (rule mat_max_id[OF mat0_leastIII[OF A] A], simp)

lemma mat_arc_pos_one:
  assumes n0: "n > 0"
  shows "mat_arc_posI arc_pos (1\<^sub>m n)"
  unfolding mat_arc_posI_def
  unfolding arc_pos_one index_one_mat(1)[OF n0 n0]
  using arc_pos_one by simp

lemma mat_arc_pos_zero:
  assumes n0: "n > 0"
  shows "\<not> mat_arc_posI arc_pos (0\<^sub>m n n)"
  unfolding mat_arc_posI_def
  unfolding index_zero_mat(1)[OF n0 n0] using arc_pos_zero by simp

lemma mat_gt_arc_plus_mono:
  assumes gt1: "mat_gt_arc A B"
  and gt2: "mat_gt_arc C D"
  and A: "(A::'a mat) \<in> carrier_mat nr nc"
  and B: "(B::'a mat) \<in> carrier_mat nr nc"
  and C: "(C::'a mat) \<in> carrier_mat nr nc"
  and D: "(D::'a mat) \<in> carrier_mat nr nc"
  shows "mat_gt_arc (A + C) (B + D)" (is "mat_gt_arc ?AC ?BD")
proof -
  show ?thesis
  proof (rule mat_comp_allI)
    fix i j
    assume i: "i < nr" and j: "j < nc"
    hence ijC: "i < dim_row C" "j < dim_col C"
      and ijD: "i < dim_row D" "j < dim_col D"
      using C D by auto
    show "?AC $$ (i,j) \<succ> ?BD $$ (i,j)"
      unfolding index_add_mat(1)[OF ijC]
      unfolding index_add_mat(1)[OF ijD]
      using plus_gt_both_mono
      using mat_comp_allE[OF gt1 A B] mat_comp_allE[OF gt2 C D] i j by auto
  qed (insert A B C D, auto)
qed

definition vec_comp_all :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> bool"
  where "vec_comp_all r v w \<equiv> \<forall>i < dim_vec v. r (v $ i) (w $ i)"

lemma vec_comp_allI:
  assumes "\<And>i. i < dim_vec v \<Longrightarrow> r (v $ i) (w $ i)"
  shows "vec_comp_all r v w"
  unfolding vec_comp_all_def using assms by auto

lemma vec_comp_allE:
  "vec_comp_all r v w \<Longrightarrow> i < dim_vec v \<Longrightarrow> r (v $ i) (w $ i)"
  unfolding vec_comp_all_def by auto

lemma scalar_prod_left_mono:
  assumes u: "u \<in> carrier_vec n"
  and v: "v \<in> carrier_vec n"
  and w: "w \<in> carrier_vec n"
  and uv: "vec_comp_all gt u v"
  shows "scalar_prod u w \<succ> scalar_prod v w"
proof -
  { fix m assume "m \<le> n"
    hence "(\<Sum>i<m. (u $ i) * (w $ i)) \<succ> (\<Sum>i<m. (v $ i) * (w $ i))"
    proof (induct m)
      case 0 show ?case using zero_leastI by simp next
      case (Suc m)
        hence uv: "u $ m \<succ> v $ m"
          using vec_comp_allE[OF uv] u by auto
        show ?case
          unfolding sum.lessThan_Suc
          apply (subst plus_gt_both_mono) 
          using times_gt_left_mono Suc times_gt_left_mono[OF uv] by auto
    qed
  }
  from this[OF order.refl]
  show ?thesis
    unfolding scalar_prod_def atLeast0LessThan
    using w by auto
qed

lemma scalar_prod_right_mono:
  assumes u: "u \<in> carrier_vec n"
  and v: "v \<in> carrier_vec n"
  and w: "w \<in> carrier_vec n"
  and vw: "vec_comp_all gt v w"
  shows "scalar_prod u v \<succ> scalar_prod u w"
proof -
  { fix m assume "m \<le> n"
    hence "(\<Sum>i<m. (u $ i) * (v $ i)) \<succ> (\<Sum>i<m. (u $ i) * (w $ i))"
    proof (induct m)
      case 0 show ?case using zero_leastI by simp next
      case (Suc m)
        hence vw: "v $ m \<succ> w $ m"
          using vec_comp_allE[OF vw] v by auto
        show ?case
          unfolding sum.lessThan_Suc
          apply (subst plus_gt_both_mono) 
          using times_gt_left_mono Suc times_gt_right_mono[OF vw] by auto
    qed
  }
  from this[OF order.refl]
  show ?thesis
    unfolding scalar_prod_def atLeast0LessThan
    using v w by auto
qed

lemma mat_gt_arc_mult_left_mono:
  assumes gt1: "mat_gt_arc A B"
  and A: "(A::'a mat) \<in> carrier_mat nr n"
  and B: "(B::'a mat) \<in> carrier_mat nr n"
  and C: "(C::'a mat) \<in> carrier_mat n nc"
  shows "mat_gt_arc (A * C) (B * C)" (is "mat_gt_arc ?AC ?BC")
proof (rule mat_comp_allI)
  fix i j assume i: "i < nr" and j: "j < nc"
  hence iA: "i < dim_row A"
    and iB: "i < dim_row B"
    and jC: "j < dim_col C"
    using A B C by auto
  show "?AC $$ (i,j) \<succ> ?BC $$ (i,j)"
    unfolding index_mult_mat(1)[OF iA jC]
    unfolding index_mult_mat(1)[OF iB jC]
  proof(rule scalar_prod_left_mono)
    show "row A i \<in> carrier_vec n" using A by auto
    show "row B i \<in> carrier_vec n" using B by auto
    show "col C j \<in> carrier_vec n" using C by auto
    show rowAB: "vec_comp_all (\<succ>) (row A i) (row B i)"
    proof (intro vec_comp_allI)
      fix j assume j: "j < dim_vec (row A i)"
      have "A $$ (i,j) \<succ> B $$ (i,j)"
        using mat_comp_allE[OF gt1 A B i] j A by simp
      thus "row A i $ j \<succ> row B i $ j"
        using A B C i j by simp
    qed
  qed
qed (insert A B C, auto)

lemma mat_gt_arc_mult_right_mono:
  assumes gt1: "mat_gt_arc B C"
  and A: "(A::'a mat) \<in> carrier_mat nr n"
  and B: "(B::'a mat) \<in> carrier_mat n nc"
  and C: "(C::'a mat) \<in> carrier_mat n nc"
  shows "mat_gt_arc (A * B) (A * C)" (is "mat_gt_arc ?AB ?AC")
proof (rule mat_comp_allI)
  fix i j assume i: "i < nr" and j: "j < nc"
  hence iA: "i < dim_row A"
    and jB: "j < dim_col B"
    and jC: "j < dim_col C"
    using A B C by auto
  show "?AB $$ (i,j) \<succ> ?AC $$ (i,j)"
    unfolding index_mult_mat(1)[OF iA jB]
    unfolding index_mult_mat(1)[OF iA jC]
  proof(rule scalar_prod_right_mono)
    show "row A i \<in> carrier_vec n" using A by auto
    show "col B j \<in> carrier_vec n" using B by auto
    show "col C j \<in> carrier_vec n" using C by auto
    show rowAB: "vec_comp_all (\<succ>) (col B j) (col C j)"
    proof (intro vec_comp_allI)
      fix i assume i: "i < dim_vec (col B j)"
      have "B $$ (i,j) \<succ> C $$ (i,j)"
        using mat_comp_allE[OF gt1 B C] i j B by simp
      thus "col B j $ i \<succ> col C j $ i"
        using A B C i j by simp
    qed
  qed
qed (insert A B C, auto)

lemma mat_arc_pos_plus:
  assumes n0: "n > 0" 
  and A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat n n"
  and arc_pos: "mat_arc_pos A"
  shows "mat_arc_pos (A + B)"
  unfolding mat_arc_posI_def
  apply (subst index_add_mat(1))
  using arc_pos_plus[OF arc_pos[unfolded mat_arc_posI_def]]
  assms by auto

lemma scalar_prod_split_head: assumes 
  "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "n > 0" 
  shows "row A 0 \<bullet> col B 0 = A $$ (0,0) * B $$ (0,0) + (\<Sum>i = 1..<n. A $$ (0, i) * B $$ (i, 0))"
  unfolding scalar_prod_def
  using assms sum.atLeast_Suc_lessThan by auto


lemma mat_arc_pos_mult:
  assumes n0: "n > 0" 
  and A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat n n"
  and apA: "mat_arc_pos A"
  and apB: "mat_arc_pos B"
  shows "mat_arc_pos (A * B)"
  unfolding mat_arc_posI_def
  apply(subst index_mult_mat(1))
proof -
  let ?prod = "row A 0 \<bullet> col B 0"
  let ?head = "A $$ (0,0) * B $$ (0,0)"
  let ?rest = "\<Sum>i = 1..<n. A $$ (0, i) * B $$ (i, 0)"
  have ap: "arc_pos ?head"
    using apA apB
    unfolding mat_arc_posI_def
    using arc_pos_mult by auto
  have split: "?prod = ?head + ?rest"
    by (rule scalar_prod_split_head[OF A B n0])
  show "arc_pos (row A 0 \<bullet> col B 0)"
    unfolding split
    using ap arc_pos_plus by auto
qed (insert A B n0, auto)

lemma mat_arc_pos_mat_default:
  assumes n0: "n > 0" shows "mat_arc_pos (mat_default default n)"
  unfolding mat_arc_posI_def
  unfolding mat_default_def
  unfolding index_mat(1)[OF n0 n0]
  using arc_pos_default by simp

lemma mat_not_all_ge:
  assumes n_pos: "n > 0"
  and A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat n n"
  and apB: "mat_arc_pos B"
  shows "\<exists>C. C \<in> carrier_mat n n \<and> mat_ge C (0\<^sub>m n n) \<and> mat_arc_pos C \<and> \<not> mat_ge A (B * C)"
proof -
  define c where "c = A $$ (0,0)"
  from apB have "arc_pos (B $$ (0,0))" unfolding mat_arc_posI_def .
  from not_all_ge[OF this, of c] obtain e where e0: "e \<ge> 0" and ae: "arc_pos e"
    and nc: "\<not> c \<ge> B $$ (0,0) * e" by auto
  let ?f = "\<lambda> i j. if i = 0 \<and> j = 0 then e else 0"
  let ?C = "mat n n (\<lambda> (i,j). ?f i j)"
  have C: "?C \<in> carrier_mat n n" by auto
  have C00: "?C $$ (0,0) = e" using n_pos by auto
  show ?thesis
  proof(intro exI conjI)
    show "?C \<ge>\<^sub>m 0\<^sub>m n n" 
      by (rule mat_geI[of _ n n], auto simp: ge_refl e0)
    show "mat_arc_pos ?C" 
      unfolding mat_arc_posI_def 
      unfolding C00 by (rule ae)
    let ?mult = "B * ?C"
    from n_pos obtain nn where n: "n = Suc nn" by (cases n, auto)
    have col: "col ?C 0 = vec n (?f 0)" using n_pos by auto
    let ?prod = "row B 0 \<bullet> col ?C 0"
    let ?head = "B $$ (0,0) * ?C $$ (0,0)"
    let ?rest = "\<Sum>i = 1..<n. B $$ (0, i) * ?C $$ (i, 0)"

    from n_pos B have "?mult $$ (0,0) = ?prod" by auto
    also have "\<dots> = ?head + ?rest"
      by (rule scalar_prod_split_head[OF B C n_pos])
    also have "?rest = 0"
      by (rule sum.neutral, auto)
    finally have "?mult $$ (0,0) = B $$ (0,0) * e" using n_pos by simp
    with nc c_def have not_ge: "\<not> A $$ (0,0) \<ge> ?mult $$ (0,0)" by simp
    show "\<not> A \<ge>\<^sub>m ?mult" 
    proof
      assume "A \<ge>\<^sub>m ?mult"
      from mat_geD[OF this, of 0 0] A B not_ge n_pos show False by auto
    qed
  qed auto
qed

end

context SN_both_mono_ordered_semiring_1
begin

lemma mat_gt_arc_SN:
  assumes n_pos: "n > 0"
  shows "SN {(A,B) \<in> carrier_mat n n \<times> carrier_mat n n. mat_arc_pos B \<and> mat_gt_arc A B}"
  (is "SN ?rel")
proof (rule ccontr)
  assume "\<not> SN ?rel"
  then obtain f A where "f (0 :: nat) = A" and steps: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" unfolding SN_defs by blast
  hence pos: "\<forall> i. arc_pos (f (Suc i) $$ (0,0))" unfolding mat_arc_posI_def by blast
  have gt: "\<forall> i. f i $$ (0,0) \<succ> f (Suc i) $$ (0,0)"
  proof
    fix i
    from steps 
    have wf1: "f i \<in> carrier_mat n n"
      and wf2: "f (Suc i) \<in> carrier_mat n n"
      and gt: "mat_gt_arc (f i) (f (Suc i))" by auto
    show "f i $$ (0,0) \<succ>  f (Suc i) $$ (0,0)"
      using mat_comp_allE[OF gt wf1 wf2]
      using index_zero_mat n_pos by force
  qed
  from pos gt SN show False unfolding SN_defs by force
qed


end

end
