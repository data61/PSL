section \<open>Integral and Bounded Matrices and Vectors\<close>

text \<open>We define notions of integral vectors and matrices and bounded vectors and matrices
  and prove some preservation lemmas. Moreover, we prove a bound on determinants.\<close>
theory Integral_Bounded_Vectors
  imports
    Missing_VS_Connect
    Sum_Vec_Set
    LLL_Basis_Reduction.Gram_Schmidt_2 (* for some simp-rules *)
begin

(* TODO: move into theory Norms *)
lemma sq_norm_unit_vec[simp]: assumes i: "i < n"
  shows "\<parallel>unit_vec n i\<parallel>\<^sup>2 = (1 :: 'a :: {comm_ring_1,conjugatable_ring})"
proof -
  from i have id: "[0..<n] = [0..<i] @ [i] @ [Suc i ..< n]"
    by (metis append_Cons append_Nil diff_zero length_upt list_trisect)
  show ?thesis unfolding sq_norm_vec_def unit_vec_def
    by (auto simp: o_def id, subst (1 2) sum_list_0, auto)
qed

definition Ints_vec ("\<int>\<^sub>v") where
  "\<int>\<^sub>v = {x. \<forall> i < dim_vec x. x $ i \<in> \<int>}"

definition indexed_Ints_vec  where
  "indexed_Ints_vec I = {x. \<forall> i < dim_vec x. i \<in> I \<longrightarrow> x $ i \<in> \<int>}"

lemma indexed_Ints_vec_UNIV: "\<int>\<^sub>v = indexed_Ints_vec UNIV"
  unfolding Ints_vec_def indexed_Ints_vec_def by auto

lemma indexed_Ints_vec_subset: "\<int>\<^sub>v \<subseteq> indexed_Ints_vec I"
  unfolding Ints_vec_def indexed_Ints_vec_def by auto

lemma Ints_vec_vec_set: "v \<in> \<int>\<^sub>v = (vec_set v \<subseteq> \<int>)"
  unfolding Ints_vec_def vec_set_def by auto

definition Ints_mat ("\<int>\<^sub>m") where
  "\<int>\<^sub>m = {A. \<forall> i < dim_row A. \<forall> j < dim_col A. A $$ (i,j) \<in> \<int>}"

lemma Ints_mat_elements_mat: "A \<in> \<int>\<^sub>m = (elements_mat A \<subseteq> \<int>)"
  unfolding Ints_mat_def elements_mat_def by force

lemma minus_in_Ints_vec_iff[simp]: "(-x) \<in> \<int>\<^sub>v \<longleftrightarrow> (x :: 'a :: ring_1 vec) \<in> \<int>\<^sub>v"
  unfolding Ints_vec_vec_set by (auto simp: minus_in_Ints_iff)

lemma minus_in_Ints_mat_iff[simp]: "(-A) \<in> \<int>\<^sub>m \<longleftrightarrow> (A :: 'a :: ring_1 mat) \<in> \<int>\<^sub>m"
  unfolding Ints_mat_elements_mat by (auto simp: minus_in_Ints_iff)

lemma Ints_vec_rows_Ints_mat[simp]: "set (rows A) \<subseteq> \<int>\<^sub>v \<longleftrightarrow> A \<in> \<int>\<^sub>m"
  unfolding rows_def Ints_vec_def Ints_mat_def by force

lemma unit_vec_integral[simp,intro]: "unit_vec n i \<in> \<int>\<^sub>v"
  unfolding Ints_vec_def by (auto simp: unit_vec_def)

lemma diff_indexed_Ints_vec:
  "x \<in> carrier_vec n \<Longrightarrow> y \<in> carrier_vec n \<Longrightarrow> x \<in> indexed_Ints_vec I \<Longrightarrow> y \<in> indexed_Ints_vec I
  \<Longrightarrow> x - y \<in> indexed_Ints_vec I"
  unfolding indexed_Ints_vec_def by auto

lemma smult_indexed_Ints_vec: "x \<in> \<int> \<Longrightarrow> v \<in> indexed_Ints_vec I \<Longrightarrow> x \<cdot>\<^sub>v v \<in> indexed_Ints_vec I" 
  unfolding indexed_Ints_vec_def smult_vec_def by simp

lemma add_indexed_Ints_vec:
  "x \<in> carrier_vec n \<Longrightarrow> y \<in> carrier_vec n \<Longrightarrow> x \<in> indexed_Ints_vec I \<Longrightarrow> y \<in> indexed_Ints_vec I
  \<Longrightarrow> x + y \<in> indexed_Ints_vec I"
  unfolding indexed_Ints_vec_def by auto

lemma (in vec_space) lincomb_indexed_Ints_vec: assumes cI: "\<And> x. x \<in> C \<Longrightarrow> c x \<in> \<int>"
  and C: "C \<subseteq> carrier_vec n"
  and CI: "C \<subseteq> indexed_Ints_vec I"
shows "lincomb c C \<in> indexed_Ints_vec I"
proof -
  from C have id: "dim_vec (lincomb c C) = n" by auto
  show ?thesis unfolding indexed_Ints_vec_def mem_Collect_eq id
  proof (intro allI impI)
    fix i
    assume i: "i < n" and iI: "i \<in> I"
    have "lincomb c C $ i = (\<Sum>x\<in>C. c x * x $ i)"
      by (rule lincomb_index[OF i C])
    also have "\<dots> \<in> \<int>"
      by (intro Ints_sum Ints_mult cI, insert i iI CI[unfolded indexed_Ints_vec_def] C, force+)
    finally show "lincomb c C $ i \<in> \<int>" .
  qed
qed

definition "Bounded_vec (b :: 'a :: linordered_idom) = {x . \<forall> i < dim_vec x . abs (x $ i) \<le> b}"

lemma Bounded_vec_vec_set: "v \<in> Bounded_vec b \<longleftrightarrow> (\<forall> x \<in> vec_set v. abs x \<le> b)"
  unfolding Bounded_vec_def vec_set_def by auto

definition "Bounded_mat (b :: 'a :: linordered_idom) =
  {A . (\<forall> i < dim_row A . \<forall> j < dim_col A. abs (A $$ (i,j)) \<le> b)}"

lemma Bounded_mat_elements_mat: "A \<in> Bounded_mat b \<longleftrightarrow> (\<forall> x \<in> elements_mat A. abs x \<le> b)"
  unfolding Bounded_mat_def elements_mat_def by auto

lemma Bounded_vec_rows_Bounded_mat[simp]: "set (rows A) \<subseteq> Bounded_vec B \<longleftrightarrow> A \<in> Bounded_mat B"
  unfolding rows_def Bounded_vec_def Bounded_mat_def by force

lemma unit_vec_Bounded_vec[simp,intro]: "unit_vec n i \<in> Bounded_vec (max 1 Bnd)"
  unfolding Bounded_vec_def unit_vec_def by auto

lemma Bounded_matD: assumes "A \<in> Bounded_mat b"
  "A \<in> carrier_mat nr nc"
shows "i < nr \<Longrightarrow> j < nc \<Longrightarrow> abs (A $$ (i,j)) \<le> b"
  using assms unfolding Bounded_mat_def by auto

lemma Bounded_vec_mono: "b \<le> B \<Longrightarrow> Bounded_vec b \<subseteq> Bounded_vec B"
  unfolding Bounded_vec_def by auto

lemma Bounded_mat_mono: "b \<le> B \<Longrightarrow> Bounded_mat b \<subseteq> Bounded_mat B"
  unfolding Bounded_mat_def by force

lemma finite_Bounded_vec_Max:
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
  shows "A \<subseteq> Bounded_vec (Max { abs (a $ i) | a i. a \<in> A \<and> i < n})"
proof
  let ?B = "{ abs (a $ i) | a i. a \<in> A \<and> i < n}"
  have fin: "finite ?B"
    by (rule finite_subset[of _ "(\<lambda> (a,i). abs (a $ i)) ` (A \<times> {0 ..< n})"], insert fin, auto)
  fix a
  assume a: "a \<in> A"
  show "a \<in> Bounded_vec (Max ?B)"
    unfolding Bounded_vec_def
    by (standard, intro allI impI Max_ge[OF fin], insert a A, force)
qed

definition det_bound :: "nat \<Rightarrow> 'a :: linordered_idom \<Rightarrow> 'a" where
  "det_bound n x = fact n * (x^n)"

lemma det_bound: assumes A: "A \<in> carrier_mat n n"
  and x: "A \<in> Bounded_mat x"
shows "abs (det A) \<le> det_bound n x"
proof -
  have "abs (det A) = abs (\<Sum>p | p permutes {0..<n}. signof p * (\<Prod>i = 0..<n. A $$ (i, p i)))"
    unfolding det_def'[OF A] ..
  also have "\<dots> \<le> (\<Sum>p | p permutes {0..<n}. abs (signof p * (\<Prod>i = 0..<n. A $$ (i, p i))))"
    by (rule sum_abs)
  also have "\<dots> = (\<Sum>p | p permutes {0..<n}. (\<Prod>i = 0..<n. abs (A $$ (i, p i))))"
    by (rule sum.cong[OF refl], auto simp: abs_mult abs_prod signof_def)
  also have "\<dots> \<le> (\<Sum>p | p permutes {0..<n}. (\<Prod>i = 0..<n. x))"
    by (intro sum_mono prod_mono conjI Bounded_matD[OF x A], auto)
  also have "\<dots> = fact n * x^n" by (auto simp add: card_permutations)
  finally show "abs (det A) \<le> det_bound n x" unfolding det_bound_def by auto
qed

lemma minus_in_Bounded_vec[simp]:
  "(-x) \<in> Bounded_vec b \<longleftrightarrow> x \<in> Bounded_vec b"
  unfolding Bounded_vec_def by auto

lemma sum_in_Bounded_vecI[intro]: assumes
  xB: "x \<in> Bounded_vec B1" and
  yB: "y \<in> Bounded_vec B2" and
  x: "x \<in> carrier_vec n" and
  y: "y \<in> carrier_vec n"
shows "x + y \<in> Bounded_vec (B1 + B2)"
proof -
  from x y have id: "dim_vec (x + y) = n" by auto
  show ?thesis unfolding Bounded_vec_def mem_Collect_eq id
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    with x y xB yB have *: "abs (x $ i) \<le> B1" "abs (y $ i) \<le> B2"
      unfolding Bounded_vec_def by auto
    thus "\<bar>(x + y) $ i\<bar> \<le> B1 + B2" using i x y by simp
  qed
qed

lemma (in gram_schmidt) lincomb_card_bound: assumes XBnd: "X \<subseteq> Bounded_vec Bnd"
  and X: "X \<subseteq> carrier_vec n"
  and Bnd: "Bnd \<ge> 0"
  and c: "\<And> x. x \<in> X \<Longrightarrow> abs (c x) \<le> 1"
  and card: "card X \<le> k"
shows "lincomb c X \<in> Bounded_vec (of_nat k * Bnd)"
proof -
  from X have dim: "dim_vec (lincomb c X) = n" by auto
  show ?thesis unfolding Bounded_vec_def mem_Collect_eq dim
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    have "abs (lincomb c X $ i) = abs (\<Sum>x\<in>X. c x * x $ i)"
      by (subst lincomb_index[OF i X], auto)
    also have "\<dots> \<le> (\<Sum>x\<in>X. abs (c x * x $ i))" by auto
    also have "\<dots> = (\<Sum>x\<in>X. abs (c x) * abs (x $ i))" by (auto simp: abs_mult)
    also have "\<dots> \<le> (\<Sum>x\<in>X. 1 * abs (x $ i))"
      by (rule sum_mono[OF mult_right_mono], insert c, auto)
    also have "\<dots> = (\<Sum>x\<in>X. abs (x $ i))" by simp
    also have "\<dots> \<le> (\<Sum>x\<in>X. Bnd)"
      by (rule sum_mono, insert i XBnd[unfolded Bounded_vec_def] X, force)
    also have "\<dots> = of_nat (card X) * Bnd" by simp
    also have "\<dots> \<le> of_nat k * Bnd"
      by (rule mult_right_mono[OF _ Bnd], insert card, auto)
    finally show "abs (lincomb c X $ i) \<le> of_nat k * Bnd" by auto
  qed
qed

lemma bounded_vecset_sum:
  assumes Acarr: "A \<subseteq> carrier_vec n"
    and Bcarr: "B \<subseteq> carrier_vec n"
    and sum: "C = A + B"
    and Cbnd: "\<exists> bndC. C \<subseteq> Bounded_vec bndC"
  shows "A \<noteq> {} \<Longrightarrow> (\<exists> bndB. B \<subseteq> Bounded_vec bndB)"
    and "B \<noteq> {} \<Longrightarrow> (\<exists> bndA. A \<subseteq> Bounded_vec bndA)"
proof -
  {
    fix A B :: "'a vec set"
    assume Acarr: "A \<subseteq> carrier_vec n"
    assume Bcarr: "B \<subseteq> carrier_vec n"
    assume sum: "C = A + B"
    assume Ane: "A \<noteq> {}"
    have "\<exists> bndB. B \<subseteq> Bounded_vec bndB"
    proof(cases "B = {}")
      case Bne: False
      from Cbnd obtain bndC where bndC: "C \<subseteq> Bounded_vec bndC" by auto
      from Ane obtain a where aA: "a \<in> A" and acarr: "a \<in> carrier_vec n" using Acarr by auto
      let ?M = "{abs (a $ i) | i. i < n}"
      have finM: "finite ?M" by simp
      define nb where "nb = abs bndC + Max ?M"
      {
        fix b
        assume bB: "b \<in> B" and bcarr: "b \<in> carrier_vec n"
        have ab: "a + b \<in> Bounded_vec bndC" using aA bB bndC sum by auto
        {
          fix i
          assume i_lt_n: "i < n"
          hence ai_le_max: "abs(a $ i) \<le> Max ?M" using acarr finM Max_ge by blast
          hence "abs(a $ i + b $ i) \<le> abs bndC"
            using ab bcarr acarr index_add_vec(1) i_lt_n unfolding Bounded_vec_def by auto
          hence "abs(b $ i) \<le> abs bndC + abs(a $ i)" by simp
          hence "abs(b $ i) \<le> nb" using i_lt_n bcarr ai_le_max unfolding nb_def by simp
        }
        hence "b \<in> Bounded_vec nb" unfolding Bounded_vec_def using bcarr carrier_vecD by blast
      }
      hence "B \<subseteq> Bounded_vec nb" unfolding Bounded_vec_def using Bcarr by auto
      thus ?thesis by auto
    qed auto
  } note theor = this
  show "A \<noteq> {} \<Longrightarrow> (\<exists> bndB. B \<subseteq> Bounded_vec bndB)" using theor[OF Acarr Bcarr sum] by simp
  have CBA: "C = B + A" unfolding sum by (rule comm_add_vecset[OF Acarr Bcarr])
  show "B \<noteq> {} \<Longrightarrow> \<exists> bndA. A \<subseteq> Bounded_vec bndA" using theor[OF Bcarr Acarr CBA] by simp
qed

end