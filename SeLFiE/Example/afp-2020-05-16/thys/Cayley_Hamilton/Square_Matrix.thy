(*  Title:      Cayley_Hamilton/Square_Matrix.thy
    Author:     Johannes Hölzl, TU München *)

theory Square_Matrix
imports
  "HOL-Analysis.Determinants"
  "HOL-Analysis.Cartesian_Euclidean_Space"
begin

lemma smult_axis: "x *s axis i y = axis i (x * y::_::mult_zero)"
  by (simp add: axis_def vec_eq_iff)

typedef ('a, 'n) sq_matrix = "UNIV :: ('n \<Rightarrow> 'n \<Rightarrow> 'a) set"
  morphisms to_fun of_fun
  by (rule UNIV_witness)

syntax "_sq_matrix" :: "type \<Rightarrow> type \<Rightarrow> type" ("(_ ^^/ _)" [15, 16] 15)

parse_translation \<open>
  let
    fun vec t u = Syntax.const @{type_syntax sq_matrix} $ t $ u;
    fun sq_matrix_tr [t, u] =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            vec t (Syntax.const @{syntax_const "_ofsort"} $ v $
              Syntax.const @{class_syntax finite})
          else vec t u
      | _ => vec t u)
  in
    [(@{syntax_const "_sq_matrix"}, K sq_matrix_tr)]
  end
\<close>

setup_lifting type_definition_sq_matrix

lift_definition map_sq_matrix :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a^^'b \<Rightarrow> 'c^^'b" is
  "\<lambda>f M i j. f (M i j)" .

lift_definition from_vec :: "'a^'n^'n \<Rightarrow> 'a^^'n" is
  "\<lambda>M i j. M $ i $ j" .

lift_definition to_vec :: "'a^^'n \<Rightarrow> 'a^'n^'n" is
  "\<lambda>M. \<chi> i j. M i j" .

lemma from_vec_eq_iff: "from_vec M = from_vec N \<longleftrightarrow> M = N"
  by transfer (auto simp: vec_eq_iff fun_eq_iff)

lemma to_vec_from_vec[simp]: "to_vec (from_vec M) = M"
  by transfer (simp add: vec_eq_iff)

lemma from_vec_to_vec[simp]: "from_vec (to_vec M) = M"
  by transfer (simp add: vec_eq_iff fun_eq_iff)

lemma map_sq_matrix_compose[simp]: "map_sq_matrix f (map_sq_matrix g M) = map_sq_matrix (\<lambda>x. f (g x)) M"
  by transfer simp

lemma map_sq_matrix_ident[simp]: "map_sq_matrix (\<lambda>x. x) M = M"
  by transfer (simp add: vec_eq_iff)

lemma map_sq_matrix_cong:
  "M = N \<Longrightarrow> (\<And>i j. f (to_fun N i j) = g (to_fun N i j)) \<Longrightarrow> map_sq_matrix f M = map_sq_matrix g N"
  by transfer simp

lift_definition diag :: "'a::zero \<Rightarrow> 'a^^'n" is
  "\<lambda>k i j. if i = j then k else 0" .

lemma diag_eq_iff: "diag x = diag y \<longleftrightarrow>  x = y"
  by transfer (simp add: fun_eq_iff)

lemma map_sq_matrix_diag[simp]: "f 0 = 0 \<Longrightarrow> map_sq_matrix f (diag c) = diag (f c)"
  by transfer (simp add: fun_eq_iff)

lift_definition smult_sq_matrix :: "'a::times \<Rightarrow> 'a^^'n \<Rightarrow> 'a^^'n" (infixr "*\<^sub>S" 75) is
  "\<lambda>c M i j. c * M i j" .

lemma smult_map_sq_matrix:
  "(\<And>y. f (x * y) = z * f y) \<Longrightarrow> map_sq_matrix f (x *\<^sub>S A) = z *\<^sub>S map_sq_matrix f A"
  by transfer simp

lemma map_sq_matrix_smult: "c *\<^sub>S map_sq_matrix f A = map_sq_matrix (\<lambda>x. c * f x) A"
  by transfer simp

lemma one_smult[simp]: "(1::_::monoid_mult) *\<^sub>S x = x"
  by transfer simp

lemma smult_diag: "x *\<^sub>S diag y = diag (x * y::_::mult_zero)"
  by transfer (simp add: fun_eq_iff)

instantiation sq_matrix :: (semigroup_add, finite) semigroup_add
begin

lift_definition plus_sq_matrix :: "'a^^'b \<Rightarrow> 'a^^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>A B i j. A i j + B i j" .

instance
  by standard (transfer, simp add: field_simps)

end

lemma map_sq_matrix_add:
  "(\<And>a b. f (a + b) = f a + f b) \<Longrightarrow> map_sq_matrix f (A + B) = map_sq_matrix f A + map_sq_matrix f B"
  by transfer simp

lemma add_map_sq_matrix: "map_sq_matrix f A + map_sq_matrix g A = map_sq_matrix (\<lambda>x. f x + g x) A"
  by transfer simp

instantiation sq_matrix :: (monoid_add, finite) monoid_add
begin

lift_definition zero_sq_matrix :: "'a^^'b" is "\<lambda>i j. 0" .

instance
  by standard (transfer, simp)+

end

lemma diag_0: "diag 0 = 0"
  by transfer simp

lemma diag_0_eq: "diag x = 0 \<longleftrightarrow> x = 0"
  by transfer (simp add: fun_eq_iff)

lemma zero_map_sq_matrix: "f 0 = 0 \<Longrightarrow> map_sq_matrix f 0 = 0"
  by transfer simp

lemma map_sq_matrix_0[simp]: "map_sq_matrix (\<lambda>x. 0) A = 0"
  by transfer simp

instance sq_matrix :: (ab_semigroup_add, finite) ab_semigroup_add
  by standard (transfer, simp add: field_simps)+

instantiation sq_matrix :: (minus, finite) minus
begin

lift_definition minus_sq_matrix :: "'a^^'b \<Rightarrow> 'a^^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>A B i j. A i j - B i j" .

instance ..
end

instantiation sq_matrix :: (group_add, finite) group_add
begin

lift_definition uminus_sq_matrix :: "'a^^'b \<Rightarrow> 'a^^'b" is
  "uminus" .

instance
  by standard (transfer, simp)+

end

lemma map_sq_matrix_diff:
  "(\<And>a b. f (a - b) = f a - f b) \<Longrightarrow> map_sq_matrix f (A - B) = map_sq_matrix f A - map_sq_matrix f B"
  by transfer (simp add: vec_eq_iff)

lemma smult_diff: fixes a :: "'a::comm_ring_1" shows "a *\<^sub>S (A - B) = a *\<^sub>S A - a *\<^sub>S B"
  by transfer (simp add: field_simps)

instance sq_matrix :: (cancel_semigroup_add, finite) cancel_semigroup_add
  by (standard; transfer, simp add: field_simps fun_eq_iff)

instance sq_matrix :: (cancel_ab_semigroup_add, finite) cancel_ab_semigroup_add
  by (standard; transfer, simp add: field_simps)

instance sq_matrix :: (comm_monoid_add, finite) comm_monoid_add
  by (standard; transfer, simp add: field_simps)

lemma map_sq_matrix_sum:
  "f 0 = 0 \<Longrightarrow> (\<And>a b. f (a + b) = f a + f b) \<Longrightarrow>
  map_sq_matrix f (\<Sum>i\<in>I. A i) = (\<Sum>i\<in>I. map_sq_matrix f (A i))"
  by (induction I rule: infinite_finite_induct)
     (auto simp: zero_map_sq_matrix map_sq_matrix_add)

lemma sum_map_sq_matrix: "(\<Sum>i\<in>I. map_sq_matrix (f i) A) = map_sq_matrix (\<lambda>x. \<Sum>i\<in>I. f i x) A"
  by (induction I rule: infinite_finite_induct) (simp_all add: add_map_sq_matrix)

lemma smult_zero[simp]: fixes a :: "'a::ring_1" shows "a *\<^sub>S 0 = 0"
  by transfer (simp add: vec_eq_iff)

lemma smult_right_add: fixes a :: "'a::ring_1" shows "a *\<^sub>S (x + y) = a *\<^sub>S x + a *\<^sub>S y"
  by transfer (simp add: vec_eq_iff field_simps)

lemma smult_sum: fixes a :: "'a::ring_1" shows "(\<Sum>i\<in>I. a *\<^sub>S f i) = a *\<^sub>S (sum f I)"
  by (induction I rule: infinite_finite_induct)
     (simp_all add: smult_right_add vec_eq_iff)

instance sq_matrix :: (ab_group_add, finite) ab_group_add
  by standard (transfer, simp add: field_simps)+

instantiation sq_matrix :: ("semiring_0", finite) semiring_0
begin

lift_definition times_sq_matrix :: "'a^^'b \<Rightarrow> 'a^^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>M N i j. \<Sum>k\<in>UNIV. M i k * N k j" .

instance
proof
  fix a b c :: "'a^^'b" show "a * b * c = a * (b * c)"
    by transfer
       (auto simp: fun_eq_iff sum_distrib_left sum_distrib_right field_simps intro: sum.swap)
qed (transfer, simp add: vec_eq_iff sum.distrib field_simps)+
end

lemma diag_mult: "diag x * A = x *\<^sub>S A"
  by transfer  (simp add: if_distrib[where f="\<lambda>x. x * a" for a] sum.If_cases)

lemma mult_diag:
  fixes x :: "'a::comm_ring_1"
  shows "A * diag x = x *\<^sub>S A"
  by transfer (simp add: if_distrib[where f="\<lambda>x. a * x" for a] mult.commute sum.If_cases)

lemma smult_mult1: fixes a :: "'a::comm_ring_1" shows "a *\<^sub>S (A * B) = (a *\<^sub>S A) * B"
  by transfer (simp add: sum_distrib_left field_simps)

lemma smult_mult2: fixes a :: "'a::comm_ring_1" shows "a *\<^sub>S (A * B) = A * (a *\<^sub>S B)"
  by transfer (simp add: sum_distrib_left field_simps)

lemma map_sq_matrix_mult:
  fixes f :: "'a::semiring_1 \<Rightarrow> 'b::semiring_1"
  assumes f: "\<And>a b. f (a + b) = f a + f b" "\<And>a b. f (a * b) = f a * f b" "f 0 = 0"
  shows "map_sq_matrix f (A * B) = map_sq_matrix f A * map_sq_matrix f B"
proof (transfer fixing: f)
  fix A B :: "'c \<Rightarrow> 'c \<Rightarrow> 'a"
  { fix I i j have "f (\<Sum>k\<in>I. A i k * B k j) = (\<Sum>k\<in>I. f (A i k) * f (B k j))"
      by (induction I rule: infinite_finite_induct) (auto simp add: f) }
  then show "(\<lambda>i j. f (\<Sum>k\<in>UNIV. A i k * B k j)) = (\<lambda>i j. \<Sum>k\<in>UNIV. f (A i k) * f (B k j))"
    by simp
qed

lemma from_vec_mult[simp]: "from_vec (M ** N) = from_vec M * from_vec N"
  by transfer (simp add: matrix_matrix_mult_def fun_eq_iff vec_eq_iff)

instantiation sq_matrix :: ("semiring_1", finite) semiring_1
begin

lift_definition one_sq_matrix :: "'a^^'b" is
  "\<lambda>i j. if i = j then 1 else 0" .

instance
  by standard (transfer, simp add: fun_eq_iff sum.If_cases
       if_distrib[where f="\<lambda>x. x * b" for b] if_distrib[where f="\<lambda>x. b * x" for b])+
end

instance sq_matrix :: ("semiring_1", finite) numeral ..

lemma diag_1: "diag 1 = 1"
  by transfer simp

lemma diag_1_eq: "diag x = 1 \<longleftrightarrow> x = 1"
  by transfer (simp add: fun_eq_iff)

instance sq_matrix :: ("ring_1", finite) ring_1
  by standard simp_all

interpretation sq_matrix: vector_space smult_sq_matrix
  by standard (transfer, simp add: vec_eq_iff field_simps)+

instantiation sq_matrix :: (real_vector, finite) real_vector
begin

lift_definition scaleR_sq_matrix :: "real \<Rightarrow> 'a^^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>r A i j. r *\<^sub>R A i j" .

instance
  by standard (transfer, simp add: scaleR_add_right scaleR_add_left)+

end

instance sq_matrix :: ("semiring_1", finite) Rings.dvd ..

lift_definition transpose :: "'a^^'n \<Rightarrow> 'a^^'n" is
  "\<lambda>M i j. M j i" .

lemma transpose_transpose[simp]: "transpose (transpose A) = A"
  by transfer simp

lemma transpose_diag[simp]: "transpose (diag c) = diag c"
  by transfer (simp add: fun_eq_iff)

lemma transpose_zero[simp]: "transpose 0 = 0"
  by transfer simp

lemma transpose_one[simp]: "transpose 1 = 1"
  by transfer (simp add: fun_eq_iff)

lemma transpose_add[simp]: "transpose (A + B) = transpose A + transpose B"
  by transfer simp

lemma transpose_minus[simp]: "transpose (A - B) = transpose A - transpose B"
  by transfer simp

lemma transpose_uminus[simp]: "transpose (- A) = - transpose A"
  by transfer (simp add: fun_eq_iff)

lemma transpose_mult[simp]:
  "transpose (A * B :: 'a::comm_semiring_0^^'n) = transpose B * transpose A"
  by transfer (simp add: field_simps)

lift_definition trace :: "'a::comm_monoid_add^^'n \<Rightarrow> 'a" is
  "\<lambda>M. \<Sum>i\<in>UNIV. M i i" .

lemma trace_diag[simp]: "trace (diag c::'a::semiring_1^^'n) = of_nat CARD('n) * c"
  by transfer simp

lemma trace_0[simp]: "trace 0 = 0"
  by transfer simp

lemma trace_1[simp]: "trace (1::'a::semiring_1^^'n) = of_nat CARD('n)"
  by transfer simp

lemma trace_plus[simp]: "trace (A + B) = trace A + trace B"
  by transfer (simp add: sum.distrib)

lemma trace_minus[simp]: "trace (A - B) = (trace A - trace B::_::ab_group_add)"
  by transfer (simp add: sum_subtractf)

lemma trace_uminus[simp]: "trace (- A) = - (trace A::_::ab_group_add)"
  by transfer (simp add: sum_negf)

lemma trace_smult[simp]: "trace (s *\<^sub>S A) = (s * trace A::_::semiring_0)"
  by transfer (simp add: sum_distrib_left)

lemma trace_transpose[simp]: "trace (transpose A) = trace A"
  by transfer simp

lemma trace_mult_symm:
  fixes A B :: "'a::comm_semiring_0^^'n"
  shows "trace (A * B) = trace (B * A)"
  by transfer (auto intro: sum.swap simp: mult.commute)

lift_definition det :: "'a::comm_ring_1^^'n \<Rightarrow> 'a" is
  "\<lambda>A. (\<Sum>p|p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. A i (p i)))" .

lemma det_eq: "det A = (\<Sum>p|p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. to_fun A i (p i)))"
  by transfer rule

lemma permutes_UNIV_permutation: "permutation p \<longleftrightarrow> p permutes (UNIV::_::finite)"
  by (auto simp: permutation_permutes permutes_def)

lemma det_0[simp]: "det 0 = 0"
  by transfer (simp add: zero_power)

lemma det_transpose: "det (transpose A) = det A"
  apply transfer
  apply (subst sum_permutations_inverse)
  apply (rule sum.cong[OF refl])
  apply (simp add: sign_inverse permutes_UNIV_permutation)
  apply (subst prod.reindex_bij_betw[symmetric])
  apply (rule permutes_imp_bij)
  apply assumption
  apply (simp add: permutes_inverses)
  done

lemma det_diagonal:
  fixes A :: "'a::comm_ring_1^^'n"
  shows "(\<And>i j. i \<noteq> j \<Longrightarrow> to_fun A i j = 0) \<Longrightarrow> det A = (\<Prod>i\<in>UNIV. to_fun A i i)"
proof transfer
  fix A :: "'n \<Rightarrow> 'n \<Rightarrow> 'a" assume neq: "\<And>i j. i \<noteq> j \<Longrightarrow> A i j = 0"
  let ?pp = "\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A i (p i))"

  { fix p :: "'n \<Rightarrow> 'n" assume p: "p permutes UNIV" "p \<noteq> id"
    then obtain i where i: "i \<noteq> p i"
      unfolding id_def by metis
    with neq[OF i] have "(\<Prod>i\<in>UNIV. A i (p i)) = 0"
      by (intro prod_zero) auto }
  then have "(\<Sum>p | p permutes UNIV. ?pp p) = (\<Sum>p\<in>{id}. ?pp p)"
    by (intro sum.mono_neutral_cong_right) (auto intro: permutes_id)
  then show "(\<Sum>p | p permutes UNIV. ?pp p) = (\<Prod>i\<in>UNIV. A i i)"
     by (simp add: sign_id)
qed

lemma det_1[simp]: "det (1::'a::comm_ring_1^^'n) = 1"
  by (subst det_diagonal) (transfer, simp)+

lemma det_lowerdiagonal:
  fixes A :: "'a::comm_ring_1^^'n::{finite,wellorder}"
  shows "(\<And>i j. i < j \<Longrightarrow> to_fun A i j = 0) \<Longrightarrow> det A = (\<Prod>i\<in>UNIV. to_fun A i i)"
proof transfer
  fix A :: "'n \<Rightarrow> 'n \<Rightarrow> 'a" assume ld: "\<And>i j. i < j \<Longrightarrow> A i j = 0"
  let ?pp = "\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A i (p i))"

  { fix p :: "'n \<Rightarrow> 'n" assume p: "p permutes UNIV" "p \<noteq> id"
    with permutes_natset_le[OF p(1)] obtain i where i: "p i > i"
      by (metis not_le)
    with ld[OF i] have "(\<Prod>i\<in>UNIV. A i (p i)) = 0"
      by (intro prod_zero) auto }
  then have "(\<Sum>p | p permutes UNIV. ?pp p) = (\<Sum>p\<in>{id}. ?pp p)"
    by (intro sum.mono_neutral_cong_right) (auto intro: permutes_id)
  then show "(\<Sum>p | p permutes UNIV. ?pp p) = (\<Prod>i\<in>UNIV. A i i)"
     by (simp add: sign_id)
qed

lemma det_upperdiagonal:
  fixes A :: "'a::comm_ring_1^^'n::{finite, wellorder}"
  shows "(\<And>i j. j < i \<Longrightarrow> to_fun A i j = 0) \<Longrightarrow> det A = (\<Prod>i\<in>UNIV. to_fun A i i)"
  using det_lowerdiagonal[of "transpose A"]
  unfolding det_transpose transpose.rep_eq .

lift_definition perm_rows :: "'a^^'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a^^'b" is
  "\<lambda>M p i j. M (p i) j" .

lift_definition perm_cols :: "'a^^'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a^^'b" is
  "\<lambda>M p i j. M i (p j)" .

lift_definition upd_rows :: "'a^^'b \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a^'b) \<Rightarrow> 'a^^'b" is
  "\<lambda>M S v i j. if i \<in> S then v i $ j else M i j" .

lift_definition upd_cols :: "'a^^'b \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a^'b) \<Rightarrow> 'a^^'b" is
  "\<lambda>M S v i j. if j \<in> S then v j $ i else M i j" .

lift_definition upd_row :: "'a^^'b \<Rightarrow> 'b \<Rightarrow> 'a^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>M i' v i j. if i = i' then v $ j else M i j" .

lift_definition upd_col :: "'a^^'b \<Rightarrow> 'b \<Rightarrow> 'a^'b \<Rightarrow> 'a^^'b" is
  "\<lambda>M j' v i j. if j = j' then v $ i else M i j" .

lift_definition row :: "'a^^'b \<Rightarrow> 'b \<Rightarrow> 'a^'b" is
  "\<lambda>M i. \<chi> j. M i j" .

lift_definition col :: "'a^^'b \<Rightarrow> 'b \<Rightarrow> 'a^'b" is
  "\<lambda>M j. \<chi> i. M i j" .

lemma perm_rows_transpose: "perm_rows (transpose M) p = transpose (perm_cols M p)"
  by transfer simp

lemma perm_cols_transpose: "perm_cols (transpose M) p = transpose (perm_rows M p)"
  by transfer simp

lemma upd_row_transpose: "upd_row (transpose M) i p = transpose (upd_col M i p)"
  by transfer simp

lemma upd_col_transpose: "upd_col (transpose M) i p = transpose (upd_row M i p)"
  by transfer simp

lemma upd_rows_transpose: "upd_rows (transpose M) i p = transpose (upd_cols M i p)"
  by transfer simp

lemma upd_cols_transpose: "upd_cols (transpose M) i p = transpose (upd_rows M i p)"
  by transfer simp

lemma upd_rows_empty[simp]: "upd_rows M {} f = M"
  by transfer simp

lemma upd_cols_empty[simp]: "upd_cols M {} f = M"
  by transfer simp

lemma upd_rows_single[simp]: "upd_rows M {i} f = upd_row M i (f i)"
  by transfer (simp add: fun_eq_iff)

lemma upd_cols_single[simp]: "upd_cols M {i} f = upd_col M i (f i)"
  by transfer (simp add: fun_eq_iff)

lemma upd_rows_insert: "upd_rows M (insert i I) f = upd_row (upd_rows M I f) i (f i)"
  by transfer (auto simp: fun_eq_iff)

lemma upd_rows_insert_rev: "upd_rows M (insert i I) f = upd_rows (upd_row M i (f i)) I f"
  by transfer (auto simp: fun_eq_iff)

lemma upd_rows_upd_row_swap: "i \<notin> I \<Longrightarrow> upd_rows (upd_row M i x) I f = upd_row (upd_rows M I f) i x"
  by transfer (simp add: fun_eq_iff)

lemma upd_cols_insert: "upd_cols M (insert i I) f = upd_col (upd_cols M I f) i (f i)"
  by transfer (auto simp: fun_eq_iff)

lemma upd_cols_insert_rev: "upd_cols M (insert i I) f = upd_cols (upd_col M i (f i)) I f"
  by transfer (auto simp: fun_eq_iff)

lemma upd_cols_upd_col_swap: "i \<notin> I \<Longrightarrow> upd_cols (upd_col M i x) I f = upd_col (upd_cols M I f) i x"
  by transfer (simp add: fun_eq_iff)

lemma upd_rows_cong[cong]:
  "M = N \<Longrightarrow> T = S \<Longrightarrow> (\<And>s. s \<in> S =simp=> f s = g s) \<Longrightarrow> upd_rows M T f = upd_rows N S g"
  unfolding simp_implies_def
  by transfer (auto simp: fun_eq_iff)

lemma upd_cols_cong[cong]:
  "M = N \<Longrightarrow> T = S \<Longrightarrow> (\<And>s. s \<in> S =simp=> f s = g s) \<Longrightarrow> upd_cols M T f = upd_cols N S g"
  unfolding simp_implies_def
  by transfer (auto simp: fun_eq_iff)

lemma row_upd_row_If: "row (upd_row M i x) j = (if i = j then x else row M j)"
  by transfer (simp add: vec_eq_iff fun_eq_iff)

lemma row_upd_row[simp]: "row (upd_row M i x) i = x"
  by (simp add: row_upd_row_If)

lemma col_upd_col_If: "col (upd_col M i x) j = (if i = j then x else col M j)"
  by transfer (simp add: vec_eq_iff)

lemma col_upd_col[simp]: "col (upd_col M i x) i = x"
  by (simp add: col_upd_col_If)

lemma upd_row_row[simp]: "upd_row M i (row M i) = M"
  by transfer (simp add: fun_eq_iff)

lemma upd_row_upd_row_cancel[simp]: "upd_row (upd_row M i x) i y = upd_row M i y"
  by transfer (simp add: fun_eq_iff)

lemma upd_col_upd_col_cancel[simp]: "upd_col (upd_col M i x) i y = upd_col M i y"
  by transfer (simp add: fun_eq_iff)

lemma upd_col_col[simp]: "upd_col M i (col M i) = M"
  by transfer (simp add: fun_eq_iff)

lemma row_transpose: "row (transpose M) i = col M i"
  by transfer simp

lemma col_transpose: "col (transpose M) i = row M i"
  by transfer simp

lemma det_perm_cols:
  fixes A :: "'a::comm_ring_1^^'n"
  assumes p: "p permutes UNIV"
  shows "det (perm_cols A p) = of_int (sign p) * det A"
proof (transfer fixing: p)
  fix A :: "'n \<Rightarrow> 'n \<Rightarrow> 'a"
  from p have "(\<Sum>q | q permutes UNIV. of_int (sign q) * (\<Prod>i\<in>UNIV. A i (p (q i)))) =
    (\<Sum>q | q permutes UNIV. of_int (sign (inv p \<circ> q)) * (\<Prod>i\<in>UNIV. A i (q i)))"
    by (intro sum.reindex_bij_witness[where j="\<lambda>q. p \<circ> q" and i="\<lambda>q. inv p \<circ> q"])
       (auto simp: comp_assoc[symmetric] permutes_inv_o permutes_compose permutes_inv)
  with p show "(\<Sum>q | q permutes UNIV. of_int (sign q) * (\<Prod>i\<in>UNIV. A i (p (q i)))) =
      of_int (sign p) * (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. A i (p i)))"
    by (auto intro!: sum.cong simp: sum_distrib_left sign_compose permutes_inv sign_inverse permutes_UNIV_permutation)
qed

lemma det_perm_rows:
  fixes A :: "'a::comm_ring_1^^'n"
  assumes p: "p permutes UNIV"
  shows "det (perm_rows A p) = of_int (sign p) * det A"
  using det_perm_cols[OF p, of "transpose A"] by (simp add: det_transpose perm_cols_transpose)

lemma det_row_add: "det (upd_row M i (a + b)) = det (upd_row M i a) + det (upd_row M i b)"
  by transfer (simp add: prod.If_cases sum.distrib[symmetric] field_simps)

lemma det_row_mul: "det (upd_row M i (c *s a)) = c * det (upd_row M i a)"
  by transfer (simp add: prod.If_cases sum_distrib_left field_simps)

lemma det_row_uminus: "det (upd_row M i (- a)) = - det (upd_row M i a)"
  by (simp add: vector_sneg_minus1 det_row_mul)

lemma det_row_minus: "det (upd_row M i (a - b)) = det (upd_row M i a) - det (upd_row M i b)"
  unfolding diff_conv_add_uminus det_row_add det_row_uminus ..

lemma det_row_0: "det (upd_row M i 0) = 0"
  using det_row_mul[of M i 0] by simp

lemma det_row_sum: "det (upd_row M i (\<Sum>s\<in>S. a s)) = (\<Sum>s\<in>S. det (upd_row M i (a s)))"
  by (induction S rule: infinite_finite_induct) (simp_all add: det_row_0 det_row_add)

lemma det_col_add: "det (upd_col M i (a + b)) = det (upd_col M i a) + det (upd_col M i b)"
  using det_row_add[of "transpose M" i a b] by (simp add: upd_row_transpose det_transpose)

lemma det_col_mul: "det (upd_col M i (c *s a)) = c * det (upd_col M i a)"
  using det_row_mul[of "transpose M" i c a] by (simp add: upd_row_transpose det_transpose)

lemma det_col_uminus: "det (upd_col M i (- a)) = - det (upd_col M i a)"
  by (simp add: vector_sneg_minus1 det_col_mul)

lemma det_col_minus: "det (upd_col M i (a - b)) = det (upd_col M i a) - det (upd_col M i b)"
  unfolding diff_conv_add_uminus det_col_add det_col_uminus ..

lemma det_col_0: "det (upd_col M i 0) = 0"
  using det_col_mul[of M i 0] by simp

lemma det_col_sum: "det (upd_col M i (\<Sum>s\<in>S. a s)) = (\<Sum>s\<in>S. det (upd_col M i (a s)))"
  by (induction S rule: infinite_finite_induct) (simp_all add: det_col_0 det_col_add)

(* Proof by Jose Divason *)
lemma det_identical_cols:
  assumes "i \<noteq> i'" shows "col A i = col A i' \<Longrightarrow> det A = 0"
proof (transfer fixing: i i')
  fix A :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" assume "(\<chi> j. A j i) = (\<chi> i. A i i')"
  then have [simp]: "\<And>j q. A j (Fun.swap i i' id (q j)) = A j (q j)"
    by (auto simp: vec_eq_iff swap_def)

  let ?p = "\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A i (p i))"
  let ?s = "\<lambda>q. Fun.swap i i' id \<circ> q"
  let ?E = "{p. p permutes UNIV \<and> evenperm p}"

  have [simp]: "inj_on ?s ?E"
    by (auto simp: inj_on_def fun_eq_iff swap_def)

  note p = permutes_UNIV_permutation evenperm_comp permutes_swap_id evenperm_swap permutes_compose
    sign_compose sign_swap_id
  from \<open>i \<noteq> i'\<close> have *: "evenperm q" if "q \<notin> ?s`?E" "q permutes UNIV" for q
    using that by (auto simp add: comp_assoc[symmetric] image_iff p elim!: allE[of _ "?s q"])
  have "(\<Sum>p | p permutes UNIV. ?p p) = (\<Sum>p \<in> ?E \<union> ?s`?E. ?p p)"
    by (auto simp add: permutes_compose permutes_swap_id intro: * sum.cong)
  also have "\<dots> = (\<Sum>p\<in>?E. ?p p) + (\<Sum>p\<in>?s`?E. ?p p)"
    by (intro sum.union_disjoint) (auto simp: p \<open>i \<noteq> i'\<close>)
  also have "(\<Sum>p\<in>?s`?E. ?p p) = (\<Sum>p\<in>?E. - ?p p)"
    using \<open>i \<noteq> i'\<close> by (subst sum.reindex) (auto intro!: sum.cong simp: p)
  finally show "(\<Sum>p | p permutes UNIV. ?p p) = 0"
    by (simp add: sum_negf)
qed

lemma det_identical_rows: "i \<noteq> i' \<Longrightarrow> row A i = row A i' \<Longrightarrow> det A = 0"
  using det_identical_cols[of i i' "transpose A"] by (simp add: det_transpose col_transpose)

lemma det_cols_sum:
  "det (upd_cols M T (\<lambda>i. \<Sum>s\<in>S. a i s)) = (\<Sum>f\<in>T \<rightarrow>\<^sub>E S. det (upd_cols M T (\<lambda>i. a i (f i))))"
proof (induct T arbitrary: M rule: infinite_finite_induct)
  case (insert i T)
  have "(\<Sum>f\<in>insert i T \<rightarrow>\<^sub>E S. det (upd_cols M (insert i T) (\<lambda>i. a i (f i)))) =
    (\<Sum>s\<in>S. \<Sum>f\<in>T \<rightarrow>\<^sub>E S. det (upd_cols (upd_col M i (a i s)) T (\<lambda>i. a i (f i))))"
    unfolding sum.cartesian_product PiE_insert_eq using \<open>i \<notin> T\<close>
    by (subst sum.reindex[OF inj_combinator[OF \<open>i \<notin> T\<close>]])
       (auto intro!: sum.cong arg_cong[where f=det] upd_cols_cong
             simp: upd_cols_insert_rev simp_implies_def)
  also have "\<dots> = det (upd_col (upd_cols M T (\<lambda>i. sum (a i) S)) i (\<Sum>s\<in>S. a i s))"
    unfolding insert(3)[symmetric] by (simp add: upd_cols_upd_col_swap[OF \<open>i \<notin> T\<close>] det_col_sum)
  finally show ?case
    by (simp add: upd_cols_insert)
qed auto

lemma det_rows_sum:
  "det (upd_rows M T (\<lambda>i. \<Sum>s\<in>S. a i s)) = (\<Sum>f\<in>T \<rightarrow>\<^sub>E S. det (upd_rows M T (\<lambda>i. a i (f i))))"
  using det_cols_sum[of "transpose M" T a S] by (simp add: upd_cols_transpose det_transpose)

lemma det_rows_mult: "det (upd_rows M T (\<lambda>i. c i *s a i)) = (\<Prod>i\<in>T. c i) * det (upd_rows M T a)"
  by transfer (simp add: prod.If_cases sum_distrib_left field_simps prod.distrib)

lemma det_cols_mult: "det (upd_cols M T (\<lambda>i. c i *s a i)) = (\<Prod>i\<in>T. c i) * det (upd_cols M T a)"
  using det_rows_mult[of "transpose M" T c a] by (simp add: det_transpose upd_rows_transpose)

lemma det_perm_rows_If: "det (perm_rows B f) = (if f permutes UNIV then of_int (sign f) * det B else 0)"
proof cases
  assume "\<not> f permutes UNIV"
  moreover
  with bij_imp_permutes[of f UNIV] have "\<not> inj f"
    using finite_UNIV_inj_surj[of f] by (auto simp: bij_betw_def)
  then obtain i j where "f i = f j" "i \<noteq> j"
    by (auto simp: inj_on_def)
  moreover
  then have "row (perm_rows B f) i = row (perm_rows B f) j"
    by transfer (auto simp: vec_eq_iff)
  ultimately show ?thesis
    by (simp add: det_identical_rows)
qed (simp add: det_perm_rows)

lemma det_mult: "det (A * B) = det A * det B"
proof -
  have "A * B = upd_rows 0 UNIV (\<lambda>i. \<Sum>j\<in>UNIV. to_fun A i j *s row B j)"
    by transfer simp
  moreover have "\<And>f. upd_rows 0 UNIV (\<lambda>i. Square_Matrix.row B (f i)) = perm_rows B f"
    by transfer simp
  moreover have "det A = (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. to_fun A i (p i)))"
    by transfer rule
  ultimately show ?thesis
    by (auto simp add: det_rows_sum det_rows_mult sum_distrib_right det_perm_rows_If
             split: if_split_asm intro!: sum.mono_neutral_cong_right)
qed

lift_definition minor :: "'a^^'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a::semiring_1^^'b" is
  "\<lambda>A i j k l. if k = i \<and> l = j then 1 else if k = i \<or> l = j then 0 else A k l" .

lemma minor_transpose: "minor (transpose A) i j = transpose (minor A j i)"
  by transfer (auto simp: fun_eq_iff)

lemma minor_eq_row_col: "minor M i j = upd_row (upd_col M j (axis i 1)) i (axis j 1)"
  by transfer (simp add: fun_eq_iff axis_def)

lemma minor_eq_col_row: "minor M i j = upd_col (upd_row M i (axis j 1)) j (axis i 1)"
  by transfer (simp add: fun_eq_iff axis_def)

lemma row_minor: "row (minor M i j) i = axis j 1"
  by (simp add: minor_eq_row_col)

lemma col_minor: "col (minor M i j) j = axis i 1"
  by (simp add: minor_eq_col_row)

lemma det_minor_row':
  "row B i = axis j 1 \<Longrightarrow> det (minor B i j) = det B"
proof (induction "{k. to_fun B k j \<noteq> 0} - {i}" arbitrary: B rule: infinite_finite_induct)
  case empty
  then have "\<And>k. k \<noteq> i \<longrightarrow> to_fun B k j = 0"
    by (auto simp add: card_eq_0_iff)
  with empty.prems have "axis i 1 = col B j"
    by transfer (auto simp: vec_eq_iff axis_def)
  with empty.prems[symmetric] show ?case
    by (simp add: minor_eq_row_col)
next
  case (insert r NZ)
  then have r: "r \<noteq> i" "to_fun B r j \<noteq> 0"
    by auto
  let ?B' = "upd_row B r (row B r - (to_fun B r j) *s row B i)"
  have "det (minor ?B' i j) = det ?B'"
  proof (rule insert.hyps)
    show "NZ = {k. to_fun ?B' k j \<noteq> 0} - {i}"
      using insert.hyps(2,4) insert.prems
      by transfer (auto simp add: axis_def set_eq_iff)
    show "row ?B' i = axis j 1"
      using r insert by (simp add: row_upd_row_If)
  qed
  also have "minor ?B' i j = minor B i j"
    using r insert.prems by transfer (simp add: fun_eq_iff axis_def)
  also have "det ?B' = det B"
    using \<open>r \<noteq> i\<close>
    by (simp add: det_row_minus det_row_mul det_identical_rows[OF \<open>r \<noteq> i\<close>] row_upd_row_If)
  finally show ?case .
qed simp

lemma det_minor_row: "det (minor B i j) = det (upd_row B i (axis j 1))"
proof -
  have "det (minor (upd_row B i (axis j 1)) i j) = det (upd_row B i (axis j 1))"
    by (rule det_minor_row') simp
  then show ?thesis
    by (simp add: minor_eq_col_row)
qed

lemma det_minor_col: "det (minor B i j) = det (upd_col B j (axis i 1))"
  using det_minor_row[of "transpose B" j i]
  by (simp add: minor_transpose det_transpose upd_row_transpose)

lift_definition cofactor :: "'a^^'b \<Rightarrow> 'a::comm_ring_1^^'b" is
  "\<lambda>A i j. det (minor A i j)" .

lemma cofactor_transpose: "cofactor (transpose A) = transpose (cofactor A)"
  by (simp add: cofactor_def minor_transpose det_transpose transpose.rep_eq to_fun_inject[symmetric] of_fun_inverse)

definition "adjugate A = transpose (cofactor A)"

lemma adjugate_transpose: "adjugate (transpose A) = transpose (adjugate A)"
  by (simp add: adjugate_def cofactor_transpose)

theorem adjugate_mult_det: "adjugate A * A = diag (det A)"
proof (intro to_fun_inject[THEN iffD1] fun_eq_iff[THEN iffD2] allI)
  fix i k
  have "to_fun (adjugate A * A) i k = (\<Sum>j\<in>UNIV. to_fun A j k * det (minor A j i))"
    by (simp add: adjugate_def times_sq_matrix.rep_eq transpose.rep_eq cofactor_def mult.commute of_fun_inverse)
  also have "\<dots> = det (upd_col A i (\<Sum>j\<in>UNIV. to_fun A j k *s axis j 1))"
    by (simp add: det_minor_col det_col_mul det_col_sum)
  also have "(\<Sum>j\<in>UNIV. to_fun A j k *s axis j 1) = col A k"
    by transfer (simp add: smult_axis vec_eq_iff, simp add: axis_def sum.If_cases)
  also have "det (upd_col A i (col A k)) = (if i = k then det A else 0)"
    by (auto simp: col_upd_col_If det_identical_cols[of i k])
  also have "\<dots> = to_fun (diag (det A)) i k"
    by (simp add: diag.rep_eq)
  finally show "to_fun (adjugate A * A) i k = to_fun (diag (det A)) i k" .
qed

lemma mult_adjugate_det: "A * adjugate A = diag (det A)"
proof-
  have "transpose (transpose (A * adjugate A)) = transpose (diag (det A))"
    unfolding transpose_mult adjugate_transpose[symmetric] adjugate_mult_det det_transpose ..
  then show ?thesis
    by simp
qed

end
