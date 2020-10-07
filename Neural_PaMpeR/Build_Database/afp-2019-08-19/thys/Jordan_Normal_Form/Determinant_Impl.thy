(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Equations for Determinants\<close>

text \<open>We compute determinants on arbitrary rings by applying elementary row-operations
  to bring a matrix on upper-triangular form. Then the determinant can be determined
  by multiplying all entries on the diagonal. Moreover the final result has to be divided
  by a factor which is determined by the row-operations that we performed. To this end,
  we require a division operation on the element type.

  The algorithm is parametric in a selection function for the pivot-element, e.g., for 
  matrices over polynomials it turned out that selecting a polynomial of minimal degree
  is beneficial.\<close>

theory Determinant_Impl
imports
  Polynomial_Interpolation.Missing_Polynomial
  "HOL-Computational_Algebra.Polynomial_Factorial"
  Determinant
begin

type_synonym 'a det_selection_fun = "(nat \<times> 'a)list \<Rightarrow> nat"

definition det_selection_fun :: "'a det_selection_fun \<Rightarrow> bool" where 
  "det_selection_fun f = (\<forall> xs. xs \<noteq> [] \<longrightarrow> f xs \<in> fst ` set xs)"


lemma det_selection_funD: "det_selection_fun f \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> f xs \<in> fst ` set xs"
  unfolding det_selection_fun_def by auto

definition mute_fun :: "('a :: comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a) \<Rightarrow> bool" where
  "mute_fun f = (\<forall> x y x' y' g. f x y = (x',y',g) \<longrightarrow> y \<noteq> 0 
   \<longrightarrow> x = x' * g \<and> y * x' = x * y')"

context
  fixes sel_fun :: "'a ::idom_divide det_selection_fun"
begin

subsection \<open>Properties of triangular matrices\<close>

text \<open>
  Each column of a triangular matrix should satisfy the following property.
\<close>

definition triangular_column::"nat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "triangular_column j A \<equiv> \<forall>i. j < i \<longrightarrow> i < dim_row A \<longrightarrow> A $$ (i,j) = 0"

lemma triangular_columnD [dest]:
  "triangular_column j A \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0"
  unfolding triangular_column_def by auto

lemma triangular_columnI [intro]:
  "(\<And>i. j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> triangular_column j A"
  unfolding triangular_column_def by auto

text \<open>
  The following predicate states that the first $k$ columns satisfy
  triangularity.
\<close>

definition triangular_to:: "nat \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "triangular_to k A == \<forall>j. j<k \<longrightarrow> triangular_column j A"

lemma triangular_to_triangular: "upper_triangular A = triangular_to (dim_row A) A"
  unfolding triangular_to_def triangular_column_def upper_triangular_def
  by auto

lemma triangular_toD [dest]:
  "triangular_to k A \<Longrightarrow> j < k \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0"
  unfolding triangular_to_def triangular_column_def by auto

lemma triangular_toI [intro]:
  "(\<And>i j. j < k \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> triangular_to k A"
  unfolding triangular_to_def triangular_column_def by auto

lemma triangle_growth:
  assumes tri:"triangular_to k A"
  and col:"triangular_column k A"
  shows "triangular_to (Suc k) A"
  unfolding triangular_to_def
proof (intro allI impI)
  fix i assume iSk:"i < Suc k"
  show "triangular_column i A"
  proof (cases "i = k")
    case True
      then show ?thesis using col by auto next
    case False
      then have "i < k" using iSk by auto
      thus ?thesis using tri unfolding triangular_to_def by auto
  qed
qed

lemma triangle_trans: "triangular_to k A \<Longrightarrow> k > k' \<Longrightarrow> triangular_to k' A"
  by (intro triangular_toI, elim triangular_toD, auto)


subsection \<open>Algorithms for Triangulization\<close>

context 
  fixes mf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a"
begin

private fun mute :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat" where
  "mute A_ll k l (r,A) = (let p = A $$ (k,l) in if p = 0 then (r,A) else 
    case mf A_ll p of (q',p',g) \<Rightarrow> 
      (r * q', addrow (-p') k l (multrow k q' A)))" 

lemma mute_preserves_dimensions:
  assumes "mute q k l (r,A) = (r',A')"
  shows [simp]: "dim_row A' = dim_row A" and [simp]: "dim_col A' = dim_col A"
using assms by (auto simp: Let_def split: if_splits prod.splits)

text \<open>
  Algorithm @{term "mute k l"} makes $k$-th row $l$-th column element to 0.
\<close>

lemma mute_makes_0 :
 assumes mute_fun: "mute_fun mf"
 assumes "mute (A $$ (l,l)) k l (r,A) = (r',A')"
 "l < dim_row A"
 "l < dim_col A"
 "k < dim_row A"
 "k \<noteq> l"
 shows "A' $$ (k,l) = 0"
proof -
  define a where "a = A $$ (l, l)"
  define b where "b = A $$ (k, l)"
  let ?mf = "mf (A $$ (l, l)) (A $$ (k, l))"
  obtain q' p' g where id: "?mf = (q',p',g)" by (cases ?mf, auto)
  note mf = mute_fun[unfolded mute_fun_def, rule_format, OF id]
  from assms show ?thesis
  unfolding mat_addrow_def using mf id by (auto simp: ac_simps Let_def split: if_splits)
qed

text \<open>It will not touch unexpected rows.\<close>
lemma mute_preserves:
  "mute q k l (r,A) = (r',A') \<Longrightarrow>
   i < dim_row A \<Longrightarrow>
   j < dim_col A \<Longrightarrow>
   l < dim_row A \<Longrightarrow>
   k < dim_row A \<Longrightarrow>
   i \<noteq> k \<Longrightarrow>
   A' $$ (i,j) = A $$ (i,j)"
   by (auto simp: Let_def split: if_splits prod.splits)

text \<open>It preserves $0$s in the touched row.\<close>
lemma mute_preserves_0:
  "mute q k l (r,A) = (r',A') \<Longrightarrow>
   i < dim_row A \<Longrightarrow>
   j < dim_col A \<Longrightarrow>
   l < dim_row A \<Longrightarrow>
   k < dim_row A \<Longrightarrow>
   A $$ (i,j) = 0 \<Longrightarrow>
   A $$ (l,j) = 0 \<Longrightarrow>
   A' $$ (i,j) = 0"
   by (auto simp: Let_def split: if_splits prod.splits)

text \<open>Hence, it will respect partially triangular matrix.\<close>
lemma mute_preserves_triangle:
 assumes rA' : "mute q k l (r,A) = (r',A')"
 and triA: "triangular_to l A"
 and lk: "l < k"
 and kr: "k < dim_row A"
 and lr: "l < dim_row A"
 and lc: "l < dim_col A"
 shows "triangular_to l A'"
proof (rule triangular_toI)
  fix i j
  assume jl: "j < l" and ji: "j < i" and ir': "i < dim_row A'"
  then have A0: "A $$ (i,j) = 0" using triA rA' by auto
  moreover have "A $$ (l,j) = 0" using triA jl jl lr by auto
  moreover have jc:"j < dim_col A" using jl lc by auto
  moreover have ir: "i < dim_row A" using ir' rA' by auto
  ultimately show "A' $$ (i,j) = 0"
    using mute_preserves_0[OF rA'] lr kr by auto
qed


text \<open>Recursive application of @{const mute}\<close>

private fun sub1 :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
where "sub1 q 0 l rA = rA"
  | "sub1 q (Suc k) l rA = mute q (l + Suc k) l (sub1 q k l rA)"

lemma sub1_preserves_dimensions[simp]:
  "sub1 q k l (r,A) = (r',A') \<Longrightarrow> dim_row A' = dim_row A"
  "sub1 q k l (r,A) = (r',A') \<Longrightarrow> dim_col A' = dim_col A"
proof (induction k arbitrary: r' A')
  case (Suc k)
    moreover obtain r' A' where rA': "sub1 q k l (r, A) = (r', A')" by force
    moreover fix r'' A'' assume "sub1 q (Suc k) l (r, A) = (r'', A'')" 
    ultimately show "dim_row A'' = dim_row A" "dim_col A'' = dim_col A" by auto
qed auto

lemma sub1_closed [simp]:
  "sub1 q k l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> A' \<in> carrier_mat m n"
  unfolding carrier_mat_def by auto

lemma sub1_preserves_diagnal:
  assumes "sub1 q k l (r,A) = (r',A')"
  and "l < dim_col A"
  and "k + l < dim_row A"
  shows "A' $$ (l,l) = A $$ (l,l)"
using assms
proof -
  show "k + l < dim_row A \<Longrightarrow> sub1 q k l (r,A) = (r',A') \<Longrightarrow>
    A' $$ (l,l) = A $$ (l,l)"
  proof (induction k arbitrary: r' A')
    case (Suc k)
      obtain r'' A'' where rA''[simp]: "sub1 q k l (r,A) = (r'',A'')" by force
      have [simp]:"dim_row A'' = dim_row A" and [simp]:"dim_col A'' = dim_col A"
        using snd_conv sub1_preserves_dimensions[OF rA''] by auto
      have "A'' $$ (l,l) = A $$ (l,l)" using assms Suc by auto
      have rA': "mute q (l + Suc k) l (r'', A'') = (r',A')"
        using Suc by auto
      show ?case using subst mute_preserves[OF rA'] Suc assms by auto
  qed auto
qed

text \<open>Triangularity is respected by @{const sub1}.\<close>
lemma sub1_preserves_triangle:
  assumes "sub1 q k l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lr: "l < dim_row A"
  and lc: "l < dim_col A"
  and lkr: "l + k < dim_row A"
  shows "triangular_to l A'"
using assms
proof -
  show "sub1 q k l (r,A) = (r',A') \<Longrightarrow> l + k < dim_row A \<Longrightarrow>
    triangular_to l A'"
  proof (induction k arbitrary: r' A')
  case (Suc k)
    then have "sub1 q (Suc k) l (r,A) = (r',A')" by auto
    moreover obtain r'' A''
      where rA'': "sub1 q k l (r, A) = (r'',A'')" by force
    ultimately
      have rA': "mute q (Suc (l + k)) l (r'',A'') = (r',A')" by auto
    have "triangular_to l A''" using rA'' Suc by auto
    thus ?case
      using Suc assms mute_preserves_triangle[OF rA'] rA'' by auto
  qed (insert assms,auto)
qed

context
  assumes mf: "mute_fun mf"
begin
lemma sub1_makes_0s:
  assumes "sub1 (A $$ (l,l)) k l (r,A) = (r',A')"
  and lr: "l < dim_row A"
  and lc: "l < dim_col A"
  and li: "l < i"
  and "i \<le> k + l"
  and "k + l < dim_row A"
  shows "A' $$ (i,l) = 0"
using assms
proof -
  show "sub1 (A $$ (l,l)) k l (r,A) = (r',A') \<Longrightarrow> i \<le> k + l \<Longrightarrow> k + l < dim_row A \<Longrightarrow>
    A' $$ (i,l) = 0"
  using lr lc li
  proof (induction k arbitrary: r' A')
  case (Suc k)
    obtain r' A' where rA': "sub1 (A $$ (l,l)) k l (r, A) = (r',A')" by force
    fix r'' A''
    from sub1_preserves_diagnal[OF rA'] have AA': "A $$ (l, l) = A' $$ (l, l)" using Suc(2-) by auto
    assume "sub1 (A $$ (l,l)) (Suc k) l (r, A) = (r'',A'')"
    then have rA'': "mute (A $$ (l,l)) (Suc (l + k)) l (r', A') = (r'', A'')"
      using rA' by simp
    have ir: "i < dim_row A" using Suc by auto
    have il: "i \<noteq> l" using li by auto
    have lr': "l < dim_row A'" using lr rA' by auto
    have lc': "l < dim_col A'" using lc rA' by auto
    have Slkr': "Suc (l+k) < dim_row A'" using Suc rA' by auto
    show "A'' $$ (i,l) = 0"
    proof (cases "Suc(l + k) = i")
      case True {
        have l: "Suc (l + k) \<noteq> l" by auto
        show ?thesis
          using mute_makes_0[OF mf rA''[unfolded AA'] lr' lc' Slkr' l] ir il rA'
          by (simp add:True)
      } next
      case False {
        then have ikl: "i \<le> k+l" using Suc by auto
        have ir': "i < dim_row A'" using ir rA' by auto
        have lc': "l < dim_col A'" using lc rA' by auto
        have IH: "A' $$ (i,l) = 0" using rA' Suc False by auto
        thus ?thesis using mute_preserves[OF rA'' ir' lc'] rA' False Suc
          by simp
      }
    qed
  qed auto
qed

lemma sub1_triangulizes_column:
  assumes rA': "sub1 (A $$ (l,l)) (dim_row A - Suc l) l (r,A) = (r',A')"
  and tri:"triangular_to l A"
  and r: "dim_row A > 0"
  and lr: "l < dim_row A"
  and lc: "l < dim_col A"
  shows "triangular_column l A'"
proof (intro triangular_columnI)
  fix i
  assume li: "l < i"
  assume ir: "i < dim_row A'"
    also have "... = dim_row A" using sub1_preserves_dimensions[OF rA'] by auto
    also have "... = dim_row A - l + l" using lr li by auto
    finally have ir2: "i \<le> dim_row A - l + l" by auto
  show "A' $$ (i,l) = 0"
    apply (subst sub1_makes_0s[OF rA' lr lc])
    using li ir assms
    by auto
qed

text \<open>
  The algorithm @{const sub1} increases the number of columns that form triangle.
\<close>
lemma sub1_grows_triangle:
  assumes rA': "sub1 (A $$ (l,l)) (dim_row A - Suc l) l (r,A) = (r',A')"
  and r: "dim_row A > 0"
  and tri:"triangular_to l A"
  and lr: "l < dim_row A"
  and lc: "l < dim_col A"
  shows "triangular_to (Suc l) A'"
proof -
  have "triangular_to l A'"
    using sub1_preserves_triangle[OF rA'] assms by auto
  moreover have "triangular_column l A'"
    using sub1_triangulizes_column[OF rA'] assms by auto
  ultimately show ?thesis by (rule triangle_growth)
qed
end

subsection \<open>Finding Non-Zero Elements\<close>

private definition find_non0 :: "nat \<Rightarrow> 'a mat \<Rightarrow> nat option" where
  "find_non0 l A = (let is = [Suc l ..< dim_row A];
    Ais = filter (\<lambda> (i,Ail). Ail \<noteq> 0) (map (\<lambda> i. (i, A $$ (i,l))) is)
    in case Ais of [] \<Rightarrow> None | _ \<Rightarrow> Some (sel_fun Ais))"

lemma find_non0: assumes sel_fun: "det_selection_fun sel_fun"
  and res: "find_non0 l A = Some m"
  shows "A $$ (m,l) \<noteq> 0" "l < m" "m < dim_row A"
proof -
  let ?xs = "filter (\<lambda> (i,Ail). Ail \<noteq> 0) (map (\<lambda> i. (i, A $$ (i,l))) [Suc l..<dim_row A])"
  from res[unfolded find_non0_def Let_def]
  have xs: "?xs \<noteq> []" and m: "m = sel_fun ?xs"
    by (cases ?xs, auto)+
  from det_selection_funD[OF sel_fun xs, folded m] show "A $$ (m, l) \<noteq> 0" "l < m" "m < dim_row A" by auto
qed

text \<open>
  If @{term "find_non0 l A"} fails,
  then $A$ is already triangular to $l$-th column.
\<close>

lemma find_non0_all0:
  "find_non0 l A = None \<Longrightarrow> triangular_column l A"
proof (intro triangular_columnI) 
  fix i
  let ?xs = "filter (\<lambda> (i,Ail). Ail \<noteq> 0) (map (\<lambda> i. (i, A $$ (i,l))) [Suc l..<dim_row A])"
  assume none: "find_non0 l A = None" and li: "l < i" "i < dim_row A"
  from none have xs: "?xs = []"
    unfolding find_non0_def Let_def by (cases ?xs, auto)
  from li have "(i, A $$ (i,l)) \<in> set (map (\<lambda> i. (i, A $$ (i,l))) [Suc l..<dim_row A])" by auto
  with xs show "A $$ (i,l) = 0"
    by (metis (mono_tags) xs case_prodI filter_empty_conv)
qed

subsection \<open>Determinant Preserving Growth of Triangle\<close>

text \<open>
  The algorithm @{const sub1} does not preserve determinants when it hits
  a $0$-valued diagonal element. To avoid this case, we introduce the following
  operation:
\<close>

private fun sub2 :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
  where "sub2 d l (r,A) = (
    case find_non0 l A of None \<Rightarrow> (r,A)
    | Some m \<Rightarrow> let A' = swaprows m l A in sub1 (A' $$ (l,l)) (d - Suc l) l (-r, A'))"

lemma sub2_preserves_dimensions[simp]:
  assumes rA': "sub2 d l (r,A) = (r',A')"
  shows "dim_row A' = dim_row A \<and> dim_col A' = dim_col A"
proof (cases "find_non0 l A")
  case None then show ?thesis using rA' by auto next
  case (Some m) then show ?thesis using rA' by (cases "m = l", auto simp: Let_def)
qed

lemma sub2_closed [simp]:
  "sub2 d l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> A' \<in> carrier_mat m n"
  unfolding carrier_mat_def by auto

context 
  assumes sel_fun: "det_selection_fun sel_fun"
begin

lemma sub2_preserves_triangle:
  assumes rA': "sub2 d l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lc: "l < dim_col A"
  and ld: "l < d"
  and dr: "d \<le> dim_row A"
  shows "triangular_to l A'"
proof -
  have lr: "l < dim_row A" using ld dr by auto
  show ?thesis
  proof (cases "find_non0 l A")
    case None then show ?thesis using rA' tri by simp next
    case (Some m) {
      have lm : "l < m" and mr : "m < dim_row A"
        using find_non0[OF sel_fun Some] by auto
      let ?A1 = "swaprows m l A"
  
      have tri'': "triangular_to l ?A1"
      proof (intro triangular_toI)
        fix i j
        assume jl:"j < l" and ji:"j < i" and ir1: "i < dim_row ?A1"
        have jm: "j < m" using jl lm by auto
        have ir: "i < dim_row A" using ir1 by auto
        have jc: "j < dim_col A" using jl lc by auto
        show "?A1 $$ (i, j) = 0"
        proof (cases "m=i")
          case True {
            then have li: "l \<noteq> i" using lm by auto
            hence "?A1 $$ (i,j) = A $$ (l,j)" using ir jc \<open>m=i\<close> by auto
            also have "... = 0" using tri jl lr by auto
            finally show ?thesis.
           }  next
          case False show ?thesis
            proof (cases "l=i")
              case True {
                then have "?A1 $$ (i,j) = A $$ (m,j)"
                  using ir jc \<open>m\<noteq>i\<close> by auto
                thus "?A1 $$ (i,j) = 0" using tri jl jm mr by auto
              } next
              case False {
                then have "?A1 $$ (i,j) = A $$ (i,j)"
                  using ir jc \<open>m\<noteq>i\<close> by auto
                thus "?A1 $$ (i,j) = 0" using tri jl ji ir by auto
              }
           qed
        qed
      qed
  
      let ?rA3 = "sub1 (?A1 $$ (l,l)) (d - Suc l) l (-r,?A1)"
      have [simp]: "dim_row ?A1 = dim_row A \<and> dim_col ?A1 = dim_col A" by auto
      have rA'2: "?rA3 = (r',A')" using rA' Some by (simp add: Let_def)
      have "l + (d - Suc l) < dim_row A" using ld dr by auto
      thus ?thesis
        using sub1_preserves_triangle[OF rA'2 tri''] lr lc rA' by auto
    }
  qed
qed

lemma sub2_grows_triangle:
  assumes mf: "mute_fun mf"
  and rA': "sub2 (dim_row A) l (r,A) = (r',A')"
  and tri: "triangular_to l A"
  and lc: "l < dim_col A"
  and lr: "l < dim_row A"
  shows "triangular_to (Suc l) A'"
proof (rule triangle_growth)
  show "triangular_to l A'"
    using sub2_preserves_triangle[OF rA' tri lc lr] by auto
    next
  have r0: "0 < dim_row A" using lr by auto
  show "triangular_column l A'"
    proof (cases "find_non0 l A")
      case None {
        then have "A' = A" using rA' by simp
        moreover have "triangular_column l A"  using find_non0_all0[OF None].
        ultimately show ?thesis by auto
      } next
      case (Some m) {
        have lm: "l < m" and mr: "m < dim_row A"
          using find_non0[OF sel_fun Some] by auto
        let ?A = "swaprows m l A"
        have tri2: "triangular_to l ?A"
          proof
            fix i j assume jl: "j < l" and ji:"j < i" and ir: "i < dim_row ?A"
            show "?A $$ (i,j) = 0"
            proof (cases "i = m")
              case True {
                then have "?A $$ (i,j) = A $$ (l,j)"
                  using jl lc ir by simp
                also have "... = 0"
                  using triangular_toD[OF tri jl jl] lr by auto
                finally show ?thesis by auto
              } next
              case False show ?thesis
                proof (cases "i = l")
                  case True {
                    then have "?A $$ (i,j) = A $$ (m,j)"
                      using jl lc ir by auto
                    also have "... = 0"
                      using triangular_toD[OF tri jl] jl lm mr by auto
                    finally show ?thesis by auto
                  } next
                  case False {
                    then have "?A $$ (i,j) = A $$ (i,j)"
                      using \<open>i \<noteq> m\<close> jl lc ir by auto
                    thus ?thesis using tri jl ji ir by auto
                  }
                qed
            qed
          qed
        have rA'2: "sub1 (?A $$ (l,l)) (dim_row ?A - Suc l) l (-r, ?A) = (r',A')"
          using lm Some rA' by (simp add: Let_def)
        show ?thesis
          using sub1_triangulizes_column[OF mf rA'2 tri2] r0 lr lc by auto
      }
    qed
qed
end

subsection \<open>Recursive Triangulization of Columns\<close>

text \<open>
  Now we recursively apply @{const sub2} to make the entire matrix to be triangular.
\<close>

private fun sub3 :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<times> 'a mat \<Rightarrow> 'a \<times> 'a mat"
  where "sub3 d 0 rA = rA"
  | "sub3 d (Suc l) rA = sub2 d l (sub3 d l rA)"

lemma sub3_preserves_dimensions[simp]:
  "sub3 d l (r,A) = (r',A') \<Longrightarrow> dim_row A' = dim_row A"
  "sub3 d l (r,A) = (r',A') \<Longrightarrow> dim_col A' = dim_col A"
proof (induction l arbitrary: r' A')
  case (Suc l)
    obtain r' A' where rA': "sub3 d l (r, A) = (r', A')" by force
    fix r'' A'' assume rA'': "sub3 d (Suc l) (r, A) = (r'', A'')" 
    then show "dim_row A'' = dim_row A" "dim_col A'' = dim_col A"
    using Suc rA' by auto
qed auto

lemma sub3_closed[simp]:
  "sub3 k l (r,A) = (r',A') \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> A' \<in> carrier_mat m n"
  unfolding carrier_mat_def by auto

lemma sub3_makes_triangle:
  assumes mf: "mute_fun mf"
  and sel_fun: "det_selection_fun sel_fun"
  and "sub3 (dim_row A) l (r,A) = (r',A')"
  and "l \<le> dim_row A"
  and "l \<le> dim_col A"
  shows "triangular_to l A'"
  using assms
proof -
  show "sub3 (dim_row A) l (r,A) = (r',A') \<Longrightarrow> l \<le> dim_row A \<Longrightarrow> l \<le> dim_col A \<Longrightarrow>
    triangular_to l A'"
  proof (induction l arbitrary:r' A')
    case (Suc l)
      then have Slr: "Suc l \<le> dim_row A" and Slc: "Suc l \<le> dim_col A" by auto
      hence lr: "l < dim_row A" and lc: "l < dim_col A" by auto
      moreover obtain r'' A''
        where rA'': "sub3 (dim_row A) l (r,A) = (r'',A'')" by force
      ultimately have IH: "triangular_to l A''" using Suc by auto
      have [simp]:"dim_row A'' = dim_row A" and [simp]:"dim_col A'' = dim_col A"
        using Slr Slc rA'' by auto
      fix r' A'
      assume "sub3 (dim_row A) (Suc l) (r, A) = (r', A')"
      then have rA': "sub2 (dim_row A'') l (r'',A'') = (r',A')"
        using rA'' by auto
      show "triangular_to (Suc l) A'"
        using sub2_grows_triangle[OF sel_fun mf rA'] lr lc rA'' IH by auto
  qed auto
qed

subsection \<open>Triangulization\<close>

definition triangulize :: "'a mat \<Rightarrow> 'a \<times> 'a mat"
where "triangulize A = sub3 (dim_row A) (dim_row A) (1,A)"

lemma triangulize_preserves_dimensions[simp]:
  "triangulize A = (r',A') \<Longrightarrow> dim_row A' = dim_row A"
  "triangulize A = (r',A') \<Longrightarrow> dim_col A' = dim_col A"
  unfolding triangulize_def by auto

lemma triangulize_closed[simp]:
  "triangulize A = (r',A') \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> A' \<in> carrier_mat m n"
  unfolding carrier_mat_def by auto

context
  assumes mf: "mute_fun mf"
  and sel_fun: "det_selection_fun sel_fun"
begin

theorem triangulized:
  assumes "A \<in> carrier_mat n n"
  and "triangulize A = (r',A')"
  shows "upper_triangular A'"
proof (cases "0<n")
  case True
    have rA': "sub3 (dim_row A) (dim_row A) (1,A) = (r',A')"
      using assms unfolding triangulize_def by auto
    have nr:"n = dim_row A" and nc:"n = dim_col A" and nr':"n = dim_row A'"
    using assms by auto
    thus ?thesis
      unfolding triangular_to_triangular
      using sub3_makes_triangle[OF mf sel_fun rA'] True by auto
    next
  case False
    then have nr':"dim_row A' = 0" using assms by auto
    thus ?thesis unfolding upper_triangular_def by auto
qed

subsection\<open>Divisor will not be 0\<close>

text \<open>
  Here we show that each sub-algorithm will not make $r$
  of the input/output pair $(r,A)$ to 0.
  The algorithm @{term "sub1 A_ll k l (r,A)"} requires $A_{l,l} \neq 0$.
\<close>

lemma sub1_divisor [simp]:
  assumes rA': "sub1 q k l (r, A) = (r',A')"
  and r0: "r \<noteq> 0"
  and All: "q \<noteq> 0"
  and "k + l < dim_row A "
  and lc: "l < dim_col A"
  shows "r' \<noteq> 0"
using assms
proof -
  show "sub1 q k l (r,A) = (r',A') \<Longrightarrow> k + l < dim_row A \<Longrightarrow> r' \<noteq> 0"
  proof (induction k arbitrary: r' A')
    case (Suc k)
      obtain r'' A'' where rA'': "sub1 q k l (r, A) = (r'', A'')" by force
      then have IH: "r'' \<noteq> 0" using Suc by auto
      obtain q' l' g where mf_id: "mf q (A'' $$ (Suc (l + k), l)) = (q',l',g)" by (rule prod_cases3)      
      define fact where "fact = (if A'' $$ (Suc (l+k),l) = 0 then 1 else q')"
      note mf = mf[unfolded mute_fun_def, rule_format, OF mf_id]
      have All: "q \<noteq> 0"
        using sub1_preserves_diagnal[OF rA'' lc] All Suc by auto
      moreover have "fact \<noteq> 0" unfolding fact_def using All mf by auto
      moreover assume "sub1 q (Suc k) l (r,A) = (r',A')"
        then have "mute q (Suc (l + k)) l (r'',A'') = (r',A')"
          using rA'' by auto
        hence "r'' * fact = r'"
          unfolding mute.simps fact_def Let_def mf_id using IH by (auto split: if_splits)
      ultimately show "r' \<noteq> 0" using IH by auto
  qed (insert r0, simp)
qed

text \<open>The algorithm @{term "sub2"} will not require such a condition.\<close>
lemma sub2_divisor [simp]:
  assumes rA': "sub2 k l (r, A) = (r',A')"
  and lk: "l < k"
  and kr: "k \<le> dim_row A"
  and lc: "l < dim_col A"
  and r0: "r \<noteq> 0"
  shows "r' \<noteq> 0"
using assms
proof (cases "find_non0 l A") {
  case (Some m)
    then have Aml0: "A $$ (m,l) \<noteq> 0" using find_non0[OF sel_fun] by auto
    have md: "m < dim_row A" using find_non0[OF sel_fun Some] lk kr by auto
    let ?A'' = "swaprows m l A"
    have rA'2: "sub1 (?A'' $$ (l,l)) (k - Suc l) l (-r, ?A'') = (r',A')"
      using rA' Some by (simp add: Let_def)
    have All0: "?A'' $$ (l,l) \<noteq> 0" using Aml0 md lk kr lc by auto
    show ?thesis using sub1_divisor[OF rA'2 _ All0] r0 lk kr lc by simp
} qed auto

lemma sub3_divisor [simp]:
  assumes "sub3 d l (r,A) = (r'',A'')"
  and "l \<le> d"
  and "d \<le> dim_row A"
  and "l \<le> dim_col A"
  and r0: "r \<noteq> 0"
  shows "r'' \<noteq> 0"
  using assms
proof -
  show
    "sub3 d l (r,A) = (r'',A'') \<Longrightarrow>
     l \<le> d \<Longrightarrow> d \<le> dim_row A \<Longrightarrow> l \<le> dim_col A \<Longrightarrow> ?thesis"
  proof (induction l arbitrary: r'' A'')
    case 0
      then show ?case using r0 by simp
      next
    case (Suc l)
      obtain r' A' where rA': "sub3 d l (r,A) = (r',A')" by force
      then have [simp]:"dim_row A' = dim_row A" and [simp]:"dim_col A' = dim_col A"
        by auto
      from rA' have "r' \<noteq> 0" using Suc r0 by auto
      moreover have "sub2 d l (r',A') = (r'',A'')"
        using rA' Suc by simp
      ultimately show ?case using sub2_divisor using Suc by simp
  qed
qed

theorem triangulize_divisor:
  assumes A: "A \<in> carrier_mat d d"
  shows "triangulize A = (r',A') \<Longrightarrow> r' \<noteq> 0"
unfolding triangulize_def
proof -
  assume rA': "sub3 (dim_row A) (dim_row A) (1, A) = (r', A')"
  show ?thesis using sub3_divisor[OF rA'] A by auto 
qed

subsection \<open>Determinant Preservation Results\<close>

text \<open>
  For each sub-algorithm $f$,
  we show $f(r,A) = (r',A')$ implies @{term "r * det A' = r' * det A"}.
\<close>

lemma mute_det:
  assumes "A \<in> carrier_mat n n"
  and rA': "mute q k l (r,A) = (r',A')"
  and "k < n"
  and "l < n"
  and "k \<noteq> l"
  shows "r * det A' = r' * det A"
proof (cases "A $$ (k,l) = 0")
  case True
  thus ?thesis using assms by auto
next
  case False
  obtain p' q' g where mf_id: "mf q (A $$ (k,l)) = (q',p',g)" by (rule prod_cases3)
  let ?All = "q'"
  let ?Akl = "- p'"
  let ?B = "multrow k ?All A"
  let ?C = "addrow ?Akl k l ?B"
  have "r * det A' = r * det ?C"  using assms by (simp add: Let_def mf_id False)
  also have "det ?C = det ?B" using assms by (auto simp: det_addrow)
  also have "\<dots> = ?All * det A" using assms det_multrow by auto
  also have "r * \<dots> = (r * ?All) * det A" by simp
  also have r: "r * ?All = r'" using assms by (simp add: Let_def mf_id False)
  finally show ?thesis.
qed

lemma sub1_det:
  assumes A: "A \<in> carrier_mat n n"
  and sub1: "sub1 q k l (r,A) = (r'',A'')"
  and r0: "r \<noteq> 0"
  and All0: "q \<noteq> 0"
  and l: "l + k < n"
  shows "r * det A'' = r'' * det A"
  using sub1 l
proof (induction k arbitrary: A'' r'')
  case 0
  then show ?case by auto
next
  case (Suc k)
  let ?rA' = "sub1 q k l (r,A)"
  obtain r' A' where rA':"?rA' = (r',A')" by force
  have A':"A' \<in> carrier_mat n n" using sub1_closed[OF rA'] A by auto
  have IH: "r * det A' = r' * det A" using Suc assms rA' by auto
  assume "sub1 q (Suc k) l (r,A) = (r'',A'')"
  then have rA'':"mute q (Suc (l+k)) l (r',A') = (r'',A'')" using rA' by auto
  hence lem: "r' * det A'' = r'' * det A'"
    using assms Suc A' mute_det[OF A' rA''] by auto
  hence "r * r' * det A'' = r * r'' * det A'" by auto
  also from IH have "... = r'' * r' * det A" by auto
  finally have *: "r * r' * det A'' = r'' * r' * det A" .
  then have "r * r' * det A'' div r' = r'' * r' * det A div r'" by presburger
  moreover have "r' \<noteq> 0"
    using r0 sub1_divisor[OF rA'] All0 Suc A by auto
  ultimately show ?case using * by auto
qed

lemma sub2_det:
  assumes A: "A \<in> carrier_mat d d"
  and rA': "sub2 d l (r,A) = (r',A')"
  and r0: "r \<noteq> 0"
  and ld: "l < d"
  shows "r * det A' = r' * det A"
proof (cases "find_non0 l A")
  case None then show ?thesis using assms by auto next
  case (Some m) {
    then have lm: "l < m" and md: "m < d"
      using A find_non0[OF sel_fun Some] ld by auto
    hence "m \<noteq> l" by auto
    let ?A'' = "swaprows m l A"
    have rA'2: "sub1 (?A'' $$ (l,l)) (d - Suc l) l (-r, ?A'') = (r',A')"
      using rA' Some by (simp add: Let_def)
    have A'': "?A'' \<in> carrier_mat d d" using A by auto
    hence A''ll0: "?A'' $$ (l,l) \<noteq> 0"
      using find_non0[OF sel_fun Some] ld by auto
    hence "-r * det A' = r' * det ?A''"
      using sub1_det[OF A'' rA'2] ld A r0 by auto
    also have "r * ... = -r * r' * det A"
      using det_swaprows[OF md ld \<open>m\<noteq>l\<close> A] by auto
    finally have "r * -r * det A' = -r * r' * det A" by auto
    thus ?thesis using r0 by auto
  }
qed

lemma sub3_det:
  assumes A:"A \<in> carrier_mat d d"
  and "sub3 d l (r,A) = (r'',A'')"
  and r0: "r \<noteq> 0"
  and "l \<le> d"
  shows "r * det A'' = r'' * det A"
  using assms
proof -
  have d: "d = dim_row A" using A by auto
  show "sub3 d l (r,A) = (r'',A'') \<Longrightarrow> l \<le> d \<Longrightarrow> r * det A'' = r'' * det A"
  proof (induction l arbitrary: r'' A'')
    case (Suc l)
      let ?rA' = "sub3 d l (r,A)"
      obtain r' A' where rA':"?rA' = (r',A')" by force
      then have rA'': "sub2 d l (r',A') = (r'',A'')"
        using Suc by auto
      have A': "A' \<in> carrier_mat d d" using A rA' rA'' by auto
      have r'0: "r' \<noteq> 0" using r0 sub3_divisor[OF rA'] A Suc by auto
      have "r' * det A'' = r'' * det A'"
        using Suc r'0 A by(subst sub2_det[OF A' rA''],auto)
      also have "r * ... = r'' * (r * det A')" by auto
      also have "r * det A' = r' * det A" using Suc rA' by auto
      also have "r'' * ... div r' = r'' * r' * det A div r'" by (simp add: ac_simps)
      finally show "r * det A'' = r'' * det A" using r'0 
        by (metis \<open>r * det A' = r' * det A\<close> \<open>r' * det A'' = r'' * det A'\<close> 
          mult.left_commute mult_cancel_left)
  qed simp
qed

theorem triangulize_det:
  assumes A: "A \<in> carrier_mat d d"
  and rA': "triangulize A = (r',A')"
  shows "det A * r' = det A'"
proof -
  have rA'2: "sub3 d d (1,A) = (r',A')"
    using A rA' unfolding triangulize_def by auto
  show ?thesis
  proof (cases "d = 0")
    case True
      then have A': "A' \<in> carrier_mat 0 0" using A rA'2 by auto
      have rA'3: "(r',A') = (1,A)" using True rA'2 by simp
      thus ?thesis by auto
      next
    case False
      then show ?thesis using sub3_det[OF A rA'2] assms by auto
  qed
qed
end

subsection \<open>Determinant Computation\<close>

definition det_code :: "'a mat \<Rightarrow> 'a" where
  "det_code A = (if dim_row A = dim_col A then
     case triangulize A of (m,A') \<Rightarrow>
       prod_list (diag_mat A') div m
   else 0)"

lemma det_code[simp]: assumes sel_fun: "det_selection_fun sel_fun"
  and mf: "mute_fun mf"
  shows "det_code A = det A"
  using det_code_def[simp]
proof (cases "dim_row A = dim_col A")
  case True
  then have A: "A \<in> carrier_mat (dim_row A) (dim_row A)" unfolding carrier_mat_def by auto
  obtain r' A' where rA': "triangulize A = (r',A')" by force
  from triangulize_divisor[OF mf sel_fun A] rA' have r'0: "r' \<noteq> 0" by auto
  from triangulize_det[OF mf sel_fun A rA'] have det': "det A * r' = det A'" by auto
  from triangulized[OF mf sel_fun A, unfolded rA'] have tri': "upper_triangular A'" by simp
  have A': "A' \<in> carrier_mat (dim_row A') (dim_row A')"
    using triangulize_closed[OF rA' A] by auto
  from tri' have tr: "triangular_to (dim_row A') A'" by auto
  have "det_code A = prod_list (diag_mat A') div r'" using rA' True by simp
  also have "prod_list (diag_mat A') = det A'"
    unfolding det_upper_triangular[OF tri' A'] ..
  also have "\<dots> = det A * r'" by (simp add: det')
  also have "\<dots> div r' = det A" using r'0 by auto
  finally show ?thesis .
qed (simp add: det_def)

end
end

text \<open>Now we can select an arbitrary selection and mute function. This will be important for computing
  resultants over polynomials, where usually a polynomial with small degree is preferable.

  The default however is to use the first element.\<close>

definition trivial_mute_fun :: "'a :: comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "trivial_mute_fun x y = (x,y,1)"

lemma trivial_mute_fun[simp,intro]: "mute_fun trivial_mute_fun"
  unfolding mute_fun_def trivial_mute_fun_def by auto

definition fst_sel_fun :: "'a det_selection_fun" where
  "fst_sel_fun x = fst (hd x)" 

lemma fst_sel_fun[simp]: "det_selection_fun fst_sel_fun"
  unfolding det_selection_fun_def fst_sel_fun_def by auto

context
  fixes measure :: "'a \<Rightarrow> nat" 
begin
private fun select_min_main where 
  "select_min_main m i ((j,p) # xs) = (let n = measure p in if n < m then select_min_main n j xs
    else select_min_main m i xs)"
| "select_min_main m i [] = i"

definition select_min :: "(nat \<times> 'a) list \<Rightarrow> nat" where
  "select_min xs = (case xs of ((i,p) # ys) \<Rightarrow> (select_min_main (measure p) i ys))"

lemma select_min[simp]: "det_selection_fun select_min"
  unfolding det_selection_fun_def 
proof (intro allI impI)
  fix xs :: "(nat \<times> 'a)list"
  assume "xs \<noteq> []"
  then obtain i p ys where xs: "xs = ((i,p) # ys)" by (cases xs, auto)
  then obtain m where id: "select_min xs = select_min_main m i ys" unfolding select_min_def by auto
  have "i \<in> fst ` set xs" "set ys \<subseteq> set xs" unfolding xs by auto
  thus "select_min xs \<in> fst ` set xs" unfolding id
  proof (induct ys arbitrary: m i )
    case (Cons jp ys m i)
    obtain j p where jp: "jp = (j,p)" by force
    obtain k n where res: "select_min_main m i (jp # ys) = select_min_main n k ys" 
      and k: "k \<in> fst ` set xs"
      using Cons(2-) unfolding jp by (cases "measure p < m"; force simp: Let_def)
    from Cons(1)[OF k, of n] Cons(3) 
    show ?case unfolding res by auto
  qed simp
qed
end

text \<open>For the code equation we use the trivial mute and selection function as this does
  not impose any further class restrictions.\<close>

lemma det_code_fst_sel_fun[code]: "det A = det_code fst_sel_fun trivial_mute_fun A" by simp

text \<open>But we also provide specialiced functions for more specific carriers.\<close>

definition field_mute_fun :: "'a :: field \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "field_mute_fun x y = (x/y,1,y)"

lemma field_mute_fun[simp,intro]: "mute_fun field_mute_fun"
  unfolding mute_fun_def field_mute_fun_def by auto

definition det_field :: "'a :: field mat \<Rightarrow> 'a" where 
  "det_field A = det_code fst_sel_fun field_mute_fun A"

lemma det_field[simp]: "det_field = det"
  by (intro ext, auto simp: det_field_def)

definition gcd_mute_fun :: "'a :: ring_gcd \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
  "gcd_mute_fun x y = (let g = gcd x y in (x div g, y div g,g))"

lemma gcd_mute_fun[simp,intro]: "mute_fun gcd_mute_fun"
  unfolding mute_fun_def gcd_mute_fun_def by (auto simp: Let_def div_mult_swap mult.commute)

definition det_int :: "int mat \<Rightarrow> int" where 
  "det_int A = det_code (select_min (\<lambda> x. nat (abs x))) gcd_mute_fun A"

lemma det_int[simp]: "det_int = det"
  by (intro ext, auto simp: det_int_def)

definition det_field_poly :: "'a :: {field,euclidean_ring_gcd} poly mat \<Rightarrow> 'a poly" where
  "det_field_poly A = det_code (select_min degree) gcd_mute_fun A"

lemma det_field_poly[simp]: "det_field_poly = det"
  by (intro ext, auto simp: det_field_poly_def)

end
