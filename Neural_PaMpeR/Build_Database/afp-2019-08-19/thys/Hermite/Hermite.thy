(*  
    Title:      Hermite.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Hermite Normal Form\<close>

theory Hermite
  imports 
  Echelon_Form.Echelon_Form_Inverse
  Echelon_Form.Examples_Echelon_Form_Abstract
  "HOL-Computational_Algebra.Euclidean_Algorithm"
begin

subsection\<open>Some previous properties\<close>

subsubsection\<open>Rings\<close>

subclass (in bezout_ring_div) euclidean_ring
proof
qed

subsubsection\<open>Polynomials\<close>

lemma coeff_dvd_poly: "[:coeff a (degree a):] dvd (a::'a::{field} poly)"
proof (cases "a=0")
  case True
  thus ?thesis unfolding dvd_def by simp
next
  case False
  thus ?thesis
    by (intro dvd_trans[OF is_unit_triv one_dvd]) simp
qed

lemma poly_dvd_antisym2:
  fixes p q :: "'a::field poly"
  assumes dvd1: "p dvd q" and dvd2: "q dvd p" 
  shows "p div [:coeff p (degree p):] = q div [:coeff q (degree q):]"
proof (cases "p = 0")
  case True 
  thus ?thesis
    by (metis dvd1 dvd_0_left_iff)
next
  case False have q: "q \<noteq> 0" 
    by (metis False dvd2 dvd_0_left_iff)
  have degree: "degree p = degree q"
    using \<open>p dvd q\<close> \<open>q dvd p\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>
    by (intro order_antisym dvd_imp_degree_le)
  from \<open>p dvd q\<close> obtain a where a: "q = p * a" ..
  with \<open>q \<noteq> 0\<close> have "a \<noteq> 0" by auto
  with degree a \<open>p \<noteq> 0\<close> have "degree a = 0"
    by (simp add: degree_mult_eq)
  with a show ?thesis
  proof (cases a, auto split: if_splits, metis \<open>a \<noteq> 0\<close>)
    fix aa :: 'a
    assume a1: "aa \<noteq> 0"
    assume "q = smult aa p"
    have "[:aa * coeff p (degree p):] dvd smult aa p"
      using a1 by (metis (no_types) coeff_dvd_poly coeff_smult degree_smult_eq)
    thus "p div [:coeff p (degree p):] = smult aa p div [:aa * coeff p (degree p):]"
      using a1 by (simp add: False coeff_dvd_poly dvd_div_div_eq_mult)
  qed
qed

subsubsection\<open>Units\<close>

lemma unit_prod:
  assumes "finite S"
  shows "is_unit (prod (\<lambda>i. U $ i $ i) S) = (\<forall>i\<in>S. is_unit (U $ i $ i))"
  using assms 
proof (induct)
  case empty
  thus ?case by auto
next
  case (insert a S)
  have "prod (\<lambda>i. U $ i $ i) (insert a S) = U $ a $ a * prod (\<lambda>i. U $ i $ i) S"
    by (simp add: insert.hyps(2))
  thus ?case using is_unit_mult_iff insert.hyps by auto
qed

subsubsection\<open>Upper triangular matrices\<close>

lemma is_unit_diagonal: 
  fixes U::"'a::{comm_ring_1, algebraic_semidom}^'n::{finite, wellorder}^'n::{finite, wellorder}"
  assumes U: "upper_triangular U"
  and det_U: "is_unit (det U)"
  shows "\<forall>i. is_unit (U $ i $ i)"
proof -
  have "is_unit (prod (\<lambda>i. U $ i $ i) UNIV)" 
    using det_U  det_upperdiagonal[of U] U 
    unfolding upper_triangular_def by auto
  hence "\<forall>i\<in>UNIV. is_unit (U $ i $ i)" using unit_prod[of UNIV U] by simp
  thus ?thesis by simp
qed

lemma upper_triangular_mult:
  fixes A::"'a::{semiring_1}^'n::{mod_type}^'n::{mod_type}"
  assumes A: "upper_triangular A"
  and B: "upper_triangular B"
  shows "upper_triangular (A**B)"
proof (unfold upper_triangular_def matrix_matrix_mult_def, vector, auto)
  fix i j::'n
  assume ji: "j<i"
  show "(\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ j) = 0" 
  proof (rule sum.neutral, clarify)
    fix x
    show "A $ i $ x * B $ x $ j = 0"
    proof (cases "x<i")
      case True
      thus ?thesis using A unfolding upper_triangular_def by auto
    next
      case False
      hence "x>j" using ji by auto
      thus ?thesis using A B ji unfolding upper_triangular_def by auto
    qed
  qed
qed

lemma upper_triangular_adjugate:
  fixes A::"(('a::comm_ring_1,'n::{wellorder, finite}) vec, 'n) vec"
  assumes A: "upper_triangular A"
  shows "upper_triangular (adjugate A)"
proof (auto simp add: cofactor_def upper_triangular_def adjugate_def transpose_def cofactorM_def)
  fix i j::'n assume ji: "j < i" with A show "det (minorM A j i) = 0"
    unfolding minorM_eq det_sq_matrix_eq[symmetric] from_vec_to_vec det_minor_row
    by (subst Square_Matrix.det_upperdiagonal)
       (auto simp: upd_row.rep_eq from_vec.rep_eq row_def axis_def upper_triangular_def intro!: prod_zero)
qed


lemma upper_triangular_inverse:
  fixes A::"(('a::{euclidean_semiring,comm_ring_1},'n::{wellorder, finite}) vec, 'n) vec"
  assumes A: "upper_triangular A"
  and inv_A: "invertible A"
  shows "upper_triangular (matrix_inv A)"
  using upper_triangular_adjugate[OF A]
  unfolding invertible_imp_matrix_inv[OF inv_A] 
  unfolding matrix_scalar_mult_def upper_triangular_def by auto


lemma upper_triangular_mult_diagonal:
  fixes A::"(('a::{semiring_1},'n::{wellorder, finite}) vec, 'n) vec"
  assumes A: "upper_triangular A"
  and B: "upper_triangular B"
  shows "(A**B) $ i $ i = A $ i $ i * B $ i $ i"
proof -
  have UNIV_rw: "UNIV = (insert i (UNIV-{i}))" by auto 
  have sum_0: "(\<Sum>k\<in>UNIV-{i}. A $ i $ k * B $ k $ i) = 0"
  proof (rule sum.neutral, rule)
    fix x assume x: "x \<in> UNIV - {i}"
    show "A $ i $ x * B $ x $ i = 0" 
    proof (cases "x<i")
      case True
      thus ?thesis using A unfolding upper_triangular_def by auto
    next
      case False
      hence "x>i" using x by auto
      thus ?thesis using B unfolding upper_triangular_def by auto
    qed 
  qed
  have "(A**B) $ i $ i = (\<Sum>k\<in>UNIV. A $ i $ k * B $ k $ i)"
    unfolding matrix_matrix_mult_def by simp
  also have "... = (\<Sum>k\<in>(insert i (UNIV-{i})). A $ i $ k * B $ k $ i)"
    using UNIV_rw by simp
  also have "... = (A $ i $ i * B $ i $ i) + (\<Sum>k\<in>UNIV-{i}. A $ i $ k * B $ k $ i)"  
    by (rule sum.insert, simp_all)
  finally show ?thesis unfolding sum_0 by simp
qed

subsubsection\<open>More properties of mod type\<close>

lemma add_left_neutral:
  fixes a::"'n::mod_type"
  shows "(a + b = a) = (b = 0)"
  by (auto, metis add_left_cancel monoid_add_class.add.right_neutral)

lemma from_nat_1: "from_nat 1 = 1"
  unfolding from_nat_def o_def Abs'_def
  by (metis Rep_1 Rep_mod of_nat_1 one_def)

subsubsection\<open>Div and Mod\<close>

lemma dvd_minus_eq_mod:
  fixes c::"'a::unique_euclidean_ring"
  assumes "c \<noteq> 0" and "c dvd a - b" shows "a mod c = b mod c" 
  using assms dvd_div_mult_self[of c]
  by (metis add.commute diff_add_cancel mod_mult_self1)

lemma eq_mod_dvd_minus:
  fixes c::"'a::unique_euclidean_ring"
  assumes "c \<noteq> 0" and "a mod c = b mod c" 
  shows "c dvd a - b"
  using assms by (simp add: mod_eq_dvd_iff)

lemma dvd_cong_not_eq_mod:
  fixes c::"'a::unique_euclidean_ring"
  assumes "xa mod c \<noteq> xb" and "c dvd xa mod c - xb" and "c \<noteq> 0"
  shows "xb mod c \<noteq> xb"
  using assms
  by (metis (no_types, lifting) diff_add_cancel dvdE mod_mod_trivial  mod_mult_self4)

lemma diff_mod_cong_0:
  fixes c::"'a::unique_euclidean_ring"
  assumes "xa mod c \<noteq> xb mod c" and" c dvd xa mod c - xb mod c" shows "c = 0"
  using assms dvd_cong_not_eq_mod mod_mod_trivial by blast

lemma cong_diff_mod:
  fixes c::"'a::unique_euclidean_ring"
  assumes "xa \<noteq> xb" and "c dvd xa - xb" and "xa = xa mod c" shows "xb \<noteq> xb mod c"
  by (metis assms diff_eq_diff_eq diff_numeral_special(12) dvd_0_left dvd_minus_eq_mod)

lemma exists_k_mod:
  fixes c::"'a::unique_euclidean_ring"
  shows "\<exists>k. a mod c = a + k * c"
  by (metis add.commute diff_add_cancel diff_minus_eq_add
      mult_div_mod_eq mult.commute mult_minus_left)

subsection\<open>Units, associated and congruent relations\<close>

context semiring_1
begin

definition "Units = {x::'a. (\<exists>k. 1 = x * k)}"

end


context ring_1
begin

definition cong::"'a\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>bool"
  where "cong a c b = (\<exists>k. (a - c) = b * k)" 

lemma cong_eq: "cong a c b = (b dvd (a - c))"
  unfolding ring_1_class.cong_def dvd_def by simp

end

context normalization_semidom
begin

lemma Units_eq: "Units = {x. x dvd 1}" unfolding Units_def dvd_def ..

lemma normalize_Units: "x \<in> Units \<Longrightarrow> normalize x = 1"
  by (intro is_unit_normalize) (simp_all add: Units_eq)

lemma associated_eq: "(normalize a = normalize b) \<longleftrightarrow> (\<exists>u\<in>Units. a = u*b)" 
proof
  assume A: "normalize a = normalize b"
  show "\<exists>u\<in>Units. a = u*b"
  proof (cases "a = 0 \<or> b = 0")
    case False
    from A have "a = (unit_factor a div unit_factor b) * b"
      by (metis mult_not_zero normalize_0 normalize_mult_unit_factor mult.left_commute 
           unit_div_mult_self unit_factor_is_unit)
    moreover from False have "unit_factor a div unit_factor b \<in> Units"
      by (simp add: Units_eq unit_div)
    ultimately show ?thesis by blast
  next
    case True
    with A normalize_eq_0_iff[of a] normalize_eq_0_iff[of b] have "a = 0" "b = 0" by auto
    thus ?thesis by (auto intro!: exI[of _ 1] simp: Units_def)
  qed
qed (auto simp: normalize_Units normalize_mult)

end

context unique_euclidean_ring
begin

definition "associated_rel = {(a,b). normalize a = normalize b}"

lemma equiv_associated: 
  shows "equiv UNIV associated_rel"
  unfolding associated_rel_def equiv_def refl_on_def sym_def trans_def by simp

definition "congruent_rel b = {(a,c). cong a c b}"

lemma relf_congruent_rel: "refl (congruent_rel b)"
  unfolding refl_on_def congruent_rel_def 
  unfolding cong_def 
  by (auto, metis mult_zero_right)

lemma sym_congruent_rel: "sym (congruent_rel b)"
  unfolding sym_def congruent_rel_def unfolding cong_def
  by (auto, metis add_commute add_minus_cancel diff_conv_add_uminus 
    minus_mult_commute mult.left_commute mult_1_left)

lemma trans_congruent_rel: "trans (congruent_rel b)"
  unfolding trans_def congruent_rel_def unfolding cong_def
  by (auto, metis add_assoc diff_add_cancel 
    diff_conv_add_uminus distrib_left)

lemma equiv_congruent: "equiv UNIV (congruent_rel b)"
  unfolding equiv_def 
  using relf_congruent_rel sym_congruent_rel trans_congruent_rel by auto

end

subsection\<open>Associates and residues functions\<close>

context normalization_semidom
begin

definition ass_function :: "('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "ass_function f 
  = ((\<forall>a. normalize a = normalize (f a)) \<and> pairwise (\<lambda>a b. normalize a \<noteq> normalize b) (range f))"

definition "Complete_set_non_associates S 
  = (\<exists>f. ass_function f \<and> f`UNIV = S \<and> (pairwise (\<lambda>a b. normalize a \<noteq> normalize b) S))"

end

context ring_1
begin

definition res_function :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "res_function f = (\<forall>c. (\<forall>a b. cong a b c \<longleftrightarrow> f c a = f c b) 
  \<and> pairwise (\<lambda>a b. \<not> cong a b c) (range (f c))
  \<and> (\<forall>a. \<exists>k. f c a = a + k*c))"

definition "Complete_set_residues g 
  = (\<exists>f. res_function f \<and> (\<forall>c. (pairwise (\<lambda>a b. \<not> cong a b c) (f c`UNIV)) \<and> g c = f c`UNIV))"
end

lemma ass_function_Complete_set_non_associates:
  assumes f: "ass_function f"
  shows "Complete_set_non_associates (f`UNIV)"
  unfolding Complete_set_non_associates_def ass_function_def 
  apply (rule exI[of _ f])
  using f unfolding ass_function_def unfolding pairwise_def by fast

lemma in_Ass_not_associated:
  assumes Ass_S: "Complete_set_non_associates S" 
  and x: "x\<in>S" and y: "y\<in>S" and x_not_y: "x\<noteq>y" 
  shows "normalize x \<noteq> normalize y"
  using assms unfolding Complete_set_non_associates_def pairwise_def by auto


lemma ass_function_0:
  assumes r: "ass_function ass"
  shows "(ass x = 0) = (x = 0)"
  using assms unfolding ass_function_def pairwise_def
  by (metis normalize_eq_0_iff)

lemma ass_function_0':
  assumes r: "ass_function ass"
  shows "(ass x div x = 0) = (x=0)"
  using assms unfolding ass_function_def pairwise_def
  by (metis ass_function_0 associatedD2 div_self div_by_0 dvd_normalize_div
            normalize_0 normalize_1 one_neq_zero r)


lemma res_function_Complete_set_residues:
  assumes f: "res_function f"
  shows "Complete_set_residues (\<lambda>c. (f c)`UNIV)" 
  unfolding Complete_set_residues_def
  apply (rule exI[of _ f]) using f unfolding res_function_def by blast

lemma in_Res_not_congruent:
  assumes res_g: "Complete_set_residues g" 
  and x: "x \<in> g b" and y: "y \<in> g b" and x_not_y: "x\<noteq>y" 
  shows "\<not> cong x y b" 
  using assms
  unfolding Complete_set_residues_def 
  unfolding pairwise_def
  by auto


subsubsection\<open>Concrete instances in Euclidean rings\<close>

definition "ass_function_euclidean (p::'a::{normalization_euclidean_semiring, euclidean_ring}) = normalize p"
definition "res_function_euclidean b (n::'a::{euclidean_ring}) = (if b = 0 then n else (n mod b))"

lemma ass_function_euclidean: "ass_function ass_function_euclidean"
  unfolding ass_function_def image_def ass_function_euclidean_def pairwise_def by auto

lemma res_function_euclidean: 
  "res_function (res_function_euclidean :: 'a :: unique_euclidean_ring \<Rightarrow> _)"
  by (auto simp add: pairwise_def res_function_def cong_eq image_def res_function_euclidean_def dvd_minus_eq_mod)
    (auto simp add: dvd_cong_not_eq_mod eq_mod_dvd_minus diff_mod_cong_0 cong_diff_mod exists_k_mod)

subsubsection\<open>Concrete case of the integer ring\<close>

definition "ass_function_int (n::int) = abs n"

lemma ass_function_int: "ass_function_int = ass_function_euclidean"
  by (unfold ass_function_int_def ass_function_euclidean_def) simp

lemma ass_function_int_UNIV: "(ass_function_int` UNIV) = {x. x\<ge>0}"
  unfolding ass_function_int_def image_def
  by (auto, metis abs_of_nonneg)


subsection\<open>Definition of Hermite Normal Form\<close>

text\<open>
It is worth noting that there is not a single definition of Hermite Normal Form
in the literature. For instance, some authors restrict their definitions to the case 
of square nonsingular matrices. Other authors just work with integer matrices.
Furthermore, given a matrix $A$ its Hermite Normal Form $H$ can be defined to be upper triangular 
or lower triangular. In addition, the transformation from $A$ to $H$ can be made by means of 
elementary row operations or elementary column operations. In our case, we will work as general as 
possible, so our input will be any matrix (including nonsquare ones). The output will be an upper
triangular matrix obtained by means of elementary row operations.

Hence, given a complete set of nonassociates and a complete set of residues, 
$H$ is said to be in Hermite Normal Form if:

\begin{enumerate}
\item H is in Echelon Form
\item The first nonzero element of a nonzero row belongs to the complete set of nonassociates
\item Let $h$ be the first nonzero element of a nonzero row. Then each element above $h$
  belongs to the corresponding complete set of residues of $h$
\end{enumerate}

A matrix $H$ is the Hermite Normal Form of a matrix $A$ if:
\begin{enumerate}
\item There exists an invertible matrix $P$ such that $A = PH$
\item H is in Hermite Normal Form
\end{enumerate}

The Hermite Normal Form is usually applied to integer matrices. As we have already said, there is no
one single definition of it, so some authors impose different conditions. In the particular
case of integer matrices, leading coefficients (the first nonzero element of a nonzero row)
are usually required to be positive, but it is also possible to impose them to be negative 
since we would only have to multiply by $-1$.

In the case of the elements $h_{ik}$ above a leading coefficient $h_{ij}$, 
some authors demand $0 \leq h_{ik} < h_{ij}$, 
other ones impose the conditions $h_{ik} \leq 0$ and \mbox{$\mid h_{ik} \mid < h_{ij}$}, and other ones
$- \frac{h_{ij}}{2} < h_{ik} \leq \frac{h_{ij}}{2}$. More different options are also possible.

All the possibilities can be represented selecting a complete set of nonassociates and a 
complete set of residues. The algorithm to compute the Hermite Normal Form will be 
parameterised by functions which obtain the appropriate leading coefficient and the 
suitable elements above them. We can execute the algorithm with different functions to get 
exactly which Hermite Normal Form we want. Once we fix such a complete set of nonassociates 
and the corresponding complete set of residues, the Hermite Normal Form is unique.
\<close>

subsubsection\<open>Echelon form up to row k\<close>

text\<open>We present the definition of echelon form up to a row k (not included).\<close>

definition "echelon_form_upt_row A k =
  (
    (\<forall>i. to_nat i < k \<and> is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> to_nat j < k \<and> \<not> is_zero_row j A)) \<and>  
    (\<forall>i j. i < j \<and> to_nat j <  k \<and> \<not> is_zero_row i A \<and> \<not> is_zero_row j A \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0))
  )"

lemma echelon_form_upt_row_condition1_explicit:
  assumes "echelon_form_upt_row A k"
  and "to_nat i < k" and "is_zero_row i A"
  shows "\<not> (\<exists>j. j>i \<and> to_nat j < k \<and> \<not> is_zero_row j A)" 
  using assms unfolding echelon_form_upt_row_def by blast

lemma echelon_form_upt_row_condition1_explicit':
  assumes "echelon_form_upt_row A k"
  and "to_nat i < k" and "is_zero_row i A" and "i\<le>j" and "to_nat j < k"
  shows "is_zero_row j A" 
proof (cases "i=j")
    case True thus ?thesis using assms by auto
next
    case False thus ?thesis using assms unfolding echelon_form_upt_row_def by simp
qed

lemma echelon_form_upt_row_condition1_explicit_neg:
  assumes "echelon_form_upt_row A k"
  and iA: "\<not> is_zero_row i A" and ia_i: "ia < i"
  and i: "to_nat i < k"
  shows "\<not> is_zero_row ia A"
proof -
  have "to_nat ia < k" by (metis ia_i i less_trans to_nat_mono)
  thus ?thesis using assms unfolding echelon_form_upt_row_def by blast
qed

lemma echelon_form_upt_row_condition2_explicit:
  assumes "echelon_form_upt_row A k"
  and "ia < j" and "to_nat j < k" and "\<not> is_zero_row ia A" and "\<not> is_zero_row j A"
  shows "(LEAST n. A $ ia $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)" 
  using assms unfolding echelon_form_upt_row_def by auto


lemma echelon_form_upt_row_intro:
  assumes"(\<forall>i. to_nat i < k \<and> is_zero_row i A \<longrightarrow> \<not> (\<exists>j. i<j \<and> to_nat j < k \<and> \<not> is_zero_row j A))"
  and "(\<forall>i j. i < j \<and> to_nat j <  k \<and> \<not> is_zero_row i A \<and> \<not> is_zero_row j A \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0))"
  shows "echelon_form_upt_row A k"
  using assms unfolding echelon_form_upt_row_def by simp

lemma echelon_form_echelon_form_upt_row: "echelon_form A = echelon_form_upt_row A (nrows A)"
  by (simp add: to_nat_less_card echelon_form_def echelon_form_upt_row_def ncols_def nrows_def 
      echelon_form_upt_k_def is_zero_row_upt_k_def is_zero_row_def)

subsubsection\<open>Hermite Normal Form up to row k\<close>

text\<open>Predicate to check if a matrix is in Hermite Normal form up to row k (not included).\<close>

definition "Hermite_upt_row A k associates residues = 
  (
    Complete_set_non_associates associates \<and>
    Complete_set_residues residues \<and>
    echelon_form_upt_row A k \<and>
    (\<forall>i. to_nat i < k \<and> \<not> is_zero_row i A \<longrightarrow> A $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<in> associates) \<and>
    (\<forall>i. to_nat i < k \<and> \<not> is_zero_row i A \<longrightarrow> (\<forall>j<i. A $ j $ (LEAST n. A $ i $ n \<noteq> 0) \<in> residues (A $ i $ (LEAST n. A $ i $ n \<noteq> 0))))
  )"

text\<open>The definition of Hermite Normal Form is now introduced:\<close>

definition Hermite::"'a::{bezout_ring_div,normalization_semidom} set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 
   (('a, 'b::{mod_type}) vec, 'c::{mod_type}) vec \<Rightarrow> bool"
where  "Hermite associates residues A = (
  Complete_set_non_associates associates 
  \<and> (Complete_set_residues residues) 
  \<and> echelon_form A 
  \<and> (\<forall>i. \<not> is_zero_row i A \<longrightarrow> A $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<in> associates) 
  \<and> (\<forall>i. \<not> is_zero_row i A \<longrightarrow> (\<forall>j. j<i \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) \<in> residues (A $ i $ (LEAST n. A $ i $ n \<noteq> 0))))
  )"

lemma Hermite_Hermite_upt_row: "Hermite ass res A = Hermite_upt_row A (nrows A) ass res"
  by (simp add: Hermite_def Hermite_upt_row_def to_nat_less_card is_zero_row_def 
    nrows_def ncols_def echelon_form_echelon_form_upt_row)

lemma Hermite_intro:
  assumes "Complete_set_non_associates associates"
  and "Complete_set_residues residues"
  and "echelon_form A "
  and "(\<forall>i. \<not> is_zero_row i A \<longrightarrow> A $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<in> associates)"
  and "(\<forall>i. \<not> is_zero_row i A \<longrightarrow> (\<forall>j. j<i \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) \<in> residues (A $ i $ (LEAST n. A $ i $ n \<noteq> 0))))"
  shows "Hermite associates residues A"
  using assms unfolding Hermite_def by simp

subsection\<open>Definition of an algorithm to compute the Hermite Normal Form\<close>

text\<open>
The algorithm is parameterised by three functions:

\begin{itemize}
  \item The function that computes de B\'ezout identity (necessary to compute the echelon form).
  \item The function that given an element, it returns its representative element in the associated equivalent class,
        which will be an element in the complete set of nonassociates.
  \item The function that given two elements $a$ and $b$, it returns its representative 
        element in the congruent equivalent class of $b$, which will be an element in the complete set of residues of $b$.
\end{itemize}


\<close>

primrec Hermite_reduce_above :: "'a::unique_euclidean_ring^'cols::mod_type^'rows::mod_type\<Rightarrow>nat
    \<Rightarrow>'rows\<Rightarrow>'cols\<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a^'cols::mod_type^'rows::mod_type"
where "Hermite_reduce_above A 0 i j res  = A"
    | "Hermite_reduce_above A (Suc n) i j res  = (let i'=((from_nat n)::'rows); 
    Aij = A $ i $ j;
    Ai'j = A $ i' $ j
    in 
    Hermite_reduce_above (row_add A  i' i (((res Aij (Ai'j)) - (Ai'j)) div Aij)) n i j res)"

definition "Hermite_of_row_i ass res A i = (
  if is_zero_row i A 
     then A 
  else
    let j = (LEAST n. A $ i $ n \<noteq> 0); Aij= (A $ i $ j);
    A' = mult_row A i ((ass Aij) div Aij)
    in Hermite_reduce_above A' (to_nat i) i j res)"

definition "Hermite_of_upt_row_i A i ass res = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<i])"

definition "Hermite_of A ass res bezout = 
  (let A'= echelon_form_of A bezout in Hermite_of_upt_row_i A' (nrows A) ass res)"

subsection\<open>Proving the correctness of the algorithm\<close>

subsubsection\<open>The proof\<close>

lemma Hermite_reduce_above_preserves:
  assumes n: "n\<le>to_nat a"
  shows "(Hermite_reduce_above A n i j res) $ a $ b = A $ a $ b" 
  using n
proof (induct n arbitrary: A)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case by (auto simp add: Let_def row_add_def)
  (metis Suc_le_eq from_nat_mono from_nat_to_nat_id less_irrefl to_nat_less_card)
qed


lemma Hermite_reduce_above_works:
  assumes n: "n \<le> to_nat i" and a: "to_nat a < n"
  shows "(Hermite_reduce_above A n i j res) $ a $ b 
         = row_add A a i ((res (A$i$j) (A$a$j) - (A$a$j)) div (A$i$j)) $ a $ b"
using n a
proof (induct n arbitrary: A)
  case 0 thus ?case by (simp add: row_add_def)
next
  case (Suc n)
  define A' where "A' = row_add A (from_nat n) i
    ((res (A $ i $ j) (A $ from_nat n $ j) - A $ from_nat n $ j) div A $ i $ j)"
  have n: "n < nrows A"
    unfolding nrows_def by (metis Suc.prems(1) Suc_le_eq less_trans to_nat_less_card)
  show ?case
  proof (cases "to_nat a = n")
    case False
    have a_less_n: "to_nat a < n" by (metis False Suc.prems(2) less_antisym)
    have "Hermite_reduce_above A (Suc n) i j res $ a $ b = Hermite_reduce_above A' n i j res $ a $ b "
      by (simp add: Let_def A'_def)
    also have "... = row_add A' a i ((res (A' $ i $ j) (A' $ a $ j) - A' $ a $ j) div A' $ i $ j) $ a $ b"
      by (rule Suc.hyps[OF _  a_less_n], simp add: Suc.prems(1) Suc_leD)
    also have "... = row_add A a i ((res (A $ i $ j) (A $ a $ j) - A $ a $ j) div A $ i $ j) $ a $ b"
      unfolding row_add_def A'_def
      using a_less_n Suc.prems n to_nat_from_nat_id[OF n[unfolded nrows_def]] 
      by auto
    finally show ?thesis .
  next
    case True
    hence a_eq_fn_n: "a = from_nat n" by auto
    have "Hermite_reduce_above A (Suc n) i j res $ a $ b = Hermite_reduce_above A' n i j res $ a $ b "
      by (simp add: Let_def A'_def)
    also have "... = A' $ a $ b" 
      by (rule Hermite_reduce_above_preserves, simp add: True)
    finally show ?thesis unfolding A'_def a_eq_fn_n .
  qed
qed

lemma Hermite_of_row_preserves_below:
assumes i_a: "i<a"
shows "(Hermite_of_row_i ass res A i) $ a $ b = A $ a $ b"  
proof (auto simp add: Hermite_of_row_i_def Let_def)
  let ?M="(mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
  let ?H="Hermite_reduce_above ?M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  have "?H $ a $ b = ?M $ a $ b" 
    by (rule Hermite_reduce_above_preserves) 
     (metis i_a not_le not_less_iff_gr_or_eq to_nat_mono')
  also have "... = A $ a $ b" unfolding mult_row_def using i_a by fastforce
  finally show "?H $ a $ b = A $ a $ b" .
qed

lemma Hermite_of_row_preserves_previous_cols:
assumes b: "b<(LEAST n. A $ i $ n \<noteq> 0)"
and not_zero_i_A: "\<not> is_zero_row i A"
and e: "echelon_form A"
shows "(Hermite_of_row_i ass res A i) $ a $ b = A $ a $ b"  
proof (auto simp add: Hermite_of_row_i_def Let_def)
  let ?n="(LEAST n. A $ i $ n \<noteq> 0)"
  let ?M="(mult_row A i (ass (A $ i $ ?n) div A $ i $ ?n))"
  let ?H="Hermite_reduce_above ?M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  have Aib: " A $ i $ b = 0" by (metis (mono_tags) b not_less_Least)
  show "?H $ a $ b = A $ a $ b"
  proof (cases "a\<ge>i")
    case True
    have "?H $ a $ b = ?M $ a $ b" 
      by (rule Hermite_reduce_above_preserves) (metis True to_nat_mono')
    also have "... = A $ a $ b" using Aib unfolding mult_row_def by auto
    finally show ?thesis .
  next
    let ?R="row_add ?M a i ((res (?M $ i $ ?n) (?M $ a $ ?n) - ?M $ a $ ?n) div ?M $ i $ ?n)"
    case False
    hence ia: "i>a" by simp
    have "?H $ a $ b = ?R $ a $ b" by (rule Hermite_reduce_above_works, auto simp add: ia to_nat_mono)
    also have "... = A $ a $ b" using ia Aib unfolding row_add_def mult_row_def by auto
    finally show ?thesis .
  qed
qed

lemma echelon_form_Hermite_of_condition1:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes e: "echelon_form A"
  and a: "ass_function ass"
  and not_zero_iA: "\<not> is_zero_row i A"
  and zero_ia_H: "is_zero_row ia H"
  and ia_j: "ia < j"
  shows "is_zero_row j H"
proof (cases "is_zero_row ia A")
  case True
  have zero_jA: "is_zero_row j A" by (metis True e echelon_form_condition1 ia_j)
  have ij: "i<j" by (metis e echelon_form_condition1 neq_iff not_zero_iA zero_jA)
  show ?thesis
  proof (auto simp add: is_zero_row_def is_zero_row_upt_k_def ncols_def)
    fix a
    have "H $ j $ a = M $ j $ a" 
      unfolding H 
      by (rule Hermite_reduce_above_preserves) (metis dual_order.strict_iff_order ij to_nat_mono')
    also have "... = A $ j $ a" unfolding M mult_row_def using ij by auto
    also have "... = 0" using zero_jA by (simp add: is_zero_row_def is_zero_row_upt_k_def ncols_def)
    finally show "H $ j $ a = 0" .
  qed
next
  case False note not_zero_ia_A=False
  let ?n="(LEAST n. A $ ia $ n \<noteq> 0)"
  have A_ia_n: "A $ ia $ ?n \<noteq> 0" 
    by (metis (mono_tags, lifting) LeastI is_zero_row_def is_zero_row_upt_k_def not_zero_ia_A)
  show ?thesis
  proof (cases "i \<le> ia")
    case True    
    have "H $ ia $ ?n = M $ ia $ ?n" 
      unfolding H by (rule Hermite_reduce_above_preserves, simp add: True to_nat_mono')
    also have "... \<noteq> 0" unfolding M mult_row_def using A_ia_n ass_function_0'[OF a] by auto
    finally have "H $ ia $ ?n \<noteq> 0" .
    hence not_zero_ia_H: "\<not> is_zero_row ia H"
      unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
    thus ?thesis using zero_ia_H by contradiction
  next
    case False
    let ?m="(LEAST m. A $ i $ m \<noteq> 0)"
    let ?R="row_add M ia i ((res (M $ i $ ?m) (M $ ia $ ?m) - M $ ia $ ?m) div M $ i $ ?m)"
    have ia_less_i: "ia<i" by (metis False not_less)
    have nm: "?n<?m" by (rule echelon_form_condition2_explicit[OF e ia_less_i not_zero_ia_A not_zero_iA])
    have A_im: "A $ i $ ?n = 0" by (metis (full_types) nm not_less_Least)
    have "H $ ia $ ?n = ?R $ ia $ ?n"
      unfolding H
      by (rule Hermite_reduce_above_works, auto simp add: ia_less_i to_nat_mono)
    also have "... \<noteq> 0"
      using ia_less_i A_im A_ia_n unfolding row_add_def M mult_row_def by auto
    finally have "H $ ia $ ?n \<noteq> 0" .
    hence not_zero_ia_H: "\<not> is_zero_row ia H"
      unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
    thus ?thesis using zero_ia_H by contradiction
  qed
qed

lemma row_zero_A_imp_row_zero_H:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes e: "echelon_form A"
  and not_zero_iA: "\<not> is_zero_row i A"
  and zero_j_A: "is_zero_row j A"
  shows "is_zero_row j H"
proof (auto simp add: is_zero_row_def is_zero_row_upt_k_def ncols_def)
  fix a 
  have A_ja: "A $ j $ a = 0" 
    using zero_j_A 
    by (simp add: is_zero_row_def is_zero_row_upt_k_def ncols_def)
  show "H $ j $ a = 0"
  proof (cases "i\<le>j")
    case True
    have "H $ j $ a = M $ j $ a"
      unfolding H by (rule Hermite_reduce_above_preserves, simp add: True to_nat_mono')
    also have "... = 0" unfolding M mult_row_def using True A_ja by auto 
    finally show ?thesis .
  next
    let ?n="(LEAST n. A $ i $ n \<noteq> 0)"
    let ?R="row_add M j i ((res (M $ i $ ?n) (M $ j $ ?n) - M $ j $ ?n) div M $ i $ ?n)"
    case False
    hence ji: "j<i" by simp
    have "H $ j $ a = ?R $ j $ a" 
      unfolding H by (rule Hermite_reduce_above_works, auto simp add: ji to_nat_mono)
    also have "... = 0" 
      using ji A_ja not_zero_iA e echelon_form_condition1 zero_j_A 
      unfolding row_add_def M mult_row_def by blast
    finally show ?thesis .
  qed
qed



lemma Hermite_reduce_above_Least_eq_le:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes i_ia: "i<ia"
  and not_zero_ia_H: "\<not> is_zero_row ia H"
  shows "(LEAST n. A $ ia $ n \<noteq> 0) = (LEAST n. H $ ia $ n \<noteq> 0)"
proof (rule Least_equality)
  let ?n="(LEAST n. H $ ia $ n \<noteq> 0)"
  have "A $ ia $ ?n = M $ ia $ ?n" unfolding M mult_row_def using i_ia by auto
  also have "... = H $ ia $ ?n "
    unfolding H
    by (rule Hermite_reduce_above_preserves[symmetric]) 
  (metis i_ia dual_order.strict_iff_order to_nat_mono')
  also have "... \<noteq> 0"  by (metis (mono_tags) LeastI is_zero_row_def' not_zero_ia_H)
  finally show "A $ ia $ (LEAST n. H $ ia $ n \<noteq> 0) \<noteq> 0" .
next
  fix y
  assume A_ia_y: "A $ ia $ y \<noteq> 0" 
  have "H $ ia $ y = M $ ia $ y" unfolding H
    by (rule Hermite_reduce_above_preserves) 
  (metis i_ia dual_order.strict_iff_order to_nat_mono')
  also have "... \<noteq> 0" unfolding M mult_row_def using i_ia A_ia_y by auto
  finally show "(LEAST n. H $ ia $ n \<noteq> 0) \<le> y" by (rule Least_le)
qed

lemma Hermite_reduce_above_Least_eq:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes a: "ass_function ass"
  and not_zero_iA: "\<not> is_zero_row i A"
  shows "(LEAST n. A $ i $ n \<noteq> 0) = (LEAST n. H $ i $ n \<noteq> 0)"
proof (rule Least_equality[symmetric])
  let ?n="(LEAST n. A $ i $ n \<noteq> 0)"
  have Ain: "A $ i $ ?n \<noteq> 0"
    by (metis (mono_tags, lifting) LeastI is_zero_row_def' not_zero_iA)
  have "H $ i $ ?n = M $ i $ ?n" 
    unfolding H 
    by (rule Hermite_reduce_above_preserves, simp)            
  also have "... \<noteq> 0" unfolding M mult_row_def by (auto simp add: Ain ass_function_0'[OF a])
  finally show "H $ i $ ?n \<noteq> 0" .
  fix y assume H_iy: "H $ i $ y \<noteq> 0"            
  show "(LEAST n. A $ i $ n \<noteq> 0) \<le> y" 
  proof (rule Least_le, rule ccontr, simp)
    assume Aiy: "A $ i $ y = 0"
    have "H $ i $ y = M $ i $ y" 
      unfolding H 
      by (rule Hermite_reduce_above_preserves, simp)
    also have "... = (ass (A $ i $ ?n) div A $ i $ ?n) * A $ i $ y" 
      unfolding M mult_row_def by auto
    also have "... = 0" unfolding Aiy by simp
    finally show False using H_iy by contradiction
  qed
qed


lemma Hermite_reduce_above_Least_eq_ge:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes e: "echelon_form A"
  and not_zero_iA: "\<not> is_zero_row i A"
  and not_zero_ia_A: "\<not> is_zero_row ia A"
  and not_zero_ia_H: "\<not> is_zero_row ia H"
  and ia_less_i: "ia < i"
  shows "(LEAST n. H $ ia $ n \<noteq> 0) = (LEAST n. A $ ia $ n \<noteq> 0)"
proof -
  let ?least_H = "(LEAST n. H $ ia $ n \<noteq> 0)"
  let ?least_A = "(LEAST n. A $ ia $ n \<noteq> 0)"
  let ?n= "(LEAST n. A $ i $ n \<noteq> 0)"
  let ?Ain ="A $ i $ ?n"
  let ?R="row_add M ia i ((res (M $ i $ ?n) (M $ ia $ ?n) - M $ ia $ ?n) div M $ i $ ?n)"
  have A_ia_least_A: "A $ ia $ ?least_A \<noteq> 0" 
    by (metis (mono_tags, lifting) LeastI is_zero_row_def' not_zero_ia_A)
  have H_ia_least_H: "H $ ia $ ?least_H \<noteq> 0"
    by (metis (mono_tags, lifting) LeastI is_zero_row_def' not_zero_ia_H)
  have A_i_least_ia_0: "A $ i $ (LEAST n. A $ ia $ n \<noteq> 0) = 0"
  proof -
    have "(LEAST n. A $ ia $ n \<noteq> 0) < (LEAST n. A $ i $ n \<noteq> 0)"
      using e echelon_form_condition1 echelon_form_condition2_explicit 
        ia_less_i not_zero_iA by blast
    thus ?thesis using not_less_Least by blast
  qed
  have H_ia_least_A: "H $ ia $ ?least_A \<noteq> 0"
  proof -                              
    have "H $ ia $ ?least_A = ?R $ ia $ ?least_A"
      unfolding H 
      by (rule Hermite_reduce_above_works, simp_all add: ia_less_i to_nat_mono)
    also have "... \<noteq> 0" using ia_less_i unfolding row_add_def M mult_row_def
      by (auto simp add: A_i_least_ia_0 A_ia_least_A)
    finally show ?thesis .
  qed
  hence least_H_le_least_A: "?least_H \<le> ?least_A"
    by (metis (mono_tags) not_less not_less_Least)
  have A_i_least_H: "A $ i $ ?least_H = 0"
  proof -
    have "(LEAST n. A $ ia $ n \<noteq> 0) < (LEAST n. A $ i $ n \<noteq> 0)"
      using e echelon_form_condition1 echelon_form_condition2_explicit 
        ia_less_i not_zero_iA by blast
    thus ?thesis using not_less_Least least_H_le_least_A 
      by (metis (mono_tags) dual_order.strict_trans2)
  qed
  have "A $ ia $ ?least_H \<noteq> 0"
  proof -
    have ia_not_i: "ia \<noteq> i" using ia_less_i by simp
    have "?R $ ia $ ?least_H = H $ ia $ ?least_H"
      unfolding H 
      by (rule Hermite_reduce_above_works[symmetric], simp_all add: ia_less_i to_nat_mono)
    also have "... \<noteq> 0" by (rule H_ia_least_H)
    finally have R_ia_least_H: "?R $ ia $ ?least_H \<noteq> 0" .
    hence "A $ ia $ ?least_H + (res (ass (?Ain) div ?Ain * ?Ain) 
      (A $ ia $ (LEAST n. A $ i $ n \<noteq> 0)) - A $ ia $ (LEAST n. A $ i $ n \<noteq> 0)) 
      div (ass (?Ain) div ?Ain * ?Ain) * (ass (?Ain) div ?Ain * A $ i $ ?least_H) \<noteq> 0" 
      using ia_not_i unfolding row_add_def M mult_row_def by auto
    thus ?thesis using ia_less_i A_i_least_H unfolding row_add_def M mult_row_def by auto 
  qed
  hence least_A_le_least_H: "?least_A \<le> ?least_H" by (metis (poly_guards_query) Least_le)
  show ?thesis using least_A_le_least_H least_H_le_least_A by simp
qed


lemma Hermite_reduce_above_Least:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) 
  div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes e: "echelon_form A"
  and a: "ass_function ass"
  and not_zero_iA: "\<not> is_zero_row i A"
  and not_zero_ia_A: "\<not> is_zero_row ia A"
  and not_zero_ia_H: "\<not> is_zero_row ia H"
  shows "(LEAST n. H $ ia $ n \<noteq> 0) = (LEAST n. A $ ia $ n \<noteq> 0)"
proof (cases "ia<i")
  case True
  show ?thesis 
    unfolding H M 
    by (rule Hermite_reduce_above_Least_eq_ge[OF e not_zero_iA not_zero_ia_A _ True]) 
       (metis H M not_zero_ia_H)
next
  case False
  hence i_le_ia: "i\<le>ia" by simp
  show ?thesis  
  proof (cases "ia=i")
    case True
    show ?thesis
      unfolding True H M 
      by (rule Hermite_reduce_above_Least_eq[symmetric, OF a not_zero_iA])
  next
    case False
    hence i_ia: "i<ia" using i_le_ia by simp
    show ?thesis
      unfolding H M 
      by (rule Hermite_reduce_above_Least_eq_le[symmetric, OF i_ia], metis H M not_zero_ia_H)
  qed
qed


lemma echelon_form_Hermite_of_condition2:
  fixes res ass i A
  defines M: "M \<equiv> mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  defines H: "H \<equiv> Hermite_reduce_above M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  assumes e: "echelon_form A"
  and a: "ass_function ass"
  and not_zero_iA: "\<not> is_zero_row i A"
  and ia_less_j: "ia < j"
  and not_zero_ia_H: "\<not> is_zero_row ia H"
  and not_zero_j_H: "\<not> is_zero_row j H"
  shows "(LEAST n. H $ ia $ n \<noteq> 0) < (LEAST n. H $ j $ n \<noteq> 0)"
proof -
  let ?n= "(LEAST n. A $ i $ n \<noteq> 0)"
  have Ain: "A $ i $ ?n \<noteq> 0" 
    by (metis (mono_tags) LeastI is_zero_row_def' not_zero_iA)
  have not_zero_j_A: "\<not> is_zero_row j A"
    using row_zero_A_imp_row_zero_H[OF e not_zero_iA] not_zero_j_H 
    unfolding H M by blast
  have not_zero_ia_A: "\<not> is_zero_row ia A"
    using row_zero_A_imp_row_zero_H[OF e not_zero_iA] not_zero_ia_H 
    unfolding H M by blast
  have Least_le_A: "(LEAST n. A $ ia $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)" 
    by (rule echelon_form_condition2_explicit[OF e ia_less_j not_zero_ia_A not_zero_j_A])
  show ?thesis
  proof (cases "i<ia")
    case True
    have ij: "i<j" by (metis True ia_less_j less_trans)
    have Least_A_ia_H_ia: "(LEAST n. A $ ia $ n \<noteq> 0) = (LEAST n. H $ ia $ n \<noteq> 0)"
      unfolding H M      
      by (rule Hermite_reduce_above_Least_eq_le[OF True], metis H M not_zero_ia_H)
    moreover have Least_A_ia_H_ia: "(LEAST n. A $ j $ n \<noteq> 0) = (LEAST n. H $ j $ n \<noteq> 0)"
      unfolding H M      
      by (rule Hermite_reduce_above_Least_eq_le[OF ij], metis H M not_zero_j_H)      
    ultimately show ?thesis using Least_le_A by simp
  next
    case False
    hence ia_le_i: "ia\<le>i" by simp
    show ?thesis
    proof (cases "i=ia")
      case True thus ?thesis 
        using Hermite_reduce_above_Least_eq[OF a not_zero_iA] Least_le_A 
        using Hermite_reduce_above_Least_eq_le[OF ia_less_j] 
        using not_zero_j_H unfolding H M by fastforce
    next
      case False
      hence ia_less_i: "ia<i" using ia_le_i by simp
      have Least_H_ia_A_ia: "(LEAST n. H $ ia $ n \<noteq> 0) = (LEAST n. A $ ia $ n \<noteq> 0)"
        unfolding H M 
        by (rule Hermite_reduce_above_Least_eq_ge[OF e not_zero_iA not_zero_ia_A _ ia_less_i]) 
      (metis H M not_zero_ia_H)
      show ?thesis
      proof (cases "j<i")
        case True
        have "(LEAST n. H $ j $ n \<noteq> 0) = (LEAST n. A $ j $ n \<noteq> 0)"
          unfolding H M 
          by (rule Hermite_reduce_above_Least_eq_ge[OF e not_zero_iA not_zero_j_A _ True])
        (metis H M not_zero_j_H)
        thus ?thesis by (simp add: Least_H_ia_A_ia Least_le_A)
      next
        case False
        hence j_ge_i: "j\<ge>i" by auto
        show ?thesis
        proof (cases "j=i")
          case True
          have "(LEAST n. H $ j $ n \<noteq> 0) = (LEAST n. A $ j $ n \<noteq> 0)"
            unfolding H M 
            using Hermite_reduce_above_Least_eq True a not_zero_iA by fastforce
          thus ?thesis by (simp add: Least_H_ia_A_ia Least_le_A)
        next
          case False
          hence j_sg_i: "j>i" using j_ge_i by simp 
          have "(LEAST n. H $ j $ n \<noteq> 0) = (LEAST n. A $ j $ n \<noteq> 0)"
            unfolding H M
            by (rule Hermite_reduce_above_Least_eq_le[symmetric, OF j_sg_i])
          (metis H M not_zero_j_H)
          thus ?thesis by (simp add: Least_H_ia_A_ia Least_le_A)
        qed
      qed
    qed
  qed
qed

lemma echelon_form_Hermite_of_row:
  assumes a: "ass_function ass"
  and "res_function res"
  and e: "echelon_form A"
  shows "echelon_form (Hermite_of_row_i ass res A i)"
proof (rule echelon_form_intro, auto simp add: Hermite_of_row_i_def Let_def)
  fix ia j
  assume "is_zero_row i A" and "is_zero_row ia A" and "ia < j" 
  thus "is_zero_row j A" using echelon_form_condition1[OF e] by blast
next
  fix ia j
  assume "is_zero_row i A" and "ia < j" and "\<not> is_zero_row ia A" and "\<not> is_zero_row j A" 
  thus "(LEAST n. A $ ia $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
    using echelon_form_condition2[OF e] by blast
next
  fix ia j
  assume "\<not> is_zero_row i A"
    and "is_zero_row ia (Hermite_reduce_above 
    (mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0)))
    (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res)"
    and "ia < j"
  thus "is_zero_row j (Hermite_reduce_above 
    (mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0)))
    (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res)"
    using echelon_form_Hermite_of_condition1[OF e a] by blast
next
  fix ia j
  let ?H="(Hermite_reduce_above (mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) 
    div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))) (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res)"
  assume "\<not> is_zero_row i A"
    and "ia < j"
    and "\<not> is_zero_row ia ?H"
    and "\<not> is_zero_row j ?H"
  thus "(LEAST n. ?H $ ia $ n \<noteq> 0) < (LEAST n. ?H $ j $ n \<noteq> 0)"
    using echelon_form_Hermite_of_condition2[OF e a] by blast
qed


lemma echelon_form_fold_Hermite_of_row_i:
  assumes e: "echelon_form A" and a: "ass_function ass" and r: "res_function res"
  shows "echelon_form (foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k]))"
proof (induct k)
  case 0
  thus ?case by (simp add: e) 
next
  case (Suc k)
  show ?case by (simp, rule echelon_form_Hermite_of_row[OF a r Suc.hyps])
qed


lemma echelon_form_Hermite_of_upt_row_i:
  assumes e: "echelon_form A" and a: "ass_function ass" and r: "res_function res"
  shows "echelon_form (Hermite_of_upt_row_i A k ass res)"
  unfolding Hermite_of_upt_row_i_def 
  using echelon_form_fold_Hermite_of_row_i assms by auto

lemma echelon_form_Hermite_of:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  shows "echelon_form (Hermite_of A ass res bezout)"
  unfolding Hermite_of_def Hermite_of_upt_row_i_def Let_def nrows_def
  by (rule echelon_form_fold_Hermite_of_row_i[OF echelon_form_echelon_form_of[OF b] a r])

lemma in_ass_Hermite_of_row:
  assumes a: "ass_function ass"
  and "res_function res"
  and not_zero_i_A: "\<not> is_zero_row i A"
  shows "(Hermite_of_row_i ass res A i) $ i $ (LEAST n. (Hermite_of_row_i ass res A i) $ i $ n \<noteq> 0) \<in> range ass"
unfolding Hermite_of_row_i_def using not_zero_i_A 
proof (auto simp add: Let_def)
  let ?M="(mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))) "
  let ?H="Hermite_reduce_above ?M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  let ?Ain="A $ i $ (LEAST n. A $ i $ n \<noteq> 0)"
  have Ain: "?Ain \<noteq> 0"
    by (metis (mono_tags) LeastI is_zero_row_def' not_zero_i_A)
  have least_eq: "(LEAST n. ?H $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)" 
    by (rule Hermite_reduce_above_Least_eq[OF a not_zero_i_A, symmetric])
  have "?H $ i $ (LEAST n. ?H $ i $ n \<noteq> 0) = ?M $ i $ (LEAST n. ?H $ i $ n \<noteq> 0)" 
    by (rule Hermite_reduce_above_preserves, simp)
  also have "... =  ass (?Ain) div ?Ain * ?Ain"
    unfolding mult_row_def least_eq[unfolded mult_row_def] by simp
  also have "... = ass ?Ain" 
  proof (rule dvd_div_mult_self)
    show "?Ain dvd ass ?Ain"
      using a unfolding ass_function_def by (simp add: associatedD2)
  qed
  also have "... \<in> range ass" by simp
  finally show "?H $ i $ (LEAST n. ?H $ i $ n \<noteq> 0) \<in> range ass" .
qed


lemma Hermite_of_upt_row_preserves_below:
  assumes i: "to_nat a\<ge>k"
  shows "Hermite_of_upt_row_i A k ass res $ a $ b = A $ a $ b"
  using i
proof (induct k)
  case 0
  thus ?case unfolding Hermite_of_upt_row_i_def by auto
next
  case (Suc k)
  show ?case
    by (simp add: Hermite_of_upt_row_i_def, 
      metis Hermite_of_upt_row_i_def Hermite_of_row_preserves_below Suc.hyps Suc.prems 
      Suc_leD Suc_le_eq from_nat_mono from_nat_to_nat_id to_nat_less_card)
qed


lemma not_zero_Hermite_reduce_above:
  fixes ass i A
  defines M: "M\<equiv>(mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
  assumes not_zero_a_A: "\<not> is_zero_row a A"
  and not_zero_i_A: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  and n: "n \<le> to_nat i"
  shows "\<not> is_zero_row a (Hermite_reduce_above M n i (LEAST n. A $ i $ n \<noteq> 0) res)"
proof -
  let ?H = "(Hermite_reduce_above M n i (LEAST n. A $ i $ n \<noteq> 0) res)"
  let ?n="LEAST n. A $ a $ n \<noteq> 0"
  let ?m="LEAST n. A $ i $ n \<noteq> 0"
  have Aan: "A $ a $ ?n \<noteq> 0"
    by (metis (mono_tags) LeastI not_zero_a_A is_zero_row_def')
  have Aim: "A $ i $ ?m \<noteq> 0"
    by (metis (mono_tags) LeastI not_zero_i_A is_zero_row_def')
  show ?thesis
  proof (cases "n\<le>to_nat a")
    case True
    have "?H $ a $ ?n = M $ a $ ?n" 
      by (metis Hermite_reduce_above_preserves True)
    also have "... \<noteq> 0" unfolding M mult_row_def using ass_function_0'[OF a] Aan by auto
    finally show ?thesis unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  next
    let ?R="row_add M a i
      ((res (M $ i $ ?m) (M $ a $ ?m) - M $ a $ ?m) div M $ i $ ?m)"
    case False
    hence a_n: "to_nat a < n" by simp  
    have ai: "a < i" 
      by (metis False dual_order.trans n nat_less_le not_less_iff_gr_or_eq to_nat_mono)
    have "(LEAST n. A $ a $ n \<noteq> 0) < ?m" 
      by (rule echelon_form_condition2_explicit[OF e ai not_zero_a_A not_zero_i_A])
    hence Ain: "A $ i $ (LEAST n. A $ a $ n \<noteq> 0) = 0"
      by (metis (full_types) not_less_Least)
    have a_not_i: "a \<noteq> i" by (metis False n)
    have "?H $ a $ ?n = ?R $ a $ ?n" 
      by (rule Hermite_reduce_above_works[OF n a_n])
    also have "... \<noteq> 0" using a_not_i Aan Ain unfolding row_add_def M mult_row_def by auto
    finally show ?thesis unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  qed
qed



lemma Least_Hermite_of_row_i:
  assumes i: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  shows "(LEAST n. Hermite_of_row_i ass res A i $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
proof -
  let ?M="mult_row A i (ass (A $ i $ (LEAST n. A $ i $ n \<noteq> 0)) div A $ i $ (LEAST n. A $ i $ n \<noteq> 0))"
  let ?H="Hermite_reduce_above ?M (to_nat i) i (LEAST n. A $ i $ n \<noteq> 0) res"
  have "(LEAST n. Hermite_of_row_i ass res A i $ i $ n \<noteq> 0) = (LEAST n. ?H $ i $ n \<noteq> 0)" 
    using i unfolding Hermite_of_row_i_def  unfolding Let_def by auto
  also have "... = (LEAST n. A $ i $ n \<noteq> 0)" 
    by (rule Hermite_reduce_above_Least[OF e a i i])
       (rule not_zero_Hermite_reduce_above[OF i i e a], simp)
  finally show ?thesis .
qed


lemma Least_Hermite_of_row_i2:
  assumes i: "\<not> is_zero_row i A" and k: "\<not> is_zero_row k A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  shows "(LEAST n. Hermite_of_row_i ass res A k $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
proof -
  let ?M="mult_row A k (ass (A $ k $ (LEAST n. A $ k $ n \<noteq> 0)) div A $ k $ (LEAST n. A $ k $ n \<noteq> 0))"
  let ?H="Hermite_reduce_above ?M (to_nat k) k (LEAST n. A $ k $ n \<noteq> 0) res"
  have "(LEAST n. Hermite_of_row_i ass res A k $ i $ n \<noteq> 0) = (LEAST n. ?H $ i $ n \<noteq> 0)" 
    using k unfolding Hermite_of_row_i_def  unfolding Let_def by auto
  also have "... = (LEAST n. A $ i $ n \<noteq> 0)" 
    by (rule Hermite_reduce_above_Least[OF e a k i])
       (simp add: a e i k not_zero_Hermite_reduce_above)
  finally show ?thesis .
qed

lemma Hermite_of_row_i_works:
  fixes i A ass
  defines n:"n \<equiv>(LEAST n. A $ i $ n \<noteq> 0)"
  defines M:"M \<equiv> (mult_row A i (ass (A $ i $ n) div A $ i $ n))"
  assumes ai: "a < i"
  and i: "\<not> is_zero_row i A"
  shows "Hermite_of_row_i ass res A i $ a $ b = 
  row_add M a i ((res (M $ i $ n) (M $ a $ n) 
  - M $ a $ n) div M $ i $ n) $ a $ b"
proof -
  let ?H="Hermite_reduce_above M (to_nat i) i n res"
  have "Hermite_of_row_i ass res A i $ a $ b = ?H $ a $ b" 
    unfolding Hermite_of_row_i_def Let_def M n using i by simp
  also have "... =   row_add M a i ((res (M $ i $ n) (M $ a $ n) 
    - M $ a $ n) div M $ i $ n) $ a $ b"
    by (rule Hermite_reduce_above_works, auto simp add: ai to_nat_mono)
  finally show ?thesis .
qed

lemma Hermite_of_row_i_works2:
  fixes i A ass
  defines n:"n \<equiv>(LEAST n. A $ i $ n \<noteq> 0)"
  defines M:"M \<equiv> (mult_row A i (ass (A $ i $ n) div A $ i $ n))"
  assumes i: "\<not> is_zero_row i A"
  shows "Hermite_of_row_i ass res A i $ i $ b = M $ i $ b"
proof -
  let ?H="Hermite_reduce_above M (to_nat i) i n res"
  have "Hermite_of_row_i ass res A i $ i $ b = ?H $ i $ b" 
    unfolding Hermite_of_row_i_def Let_def M n using i by simp
  also have "... = M $ i $ b" by (rule Hermite_reduce_above_preserves, simp)
  finally show ?thesis .
qed



lemma Hermite_of_upt_row_preserves_nonzero_rows_ge:
  assumes i: "\<not> is_zero_row i A" and i2: "to_nat i\<ge>k"
  shows "\<not> is_zero_row i (Hermite_of_upt_row_i A k ass res)"
proof -
  let ?n="LEAST n. A $ i $ n \<noteq> 0"
  have Ain: "A $ i $ ?n \<noteq> 0" by (metis (mono_tags) LeastI i is_zero_row_def')
  have "Hermite_of_upt_row_i A k ass res $ i $ ?n = A $ i $ ?n"
    by (rule Hermite_of_upt_row_preserves_below[OF i2])
  also have "... \<noteq> 0"  by (metis (mono_tags) LeastI i is_zero_row_def')
  finally have "Hermite_of_upt_row_i A k ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<noteq> 0" .
  thus ?thesis unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
qed




lemma Hermite_of_upt_row_i_Least_ge:
  assumes i: "\<not> is_zero_row i A"
  and i2: "to_nat i\<ge>k"
  shows "(LEAST n. Hermite_of_upt_row_i A k ass res $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
proof (rule Least_equality)
  let ?n="LEAST n. A $ i $ n \<noteq> 0"
  have Ain: "A $ i $ ?n \<noteq> 0" by (metis (mono_tags) LeastI i is_zero_row_def')
  have "Hermite_of_upt_row_i A k ass res $ i $ ?n = A $ i $ ?n"
    by (rule Hermite_of_upt_row_preserves_below[OF i2])
  also have "... \<noteq> 0"  by (metis (mono_tags) LeastI i is_zero_row_def')
  finally show "Hermite_of_upt_row_i A k ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<noteq> 0" .
  fix y
  assume H: "Hermite_of_upt_row_i A k ass res $ i $ y \<noteq> 0"
  show "(LEAST n. A $ i $ n \<noteq> 0) \<le> y" 
    by (rule Least_le, metis Hermite_of_upt_row_preserves_below H i2)
qed

lemma Hermite_of_upt_row_i_Least:
  assumes iA: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  and r: "res_function res"
  and k: "k\<le>nrows A"
  shows "(LEAST n. Hermite_of_upt_row_i A k ass res $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
proof (cases "to_nat i\<ge>k")
  case True
  thus ?thesis using Hermite_of_upt_row_i_Least_ge iA by blast
next
  case False
  hence i_less_k: "to_nat i<k" by simp
  thus ?thesis using e iA k
  proof (induct k arbitrary: A)
    case 0
    thus ?case
      unfolding Hermite_of_upt_row_i_def by simp
  next
    case (Suc k)
    have k: "k\<le>nrows A" using Suc.prems unfolding nrows_def by simp
    have k2: "k<nrows A" using Suc.prems unfolding nrows_def by simp
    define A' where "A' = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k])"
    have A'_def2: "A' = Hermite_of_upt_row_i A k ass res"
      unfolding Hermite_of_upt_row_i_def A'_def ..
    have e: "echelon_form A'"
      unfolding A'_def2 
      by (rule echelon_form_Hermite_of_upt_row_i[OF _ a r], auto simp add: Suc.prems)
    show ?case
    proof (cases "to_nat i = k")
      case True
      have i_fn_k: "from_nat k = i" by (metis True from_nat_to_nat_id)
      have not_zero_i_A':  "\<not> is_zero_row i A'" 
        unfolding A'_def2
        by (rule Hermite_of_upt_row_preserves_nonzero_rows_ge, auto simp add: Suc.prems True)
      have "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_row_i ass res A' (from_nat k)" 
        unfolding Hermite_of_upt_row_i_def A'_def by auto
      also have "(LEAST n. ... $ i $ n \<noteq> 0) = (LEAST n. A' $ i $ n \<noteq> 0)" 
        unfolding i_fn_k 
        by (rule Least_Hermite_of_row_i[OF not_zero_i_A' e a])
      also have "... = (LEAST n. A $ i $ n \<noteq> 0)"
        unfolding A'_def2
        by (rule Hermite_of_upt_row_i_Least_ge, auto simp add: True Suc.prems)
      finally show ?thesis .
    next
      case False
      hence i_less_k: "to_nat i < k" using Suc.prems by simp
      hence i_less_k2: "i < from_nat k"
        by (metis from_nat_mono from_nat_to_nat_id k2 nrows_def)
      show ?thesis
      proof (cases "is_zero_row (from_nat k) A'")
        case True
        have H: "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_upt_row_i A k ass res"
          using True by (simp add:  Hermite_of_upt_row_i_def Hermite_of_row_i_def A'_def Let_def )
        show ?thesis unfolding H by (rule Suc.hyps[OF i_less_k], auto simp add: Suc.prems k)
      next
        case False
        have not_zero_i_A': "\<not> is_zero_row i A'"
          using e False i_less_k2 echelon_form_condition1 by blast
        have "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_row_i ass res A' (from_nat k)" 
          unfolding Hermite_of_upt_row_i_def A'_def by auto
        also have "(LEAST n. ... $ i $ n \<noteq> 0) = (LEAST n. A' $ i $ n \<noteq> 0)" 
          by (rule Least_Hermite_of_row_i2[OF not_zero_i_A' False e a])
        also have "... = (LEAST n. A $ i $ n \<noteq> 0)"
          unfolding A'_def2 by (rule Suc.hyps[OF i_less_k], auto simp add: Suc.prems k)
        finally show ?thesis .
      qed
    qed
  qed
qed


lemma Hermite_of_upt_row_preserves_nonzero_rows:
  assumes i: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  and r: "res_function res"
  and k: "k\<le>nrows A"
  shows "\<not> is_zero_row i (Hermite_of_upt_row_i A k ass res)"
proof -
  let ?n="LEAST n. A $ i $ n \<noteq> 0"
  have Ain: "A $ i $ ?n \<noteq> 0" by (metis (mono_tags) LeastI i is_zero_row_def')
  show ?thesis
  proof (cases "to_nat i\<ge>k")
    case True thus ?thesis using Hermite_of_upt_row_preserves_nonzero_rows_ge i by blast
  next
    case False
    hence i_less_k: "to_nat i<k" by auto
    thus ?thesis using i k
    proof (induct k)
      case 0
      thus ?case by (metis less_nat_zero_code)
    next
      case (Suc k)
      have k_nrows: "k \<le> nrows A" using Suc.prems unfolding nrows_def by auto
      have k_nrows2: "k < nrows A" using Suc.prems unfolding nrows_def by auto
      define A' where "A' = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k])"
      have A'_def2: "A' = Hermite_of_upt_row_i A k ass res"
        unfolding Hermite_of_upt_row_i_def A'_def ..
      have least_A'_A: "(LEAST n. A' $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
        unfolding A'_def2 
        by (rule Hermite_of_upt_row_i_Least[OF _ e a r], auto simp add: k_nrows Suc.prems)
      have e: "echelon_form A'"
        unfolding A'_def2 by (simp add: a e echelon_form_Hermite_of_upt_row_i r)
      show ?case
      proof (cases "to_nat i = k")
        let ?M="mult_row A' i (ass (A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0)) div A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0))"
        case True
        hence fn_k_i: "from_nat k = i" by (metis from_nat_to_nat_id)
        have not_zero_i_A': "\<not> is_zero_row i A'"
          by (unfold A'_def2) 
        (rule Hermite_of_upt_row_preserves_nonzero_rows_ge, auto simp add: True Suc.prems)
        have A'_i_l: "(A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0)) \<noteq> 0" 
          by (metis (mono_tags) LeastI is_zero_row_def' not_zero_i_A')
        have "Hermite_of_upt_row_i A (Suc k) ass res $ i $ ?n =
          Hermite_of_row_i ass res A' (from_nat k) $ i $ ?n" 
          unfolding Hermite_of_upt_row_i_def A'_def by simp
        also have "... = ?M $ i $ ?n" unfolding fn_k_i 
          by (rule Hermite_of_row_i_works2[OF not_zero_i_A'])
        also have "... \<noteq> 0" 
          using A'_i_l unfolding mult_row_def 
          by (simp add:  ass_function_0'[OF a]  least_A'_A)
        finally show ?thesis unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
      next
        case False
        hence i_k: "to_nat i < k" by (metis Suc.prems(1) less_antisym)
        hence i_k2: "i< from_nat k"  using i_k Suc.prems
          by (metis from_nat_mono from_nat_to_nat_id k_nrows2 nrows_def)
        have not_zero_i_A': "\<not> is_zero_row i A'"
          unfolding A'_def2 by (rule Suc.hyps[OF i_k Suc.prems(2) k_nrows])
        show ?thesis 
        proof (cases "is_zero_row (from_nat k) A'")
          case False
          have Ain: "A' $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<noteq> 0" unfolding least_A'_A[symmetric]
            by (metis (mono_tags) LeastI is_zero_row_def' not_zero_i_A')
          have Akn: "A' $ (from_nat k) $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
          proof -
            have "(LEAST n. A' $ i $ n \<noteq> 0) < (LEAST n. A' $ (from_nat k) $ n \<noteq> 0)"
              by (rule echelon_form_condition2_explicit[OF e i_k2 not_zero_i_A' False])
            thus ?thesis by (metis (mono_tags)  least_A'_A not_less_Least)
          qed
          let ?m="(LEAST n. A' $ from_nat k $ n \<noteq> 0)"
          let ?M="mult_row A' (from_nat k)
            (ass (A' $ from_nat k $ ?m) div
            A' $ from_nat k $ ?m)"
          have "Hermite_of_upt_row_i A (Suc k) ass res $ i $ ?n =
            Hermite_of_row_i ass res A' (from_nat k) $ i $ ?n" 
            unfolding Hermite_of_upt_row_i_def A'_def by simp
          also have "... = row_add (mult_row A' (from_nat k)
            (ass (A' $ from_nat k $ ?m) div A' $ from_nat k $ ?m)) i (from_nat k)
            ((res (?M $ from_nat k $ ?m) (?M $ i $ ?m) - ?M $ i $ ?m) div ?M $ from_nat k $ ?m) $ i $ ?n"
            by (rule Hermite_of_row_i_works[OF i_k2 False])
          also have "... \<noteq> 0" using i_k2 Ain Akn unfolding row_add_def mult_row_def by auto
          finally show ?thesis unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
        next
          case True
          have "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_upt_row_i A k ass res"
            using True by (simp add:  Hermite_of_upt_row_i_def Hermite_of_row_i_def A'_def Let_def)
          thus ?thesis using not_zero_i_A' unfolding A'_def2 by simp
        qed
      qed
    qed
  qed
qed

lemma Hermite_of_upt_row_i_in_range:
  fixes k ass res
  assumes not_zero_i_A: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  and r: "res_function res"
  and k: "to_nat i<k"
  and k2: "k\<le>nrows A"
  shows "Hermite_of_upt_row_i A k ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<in> range ass"
  using k not_zero_i_A k2
proof (induct k)
  case 0
  thus ?case by auto
next
  case (Suc k)
  have k: "k\<le>nrows A" using Suc.prems unfolding nrows_def by simp
  have k2: "k<nrows A" using Suc.prems unfolding nrows_def by simp
  define A' where "A' = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k])"
  have A'_def2: "A' = Hermite_of_upt_row_i A k ass res" unfolding Hermite_of_upt_row_i_def A'_def ..
  define M where "M = mult_row A' i (ass (A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0)) div A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0))"
  have not_zero_A': "\<not> is_zero_row i A'" 
    using Hermite_of_upt_row_preserves_nonzero_rows[OF not_zero_i_A e a r k]
    unfolding A'_def Hermite_of_upt_row_i_def by simp
  have e_A': "echelon_form A'" by (metis A'_def a e echelon_form_fold_Hermite_of_row_i r)
  have least_eq: "(LEAST n. (Hermite_of_row_i ass res A' i) $ i $ n \<noteq> 0) = (LEAST n. A' $ i $ n \<noteq> 0)" 
    by (rule Least_Hermite_of_row_i[OF not_zero_A' e_A' a])
  have least_eq2: "(LEAST n. A' $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
    unfolding A'_def2 
    by (rule Hermite_of_upt_row_i_Least[OF not_zero_i_A e a r k])
  show ?case
  proof (cases "to_nat i = k")
    case True
    have fn_k_i: "from_nat k = i" by (metis True from_nat_to_nat_id)    
    have "(Hermite_of_upt_row_i A (Suc k) ass res) $ i $ (LEAST n. A $ i $ n \<noteq> 0) = 
      (Hermite_of_row_i ass res A' i) $ i $ (LEAST n. A $ i $ n \<noteq> 0)" 
      unfolding Hermite_of_upt_row_i_def
      by (simp add: A'_def fn_k_i) 
    also have "... = (Hermite_of_row_i ass res A' i) $ i $ (LEAST n. (Hermite_of_row_i ass res A' i) $ i $ n \<noteq> 0)"
      unfolding least_eq least_eq2 ..
    also have "... \<in> range ass" by (rule in_ass_Hermite_of_row[OF a r not_zero_A'])
    finally show ?thesis .
  next
    case False
    hence i_less_k: "to_nat i < k" using Suc.prems by auto
    hence i_less_k2: "i < from_nat k" using Suc.prems
      by (metis from_nat_mono from_nat_to_nat_id k2 nrows_def)
    show ?thesis 
    proof (cases "is_zero_row (from_nat k) A'")
      case True
      have "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_upt_row_i A k ass res"
        using True by (simp add:  Hermite_of_upt_row_i_def Hermite_of_row_i_def A'_def Let_def )
      thus ?thesis using Suc.hyps not_zero_i_A k i_less_k by auto
    next
      case False          
      have "(Hermite_of_upt_row_i A (Suc k) ass res) $ i $ (LEAST n. A $ i $ n \<noteq> 0)
        = (Hermite_of_row_i ass res A' (from_nat k)) $ i $ (LEAST n. A $ i $ n \<noteq> 0)"
        unfolding Hermite_of_upt_row_i_def A'_def by auto
      also have "... = A' $ i $ (LEAST n. A $ i $ n \<noteq> 0)" 
      proof (rule Hermite_of_row_preserves_previous_cols[OF _ False e_A'])
        show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A' $ mod_type_class.from_nat k $ n \<noteq> 0)"
          unfolding least_eq2[symmetric] 
          by (rule echelon_form_condition2_explicit[OF e_A' i_less_k2 not_zero_A' False])
      qed
      also have "... \<in> range ass" 
        unfolding A'_def using Suc.prems Suc.hyps 
        unfolding Hermite_of_upt_row_i_def using i_less_k by auto
      finally show ?thesis .
    qed
  qed
qed



lemma Hermite_of_upt_row_preserves_zero_rows_ge:
  assumes i: "is_zero_row i A"
  and k: "k \<le> nrows A"
  and ik: "to_nat i\<ge>k"
  shows "is_zero_row i (Hermite_of_upt_row_i A k ass res)"
proof (unfold is_zero_row_def', clarify)
  fix j 
  have "Hermite_of_upt_row_i A k ass res $ i $ j = A $ i $ j" 
    by (metis Hermite_of_upt_row_preserves_below ik)
  also have "... = 0" using i unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by simp
  finally show "Hermite_of_upt_row_i A k ass res $ i $ j = 0" .
qed


lemma Hermite_of_upt_row_preserves_zero_rows:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes i: "is_zero_row i A"
  and e: "echelon_form A" and a: "ass_function ass" and r: "res_function res" and k: "k \<le> nrows A"
  shows "is_zero_row i (Hermite_of_upt_row_i A k ass res)"
proof (cases "to_nat i\<ge>k")
  case True
  show ?thesis by (rule Hermite_of_upt_row_preserves_zero_rows_ge[OF i k True])
next
  case False
  hence i_k: "to_nat i < k" by simp
  show ?thesis
    using k i_k
  proof (induct k)
    case 0
    thus ?case unfolding Hermite_of_upt_row_i_def by (simp add: i)
  next
    case (Suc k)
    have k: "k\<le>nrows A" using Suc.prems unfolding nrows_def by auto
    have k2: "k<nrows A" using Suc.prems unfolding nrows_def by simp
    define A' where "A' = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k])"
    have A'_def2: "A' = Hermite_of_upt_row_i A k ass res"
      unfolding Hermite_of_upt_row_i_def A'_def ..
    show ?case unfolding is_zero_row_def' 
    proof (clarify, cases "to_nat i = k")
      fix j
      case True
      have fn_k_i: "from_nat k = i" by (metis True from_nat_to_nat_id)    
      have "(Hermite_of_upt_row_i A (Suc k) ass res) = 
        (Hermite_of_row_i ass res A' i)" 
        unfolding Hermite_of_upt_row_i_def
        by (simp add: A'_def fn_k_i)  
      moreover have "is_zero_row i (Hermite_of_upt_row_i A k ass res)"
        by (rule Hermite_of_upt_row_preserves_zero_rows_ge[OF i k], simp add: True)
      ultimately show "(Hermite_of_upt_row_i A (Suc k) ass res) $ i $ j = 0" 
        unfolding is_zero_row_def' A'_def2 Hermite_of_row_i_def by auto
    next
      fix j
      case False
      hence i_less_k: "to_nat i < k" using Suc.prems by auto
      hence i_less_k2: "i < from_nat k" using Suc.prems
        by (metis from_nat_mono from_nat_to_nat_id k2 nrows_def)
      show "(Hermite_of_upt_row_i A (Suc k) ass res) $ i $ j = 0" 
      proof (cases "is_zero_row (from_nat k) A'")
        case True
        have "is_zero_row i (Hermite_of_upt_row_i A k ass res)" by (metis Suc.hyps i_less_k k)
        moreover have "Hermite_of_upt_row_i A (Suc k) ass res $ i $ j = Hermite_of_upt_row_i A k ass res $ i $ j"
          using True by (simp add:  Hermite_of_upt_row_i_def Hermite_of_row_i_def A'_def Let_def)
        ultimately show ?thesis unfolding is_zero_row_def' by auto
      next
        case False
        have "is_zero_row i (Hermite_of_upt_row_i A k ass res)" by (metis Suc.hyps i_less_k k)
        moreover have "\<not> is_zero_row i (Hermite_of_upt_row_i A k ass res)"
          using echelon_form_condition1
          by (metis A'_def2 False e a r echelon_form_Hermite_of_upt_row_i i_less_k2)
        ultimately show ?thesis by contradiction
      qed
    qed
  qed
qed

lemma Hermite_of_preserves_zero_rows:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes i: "is_zero_row i (echelon_form_of A bezout)"
  and a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  shows "is_zero_row i (Hermite_of A ass res bezout)"
  unfolding Hermite_of_def Let_def
  by (rule Hermite_of_upt_row_preserves_zero_rows[OF i echelon_form_echelon_form_of[OF b] a r]) 
(auto simp add: nrows_def)

lemma Hermite_of_Least:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes i: "\<not> is_zero_row i (Hermite_of A ass res bezout)"
  and a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  shows "(LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0) = (LEAST n. (echelon_form_of A bezout) $ i $ n \<noteq> 0)"
proof -
  have non_zero_i_eA: "\<not> is_zero_row i (echelon_form_of A bezout)"
    using Hermite_of_preserves_zero_rows[OF _ a r b] i by auto
  have e: "echelon_form (echelon_form_of A bezout)" by (rule echelon_form_echelon_form_of[OF b])
  show ?thesis
    unfolding Hermite_of_def Let_def
    by (rule Hermite_of_upt_row_i_Least[OF non_zero_i_eA e a r], simp add: nrows_def)
qed

lemma in_associates_Hermite_of:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  and i: "\<not> is_zero_row i (Hermite_of A ass res bezout)"
  shows "Hermite_of A ass res bezout $ i $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0) \<in> range ass"
proof -
  have non_zero_i_eA: "\<not> is_zero_row i (echelon_form_of A bezout)"
    using Hermite_of_preserves_zero_rows[OF _ a r b] i by auto
  have e: "echelon_form (echelon_form_of A bezout)"
    by (rule echelon_form_echelon_form_of[OF b])
  have least: "(LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0) = (LEAST n. (echelon_form_of A bezout) $ i $ n \<noteq> 0)"
    by (rule Hermite_of_Least[OF i a r b])
  show ?thesis unfolding least
    unfolding Hermite_of_def Let_def
    by (rule Hermite_of_upt_row_i_in_range[OF non_zero_i_eA e a r])
       (auto simp add: to_nat_less_card nrows_def)
qed

lemma Hermite_of_row_i_range_res:
  assumes ji: "j<i" and not_zero_i_A: "\<not> is_zero_row i A" and r: "res_function res"
  shows "Hermite_of_row_i ass res A i $ j $ (LEAST n. A $ i $ n \<noteq> 0) 
  \<in> range (res (Hermite_of_row_i ass res A i $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
proof -
  let ?n="(LEAST n. A $ i $ n \<noteq> 0)"
  define M where "M = mult_row A i (ass (A $ i $ ?n) div A $ i $ ?n)"
  let ?R="row_add M j i ((res (M $ i $ ?n) (M $ j $ ?n) 
    - M $ j $ ?n) div M $ i $ ?n)"
  have Hii: "Hermite_of_row_i ass res A i $ i $ ?n = M $ i $ ?n"
    unfolding M_def by (rule Hermite_of_row_i_works2[OF not_zero_i_A])
  have rw: "Hermite_of_row_i ass res A i $ j $ ?n = ?R $ j $ ?n" 
    unfolding M_def by (rule Hermite_of_row_i_works[OF ji not_zero_i_A])
  show ?thesis
  proof -
    have "\<forall>b ba. \<exists>bb. ba + bb * b = res b ba"
      using r unfolding res_function_def by metis
    thus ?thesis using rw unfolding image_def Hii row_add_def by auto
      (metis (lifting) add_diff_cancel_left' nonzero_mult_div_cancel_left mult.commute mult_eq_0_iff)
  qed
qed


lemma Hermite_of_upt_row_i_in_range_res:
  fixes k ass res
  assumes not_zero_i_A: "\<not> is_zero_row i A"
  and e: "echelon_form A"
  and a: "ass_function ass"
  and r: "res_function res"
  and k: "to_nat i<k"
  and k2: "k\<le>nrows A"
  and j: "j<i"
  shows "Hermite_of_upt_row_i A k ass res $ j $ (LEAST n. A $ i $ n \<noteq> 0) 
  \<in> range (res (Hermite_of_upt_row_i A k ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
  using k not_zero_i_A k2
proof (induct k)
  case 0 thus ?case by auto
next
  case (Suc k)
  let ?n="(LEAST n. A $ i $ n \<noteq> 0)"
  have k: "k\<le>nrows A" using Suc.prems unfolding nrows_def by simp
  have k2: "k<nrows A" using Suc.prems unfolding nrows_def by simp
  define A' where "A' = foldl (Hermite_of_row_i ass res) A (map from_nat [0..<k])"
  have A'_def2: "A' = Hermite_of_upt_row_i A k ass res" unfolding Hermite_of_upt_row_i_def A'_def ..
  define M where "M = mult_row A' i (ass (A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0)) div A' $ i $ (LEAST n. A' $ i $ n \<noteq> 0))"
  have not_zero_A': "\<not> is_zero_row i A'" 
    using Hermite_of_upt_row_preserves_nonzero_rows[OF not_zero_i_A e a r k]
    unfolding A'_def Hermite_of_upt_row_i_def by simp
  have e_A': "echelon_form A'" by (metis A'_def a e echelon_form_fold_Hermite_of_row_i r)
  have least_eq: "(LEAST n. (Hermite_of_row_i ass res A' i) $ i $ n \<noteq> 0) = (LEAST n. A' $ i $ n \<noteq> 0)" 
    by (rule Least_Hermite_of_row_i[OF not_zero_A' e_A' a])
  have least_eq2: "(LEAST n. A' $ i $ n \<noteq> 0) = (LEAST n. A $ i $ n \<noteq> 0)"
    unfolding A'_def2 
    by (rule Hermite_of_upt_row_i_Least[OF not_zero_i_A e a r k])
  show ?case
  proof (cases "to_nat i = k")
    case True
    have fn_k_i: "from_nat k = i" by (metis True from_nat_to_nat_id)    
    have H_rw: "(Hermite_of_upt_row_i A (Suc k) ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0)) 
      = (Hermite_of_row_i ass res A' i $ i $ (LEAST n. A' $ i $ n \<noteq> 0))"
      by (simp add: Hermite_of_upt_row_i_def A'_def fn_k_i least_eq2[unfolded A'_def])
    have "(Hermite_of_upt_row_i A (Suc k) ass res) $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 
      (Hermite_of_row_i ass res A' i) $ j $ (LEAST n. A $ i $ n \<noteq> 0)" 
      unfolding Hermite_of_upt_row_i_def
      by (simp add: A'_def fn_k_i)
    also have "... = (Hermite_of_row_i ass res A' i) $ j $ (LEAST n. A' $ i $ n \<noteq> 0)"
      unfolding least_eq2 ..
    also have "... \<in> range (res (Hermite_of_row_i ass res A' i $ i $ (LEAST n. A' $ i $ n \<noteq> 0)))"
      by (rule Hermite_of_row_i_range_res[OF j not_zero_A' r])
    also have "... = range ((res (Hermite_of_upt_row_i A (Suc k) ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0))))"
      unfolding H_rw ..
    finally show ?thesis .
  next
    case False
    hence i_less_k: "to_nat i < k" using Suc.prems by auto
    hence i_less_k2: "i < from_nat k" using Suc.prems
      by (metis from_nat_mono from_nat_to_nat_id k2 nrows_def)
    show ?thesis 
    proof (cases "is_zero_row (from_nat k) A'")
      case True
      have "Hermite_of_upt_row_i A (Suc k) ass res = Hermite_of_upt_row_i A k ass res"
        using True by (simp add:  Hermite_of_upt_row_i_def Hermite_of_row_i_def A'_def Let_def )
      thus ?thesis using Suc.hyps not_zero_i_A k i_less_k by auto
    next
      case False
      have H_rw: "(Hermite_of_upt_row_i A (Suc k) ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0)) = 
        A' $ i $ (LEAST n. A $ i $ n \<noteq> 0)" 
      proof (auto simp add: Hermite_of_upt_row_i_def A'_def[symmetric],
          rule Hermite_of_row_preserves_previous_cols[OF _ False e_A'])
        have "(LEAST n. A' $ i $ n \<noteq> 0) < (LEAST n. A' $ mod_type_class.from_nat k $ n \<noteq> 0)"
          by (rule echelon_form_condition2_explicit[OF e_A' i_less_k2 not_zero_A' False])
        thus "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A' $ mod_type_class.from_nat k $ n \<noteq> 0)"
          unfolding least_eq2 .
      qed   
      have "(Hermite_of_upt_row_i A (Suc k) ass res) $ j $ (LEAST n. A $ i $ n \<noteq> 0)
        = (Hermite_of_row_i ass res A' (from_nat k)) $ j $ (LEAST n. A $ i $ n \<noteq> 0)"
        unfolding Hermite_of_upt_row_i_def A'_def by auto
      also have "... = A' $ j $ (LEAST n. A $ i $ n \<noteq> 0)" 
      proof (rule Hermite_of_row_preserves_previous_cols[OF _ False e_A'])
        show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A' $ mod_type_class.from_nat k $ n \<noteq> 0)"
          unfolding least_eq2[symmetric] 
          by (rule echelon_form_condition2_explicit[OF e_A' i_less_k2 not_zero_A' False])
      qed
      also have "... \<in> range (res (Hermite_of_upt_row_i A k ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
        unfolding A'_def2
        by (rule Suc.hyps[OF i_less_k], auto simp add: Suc.prems k)
      also have "... = range (res (Hermite_of_upt_row_i A (Suc k) ass res $ i $ (LEAST n. A $ i $ n \<noteq> 0)))" 
        unfolding H_rw A'_def2 ..
      finally show ?thesis .
    qed
  qed
qed


lemma in_residues_Hermite_of:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  and i: "\<not> is_zero_row i (Hermite_of A ass res bezout)"
  and ji: "j < i"
  shows "Hermite_of A ass res bezout $ j $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0)
  \<in> range (res (Hermite_of A ass res bezout $ i $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0)))"
proof -
  have non_zero_i_eA: "\<not> is_zero_row i (echelon_form_of A bezout)"
    using Hermite_of_preserves_zero_rows[OF _ a r b] i by auto
  have e: "echelon_form (echelon_form_of A bezout)"
    by (rule echelon_form_echelon_form_of[OF b])
  have least: "(LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0) = (LEAST n. (echelon_form_of A bezout) $ i $ n \<noteq> 0)"
    by (rule Hermite_of_Least[OF i a r b])
  show ?thesis unfolding least
    unfolding Hermite_of_def Let_def
    by (rule Hermite_of_upt_row_i_in_range_res[OF non_zero_i_eA e a r _ _ ji])
  (auto simp add: to_nat_less_card nrows_def)
qed

lemma Hermite_Hermite_of:
  assumes a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  shows "Hermite (range ass) (\<lambda>c. range (res c)) (Hermite_of A ass res bezout)"
proof (rule Hermite_intro, auto)
  show "Complete_set_non_associates (range ass)"
    by (simp add: ass_function_Complete_set_non_associates a)
  show "Complete_set_residues (\<lambda>c. range (res c))"
    by (simp add: r res_function_Complete_set_residues)
  show "echelon_form (Hermite_of A ass res bezout)"
    by (simp add: a b echelon_form_Hermite_of r)
  fix i 
  assume i: "\<not> is_zero_row i (Hermite_of A ass res bezout)" 
  show "Hermite_of A ass res bezout $ i $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0) \<in> range ass"
    by (rule in_associates_Hermite_of[OF a r b i])
next
  fix i j assume i: "\<not> is_zero_row i (Hermite_of A ass res bezout)" and j: "j < i"
  show "Hermite_of A ass res bezout $ j $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0)
    \<in> range (res (Hermite_of A ass res bezout $ i $ (LEAST n. Hermite_of A ass res bezout $ i $ n \<noteq> 0)))"
    by (rule in_residues_Hermite_of[OF a r b i j])
qed


subsubsection\<open>Proving that the Hermite Normal Form is computed by means of elementary operations\<close>

lemma invertible_Hermite_reduce_above:
  assumes n: "n \<le> to_nat i"
  shows "\<exists>P. invertible P \<and> Hermite_reduce_above A n i j res = P ** A"
  using n
proof (induct n arbitrary: A)
  case 0 thus ?case by (auto, metis invertible_def matrix_mul_lid)
next
  case (Suc n)
  let ?R="(row_add A (from_nat n) i ((res (A $ i $ j) (A $ from_nat n $ j) - A $ from_nat n $ j) div A $ i $ j))"
  obtain Q where inv_Q: "invertible Q" and H_QR: "Hermite_reduce_above ?R n i j res = Q ** ?R"
    using Suc.hyps Suc.prems by auto
  let ?P="(row_add (mat 1) (from_nat n) i ((res (A $ i $ j) (A $ from_nat n $ j) - A $ from_nat n $ j) div A $ i $ j))"
  have inv_P: "invertible ?P" 
  proof (rule invertible_row_add)
    show "mod_type_class.from_nat n \<noteq> i"
      by (metis Suc.prems Suc_le_eq add_to_nat_def from_nat_mono less_irrefl 
          monoid_add_class.add.right_neutral to_nat_0 to_nat_less_card)
  qed
  have inv_QP: "invertible (Q ** ?P)" by (metis inv_P inv_Q invertible_mult)
  have "Hermite_reduce_above A (Suc n) i j res = Hermite_reduce_above ?R n i j res"
    by (auto simp add: Let_def)
  also have "... = Q ** ?R" unfolding H_QR ..
  also have "... = Q ** (?P ** A)" by (subst row_add_mat_1[symmetric], rule refl)
  also have "... = (Q ** ?P) ** A" by (simp add: matrix_mul_assoc)
  finally show ?case using inv_QP by auto
qed



lemma invertible_Hermite_of_row_i:
  assumes a: "ass_function ass"
  shows "\<exists>P. invertible P \<and> Hermite_of_row_i ass res A i = P ** A"
  unfolding Hermite_of_row_i_def 
proof (auto simp add: Let_def, metis invertible_def matrix_mul_lid)
  let ?n="LEAST n. A $ i $ n \<noteq> 0"
  let ?M="mult_row A i (ass (A $ i $ ?n) div A $ i $ ?n)"
  let ?P="mult_row (mat 1) i (ass (A $ i $ ?n) div A $ i $ ?n)"
  let ?Ain="A $ i $ ?n"
  have ass_dvd: "ass ?Ain dvd ?Ain" using a unfolding ass_function_def by (simp add: associatedD1)
  have ass_dvd': "?Ain dvd ass ?Ain" using a unfolding ass_function_def by (simp add: associatedD1)
  assume iA: "\<not> is_zero_row i A"
  have Ain_0: "A $ i $ ?n \<noteq> 0" by (metis (mono_tags) LeastI iA is_zero_row_def')
  have ass_Ain_0: "ass (A $ i $ ?n) \<noteq> 0" by (metis Ain_0 ass_dvd dvd_0_left_iff) 
  have inv_P: "invertible ?P" 
  proof (rule invertible_mult_row[of _ "A $ i $ ?n div ass (A $ i $ ?n)"]) 
    have "ass ?Ain div ?Ain * (?Ain div ass ?Ain) = (ass ?Ain div ?Ain * ?Ain) div ass ?Ain" 
      by (rule div_mult_swap[OF ass_dvd])
    also have "... = (ass ?Ain) div ass ?Ain" unfolding dvd_div_mult_self[OF ass_dvd'] ..
    also have "... = 1" using ass_Ain_0 by auto
    finally show "ass ?Ain div ?Ain * (?Ain div ass ?Ain) = 1" .
    have "?Ain div ass (?Ain) * (ass (?Ain) div ?Ain) = (?Ain div ass (?Ain) * ass (?Ain)) div ?Ain"
      by (rule div_mult_swap[OF ass_dvd'])
    also have "... = ?Ain div ?Ain" unfolding dvd_div_mult_self[OF ass_dvd] ..
    also have "... = 1" using Ain_0 by simp
    finally show "?Ain div ass (?Ain) * (ass (?Ain) div ?Ain) = 1" .
  qed
  obtain Q where inv_Q: "invertible Q" and H_QM: "Hermite_reduce_above ?M (to_nat i) i ?n res = Q ** ?M" 
    using invertible_Hermite_reduce_above by fast
  have inv_QP: "invertible (Q**?P)"
    by (metis inv_P inv_Q invertible_mult)
  have "Hermite_reduce_above ?M (to_nat i) i ?n res = Q ** ?M" by (rule H_QM)
  also have "... = Q ** (?P ** A)" by (subst mult_row_mat_1[symmetric], rule refl)
  also have "... = (Q ** ?P) ** A" by (simp add: matrix_mul_assoc)
  finally show "\<exists>P. invertible P \<and> Hermite_reduce_above ?M (to_nat i) i ?n res = P ** A"
    using inv_QP by auto
qed



lemma invertible_Hermite_of_upt_row_i:
  assumes a: "ass_function ass"
  shows "\<exists>P. invertible P \<and> Hermite_of_upt_row_i A k ass res = P ** A"
proof (induct k arbitrary: A)
  case 0
  thus ?case unfolding Hermite_of_upt_row_i_def by (auto, metis invertible_def matrix_mul_lid)
next
  case (Suc k)
  obtain Q where inv_Q: "invertible Q" and H_QA: "Hermite_of_upt_row_i A k ass res = Q ** A"
    using Suc.hyps by auto
  obtain P where inv_P: "invertible P" 
    and H_PH: "Hermite_of_row_i ass res (Hermite_of_upt_row_i A k ass res) (from_nat k) 
    = P ** (Hermite_of_upt_row_i A k ass res)" using invertible_Hermite_of_row_i[OF a] by blast
  have inv_PQ: "invertible (P**Q)" by (simp add: inv_P inv_Q invertible_mult)
  have "Hermite_of_upt_row_i A (Suc k) ass res 
    = Hermite_of_row_i ass res (Hermite_of_upt_row_i A k ass res) (from_nat k)"
    unfolding Hermite_of_upt_row_i_def by auto
  also have "... =  P ** (Hermite_of_upt_row_i A k ass res)" unfolding H_PH ..
  also have "... = P ** (Q ** A)" unfolding H_QA ..
  also have "... = (P ** Q) ** A" by (simp add: matrix_mul_assoc)
  finally show ?case using inv_PQ by blast
qed

lemma invertible_Hermite_of:
  fixes A::"'a::{bezout_ring_div,normalization_semidom,unique_euclidean_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes a: "ass_function ass" 
  and b: "is_bezout_ext bezout"
  shows "\<exists>P. invertible P \<and> Hermite_of A ass res bezout = P ** A"
proof -
  obtain P where inv_P: "invertible P" 
    and H_PH: "Hermite_of_upt_row_i (echelon_form_of A bezout) (nrows A) ass res 
    = P ** (echelon_form_of A bezout)" using invertible_Hermite_of_upt_row_i[OF a] by blast
  obtain Q where inv_Q: "invertible Q" and E_QA: "(echelon_form_of A bezout) = Q ** A" 
    using echelon_form_of_invertible[OF b, of A] by auto
  have inv_PQ: "invertible (P**Q)" by (simp add: inv_P inv_Q invertible_mult)
  have "Hermite_of A ass res bezout 
    = Hermite_of_upt_row_i (echelon_form_of A bezout) (nrows A) ass res"
    unfolding Hermite_of_def Let_def ..
  also have "... = P ** (Q ** A)" unfolding H_PH unfolding E_QA ..
  also have "... = (P ** Q) ** A" by (simp add: matrix_mul_assoc)
  finally show ?thesis using inv_PQ by blast
qed

subsubsection\<open>The final theorem\<close>

lemma Hermite:
  assumes a: "ass_function ass"
  and r: "res_function res"
  and b: "is_bezout_ext bezout"
  shows "\<exists>P. invertible P \<and> (Hermite_of A ass res bezout) = P ** A \<and> 
  Hermite (range ass) (\<lambda>c. range (res c)) (Hermite_of A ass res bezout)"
  using invertible_Hermite_of[OF a b] Hermite_Hermite_of[OF a r b] by fast

subsection\<open>Proving the uniqueness of the Hermite Normal Form\<close>

lemma diagonal_least_nonzero:
  fixes H :: "(('a :: {bezout_ring_div, normalization_euclidean_semiring, unique_euclidean_ring}, 'b :: mod_type) vec, 'b) vec"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible H" and up_H: "upper_triangular H"
  shows "(LEAST n. H $ i $ n \<noteq> 0) = i"
proof (rule Least_equality)
  show "H $ i $ i \<noteq> 0" 
    by (metis (full_types) inv_H invertible_iff_is_unit is_unit_diagonal not_is_unit_0 up_H)
  fix y
  assume Hiy: "H $ i $ y \<noteq> 0"
  show "i \<le> y" 
    using up_H unfolding upper_triangular_def
    by (metis (poly_guards_query) Hiy not_less)
qed

lemma diagonal_in_associates:
  fixes H :: "(('a :: {bezout_ring_div, normalization_euclidean_semiring, unique_euclidean_ring}, 'b :: mod_type) vec, 'b) vec"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible H" and up_H: "upper_triangular H"
  shows "H $ i $ i \<in> associates"
proof -
  have "H $ i $ i \<noteq> 0" 
    by (metis (full_types) inv_H invertible_iff_is_unit is_unit_diagonal not_is_unit_0 up_H)
  hence "\<not> is_zero_row i H" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  thus ?thesis using H unfolding Hermite_def unfolding diagonal_least_nonzero[OF H inv_H up_H] 
    by auto
qed

lemma above_diagonal_in_residues:
  fixes H :: "(('a :: {bezout_ring_div, normalization_euclidean_semiring, unique_euclidean_ring}, 'b :: mod_type) vec, 'b) vec"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible H" and up_H: "upper_triangular H"
  and j_i: "j<i"
  shows "H $ j $ (LEAST n. H $ i $ n \<noteq> 0) \<in> residues (H $ i $ (LEAST n. H $ i $ n \<noteq> 0))" 
proof -
  have "H $ i $ i \<noteq> 0" 
    by (metis (full_types) inv_H invertible_iff_is_unit is_unit_diagonal not_is_unit_0 up_H)
  hence "\<not> is_zero_row i H" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  thus ?thesis using H j_i unfolding Hermite_def unfolding diagonal_least_nonzero[OF H inv_H up_H] 
    by auto
qed

text\<open>The uniqueness of the Hermite Normal Form is proven following the proof presented in the book
  Integral Matrices (1972) by Morris Newman.\<close>

lemma Hermite_unique:
  fixes K::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring}^'n::mod_type^'n::mod_type"
  assumes A_PH: "A = P ** H" 
  and A_QK: "A = Q ** K"
  and inv_A: "invertible A"
  and inv_P: "invertible P"
  and inv_Q: "invertible Q"
  and H: "Hermite associates residues H"
  and K: "Hermite associates residues K"
  shows "H = K"
proof -
  have cs_residues: "Complete_set_residues residues" using H unfolding Hermite_def by simp
  have inv_H: "invertible H" 
    by (metis A_PH inv_A inv_P invertible_def invertible_mult matrix_mul_assoc matrix_mul_lid)
  have inv_K: "invertible K" 
    by (metis A_QK inv_A inv_Q invertible_def invertible_mult matrix_mul_assoc matrix_mul_lid)
  define U where "U = (matrix_inv P)**Q"
  have inv_U: "invertible U" 
    by (metis U_def inv_P inv_Q invertible_def invertible_mult matrix_inv_left matrix_inv_right)
  have H_UK: "H = U ** K" using A_PH A_QK inv_P 
    by (metis U_def matrix_inv_left matrix_mul_assoc matrix_mul_lid)
  have "det K *k U = H ** adjugate K"
    unfolding H_UK matrix_mul_assoc[symmetric] mult_adjugate_det matrix_mul_mat ..
  have upper_triangular_H: "upper_triangular H" 
    by (metis H Hermite_def echelon_form_imp_upper_triagular)
  have upper_triangular_K: "upper_triangular K" 
    by (metis K Hermite_def echelon_form_imp_upper_triagular)
  have upper_triangular_U: "upper_triangular U" 
    by (metis H_UK inv_K matrix_inv_right matrix_mul_assoc matrix_mul_rid upper_triangular_H 
      upper_triangular_K upper_triangular_inverse upper_triangular_mult)
  have unit_det_U: "is_unit (det U)" by (metis inv_U invertible_iff_is_unit)
  have is_unit_diagonal_U: "(\<forall>i. is_unit (U $ i $ i))"
    by (rule is_unit_diagonal[OF upper_triangular_U unit_det_U])
  have Uii_1: "(\<forall>i. (U $ i $ i) = 1)" and Hii_Kii: "(\<forall>i. (H $ i $ i) = (K $ i $ i))"
  proof (auto)
    fix i
    have Hii: "H $ i $ i \<in> associates" 
      by (rule diagonal_in_associates[OF H inv_H upper_triangular_H])
    have Kii: "K $ i $ i \<in> associates"
      by (rule diagonal_in_associates[OF K inv_K upper_triangular_K])
    have ass_Hii_Kii: "normalize (H $ i $ i) = normalize (K $ i $ i)" 
      by (meson associatedI inv_H inv_K invertible_iff_is_unit is_unit_diagonal
                unit_imp_dvd upper_triangular_H upper_triangular_K)
    show Hii_eq_Kii: "H $ i $ i = K $ i $ i"
      by (metis Hermite_def Hii K Kii ass_Hii_Kii in_Ass_not_associated)
    have "H $ i $ i = U $ i $ i * K $ i $ i" 
      by (metis H_UK upper_triangular_K upper_triangular_U upper_triangular_mult_diagonal)
    thus "U $ i $ i = 1" unfolding Hii_eq_Kii mult_cancel_right1 
      by (metis Hii_eq_Kii inv_H invertible_iff_is_unit
        is_unit_diagonal not_is_unit_0 upper_triangular_H)
  qed
  have zero_above: "\<forall>j s. j\<ge>1 \<and> j < ncols A - to_nat s \<longrightarrow> U $ s $ (s + from_nat j) = 0"
  proof (clarify)
    fix j s assume  "1 \<le> j" and "j < ncols A - (to_nat (s::'n))"
    thus "U $ s $ (s + from_nat j) = 0"
    proof (induct j rule: less_induct)
      fix p 
      assume induct_step: "(\<And>y. y < p \<Longrightarrow> 1 \<le> y \<Longrightarrow> y < ncols A - to_nat s \<Longrightarrow> U $ s $ (s + from_nat y) = 0)"
        and p1: "1 \<le> p" and p2: "p < ncols A - to_nat s"
      have s_less: "s < s + from_nat p" using p1 p2 unfolding ncols_def
        by (metis One_nat_def add.commute add_diff_cancel_right' add_lessD1 add_to_nat_def 
          from_nat_to_nat_id less_diff_conv neq_iff not_le
          to_nat_from_nat_id to_nat_le zero_less_Suc)
      show "U $ s $ (s + from_nat p) = 0"
      proof -
        have UNIV_rw: "UNIV = insert s (UNIV-{s})" by auto
        have UNIV_s_rw: "UNIV-{s} = insert (s + from_nat p) ((UNIV-{s}) - {s + from_nat p})" 
          using p1 p2 s_less unfolding ncols_def by (auto simp: algebra_simps)
        have sum_rw: "(\<Sum>k\<in>UNIV-{s}. U $ s $ k * K $ k $ (s + from_nat p)) 
          = U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p) 
          + (\<Sum>k\<in>(UNIV-{s})-{s + from_nat p}. U $ s $ k * K $ k $ (s + from_nat p))"
          using UNIV_s_rw sum.insert by (metis (erased, lifting) Diff_iff finite singletonI)
        have sum_0: "(\<Sum>k\<in>(UNIV-{s})-{s + from_nat p}. U $ s $ k * K $ k $ (s + from_nat p)) = 0"
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> UNIV - {s} - {s + from_nat p}"
          show "U $ s $ x * K $ x $ (s + from_nat p) = 0" 
          proof (cases "x<s")
            case True
            thus ?thesis using upper_triangular_U unfolding upper_triangular_def
              by auto
          next
            case False
            hence x_g_s: "x>s" using x by (metis Diff_iff neq_iff singletonI)
            show ?thesis 
            proof (cases "x<s+from_nat p")
              case True
              define a where "a = to_nat x - to_nat s"
              from x_g_s have "to_nat s < to_nat x" by (rule to_nat_mono)
              hence xa: "x=s+(from_nat a)" unfolding a_def add_to_nat_def
                by (simp add: less_imp_diff_less to_nat_less_card algebra_simps to_nat_from_nat_id)
              have "U $ s $ x =0" 
              proof (unfold xa, rule induct_step)
                show a_p: "a<p" unfolding a_def using p2 unfolding ncols_def 
                proof -
                  have "x < from_nat (to_nat s + to_nat (from_nat p::'n))"
                    by (metis (no_types) True add_to_nat_def)
                  hence "to_nat x - to_nat s < to_nat (from_nat p::'n)"
                    by (simp add: add.commute less_diff_conv2 less_imp_le to_nat_le x_g_s)
                  thus "to_nat x - to_nat s < p"
                    by (metis (no_types) from_nat_eq_imp_eq from_nat_to_nat_id le_less_trans 
                        less_imp_le not_le to_nat_less_card)
                qed                    
                show "1 \<le> a" 
                  by (auto simp add: a_def p1 p2) (metis Suc_leI to_nat_mono x_g_s zero_less_diff)
                show "a < ncols A - to_nat s" using a_p p2 by auto
              qed
              thus ?thesis by simp
            next
              case False
              hence "x>s+from_nat p" using x_g_s x by auto
              thus ?thesis using upper_triangular_K unfolding upper_triangular_def
                by auto
            qed
          qed 
        qed
        have "H $ s $ (s + from_nat p) = (\<Sum>k\<in>UNIV. U $ s $ k * K $ k $ (s + from_nat p))"
          unfolding H_UK matrix_matrix_mult_def by auto
        also have "... = (\<Sum>k\<in>insert s (UNIV-{s}). U $ s $ k * K $ k $ (s + from_nat p))"
          using UNIV_rw by simp
        also have "... = U $ s $ s * K $ s $ (s + from_nat p) 
          + (\<Sum>k\<in>UNIV-{s}. U $ s $ k * K $ k $ (s + from_nat p))"
          by (rule sum.insert, simp_all)
        also have "... = U $ s $ s * K $ s $ (s + from_nat p) 
          + U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p)"
          unfolding sum_rw sum_0 by simp
        finally have H_s_sp: "H $ s $ (s + from_nat p) 
          = U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p) + K $ s $ (s + from_nat p)"
          using Uii_1 by auto
        hence cong_HK: "cong (H $ s $ (s + from_nat p)) (K $ s $ (s + from_nat p)) (K $ (s+from_nat p) $ (s + from_nat p))"
          unfolding cong_def by auto
        have H_s_sp_residues: "(H $ s $ (s + from_nat p)) \<in> residues (K $ (s+from_nat p) $ (s + from_nat p))" 
          using above_diagonal_in_residues[OF H inv_H upper_triangular_H s_less]
          unfolding diagonal_least_nonzero[OF H inv_H upper_triangular_H]
          by (metis Hii_Kii)
        have K_s_sp_residues: "(K $ s $ (s + from_nat p)) \<in> residues (K $ (s+from_nat p) $ (s + from_nat p))"
          using above_diagonal_in_residues[OF K inv_K upper_triangular_K s_less]
          unfolding diagonal_least_nonzero[OF K inv_K upper_triangular_K] .
        have Hs_sp_Ks_sp: "(H $ s $ (s + from_nat p)) = (K $ s $ (s + from_nat p))"             
          using cong_HK in_Res_not_congruent[OF cs_residues H_s_sp_residues K_s_sp_residues]
          by fast
        have "is_unit (K $ (s + from_nat p) $ (s + from_nat p))" 
          by (metis Hii_Kii inv_H invertible_iff_is_unit is_unit_diagonal upper_triangular_H)
        hence "K $ (s + from_nat p) $ (s + from_nat p) \<noteq> 0" by (metis not_is_unit_0)
        thus ?thesis unfolding from_nat_1 using H_s_sp unfolding Hs_sp_Ks_sp by auto
      qed 
    qed 
  qed
  have "U = mat 1" 
  proof (unfold mat_def vec_eq_iff, auto)
    fix ia show "U $ ia $ ia = 1" using Uii_1 by simp
    fix i assume i_ia: "i \<noteq> ia"
    show "U $ i $ ia = 0"
    proof (cases "ia<i")
      case True
      thus ?thesis using upper_triangular_U unfolding upper_triangular_def by auto
    next
      case False
      hence i_less_ia: "i<ia" using i_ia by auto
      define a where "a = to_nat ia - to_nat i"
      have ia_eq: "ia = i + from_nat a" unfolding a_def
        by (metis i_less_ia a_def add_to_nat_def dual_order.strict_iff_order from_nat_to_nat_id 
            le_add_diff_inverse less_imp_diff_less to_nat_from_nat_id to_nat_less_card to_nat_mono)
      have "1 \<le> a" unfolding a_def
        by (metis diff_is_0_eq i_less_ia less_one not_less to_nat_mono)
      moreover have "a < ncols A - to_nat i"
        unfolding a_def ncols_def
        by (metis False diff_less_mono not_less to_nat_less_card to_nat_mono')
      ultimately show ?thesis using zero_above unfolding ia_eq by blast
    qed
  qed
  thus ?thesis using H_UK matrix_mul_lid by fast
qed
  

subsection\<open>Examples of execution\<close>

value[code] "let A = list_of_list_to_matrix ([[37,8,6],[5,4,-8],[3,24,-7]])::int^3^3
  in matrix_to_list_of_list (Hermite_of A ass_function_euclidean res_function_euclidean euclid_ext2)"

value[code] "let A = list_of_list_to_matrix ([[[:3,4,5:],[:-2,1:]],[[:-1,0,2:],[:0,1,4,1:]]])::real poly^2^2
  in matrix_to_list_of_list (Hermite_of A ass_function_euclidean res_function_euclidean euclid_ext2)"

end
