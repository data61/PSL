(* Title:      Matrix Model of Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Matrices\<close>

theory Matrix
imports "HOL-Word.Word" Dioid
begin

text \<open>In this section we formalise a perhaps more natural version of
matrices of fixed dimension ($m \times n$-matrices). It is well known
that such matrices over a Kleene algebra form a Kleene
algebra~\cite{conway71regular}.\<close>

subsection \<open>Type Definition\<close>

typedef (overloaded) 'a atMost = "{..<LENGTH('a::len)}"
by auto

declare Rep_atMost_inject [simp]

lemma UNIV_atMost:
  "(UNIV::'a atMost set) = Abs_atMost ` {..<LENGTH('a::len)}"
 apply auto
 apply (rule Abs_atMost_induct)
 apply auto
done

lemma finite_UNIV_atMost [simp]: "finite (UNIV::('a::len) atMost set)"
  by (simp add: UNIV_atMost)

text \<open>Our matrix type is similar to \mbox{\<open>'a^'n^'m\<close>} from
{\em HOL/Multivariate\_Analysis/Finite\_Cartesian\_Product.thy}, but
(i)~we explicitly define a type constructor for matrices and square
matrices, and (ii)~in the definition of operations, e.g., matrix
multiplication, we impose weaker sort requirements on the element
type.\<close>

context notes [[typedef_overloaded]]
begin

datatype ('a,'m,'n) matrix = Matrix "'m atMost \<Rightarrow> 'n atMost \<Rightarrow> 'a"

datatype ('a,'m) sqmatrix = SqMatrix "'m atMost \<Rightarrow> 'm atMost \<Rightarrow> 'a"

end

fun sqmatrix_of_matrix where
  "sqmatrix_of_matrix (Matrix A) = SqMatrix A"

fun matrix_of_sqmatrix where
  "matrix_of_sqmatrix (SqMatrix A) = Matrix A"


subsection \<open>0 and 1\<close>

instantiation matrix :: (zero,type,type) zero
begin
  definition zero_matrix_def: "0 \<equiv> Matrix (\<lambda>i j. 0)"
  instance ..
end

instantiation sqmatrix :: (zero,type) zero
begin
  definition zero_sqmatrix_def: "0 \<equiv> SqMatrix (\<lambda>i j. 0)"
  instance ..
end

text \<open>Tricky sort issues: compare @{term one_matrix} with @{term
one_sqmatrix} \dots\<close>

instantiation matrix :: ("{zero,one}",len,len) one
begin
  definition one_matrix_def:
    "1 \<equiv> Matrix (\<lambda>i j. if Rep_atMost i = Rep_atMost j then 1 else 0)"
  instance ..
end

instantiation sqmatrix :: ("{zero,one}",type) one
begin
  definition one_sqmatrix_def:
    "1 \<equiv> SqMatrix (\<lambda>i j. if i = j then 1 else 0)"
  instance ..
end


subsection \<open>Matrix Addition\<close>

fun matrix_plus where
  "matrix_plus (Matrix A) (Matrix B) = Matrix (\<lambda>i j. A i j + B i j)"

instantiation matrix :: (plus,type,type) plus
begin
  definition plus_matrix_def: "A + B \<equiv> matrix_plus A B"
  instance ..
end

lemma plus_matrix_def' [simp]:
  "Matrix A + Matrix B = Matrix (\<lambda>i j. A i j + B i j)"
  by (simp add: plus_matrix_def)

instantiation sqmatrix :: (plus,type) plus
begin
  definition plus_sqmatrix_def:
    "A + B \<equiv> sqmatrix_of_matrix (matrix_of_sqmatrix A + matrix_of_sqmatrix B)"
  instance ..
end

lemma plus_sqmatrix_def' [simp]:
  "SqMatrix A + SqMatrix B = SqMatrix (\<lambda>i j. A i j + B i j)"
  by (simp add: plus_sqmatrix_def)

lemma matrix_add_0_right [simp]:
  "A + 0 = (A::('a::monoid_add,'m,'n) matrix)"
  by (cases A, simp add: zero_matrix_def)

lemma matrix_add_0_left [simp]:
  "0 + A = (A::('a::monoid_add,'m,'n) matrix)"
  by (cases A, simp add: zero_matrix_def)

lemma matrix_add_commute [simp]:
  "(A::('a::ab_semigroup_add,'m,'n) matrix) + B = B + A"
  by (cases A, cases B, simp add: add.commute)

lemma matrix_add_assoc:
  "(A::('a::semigroup_add,'m,'n) matrix) + B + C = A + (B + C)"
  by (cases A, cases B, cases C, simp add: add.assoc)

lemma matrix_add_left_commute [simp]:
  "(A::('a::ab_semigroup_add,'m,'n) matrix) + (B + C) = B + (A + C)"
  by (metis matrix_add_assoc matrix_add_commute)

lemma sqmatrix_add_0_right [simp]:
  "A + 0 = (A::('a::monoid_add,'m) sqmatrix)"
  by (cases A, simp add: zero_sqmatrix_def)

lemma sqmatrix_add_0_left [simp]:
  "0 + A = (A::('a::monoid_add,'m) sqmatrix)"
  by (cases A, simp add: zero_sqmatrix_def)

lemma sqmatrix_add_commute [simp]:
  "(A::('a::ab_semigroup_add,'m) sqmatrix) + B = B + A"
  by (cases A, cases B, simp add: add.commute)

lemma sqmatrix_add_assoc:
  "(A::('a::semigroup_add,'m) sqmatrix) + B + C = A + (B + C)"
  by (cases A, cases B, cases C, simp add: add.assoc)

lemma sqmatrix_add_left_commute [simp]:
  "(A::('a::ab_semigroup_add,'m) sqmatrix) + (B + C) = B + (A + C)"
  by (metis sqmatrix_add_commute sqmatrix_add_assoc)


subsection \<open>Order (via Addition)\<close>

instantiation matrix :: (plus,type,type) plus_ord
begin
  definition less_eq_matrix_def:
    "(A::('a, 'b, 'c) matrix) \<le> B \<equiv> A + B = B"
  definition less_matrix_def:
    "(A::('a, 'b, 'c) matrix) < B \<equiv> A \<le> B \<and> A \<noteq> B"

  instance
  proof
    fix A B :: "('a, 'b, 'c) matrix"
    show "A \<le> B \<longleftrightarrow> A + B = B"
      by (metis less_eq_matrix_def)
    show "A < B \<longleftrightarrow> A \<le> B \<and> A \<noteq> B"
      by (metis less_matrix_def)
  qed
end

instantiation sqmatrix :: (plus,type) plus_ord
begin
  definition less_eq_sqmatrix_def:
    "(A::('a, 'b) sqmatrix) \<le> B \<equiv> A + B = B"
  definition less_sqmatrix_def:
    "(A::('a, 'b) sqmatrix) < B \<equiv> A \<le> B \<and> A \<noteq> B"

  instance
  proof
    fix A B :: "('a, 'b) sqmatrix"
    show "A \<le> B \<longleftrightarrow> A + B = B"
      by (metis less_eq_sqmatrix_def)
    show "A < B \<longleftrightarrow> A \<le> B \<and> A \<noteq> B"
      by (metis less_sqmatrix_def)
  qed
end


subsection \<open>Matrix Multiplication\<close>

fun matrix_times :: "('a::{comm_monoid_add,times},'m,'k) matrix \<Rightarrow> ('a,'k,'n) matrix \<Rightarrow> ('a,'m,'n) matrix" where
  "matrix_times (Matrix A) (Matrix B) = Matrix (\<lambda>i j. sum (\<lambda>k. A i k * B k j) (UNIV::'k atMost set))"

notation matrix_times (infixl "*\<^sub>M" 70)

instantiation sqmatrix :: ("{comm_monoid_add,times}",type) times
begin
  definition times_sqmatrix_def:
    "A * B = sqmatrix_of_matrix (matrix_of_sqmatrix A *\<^sub>M matrix_of_sqmatrix B)"
  instance ..
end

lemma times_sqmatrix_def' [simp]:
  "SqMatrix A * SqMatrix B = SqMatrix (\<lambda>i j. sum (\<lambda>k. A i k * B k j) (UNIV::'k atMost set))"
  by (simp add: times_sqmatrix_def)

lemma matrix_mult_0_right [simp]:
  "(A::('a::{comm_monoid_add,mult_zero},'m,'n) matrix) *\<^sub>M 0 = 0"
  by (cases A, simp add: zero_matrix_def)

lemma matrix_mult_0_left [simp]:
  "0 *\<^sub>M (A::('a::{comm_monoid_add,mult_zero},'m,'n) matrix) = 0"
  by (cases A, simp add: zero_matrix_def)

lemma sum_delta_r_0 [simp]:
  "\<lbrakk> finite S; j \<notin> S \<rbrakk> \<Longrightarrow> (\<Sum>k\<in>S. f k * (if k = j then 1 else (0::'b::{semiring_0,monoid_mult}))) = 0"
  by (induct S rule: finite_induct, auto)

lemma sum_delta_r_1 [simp]:
  "\<lbrakk> finite S; j \<in> S \<rbrakk> \<Longrightarrow> (\<Sum>k\<in>S. f k * (if k = j then 1 else (0::'b::{semiring_0,monoid_mult}))) = f j"
  by (induct S rule: finite_induct, auto)

lemma matrix_mult_1_right [simp]:
  "(A::('a::{semiring_0,monoid_mult},'m::len,'n::len) matrix) *\<^sub>M 1 = A"
  by (cases A, simp add: one_matrix_def)

lemma sum_delta_l_0 [simp]:
  "\<lbrakk> finite S; i \<notin> S \<rbrakk> \<Longrightarrow> (\<Sum>k\<in>S. (if i = k then 1 else (0::'b::{semiring_0,monoid_mult})) * f k j) = 0"
  by (induct S rule: finite_induct, auto)

lemma sum_delta_l_1 [simp]:
  "\<lbrakk> finite S; i \<in> S \<rbrakk> \<Longrightarrow> (\<Sum>k\<in>S. (if i = k then 1 else (0::'b::{semiring_0,monoid_mult})) * f k j) = f i j"
  by (induct S rule: finite_induct, auto)

lemma matrix_mult_1_left [simp]:
  "1 *\<^sub>M (A::('a::{semiring_0,monoid_mult},'m::len,'n::len) matrix) = A"
  by (cases A, simp add: one_matrix_def)

lemma matrix_mult_assoc:
  "(A::('a::semiring_0,'m,'n) matrix) *\<^sub>M B *\<^sub>M C = A *\<^sub>M (B *\<^sub>M C)"
 apply (cases A)
 apply (cases B)
 apply (cases C)
 apply (simp add: sum_distrib_right sum_distrib_left mult.assoc)
 apply (subst sum.swap)
 apply (rule refl)
done

lemma matrix_mult_distrib_left:
  "(A::('a::{comm_monoid_add,semiring},'m,'n::len) matrix) *\<^sub>M (B + C) = A *\<^sub>M B + A *\<^sub>M C"
  by (cases A, cases B, cases C, simp add: distrib_left sum.distrib)

lemma matrix_mult_distrib_right:
  "((A::('a::{comm_monoid_add,semiring},'m,'n::len) matrix) + B) *\<^sub>M C = A *\<^sub>M C + B *\<^sub>M C"
  by (cases A, cases B, cases C, simp add: distrib_right sum.distrib)

lemma sqmatrix_mult_0_right [simp]:
  "(A::('a::{comm_monoid_add,mult_zero},'m) sqmatrix) * 0 = 0"
  by (cases A, simp add: zero_sqmatrix_def)

lemma sqmatrix_mult_0_left [simp]:
  "0 * (A::('a::{comm_monoid_add,mult_zero},'m) sqmatrix) = 0"
  by (cases A, simp add: zero_sqmatrix_def)

lemma sqmatrix_mult_1_right [simp]:
  "(A::('a::{semiring_0,monoid_mult},'m::len) sqmatrix) * 1 = A"
  by (cases A, simp add: one_sqmatrix_def)

lemma sqmatrix_mult_1_left [simp]:
  "1 * (A::('a::{semiring_0,monoid_mult},'m::len) sqmatrix) = A"
  by (cases A, simp add: one_sqmatrix_def)

lemma sqmatrix_mult_assoc:
  "(A::('a::{semiring_0,monoid_mult},'m) sqmatrix) * B * C = A * (B * C)"
 apply (cases A)
 apply (cases B)
 apply (cases C)
 apply (simp add: sum_distrib_right sum_distrib_left mult.assoc)
 apply (subst sum.swap)
 apply (rule refl)
done

lemma sqmatrix_mult_distrib_left:
  "(A::('a::{comm_monoid_add,semiring},'m::len) sqmatrix) * (B + C) = A * B + A * C"
  by (cases A, cases B, cases C, simp add: distrib_left sum.distrib)

lemma sqmatrix_mult_distrib_right:
  "((A::('a::{comm_monoid_add,semiring},'m::len) sqmatrix) + B) * C = A * C + B * C"
  by (cases A, cases B, cases C, simp add: distrib_right sum.distrib)


subsection \<open>Square-Matrix Model of Dioids\<close>

text \<open>The following subclass proofs are necessary to connect parts
of our algebraic hierarchy to the hierarchy found in the Isabelle/HOL
library.\<close>

subclass (in ab_near_semiring_one_zerol) comm_monoid_add
proof
  fix a :: 'a
  show "0 + a = a"
    by (fact add_zerol)
qed

subclass (in semiring_one_zero) semiring_0
proof
  fix a :: 'a
  show "0 * a = 0"
    by (fact annil)
  show "a * 0 = 0"
    by (fact annir)
qed

subclass (in ab_near_semiring_one) monoid_mult ..

instantiation sqmatrix :: (dioid_one_zero,len) dioid_one_zero
begin
  instance
  proof
    fix A B C :: "('a, 'b) sqmatrix"
    show "A + B + C = A + (B + C)"
      by (fact sqmatrix_add_assoc)
    show "A + B = B + A"
      by (fact sqmatrix_add_commute)
    show "A * B * C = A * (B * C)"
      by (fact sqmatrix_mult_assoc)
    show "(A + B) * C = A * C + B * C"
      by (fact sqmatrix_mult_distrib_right)
    show "1 * A = A"
      by (fact sqmatrix_mult_1_left)
    show "A * 1 = A"
      by (fact sqmatrix_mult_1_right)
    show "0 + A = A"
      by (fact sqmatrix_add_0_left)
    show "0 * A = 0"
      by (fact sqmatrix_mult_0_left)
    show "A * 0 = 0"
      by (fact sqmatrix_mult_0_right)
    show "A + A = A"
      by (cases A, simp)
    show "A * (B + C) = A * B + A * C"
      by (fact sqmatrix_mult_distrib_left)
  qed
end

subsection \<open>Kleene Star for Matrices\<close>

text \<open>We currently do not implement the Kleene star of matrices,
since this is complicated.\<close>

end
