(*  Title:       Executable Matrix Operations on Matrices of Arbitrary Dimensions
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Basic Operations on Matrices\<close>

theory Matrix_Legacy
imports
  Utility
  Ordered_Semiring
begin

text \<open>This theory is marked as legacy, since there is a better
  implementation of matrices available in @{file \<open>../Jordan_Normal_Form/Matrix.thy\<close>}.
  That formalization is more abstract, more complete in terms of operations,
  and it still provides an efficient implementation.\<close>

text \<open>
  This theory provides the operations of matrix addition, multiplication,
  and transposition as executable functions.
  Most properties are proven via pointwise equality of matrices.
\<close>


subsection \<open>types and well-formedness of vectors / matrices\<close>

type_synonym 'a vec = "'a list"
type_synonym 'a mat = "'a vec list" (* list of column-vectors *)


(* vector of given length *)
definition vec :: "nat \<Rightarrow> 'x vec \<Rightarrow> bool"
 where "vec n x = (length x = n)"

(* matrix of given number of rows and columns *)
definition mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> bool" where
 "mat nr nc m = (length m = nc \<and> Ball (set m) (vec nr))"

subsection \<open>definitions / algorithms\<close>

text \<open>note that these algorithms are generic in all basic definitions / operations
like 0 (ze) 1 (on) addition (pl) multiplication (ti) and in the dimension(s) of the matrix/vector.
Hence, many of these algorithms require these definitions/operations/sizes as arguments.
All indices start from 0.
\<close>

(* the 0 vector *)
definition vec0I :: "'a \<Rightarrow> nat \<Rightarrow> 'a vec" where
 "vec0I ze n = replicate n ze"

(* the 0 matrix *)
definition mat0I :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat0I ze nr nc = replicate nc (vec0I ze nr)"

(* the i-th unit vector of size n *)
definition vec1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a vec"
  where "vec1I ze on n i \<equiv> replicate i ze @ on # replicate (n - 1 - i) ze"

(* the 1 matrix *)
definition mat1I :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat1I ze on n \<equiv> map (vec1I ze on n) [0 ..< n]"


(* vector addition *)
definition vec_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
 "vec_plusI pl v w = map (\<lambda> xy. pl (fst xy) (snd xy)) (zip v w)"

(* matrix addition *)
definition mat_plusI :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "mat_plusI pl m1 m2 = map (\<lambda> uv. vec_plusI pl (fst uv) (snd uv)) (zip m1 m2)"

(* scalar product *)
definition scalar_prodI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a" where
 "scalar_prodI ze pl ti v w = foldr (\<lambda> (x,y) s. pl (ti x y) s) (zip v w) ze"

(* the m-th row of a matrix *)
definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "row m i \<equiv> map (\<lambda> w. w ! i) m"

(* the m-th column of a matrix *)
definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "col m i \<equiv> m ! i"

(* transposition of a matrix (number of rows of matrix has to be given since otherwise one
   could not compute transpose [] which might be [] or [[]] or [[], []], or ...) *)
fun transpose :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
 where "transpose nr [] = replicate nr []"
     | "transpose nr (v # m) = map (\<lambda> (vi,mi). (vi # mi)) (zip v (transpose nr m))"

(* matrix-vector multiplication, assumes the transposed matrix is given *)
definition matT_vec_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
 where "matT_vec_multI ze pl ti m v = map (\<lambda> w. scalar_prodI ze pl ti w v) m"

(* matrix-matrix multiplication, number of rows of left matrix has to be given (as transpose is used) *)
definition mat_multI :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_multI ze pl ti nr m1 m2 \<equiv> map (matT_vec_multI ze pl ti (transpose nr m1)) m2"

(* power of a square matrix *)
fun mat_powI :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> 'a mat"
  where "mat_powI ze on pl ti n m 0 = mat1I ze on n"
      | "mat_powI ze on pl ti n m (Suc i) = mat_multI ze pl ti n (mat_powI ze on pl ti n m i) m"

definition sub_vec :: "nat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "sub_vec = take"

(* taking only the upper left sub matrix *)
definition sub_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "sub_mat nr nc m = map (sub_vec nr) (take nc m)"


(* map on vectors *)
definition vec_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "vec_map = map"

(* map on matrices *)
definition mat_map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
  where "mat_map f = map (vec_map f)"

subsection \<open>algorithms preserve dimensions\<close>

lemma vec0[simp,intro]: "vec nr (vec0I ze nr)"
  by (simp add: vec_def vec0I_def)

lemma replicate_prop:
  assumes "P x"
  shows "\<forall>y\<in>set (replicate n x). P y"
  using assms by (induct n) simp_all

lemma mat0[simp,intro]: "mat nr nc (mat0I ze nr nc)"
unfolding mat_def mat0I_def
using replicate_prop[of "vec nr" "vec0I ze nr" "nc"] by simp

lemma vec1[simp,intro]: assumes "i < nr" shows "vec nr (vec1I ze on nr i)"
unfolding vec_def vec1I_def using assms by auto

lemma mat1[simp,intro]: "mat nr nr (mat1I ze on nr)"
unfolding mat_def mat1I_def using vec1 by auto

lemma vec_plus[simp,intro]: "\<lbrakk>vec nr u; vec nr v\<rbrakk> \<Longrightarrow> vec nr (vec_plusI pl u v)"
unfolding vec_plusI_def vec_def
by auto

lemma mat_plus[simp,intro]: assumes "mat nr nc m1" and "mat nr nc m2" shows "mat nr nc (mat_plusI pl m1 m2)"
using assms
unfolding mat_def mat_plusI_def
proof (simp, induct nc arbitrary: m1 m2, simp)
  case (Suc nn)
  show ?case
  proof (cases m1)
    case Nil with Suc show ?thesis by auto
  next
    case (Cons v1 mm1) note oCons = this
    with Suc have l1: "length mm1 = nn" by auto
    show ?thesis
    proof (cases m2)
      case Nil with Suc show ?thesis by auto
    next
      case (Cons v2 mm2)
      with Suc have l2: "length mm2 = nn" by auto
      show ?thesis by (simp add: Cons oCons, intro conjI[OF vec_plus], (simp add: Cons oCons Suc)+, rule Suc, auto simp: Cons oCons Suc l1 l2)
    qed
  qed
qed

lemma vec_map[simp,intro]: "vec nr u \<Longrightarrow> vec nr (vec_map f u)"
unfolding vec_map_def vec_def
by auto

lemma mat_map[simp,intro]: "mat nr nc m \<Longrightarrow> mat nr nc (mat_map f m)"
using vec_map
unfolding mat_map_def mat_def
by auto

fun vec_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a vec \<Rightarrow> 'b \<Rightarrow> 'b"
  where [code_unfold]: "vec_fold f = foldr f"

fun mat_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a mat \<Rightarrow> 'b \<Rightarrow> 'b"
  where [code_unfold]: "mat_fold f = foldr (vec_fold f)"


lemma concat_mat: "mat nr nc m \<Longrightarrow>
  concat m = [ m ! i ! j. i \<leftarrow> [0 ..< nc], j \<leftarrow> [0 ..< nr] ]"
proof (induct m arbitrary: nc)
  case Nil
  thus ?case unfolding mat_def by auto
next
  case (Cons v m snc)
  from Cons(2) obtain nc where snc: "snc = Suc nc" and mat: "mat nr nc m" and v: "vec nr v"
    unfolding mat_def by (cases snc, auto)
  from v have nr: "nr = length v" unfolding vec_def by auto
  have v: "map (\<lambda> i. v ! i) [0 ..< nr] = v" unfolding nr map_nth by simp
  note IH = Cons(1)[OF mat]
  show ?case
    unfolding snc
    unfolding map_upt_Suc
    unfolding nth.simps nat.simps concat.simps
    unfolding IH v ..
qed


lemma row: assumes "mat nr nc m"
  and "i < nr"
  shows "vec nc (row m i)"
  using assms
  unfolding vec_def row_def mat_def
  by (auto simp: vec_def)

lemma col: assumes "mat nr nc m"
  and "i < nc"
  shows "vec nr (col m i)"
  using assms
  unfolding vec_def col_def mat_def
  by (auto simp: vec_def)

lemma transpose[simp,intro]: assumes "mat nr nc m"
  shows "mat nc nr (transpose nr m)"
using assms
proof (induct m arbitrary: nc)
  case (Cons v m)
  from \<open>mat nr nc (v # m)\<close> obtain ncc where nc: "nc = Suc ncc" by (cases nc, auto simp: mat_def)
  with Cons have wfRec: "mat ncc nr (transpose nr m)" unfolding mat_def by auto
  have "min nr (length (transpose nr m)) = nr" using wfRec unfolding mat_def by auto
  moreover have "Ball (set (transpose nr (v # m))) (vec nc)"
  proof -
    {
      fix a b
      assume mem: "(a,b) \<in> set (zip v (transpose nr m))"
      from mem have "b \<in> set (transpose nr m)" by (rule set_zip_rightD)
      with wfRec have "length b = ncc" unfolding mat_def using vec_def[of ncc] by auto
      hence "length (case_prod (#) (a,b)) = Suc ncc" by auto
    }
    thus ?thesis
      by (auto simp: vec_def nc)
  qed
  moreover from \<open>mat nr nc (v # m)\<close> have wfV: "length v = nr" unfolding mat_def by (simp add: vec_def)
  ultimately
  show ?case unfolding mat_def
    by (intro conjI, auto simp: wfV wfRec mat_def vec_def)
qed (simp add: mat_def vec_def set_replicate_conv_if)


lemma matT_vec_multI: assumes "mat nr nc m"
  shows "vec nc (matT_vec_multI ze pl ti m v)"
  unfolding matT_vec_multI_def
  using assms
  unfolding mat_def
  by (simp add: vec_def)

lemma mat_mult[simp,intro]: assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  shows "mat nr nc (mat_multI ze pl ti nr m1 m2)"
using assms
unfolding mat_def mat_multI_def by (auto simp: matT_vec_multI[OF transpose[OF wf1]])

lemma mat_pow[simp,intro]: assumes "mat n n m"
  shows "mat n n (mat_powI ze on pl ti n m i)"
proof (induct i)
  case 0
  show ?case unfolding mat_powI.simps by (rule mat1)
next
  case (Suc i)
  show ?case unfolding mat_powI.simps
    by (rule mat_mult[OF Suc assms])
qed

lemma sub_vec[simp,intro]: assumes "vec nr v" and "sd \<le> nr"
  shows "vec sd (sub_vec sd v)"
using assms unfolding vec_def sub_vec_def by auto

lemma sub_mat[simp,intro]: assumes wf: "mat nr nc m" and sr: "sr \<le> nr" and sc: "sc \<le> nc"
  shows "mat sr sc (sub_mat sr sc m)"
using assms in_set_takeD[of _ sc m] sub_vec[OF _ sr] unfolding mat_def sub_mat_def by auto


subsection \<open>properties of algorithms which do not depend on properties of type of matrix\<close>

lemma mat0_index[simp]: assumes "i < nc" and "j < nr"
  shows "mat0I ze nr nc ! i ! j = ze"
unfolding mat0I_def vec0I_def using assms by auto

lemma mat0_row[simp]: assumes "i < nr"
  shows "row (mat0I ze nr nc) i = vec0I ze nc"
unfolding row_def mat0I_def vec0I_def
using assms by auto


lemma mat0_col[simp]: assumes "i < nc"
  shows "col (mat0I ze nr nc) i = vec0I ze nr"
unfolding mat0I_def col_def
using assms by auto

lemma vec1_index: assumes j: "j < n"
  shows "vec1I ze on n i ! j = (if i = j then on else ze)" (is "_ = ?r")
unfolding vec1I_def
proof -
  let ?l = "replicate i ze @ on # replicate (n - 1 - i) ze"
  have len: "length ?l > i" by auto
  have len2: "length (replicate i ze @ on # []) > i" by auto
  show "?l ! j = ?r"
  proof (cases "j = i")
    case True
    thus ?thesis by (simp add: nth_append)
  next
    case False
    show ?thesis
    proof (cases "j < i")
      case True
      thus ?thesis by (simp add: nth_append)
    next
      case False
      with \<open>j \<noteq> i\<close> have gt: "j > i" by auto
      from this have "\<exists> k. j = i + Suc k" by arith
      from this obtain k where k: "j = i + Suc k" by auto
      with j show ?thesis by (simp add: nth_append)
    qed
  qed
qed


lemma col_transpose_is_row[simp]:
  assumes wf: "mat nr nc m"
  and i: "i < nr"
  shows "col (transpose nr m) i = row m i"
using wf
proof (induct m arbitrary: nc)
  case (Cons v m)
  from \<open>mat nr nc (v # m)\<close> obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m"  by (cases nc, auto simp: mat_def)
  from \<open>mat nr nc (v # m)\<close> nc have lengths: "(\<forall> w \<in> set m. length w = nr) \<and> length v = nr \<and> length m = ncc" unfolding mat_def by (auto simp: vec_def)
  from wf Cons have colRec: "col (transpose nr m) i = row m i" by auto
  hence simpme: "transpose nr m ! i = row m i" unfolding col_def by auto
  from wf have trans: "mat ncc nr (transpose nr m)" by (rule transpose)
  hence lengths2: "(\<forall> w \<in> set (transpose nr m). length w = ncc) \<and> length (transpose nr m) = nr" unfolding mat_def by (auto simp: vec_def)
  {
    fix j
    assume "j < length (col (transpose nr (v # m)) i)"
    hence "j < Suc ncc" by (simp add: col_def lengths2 lengths i)
    hence "col (transpose nr (v # m)) i ! j = row (v # m) i ! j"
      by (cases j, simp add: row_def col_def i lengths lengths2, simp add: row_def col_def i lengths lengths2 simpme)
  } note simpme = this
  show ?case by (rule nth_equalityI, simp add: col_def row_def lengths lengths2 i, rule simpme)
qed (simp add: col_def row_def mat_def i)

lemma mat_col_eq:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nc. col m1 i = col m2 i)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    from \<open>?r\<close> show "\<And>i. i < length m1 \<Longrightarrow> m1 ! i = m2 ! i" using wf1 unfolding col_def mat_def by auto
  qed
qed

lemma mat_col_eqI:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and id: "\<And> i. i < nc \<Longrightarrow> col m1 i = col m2 i"
  shows "m1 = m2"
  unfolding mat_col_eq[OF wf1 wf2] using id by auto

lemma mat_eq:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nc. \<forall> j < nr. m1 ! i ! j = m2 ! i ! j)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule mat_col_eqI[OF wf1 wf2], unfold col_def)
    fix i
    assume i: "i < nc"
    show "m1 ! i = m2 ! i"
    proof (rule nth_equalityI)
      show "length (m1 ! i)  = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
    next
      from \<open>?r\<close> i show "\<And>j. j < length (m1 ! i) \<Longrightarrow> m1 ! i ! j = m2 ! i ! j" 
        using wf1 wf2 unfolding mat_def by (auto simp: vec_def)
    qed
  qed
qed

lemma mat_eqI:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and id: "\<And> i j. i < nc \<Longrightarrow> j < nr \<Longrightarrow> m1 ! i ! j = m2 ! i ! j"
  shows "m1 = m2"
  unfolding mat_eq[OF wf1 wf2] using id by auto

lemma vec_eq:
  assumes wf1: "vec n v1"
  and wf2: "vec n v2"
  shows "(v1 = v2) = (\<forall> i < n. v1 ! i = v2 ! i)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule nth_equalityI)
    from wf1 wf2 show "length v1 = length v2" unfolding vec_def by simp
  next
    from \<open>?r\<close> wf1 show "\<And>i. i < length v1 \<Longrightarrow> v1 ! i = v2 ! i" unfolding vec_def by simp
  qed
qed

lemma vec_eqI:
  assumes wf1: "vec n v1"
  and wf2: "vec n v2"
  and id: "\<And> i. i < n \<Longrightarrow> v1 ! i = v2 ! i"
  shows "v1 = v2"
  unfolding vec_eq[OF wf1 wf2] using id by auto


lemma row_col: assumes "mat nr nc m"
  and "i < nr" and "j < nc"
  shows "row m i ! j = col m j ! i"
using assms unfolding mat_def row_def col_def
  by auto

lemma col_index: assumes m: "mat nr nc m"
  and i: "i < nc"
  shows "col m i = map (\<lambda> j. m ! i ! j) [0 ..< nr]"
proof -
  from m[unfolded mat_def] i
  have nr: "nr = length (m ! i)" by (auto simp: vec_def)
  show ?thesis unfolding nr col_def
    by (rule map_nth[symmetric])
qed

lemma row_index: assumes m: "mat nr nc m"
  and i: "i < nr"
  shows "row m i = map (\<lambda> j. m ! j ! i) [0 ..< nc]"
proof -
  note rc = row_col[OF m i]
  from row[OF m i] have id: "length (row m i) = nc" unfolding vec_def by simp
  from map_nth[of "row m i"]
  have "row m i = map (\<lambda> j. row m i ! j) [0 ..< nc]" unfolding id by simp
  also have "... = map (\<lambda> j. m ! j ! i) [0 ..< nc]" using rc[unfolded col_def] by auto
  finally show ?thesis .
qed


lemma mat_row_eq:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  shows "(m1 = m2) = (\<forall> i < nr. row m1 i = row m2 i)" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (rule nth_equalityI)
    show "length m1 = length m2" using wf1 wf2 unfolding mat_def by auto
  next
    show "m1 ! i = m2 ! i" if i: "i < length m1" for i
    proof -
      show "m1 ! i = m2 ! i"
      proof (rule nth_equalityI)
        show "length (m1 ! i) = length (m2 ! i)" using wf1 wf2 i unfolding mat_def by (auto simp: vec_def)
      next
        show "m1 ! i ! j = m2 ! i ! j" if j: "j < length (m1 ! i)" for j
        proof -
          from i j wf1 have i1: "i < nc" and j1: "j < nr" unfolding mat_def by (auto simp: vec_def)
          from \<open>?r\<close> j1 have "col m1 i ! j = col m2 i ! j"
            by (simp add: row_col[OF wf1 j1 i1, symmetric] row_col[OF wf2 j1 i1, symmetric])
          thus "m1 ! i ! j = m2 ! i ! j" unfolding col_def .
        qed
      qed
    qed
  qed
qed

lemma mat_row_eqI:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and id: "\<And> i. i < nr \<Longrightarrow> row m1 i = row m2 i"
  shows "m1 = m2"
  unfolding mat_row_eq[OF wf1 wf2] using id by auto

lemma row_transpose_is_col[simp]:   assumes wf: "mat nr nc m"
  and i: "i < nc"
  shows "row (transpose nr m) i = col m i"
proof -
  have len: "length (row (transpose nr m) i) = length (col m i)"
    using transpose[OF wf]  wf i  unfolding row_def col_def mat_def by (auto simp: vec_def)
  show ?thesis
  proof (rule nth_equalityI[OF len])
    fix j
    assume "j < length (row (transpose nr m) i)"
    hence j: "j < nr" using transpose[OF wf] wf i unfolding row_def col_def mat_def by (auto simp: vec_def)
    show "row (transpose nr m) i ! j = col m i ! j"
      by (simp only: row_col[OF transpose[OF wf] i j],
        simp only: col_transpose_is_row[OF wf j],
        simp only: row_col[OF wf j i])
  qed
qed


lemma matT_vec_mult_to_scalar:
  assumes "mat nr nc m"
  and "vec nr v"
  and "i < nc"
  shows "matT_vec_multI ze pl ti m v ! i = scalar_prodI ze pl ti (col m i) v"
unfolding matT_vec_multI_def using assms unfolding mat_def col_def by (auto simp: vec_def)

lemma mat_vec_mult_index:
  assumes wf: "mat nr nc m"
  and wfV: "vec nc v"
  and i: "i < nr"
  shows "matT_vec_multI ze pl ti (transpose nr m) v ! i = scalar_prodI ze pl ti (row m i) v"
by (simp only:matT_vec_mult_to_scalar[OF transpose[OF wf] wfV i],
  simp only: col_transpose_is_row[OF wf i])

lemma mat_mult_index[simp] :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  and j: "j < nc"
  shows "mat_multI ze pl ti nr m1 m2 ! j ! i = scalar_prodI ze pl ti (row m1 i) (col m2 j)"
proof -
  have jlen: "j < length m2" using wf2 j unfolding mat_def by auto
  have wfj: "vec n (m2 ! j)" using jlen j wf2 unfolding mat_def by auto
  show ?thesis
    unfolding mat_multI_def
    by (simp add: jlen, simp only: mat_vec_mult_index[OF wf1 wfj i], unfold col_def, simp)
qed

lemma col_mat_mult_index :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and j: "j < nc"
  shows "col (mat_multI ze pl ti nr m1 m2) j = map (\<lambda> i. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nr]" (is "col ?l j = ?r")
proof -
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  have len: "length (col ?l j) = length ?r" and nr: "length (col ?l j) = nr" using wf1 wf2 wf12 j unfolding mat_def col_def by (auto simp: vec_def)
  show ?thesis by (rule nth_equalityI[OF len], simp add: j nr, unfold col_def, simp only:
    mat_mult_index[OF wf1 wf2 _ j], simp add: col_def)
qed

lemma row_mat_mult_index :
  assumes wf1: "mat nr n m1"
  and wf2: "mat n nc m2"
  and i: "i < nr"
  shows "row (mat_multI ze pl ti nr m1 m2) i = map (\<lambda> j. scalar_prodI ze pl ti (row m1 i) (col m2 j)) [0 ..< nc]" (is "row ?l i = ?r")
proof -
  have wf12: "mat nr nc ?l" by (rule mat_mult[OF wf1 wf2])
  hence lenL: "length ?l = nc" unfolding mat_def by simp
  have len: "length (row ?l i) = length ?r" and nc: "length (row ?l i) = nc" using wf1 wf2 wf12 i unfolding mat_def row_def by (auto simp: vec_def)
  show ?thesis by (rule nth_equalityI[OF len], simp add: i nc, unfold row_def, simp add: lenL, simp only:
    mat_mult_index[OF wf1 wf2 i], simp add: row_def)
qed

lemma scalar_prod_cons:
  "scalar_prodI ze pl ti (a # as) (b # bs) = pl (ti a b) (scalar_prodI ze pl ti as bs)"
unfolding scalar_prodI_def by auto


lemma vec_plus_index[simp]:
  assumes wf1: "vec nr v1"
  and wf2: "vec nr v2"
  and i: "i < nr"
  shows "vec_plusI pl v1 v2 ! i = pl (v1 ! i)  (v2 ! i)"
using wf1 wf2 i
unfolding vec_def vec_plusI_def
proof (induct v1 arbitrary: i v2 nr, simp)
  case (Cons a v11)
  from Cons obtain b v22 where v2: "v2 = b # v22" by (cases v2, auto)
  from v2 Cons obtain nrr where nr: "nr = Suc nrr" by (force)
  from Cons show ?case
    by (cases i, simp add: v2, auto simp: v2 nr)
qed

lemma mat_map_index[simp]: assumes wf: "mat nr nc m" and i: "i < nc" and j: "j < nr"
  shows "mat_map f m ! i ! j = f (m ! i ! j)"
proof -
  from wf i have i: "i < length m" unfolding mat_def by auto
  with wf j have j: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "mat_map f m ! i ! j = map (map f) m ! i ! j" unfolding mat_map_def vec_map_def by auto
  also have "\<dots> = map f (m ! i) ! j" using i by auto
  also have "\<dots> = f (m ! i ! j)" using j by auto
  finally show ?thesis .
qed


lemma mat_plus_index[simp]:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  and j: "j < nr"
  shows "mat_plusI pl m1 m2 ! i ! j = pl (m1 ! i ! j) (m2 ! i ! j)"
using wf1 wf2 i
unfolding mat_plusI_def mat_def
proof (simp, induct m1 arbitrary: m2 i nc, simp)
  case (Cons v1 m11)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2, rule vec_plus_index[where nr = nr], (auto simp: Cons j m2)[3])
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma col_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nc"
  shows "col (mat_plusI pl m1 m2) i = vec_plusI pl (col m1 i) (col m2 i)"
using assms
unfolding mat_plusI_def col_def mat_def
proof (induct m1 arbitrary: m2 nc i, simp)
  case (Cons v m1)
  from Cons obtain v2 m22 where m2: "m2 = v2 # m22" by (cases m2, auto)
  from m2 Cons obtain ncc where nc: "nc = Suc ncc" by force
  show ?case
  proof (cases i, simp add: m2)
    case (Suc ii)
    with Cons show ?thesis using m2 nc by auto
  qed
qed

lemma transpose_index[simp]: assumes wf: "mat nr nc m"
  and i: "i < nr"
  and j: "j < nc"
  shows "transpose nr m ! i ! j = m ! j ! i"
proof -
  have "transpose nr m ! i ! j = col (transpose nr m) i ! j" unfolding col_def by simp
  also have "\<dots> = row m i ! j" using col_transpose_is_row[OF wf i] by simp
  also have "\<dots> = m ! j ! i" unfolding row_def using wf j unfolding mat_def by (auto simp: vec_def)
  finally show ?thesis .
qed

lemma transpose_mat_plus: assumes wf: "mat nr nc m1" "mat nr nc m2"
  shows "transpose nr (mat_plusI pl m1 m2) = mat_plusI pl (transpose nr m1) (transpose nr m2)" (is "?l = ?r")
proof (rule mat_eqI)
  fix i j
  assume i: "i < nr" and j: "j < nc"
  note [simp] = transpose_index[OF _ this] mat_plus_index[OF _ _ j i] mat_plus_index[OF _ _ this]
  show "?l ! i ! j = ?r ! i ! j" using wf by simp
qed (auto intro: wf)

lemma row_mat_plus: assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and i: "i < nr"
  shows "row (mat_plusI pl m1 m2) i = vec_plusI pl (row m1 i) (row m2 i)"
  by (
    simp only: col_transpose_is_row[OF mat_plus[OF wf1 wf2] i, symmetric],
    simp only: transpose_mat_plus[OF wf1 wf2],
    simp only: col_mat_plus[OF transpose[OF wf1] transpose[OF wf2] i],
    simp only: col_transpose_is_row[OF wf1 i],
    simp only: col_transpose_is_row[OF wf2 i])


lemma col_mat1: assumes "i < nr"
  shows "col (mat1I ze on nr) i = vec1I ze on nr i"
unfolding mat1I_def col_def using assms by auto


lemma mat1_index: assumes i: "i < n" and j: "j < n"
  shows "mat1I ze on n ! i ! j = (if i = j then on else ze)"
  by (simp add: col_mat1[OF i, simplified col_def] vec1_index[OF j])

lemma transpose_mat1: "transpose nr (mat1I ze on nr) = (mat1I ze on nr)" (is "?l = ?r")
proof (rule mat_eqI)
  fix i j
  assume i:"i < nr" and j: "j < nr"
  note [simp] = transpose_index[OF _ this] mat1_index[OF this] mat1_index[OF j i]
  show "?l ! i ! j = ?r ! i ! j" by auto
qed auto

lemma row_mat1: assumes i: "i < nr"
  shows "row (mat1I ze on nr) i = vec1I ze on nr i"
by (simp only: col_transpose_is_row[OF mat1 i, symmetric],
  simp only: transpose_mat1,
  simp only: col_mat1[OF i])

lemma sub_mat_index:
  assumes wf: "mat nr nc m"
  and sr: "sr \<le> nr"
  and sc: "sc \<le> nc"
  and j: "j < sr"
  and i: "i < sc"
  shows "sub_mat sr sc m ! i ! j = m ! i ! j"
proof -
  from assms have im: "i < length m" unfolding mat_def by auto
  from assms have jm: "j < length (m ! i)" unfolding mat_def by (auto simp: vec_def)
  have "sub_mat sr sc m ! i ! j = map (take sr) (take sc m) ! i ! j"
    unfolding sub_mat_def sub_vec_def by auto
  also have "\<dots> = take sr (m ! i) ! j" using i im by auto
  also have "\<dots> = m ! i ! j" using j jm by auto
  finally show ?thesis .
qed

subsection \<open>lemmas requiring properties of plus, times, ...\<close>

context plus
begin

abbreviation vec_plus :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
where "vec_plus \<equiv> vec_plusI plus"

abbreviation mat_plus :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_plus \<equiv> mat_plusI plus"
end

context semigroup_add
begin
lemma vec_plus_assoc: assumes vec: "vec nr u" "vec nr v" "vec nr w"
 shows "vec_plus u (vec_plus v w) = vec_plus (vec_plus u v) w"
proof (rule vec_eqI)
  fix i
  assume i: "i < nr"
  note [simp] = vec_plus_index[OF _ _ i]
  from vec
  show "vec_plus u (vec_plus v w) ! i = vec_plus (vec_plus u v) w ! i"
    by (auto simp: add.assoc)
qed (auto intro: vec)

lemma mat_plus_assoc: assumes wf: "mat nr nc m1" "mat nr nc m2" "mat nr nc m3"
  shows "mat_plus m1 (mat_plus m2 m3) = mat_plus (mat_plus m1 m2) m3" (is "?l = ?r")
proof (rule mat_eqI)
  fix i j
  assume "i < nc" "j < nr"
  note [simp] = mat_plus_index[OF _ _ this]
  show "?l ! i ! j = ?r ! i ! j" using wf by (simp add: add.assoc)
qed (auto simp: wf)
end

context ab_semigroup_add
begin
lemma vec_plus_comm: "vec_plus x y = vec_plus y x"
unfolding vec_plusI_def
proof (induct x arbitrary: y)
  case (Cons a x)
  thus ?case
    by (cases y, auto simp: add.commute)
qed simp


lemma mat_plus_comm: "mat_plus m1 m2 = mat_plus m2 m1"
unfolding mat_plusI_def
proof (induct m1 arbitrary: m2)
  case (Cons v m1) note oCons = this
  thus ?case
  proof (cases m2)
    case (Cons w m2a)
    hence "mat_plus (v # m1) m2 = vec_plus v w # mat_plus m1 m2a" by (auto simp: mat_plusI_def)
    also have "\<dots> = vec_plus w v # mat_plus m1 m2a" using vec_plus_comm by auto
    finally show ?thesis using Cons oCons by (auto simp: mat_plusI_def)
  qed simp
qed simp
end

context zero
begin
abbreviation vec0 :: "nat \<Rightarrow> 'a vec"
where "vec0 \<equiv> vec0I zero"

abbreviation mat0 :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat"
where "mat0 \<equiv> mat0I zero"
end

context monoid_add
begin
lemma vec0_plus[simp]: assumes "vec nr u" shows "vec_plus (vec0 nr) u = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_vec0[simp]: assumes "vec nr u" shows "vec_plus u (vec0 nr) = u"
using assms
unfolding vec_def vec_plusI_def vec0I_def
proof (induct nr arbitrary: u)
 case (Suc nn) thus ?case by (cases u, auto)
qed simp

lemma plus_mat0[simp]: assumes wf: "mat nr nc m" shows "mat_plus m (mat0 nr nc) = m" (is "?l = ?r")
proof (rule mat_eqI)
  fix i j
  assume "i < nc" "j < nr"
  note [simp] = mat_plus_index[OF _ _ this] mat0_index[OF this]
  show "?l ! i ! j = ?r ! i ! j" using wf by simp
qed (insert wf, auto)

lemma mat0_plus[simp]: assumes wf: "mat nr nc m" shows "mat_plus (mat0 nr nc) m = m" (is "?l = ?r")
proof (rule mat_eqI)
  fix i j
  assume "i < nc" "j < nr"
  note [simp] = mat_plus_index[OF _ _ this] mat0_index[OF this]
  show "?l ! i ! j = ?r ! i ! j" using wf by simp
qed (insert wf, auto)
end

context semiring_0
begin
abbreviation scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a"
where "scalar_prod \<equiv> scalar_prodI zero plus times"

abbreviation mat_mult :: "nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
where "mat_mult \<equiv> mat_multI zero plus times"

lemma scalar_prod: "scalar_prod v1 v2 = sum_list (map (\<lambda>(x,y). x * y) (zip v1 v2))"
proof -
  obtain z where z: "zip v1 v2 = z" by auto
  show ?thesis unfolding scalar_prodI_def z
    by (induct z, auto)
qed

lemma scalar_prod_last: assumes "length v1 = length v2"
  shows "scalar_prod (v1 @ [x1]) (v2 @ [x2]) = x1 * x2 + scalar_prod v1 v2"
using assms
proof (induct v1 arbitrary: v2)
  case (Cons y1 w1)
  from Cons(2) obtain y2 w2 where v2: "v2 = Cons y2 w2" and len: "length w1 = length w2" by (cases v2, auto)
  from Cons(1)[OF len] have rec: "scalar_prod (w1 @ [x1]) (w2 @ [x2]) = x1 * x2 + scalar_prod w1 w2" .
  have "scalar_prod ((y1 # w1) @ [x1]) (v2 @ [x2]) =
    (y1 * y2 + x1 * x2) + scalar_prod w1 w2" by (simp add: scalar_prod_cons v2 rec add.assoc)
  also have "\<dots> = (x1 * x2 + y1 * y2) + scalar_prod w1 w2" using add.commute[of "x1 * x2"] by simp
  also have "\<dots> = x1 * x2 + (scalar_prod (y1 # w1) v2)" by (simp add: add.assoc scalar_prod_cons v2)
  finally show ?case .
qed (simp add: scalar_prodI_def)

lemma scalar_product_assoc:
  assumes wfm: "mat nr nc m"
  and wfr: "vec nr r"
  and wfc: "vec nc c"
  shows "scalar_prod (map (\<lambda>k. scalar_prod r (col m k)) [0..<nc]) c = scalar_prod r (map (\<lambda>k. scalar_prod (row m k) c) [0..<nr])"
using wfm wfc
unfolding col_def
proof (induct m arbitrary: nc c)
  case Nil
  hence nc: "nc = 0" unfolding mat_def by (auto)
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  let ?term = "\<lambda> r :: 'a vec. zip r (map (\<lambda> k. zero) [0..<length r])"
  let ?fun = "\<lambda> (x,y). plus (times x y)"
  have "foldr ?fun (?term r) zero = zero"
  proof (induct r, simp)
    case (Cons d r)
    have "foldr ?fun (?term (d # r)) zero = foldr ?fun ( (d,zero) # ?term r) zero" by (simp only: map_replicate_trivial, simp)
    also have "\<dots> = zero" using Cons by simp
    finally show ?case .
  qed
  hence "zero = foldr ?fun (zip r (map (\<lambda> k. zero) [0..<nr])) zero" by (simp add: nr)
  with Nil nc show ?case
    by (simp add: scalar_prodI_def row_def)
next
  case (Cons v m)
  from this obtain ncc where nc: "nc = Suc ncc" and wf: "mat nr ncc m" unfolding mat_def by (auto simp: vec_def)
  from nc \<open>vec nc c\<close> obtain a cc where c: "c = a # cc" and wfc: "vec ncc cc" unfolding vec_def by (cases c, auto)
  have rec: "scalar_prod (map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]) cc = scalar_prod r (map (\<lambda> k. scalar_prod (row m k) cc) [0..<nr])"
    by (rule Cons, rule wf, rule wfc)
  have id: "map (\<lambda>k. scalar_prod r ((v # m) ! k)) [0..<Suc ncc] = scalar_prod r v # map (\<lambda> k. scalar_prod r (m ! k)) [0..<ncc]" by (induct ncc, auto)
  from wfr have nr: "nr = length r" unfolding vec_def by auto
  with Cons have v: "length v = length r" unfolding mat_def by (auto simp: vec_def)
  have "\<forall> i < nr. vec ncc (row m i)" by (intro allI impI, rule row[OF wf], simp)
  obtain tm where tm: "tm = transpose nr m" by auto
  hence idk: "\<forall> k < length r. row m k = tm ! k" using col_transpose_is_row[OF wf] unfolding col_def by (auto simp: nr)
  hence idtm1: "map (\<lambda>k. scalar_prod (row m k) cc) [0..<length r] = map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r]"
    and idtm2: "map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (row m k) cc)) [0..<length r] = map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r]" by auto
  from tm transpose[OF wf] have "mat ncc nr tm" by simp
  with nr have "length tm = length r" and  "(\<forall> i < length r. length (tm ! i) = ncc)" unfolding mat_def by (auto simp: vec_def)
  with v have main: "plus (times (scalar_prod r v) a) (scalar_prod r (map (\<lambda>k. scalar_prod (tm ! k) cc) [0..<length r])) =
    scalar_prod r (map (\<lambda>k. plus (times (v ! k) a) (scalar_prod (tm ! k) cc)) [0..<length r])"
  proof (induct r arbitrary: v tm)
    case Nil
    thus ?case by (auto simp: scalar_prodI_def row_def)
  next
    case (Cons b r)
    from this obtain c vv where v: "v = c # vv" and vvlen: "length vv = length r" by (cases v, auto)
    from Cons obtain u mm where tm: "tm = u # mm" and mmlen: "length mm = length r"  by (cases tm, auto)
    from Cons tm have argLen: "\<forall> i < length r. length (mm ! i) = ncc" by auto
    have rec: "plus (times (scalar_prod r vv) a) (scalar_prod r (map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r])) =
     scalar_prod r (map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r])"
      (is "plus (times ?rv a) ?recl = ?recr")
      by (rule Cons, auto simp: vvlen mmlen argLen)
    have id: "map (\<lambda>k. scalar_prod ((u # mm) ! k) cc) [0..<length (b # r)] = scalar_prod u cc # map (\<lambda>k. scalar_prod (mm ! k) cc) [0..<length r]"
      by (simp, induct r, auto)
    have id2: "map (\<lambda>k. plus (times ((c # vv) ! k) a) (scalar_prod ((u # mm) ! k) cc)) [0..<length (b # r)] =
               (plus (times c a) (scalar_prod u cc)) #
               map (\<lambda>k. plus (times (vv ! k) a) (scalar_prod (mm ! k) cc)) [0..<length r]"
      by (simp, induct r, auto)
    show ?case proof (simp only: v tm, simp only: id, simp only: id2, simp only: scalar_prod_cons)
      let ?uc = "scalar_prod u cc"
      let ?bca = "times (times b c) a"
      have "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (plus ?bca (times ?rv a)) (plus (times b ?uc) ?recl)"
        by (simp add: distrib_right)
      also have "\<dots> = plus (plus ?bca (times ?rv a)) (plus ?recl (times b ?uc))" by (simp add: add.commute)
      also have "\<dots> = plus ?bca (plus (plus (times ?rv a) ?recl) (times b ?uc))" by (simp add: add.assoc)
      also have "\<dots> = plus ?bca (plus ?recr (times b ?uc))" by (simp only: rec)
      also have "\<dots> = plus ?bca (plus (times b ?uc) ?recr)" by (simp add: add.commute)
      also have "\<dots> = plus (times b (plus (times c a) ?uc)) ?recr" by (simp add: distrib_left mult.assoc add.assoc)
      finally show "plus (times (plus (times b c) ?rv) a) (plus (times b ?uc) ?recl) = plus (times b (plus (times c a) ?uc)) ?recr" .
    qed
  qed
  show ?case
    by (simp only: c scalar_prod_cons, simp only: nc, simp only: id, simp only: scalar_prod_cons, simp only: rec, simp only: nr, simp only: idtm1 idtm2, simp only: main, simp only: idtm2[symmetric], simp add: row_def scalar_prod_cons)
qed


lemma mat_mult_assoc:
  assumes wf1: "mat nr n1 m1"
  and wf2: "mat n1 n2 m2"
  and wf3: "mat n2 nc m3"
  shows "mat_mult nr (mat_mult nr m1 m2) m3 = mat_mult nr m1 (mat_mult n1 m2 m3)" (is "?m12_3 = ?m1_23")
proof -
  note wf = wf1 wf2 wf3
  let ?m12 = "mat_mult nr m1 m2"
  let ?m23 = "mat_mult n1 m2 m3"
  from wf have
    wf12: "mat nr n2 ?m12" and
    wf23: "mat n1 nc ?m23" and
    wf1_23: "mat nr nc ?m1_23" and
    wf12_3: "mat nr nc ?m12_3" by auto
  show ?thesis
  proof (rule mat_col_eqI, unfold col_def)
    fix i
    assume i: "i < nc"
    with wf1_23 wf12_3 wf3 have len: "length (?m12_3 ! i) = length (?m1_23 ! i)" and ilen: "i < length m3" unfolding mat_def by (auto simp: vec_def)
    show "?m12_3 ! i = ?m1_23 ! i"
    proof (rule nth_equalityI[OF len])
      fix j
      assume jlen: "j < length (?m12_3 ! i)"
      with wf12_3 i have j: "j < nr" unfolding mat_def by (auto simp: vec_def)
      show "?m12_3 ! i ! j = ?m1_23 ! i ! j"
        by (unfold mat_mult_index[OF wf12 wf3 j i]
              mat_mult_index[OF wf1 wf23 j i]
              row_mat_mult_index[OF wf1 wf2 j]
              col_mat_mult_index[OF wf2 wf3 i]
              scalar_product_assoc[OF wf2 row[OF wf1 j] col[OF wf3 i]], simp)
    qed
  qed (insert wf, auto)
qed

lemma mat_mult_assoc_n:
  assumes wf1: "mat n n m1"
  and wf2: "mat n n m2"
  and wf3: "mat n n m3"
  shows "mat_mult n (mat_mult n m1 m2) m3 = mat_mult n m1 (mat_mult n m2 m3)"
using assms
 by (rule mat_mult_assoc)


lemma scalar_left_zero: "scalar_prod (vec0 nn) v = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct nn arbitrary: v)
  case (Suc m)
  thus ?case by (cases v, auto)
qed simp

lemma scalar_right_zero: "scalar_prod v (vec0 nn) = zero"
  unfolding vec0I_def scalar_prodI_def
proof (induct v arbitrary: nn)
  case (Cons a vv)
  thus ?case by (cases nn, auto)
qed simp

lemma mat0_mult_left: assumes wf: "mat nc ncc m"
  shows "mat_mult nr (mat0 nr nc) m = (mat0 nr ncc)"
proof (rule mat_eqI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr (mat0 nr nc) m ! i ! j = mat0 nr ncc ! i ! j"
    by (unfold mat_mult_index[OF mat0 wf j i] mat0_index[OF i j] mat0_row[OF j] scalar_left_zero, simp)
qed (auto simp: wf)


lemma mat0_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat0 nc ncc) = (mat0 nr ncc)"
proof (rule mat_eqI)
  fix i j
  assume i: "i < ncc" and j: "j < nr"
  show "mat_mult nr m (mat0 nc ncc) ! i ! j = mat0 nr ncc ! i ! j"
    by (unfold mat_mult_index[OF wf mat0 j i] mat0_index[OF i j] mat0_col[OF i] scalar_right_zero, simp)
qed (insert wf, auto)

lemma scalar_vec_plus_distrib_right:
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod u (vec_plus v w) = plus (scalar_prod u v) (scalar_prod u w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add.commute[of _ "times a c"] distrib_left add.assoc[symmetric])
qed simp

lemma scalar_vec_plus_distrib_left:
  assumes wf1: "vec nr u"
  assumes wf2: "vec nr v"
  assumes wf3: "vec nr w"
  shows "scalar_prod (vec_plus u v) w = plus (scalar_prod u w) (scalar_prod v w)"
using assms
unfolding vec_def scalar_prodI_def vec_plusI_def
proof (induct nr arbitrary: u v w)
  case (Suc n)
  from Suc obtain a uu where u: "u = a # uu" by (cases u, auto)
  from Suc obtain b vv where v: "v = b # vv" by (cases v, auto)
  from Suc obtain c ww where w: "w = c # ww" by (cases w, auto)
  from Suc u v w have lu: "length uu = n" and lv: "length vv = n" and lw: "length ww = n" by auto
  show ?case by (simp only: u v w, simp, simp only: Suc(1)[OF lu lv lw], simp add: add.commute[of _ "times b c"] distrib_right add.assoc[symmetric])
qed simp

lemma mat_mult_plus_distrib_right:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nc ncc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr m1 (mat_plus m2 m3) = mat_plus (mat_mult nr m1 m2) (mat_mult nr m1 m3)" (is "mat_mult nr m1 ?m23 = mat_plus ?m12 ?m13")
proof -
  note wf = wf1 wf2 wf3
  let ?m1_23 = "mat_mult nr m1 ?m23"
  let ?m12_13 = "mat_plus ?m12 ?m13"
  from wf have
    wf23: "mat nc ncc ?m23" and
    wf12: "mat nr ncc ?m12" and
    wf13: "mat nr ncc ?m13" and
    wf1_23: "mat nr ncc ?m1_23" and
    wf12_13: "mat nr ncc ?m12_13" by auto
  show ?thesis
  proof (rule mat_eqI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m1_23 ! i ! j = ?m12_13 ! i ! j"
      by (unfold mat_mult_index[OF wf1 wf23 j i]
           mat_plus_index[OF wf12 wf13 i j]
           mat_mult_index[OF wf1 wf2 j i]
           mat_mult_index[OF wf1 wf3 j i]
           col_mat_plus[OF wf2 wf3 i],
        rule scalar_vec_plus_distrib_right[OF row[OF wf1 j] col[OF wf2 i] col[OF wf3 i]])
  qed (insert wf, auto)
qed

lemma mat_mult_plus_distrib_left:
  assumes wf1: "mat nr nc m1"
  and wf2: "mat nr nc m2"
  and wf3: "mat nc ncc m3"
  shows "mat_mult nr (mat_plus m1 m2) m3 = mat_plus (mat_mult nr m1 m3) (mat_mult nr m2 m3)" (is "mat_mult nr ?m12 _ = mat_plus ?m13 ?m23")
proof -
  note wf = wf1 wf2 wf3
  let ?m12_3 = "mat_mult nr ?m12 m3"
  let ?m13_23 = "mat_plus ?m13 ?m23"
  from wf have
    wf12: "mat nr nc ?m12" and
    wf13: "mat nr ncc ?m13" and
    wf23: "mat nr ncc ?m23" and
    wf12_3: "mat nr ncc ?m12_3" and
    wf13_23: "mat nr ncc ?m13_23" by auto
  show ?thesis
  proof (rule mat_eqI)
    fix i j
    assume i: "i < ncc" and j: "j < nr"
    show "?m12_3 ! i ! j = ?m13_23 ! i ! j"
      by (unfold mat_mult_index[OF wf12 wf3 j i]
           mat_plus_index[OF wf13 wf23 i j]
           mat_mult_index[OF wf1 wf3 j i]
           mat_mult_index[OF wf2 wf3 j i]
           row_mat_plus[OF wf1 wf2 j],
           rule scalar_vec_plus_distrib_left[OF row[OF wf1 j] row[OF wf2 j] col[OF wf3 i]])
  qed (insert wf, auto)
qed
end

context semiring_1
begin
abbreviation vec1 :: "nat \<Rightarrow> nat \<Rightarrow> 'a vec"
where "vec1 \<equiv> vec1I zero one"

abbreviation mat1 :: "nat \<Rightarrow> 'a mat"
where "mat1 \<equiv> mat1I zero one"

abbreviation mat_pow where "mat_pow \<equiv> mat_powI (0 :: 'a) 1 (+) (*)"


lemma scalar_left_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod (vec1 nn i) v = v ! i"
  using assms
  unfolding vec1I_def vec_def
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using scalar_left_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add.commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma scalar_right_one: assumes wf: "vec nn v"
  and i: "i < nn"
  shows "scalar_prod v (vec1 nn i) = v ! i"
  using assms
  unfolding vec1I_def vec_def
proof (induct nn arbitrary: v i)
  case (Suc n) note oSuc = this
  from this obtain a vv where v: "v = a # vv" and lvv: "length vv = n" by (cases v, auto)
  show ?case
  proof (cases i)
    case 0
    thus ?thesis using scalar_right_zero unfolding vec0I_def by (simp add: v scalar_prod_cons add.commute)
  next
    case (Suc ii)
    thus ?thesis using oSuc lvv v by (auto simp: scalar_prod_cons)
  qed
qed blast


lemma mat1_mult_right: assumes wf: "mat nr nc m"
  shows "mat_mult nr m (mat1 nc) = m"
proof (rule mat_eqI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr m (mat1 nc) ! i ! j = m ! i ! j"
    by (unfold mat_mult_index[OF wf mat1 j i]
     col_mat1[OF i]
     scalar_right_one[OF row[OF wf j] i]
     row_col[OF wf j i],
     unfold col_def, simp)
qed (insert wf, auto)


lemma mat1_mult_left: assumes wf: "mat nr nc m"
  shows "mat_mult nr (mat1 nr) m = m"
proof (rule mat_eqI)
  fix i j
  assume i: "i < nc" and j: "j < nr"
  show "mat_mult nr (mat1 nr) m ! i ! j = m ! i ! j"
    by (unfold mat_mult_index[OF mat1 wf j i]
      row_mat1[OF j]
      scalar_left_one[OF col[OF wf i] j], unfold col_def, simp)
qed (insert wf, auto)
end


declare vec0[simp del] mat0[simp del] vec0_plus[simp del] plus_vec0[simp del] plus_mat0[simp del]

subsection \<open>Connection to HOL-Algebra\<close>

definition mat_monoid :: "nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> (('a :: {plus,zero}) mat,'b) monoid_scheme" where
  "mat_monoid nr nc b \<equiv> \<lparr>
    carrier = Collect (mat nr nc),
    mult = mat_plus,
    one = mat0 nr nc,
    \<dots> = b\<rparr>"

definition mat_ring :: "nat \<Rightarrow> 'b \<Rightarrow> (('a :: semiring_1) mat,'b) ring_scheme" where
  "mat_ring n b \<equiv> \<lparr>
    carrier = Collect (mat n n),
    mult = mat_mult n,
    one = mat1 n,
    zero = mat0 n n,
    add = mat_plus,
    \<dots> = b\<rparr>"

lemma mat_monoid: "monoid (mat_monoid nr nc b :: (('a :: monoid_add) mat,'b)monoid_scheme)"
  by (unfold_locales, auto simp: mat_plus_assoc mat_monoid_def plus_mat0)

lemma mat_group: "group (mat_monoid nr nc b :: (('a :: group_add) mat,'b)monoid_scheme)" (is "group ?G")
proof -
  interpret monoid ?G by (rule mat_monoid)
  {
    fix m :: "'a mat"
    assume wf: "mat nr nc m"
    let ?m' = "mat_map uminus m"
    have "\<exists> m'. mat nr nc m' \<and> mat_plus m' m = mat0 nr nc \<and> mat_plus m m' = mat0 nr nc"
    proof (rule exI[of _ ?m'], intro conjI mat_eqI)
      fix i j
      assume "i < nc" "j < nr"
      note [simp] = mat_plus_index[OF _ _ this] mat_map_index[OF _ this] mat0_index[OF this]
      show "mat_plus ?m' m ! i ! j = mat0 nr nc ! i ! j" using wf by simp
      show "mat_plus m ?m' ! i ! j = mat0 nr nc ! i ! j" using wf by simp
    qed (auto intro: wf)
  } note Units = this
  show ?thesis
    by (unfold_locales, auto simp: mat_monoid_def Units_def Units)
qed

lemma mat_comm_monoid:
  "comm_monoid (mat_monoid nr nc b :: (('a :: comm_monoid_add) mat,'b)monoid_scheme)" (is "comm_monoid ?G")
proof -
  interpret monoid ?G by (rule mat_monoid)
  show ?thesis
    by (unfold_locales, insert mat_plus_comm, auto simp: mat_monoid_def)
qed

lemma mat_comm_group:
  "comm_group (mat_monoid nr nc b :: (('a :: ab_group_add) mat,'b)monoid_scheme)" (is "comm_group ?G")
proof -
  interpret group ?G by (rule mat_group)
  interpret comm_monoid ?G by (rule mat_comm_monoid)
  show ?thesis ..
qed

lemma mat_abelian_monoid: "abelian_monoid (mat_ring n b :: (('a :: semiring_1) mat,'b)ring_scheme)"
  unfolding mat_ring_def
  unfolding abelian_monoid_def using mat_comm_monoid[of n n, unfolded mat_monoid_def mat_ring_def]
  by simp

lemma mat_abelian_group: "abelian_group (mat_ring n b :: (('a :: {ab_group_add,semiring_1}) mat,'b)ring_scheme)"
  (is "abelian_group ?R")
proof -
  interpret abelian_monoid ?R by (rule mat_abelian_monoid)
  show ?thesis
    apply unfold_locales
    apply (rule group.Units)
    by (metis mat_group mat_monoid_def mat_ring_def partial_object.simps(1) ring.simps(1) ring.simps(2))
qed

lemma mat_semiring: "semiring (mat_ring n b :: (('a :: semiring_1) mat,'b)ring_scheme)"
  (is "semiring ?R")
proof -
  interpret abelian_monoid ?R by (rule mat_abelian_monoid)
  show ?thesis
    by (unfold_locales, unfold mat_ring_def, insert
      mat_mult_assoc mat0_mult_left mat0_mult_right mat1_mult_left mat1_mult_right
      mat_mult_plus_distrib_left mat_mult_plus_distrib_right, auto)
qed

lemma mat_ring: "ring (mat_ring n b :: (('a :: ring_1) mat,'b)ring_scheme)"
  (is "ring ?R")
proof -
  interpret abelian_group ?R by (rule mat_abelian_group)
  show ?thesis
    by (unfold_locales, unfold mat_ring_def, insert
      mat_mult_assoc mat1_mult_left mat1_mult_right mat_mult_plus_distrib_left
      mat_mult_plus_distrib_right, auto)
qed

lemma mat_pow_ring_pow: assumes mat: "mat n n (m :: ('a :: semiring_1)mat)" shows "mat_pow n m k = m [^]\<^bsub>mat_ring n b\<^esub> k"
  (is "_ = m [^]\<^bsub>?C\<^esub> k")
proof -
  interpret semiring ?C by (rule mat_semiring)
  show ?thesis
    by (induct k, auto, auto simp: mat_ring_def)
qed


end
