theory Cayley_Hamilton_Compatible
  imports
    Rings2
    Cayley_Hamilton.Cayley_Hamilton
    Gauss_Jordan.Determinants2
begin


subsection \<open>Compatibility layer btw @{theory Cayley_Hamilton.Square_Matrix} and @{theory Gauss_Jordan.Determinants2} \<close>

hide_const (open) Square_Matrix.det
hide_const (open) Square_Matrix.row
hide_const (open) Square_Matrix.col
hide_const (open) Square_Matrix.transpose
hide_const (open) Square_Matrix.cofactor
hide_const (open) Square_Matrix.adjugate

hide_fact (open) det_upperdiagonal
hide_fact (open) row_def
hide_fact (open) col_def
hide_fact (open) transpose_def

lemma det_sq_matrix_eq: "Square_Matrix.det (from_vec A) = det A"
  unfolding Square_Matrix.det.rep_eq Determinants.det_def from_vec.rep_eq ..

lemma to_vec_matrix_scalar_mult: "to_vec (x *\<^sub>S A) = x *k to_vec A"
  by transfer (simp add: matrix_scalar_mult_def)

lemma to_vec_matrix_matrix_mult: "to_vec (A * B) = to_vec A ** to_vec B"
  by transfer (simp add: matrix_matrix_mult_def)

lemma to_vec_diag: "to_vec (diag x) = mat x"
  by transfer (simp add: mat_def)

lemma to_vec_one: "to_vec 1 = mat 1"
  by transfer (simp add: mat_def)

lemma to_vec_eq_iff: "to_vec M = to_vec N \<longleftrightarrow> M = N"
  by transfer (auto simp: vec_eq_iff)

subsection\<open>Some preliminary lemmas and results\<close>

lemma invertible_iff_is_unit:
  fixes A::"'a::{comm_ring_1}^'n^'n"
  shows "invertible A \<longleftrightarrow> (det A) dvd 1"
proof 
  assume inv_A: "invertible A"
  obtain B where AB_mat: "A ** B = mat 1" using inv_A unfolding invertible_def by auto
  have "1 = det (mat 1::'a^'n^'n)" unfolding det_I ..
  also have "... = det (A ** B)" unfolding AB_mat ..
  also have "... = det A * det B" unfolding det_mul ..
  finally have "1 = det A * det B" by simp
  thus "(det A) dvd 1" unfolding dvd_def by auto
next
  assume det_unit: "(det A) dvd 1"
  from this obtain a where a: "(det A) * a = 1" unfolding dvd_def by auto
  let ?A = "to_vec (Square_Matrix.adjugate (from_vec A))"
  show "invertible A"
  proof (unfold invertible_def, rule exI[of _ "a *k ?A"])
    have "from_vec A * (a *\<^sub>S Square_Matrix.adjugate (from_vec A)) = 1"
      "(a *\<^sub>S Square_Matrix.adjugate (from_vec A)) * from_vec A = 1"
      using a unfolding smult_mult2[symmetric] mult_adjugate_det[of "from_vec A"] smult_diag det_sq_matrix_eq
         smult_mult1[symmetric] adjugate_mult_det[of "from_vec A"]
      by (simp_all add: ac_simps diag_1)
    then show "A ** (a *k ?A) = mat 1 \<and> a *k ?A ** A = mat 1"
      unfolding to_vec_eq_iff[symmetric] to_vec_matrix_matrix_mult to_vec_matrix_scalar_mult
        to_vec_from_vec to_vec_one by simp
  qed
qed

definition "minorM M i j = (\<chi> k l. if k = i \<and> l = j then 1 else if k = i \<or> l = j then 0 else M $ k $ l)"

lemma minorM_eq: "minorM M i j = to_vec (minor (from_vec M) i j)"
  unfolding minorM_def by transfer standard

definition cofactor where "cofactor A i j = det (minorM A i j)"

definition cofactorM where "cofactorM A = (\<chi> i j. cofactor A i j)"

lemma cofactorM_eq: "cofactorM = to_vec \<circ> Square_Matrix.cofactor \<circ> from_vec"
  unfolding cofactorM_def cofactor_def[abs_def] det_sq_matrix_eq[symmetric] minorM_eq fun_eq_iff
  apply rule
  apply transfer'
  apply (simp add: fun_eq_iff vec_eq_iff)
  apply transfer
  apply simp
  done

definition mat2matofpoly where "mat2matofpoly A = (\<chi> i j. [: A $ i $ j :])"

definition charpoly where charpoly_def: "charpoly A = det (mat (monom 1 (Suc 0)) - mat2matofpoly A)"

lemma charpoly_eq: "charpoly A = Cayley_Hamilton.charpoly (from_vec A)"
  unfolding charpoly_def Cayley_Hamilton.charpoly_def det_sq_matrix_eq[symmetric] X_def C_def
  apply (intro arg_cong[where f=Square_Matrix.det])
  apply transfer'
  apply (simp add: fun_eq_iff mat_def mat2matofpoly_def C_def monom_Suc)
  done

definition adjugate where "adjugate A = transpose (cofactorM A)"

lemma adjugate_eq: "adjugate = to_vec \<circ> Square_Matrix.adjugate \<circ> from_vec"
  apply (simp add: adjugate_def Square_Matrix.adjugate_def fun_eq_iff)
  apply rule
  apply transfer'
  apply (simp add: transpose_def cofactorM_eq to_vec.rep_eq
    Square_Matrix.cofactor.rep_eq)
  done

end
