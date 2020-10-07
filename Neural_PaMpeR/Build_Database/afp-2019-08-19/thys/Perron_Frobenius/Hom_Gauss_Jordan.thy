(* author: Thiemann *)
section \<open>Homomorphisms of Gauss-Jordan Elimination, Kernel and More\<close>
theory Hom_Gauss_Jordan
  imports Jordan_Normal_Form.Matrix_Kernel
   Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
begin

lemma (in comm_ring_hom) similar_mat_wit_hom: assumes
  "similar_mat_wit A B C D"
shows "similar_mat_wit (mat\<^sub>h A) (mat\<^sub>h B) (mat\<^sub>h C) (mat\<^sub>h D)"
proof -
  obtain n where n: "n = dim_row A" by auto
  note * = similar_mat_witD[OF n assms]
  from * have [simp]: "dim_row C = n" by auto
  note C = *(6) note D = *(7)
  note id = mat_hom_mult[OF C D] mat_hom_mult[OF D C]
  note ** = *(1-3)[THEN arg_cong[of _ _ "mat\<^sub>h"], unfolded id]
  note mult = mult_carrier_mat[of _ n n]
  note hom_mult = mat_hom_mult[of _ n n _ n]
  show ?thesis unfolding similar_mat_wit_def Let_def unfolding **(3) using **(1,2)
    by (auto simp: n[symmetric] hom_mult simp: *(4-) mult)
qed

lemma (in comm_ring_hom) similar_mat_hom:
  "similar_mat A B \<Longrightarrow> similar_mat (mat\<^sub>h A) (mat\<^sub>h B)"
  using similar_mat_wit_hom[of A B C D for C D]
  by (smt similar_mat_def)

context field_hom
begin
lemma hom_swaprows: "i < dim_row A \<Longrightarrow> j < dim_row A \<Longrightarrow>
  swaprows i j (mat\<^sub>h A) = mat\<^sub>h (swaprows i j A)"
  unfolding mat_swaprows_def by (rule eq_matI, auto)

lemma hom_gauss_jordan_main: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc2 \<Longrightarrow>
  gauss_jordan_main (mat\<^sub>h A) (mat\<^sub>h B) i j =
  map_prod mat\<^sub>h mat\<^sub>h (gauss_jordan_main A B i j)"
proof (induct A B i j rule: gauss_jordan_main.induct)
  case (1 A B i j)
  note IH = 1(1-4)
  note AB = 1(5-6)
  from AB have dim: "dim_row A = nr" "dim_col A = nc" by auto
  let ?h = "mat\<^sub>h"
  let ?hp = "map_prod mat\<^sub>h mat\<^sub>h"
  show ?case unfolding gauss_jordan_main.simps[of A B i j] gauss_jordan_main.simps[of "?h A" _ i j]
    index_map_mat Let_def if_distrib[of ?hp] dim
  proof (rule if_cong[OF refl], goal_cases)
    case 1
    note IH = IH[OF dim[symmetric] 1 refl]
    from 1 have ij: "i < nr" "j < nc" by auto
    hence hij: "(?h A) $$ (i,j) = hom (A $$ (i,j))" using AB by auto
    define ixs where "ixs = concat (map (\<lambda>i'. if A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr])"
    have id: "map (\<lambda>i'. if mat\<^sub>h A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr] =
       map (\<lambda>i'. if A $$ (i', j) \<noteq> 0 then [i'] else []) [Suc i..<nr]"
      by (rule map_cong[OF refl], insert ij AB, auto)
    show ?case unfolding hij hom_0_iff hom_1_iff id ixs_def[symmetric]
    proof (rule if_cong[OF refl _ if_cong[OF refl]], goal_cases)
      case 1
      note IH = IH(1,2)[OF 1, folded ixs_def]
      show ?case
      proof (cases ixs)
        case Nil
        show ?thesis unfolding Nil using IH(1)[OF Nil AB] by auto
      next
        case (Cons I ix)
        hence "I \<in> set ixs" by auto
        hence I: "I < nr" unfolding ixs_def by auto
        from AB have swap: "swaprows i I A \<in> carrier_mat nr nc" "swaprows i I B \<in> carrier_mat nr nc2"
          by auto
        show ?thesis unfolding Cons list.simps IH(2)[OF Cons swap,symmetric] using AB ij I
          by (auto simp: hom_swaprows)
      qed
    next
      case 2
      from AB have elim: "eliminate_entries (\<lambda>i. A $$ (i, j)) A i j \<in> carrier_mat nr nc"
          "eliminate_entries (\<lambda>i. A $$ (i, j)) B i j \<in> carrier_mat nr nc2"
        unfolding eliminate_entries_gen_def by auto
      show ?case unfolding IH(3)[OF 2 refl elim, symmetric]
        by (rule arg_cong2[of _ _ _ _ "\<lambda> x y. gauss_jordan_main x y (Suc i) (Suc j)"];
        intro eq_matI, insert AB ij, auto simp: eliminate_entries_gen_def hom_minus hom_mult)
    next
      case 3
      from AB have mult: "multrow i (inverse (A $$ (i, j))) A \<in> carrier_mat nr nc"
        "multrow i (inverse (A $$ (i, j))) B \<in> carrier_mat nr nc2" by auto
      show ?case unfolding IH(4)[OF 3 refl mult, symmetric]
        by (rule arg_cong2[of _ _ _ _ "\<lambda> x y. gauss_jordan_main x y i j"];
        intro eq_matI, insert AB ij, auto simp: hom_inverse hom_mult)
    qed
  qed auto
qed

lemma hom_gauss_jordan: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc2 \<Longrightarrow>
  gauss_jordan (mat\<^sub>h A) (mat\<^sub>h B) = map_prod mat\<^sub>h mat\<^sub>h (gauss_jordan A B)"
  unfolding gauss_jordan_def using hom_gauss_jordan_main by blast

lemma hom_gauss_jordan_single[simp]: "gauss_jordan_single (mat\<^sub>h A) = mat\<^sub>h (gauss_jordan_single A)"
proof -
  let ?nr = "dim_row A" let ?nc = "dim_col A"
  have 0: "0\<^sub>m ?nr 0 \<in> carrier_mat ?nr 0" by auto
  have dim: "dim_row (mat\<^sub>h A) = ?nr" by auto
  have hom0: "mat\<^sub>h (0\<^sub>m ?nr 0) = 0\<^sub>m ?nr 0" by auto
  have A: "A \<in> carrier_mat ?nr ?nc" by auto
  from hom_gauss_jordan[OF A 0] A
  show ?thesis unfolding gauss_jordan_single_def dim hom0 by (metis fst_map_prod)
qed

lemma hom_pivot_positions_main_gen: assumes A: "A \<in> carrier_mat nr nc"
  shows "pivot_positions_main_gen 0 (mat\<^sub>h A) nr nc i j = pivot_positions_main_gen 0 A nr nc i j"
proof (induct rule: pivot_positions_main_gen.induct[of nr nc A 0])
  case (1 i j)
  note IH = this
  show ?case unfolding pivot_positions_main_gen.simps[of _ _ nr nc i j]
  proof (rule if_cong[OF refl if_cong[OF refl _ refl] refl], goal_cases)
    case 1
    with A have id: "(mat\<^sub>h A) $$ (i,j) = hom (A $$ (i,j))" by simp
    note IH = IH[OF 1]
    show ?case unfolding id hom_0_iff
      by (rule if_cong[OF refl IH(1)], force, subst IH(2), auto)
  qed
qed

lemma hom_pivot_positions[simp]: "pivot_positions (mat\<^sub>h A) = pivot_positions A"
  unfolding pivot_positions_def by (subst hom_pivot_positions_main_gen, auto)

lemma hom_kernel_dim[simp]: "kernel_dim (mat\<^sub>h A) = kernel_dim A"
  unfolding kernel_dim_code by simp

lemma hom_char_matrix: assumes A: "A \<in> carrier_mat n n"
  shows "char_matrix (mat\<^sub>h A) (hom x) = mat\<^sub>h (char_matrix A x)"
  unfolding char_matrix_def
  by (rule eq_matI, insert A, auto simp: hom_minus)

lemma hom_dim_gen_eigenspace: assumes A: "A \<in> carrier_mat n n"
  shows "dim_gen_eigenspace (mat\<^sub>h A) (hom x) = dim_gen_eigenspace A x"
proof (intro ext)
  fix k
  show "dim_gen_eigenspace (mat\<^sub>h A) (hom x) k = dim_gen_eigenspace A x k"
    unfolding dim_gen_eigenspace_def hom_char_matrix[OF A]
      mat_hom_pow[OF char_matrix_closed[OF A], symmetric] by simp
qed
end
end
