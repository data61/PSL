(* Author: Thiemann *)
section \<open>An efficient algorithm to compute the growth rate of $A^n$.\<close>

theory Check_Matrix_Growth
imports 
  Spectral_Radius_Theory_2
  Sturm_Sequences.Sturm_Method
begin

hide_const (open) Coset.order

definition check_matrix_complexity :: "real mat \<Rightarrow> real poly \<Rightarrow> nat \<Rightarrow> bool" where
  "check_matrix_complexity A cp d = (count_roots_above cp 1 = 0
     \<and> (poly cp 1 = 0 \<longrightarrow> (let ord = order 1 cp in 
        d + 1 < ord \<longrightarrow> kernel_dim ((A - 1\<^sub>m (dim_row A)) ^\<^sub>m (d + 1)) = ord)))" 

lemma check_matrix_complexity: assumes A: "A \<in> carrier_mat n n" and nn: "nonneg_mat A" 
  and check: "check_matrix_complexity A (char_poly A) d" 
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_complexity_1_real[OF A nn])
  have id: "dim_gen_eigenspace A 1 (d + 1) = kernel_dim ((A - 1\<^sub>m (dim_row A)) ^\<^sub>m (d + 1))" 
    unfolding dim_gen_eigenspace_def
    by (rule arg_cong[of _ _ "\<lambda> x. kernel_dim (x ^\<^sub>m (d + 1))"], unfold char_matrix_def, insert A, auto)
  note check = check[unfolded check_matrix_complexity_def 
      Let_def count_roots_above_correct, folded id]
  have fin: "finite {x. poly (char_poly A) x = 0}" 
    by (rule poly_roots_finite, insert degree_monic_char_poly[OF A], auto)
  from check have "card {x. 1 < x \<and> poly (char_poly A) x = 0} = 0" by auto
  from this[unfolded card_eq_0_iff] fin 
  have "{x. 1 < x \<and> poly (char_poly A) x = 0} = {}" by auto
  thus "poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" for x by force
  assume "poly (char_poly A) 1 = 0" "d + 1 < order 1 (char_poly A)" 
  with check show "dim_gen_eigenspace A 1 (d + 1) = order 1 (char_poly A)" by auto
qed
end
