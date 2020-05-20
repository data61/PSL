(*
  File:     Symmetric_Polynomials_Code.thy
  Author:   Manuel Eberl (TU München)

  Code equations for symmetric polynomials (albeit not very efficient ones)
*)
section \<open>Executable Operations for Symmetric Polynomials\<close>
theory Symmetric_Polynomials_Code
  imports Symmetric_Polynomials "Polynomials.MPoly_Type_Class_FMap"
begin

(* TODO: Quite a few of these code equations should probably be moved to the Polynomials entry. *)

text \<open>
  Lastly, we shall provide some code equations to get executable code for operations related
  to symmetric polynomials, including, most notably, the fundamental theorem of symmetric
  polynomials and the recursive symmetry check.
\<close>

lemma Ball_subset_right:
  assumes "T \<subseteq> S" "\<forall>x\<in>S-T. P x"
  shows   "(\<forall>x\<in>S. P x) = (\<forall>x\<in>T. P x)"
  using assms by auto

(* This is a fairly simple theorem, but the automation somehow has a lot of problems with it *)
lemma compute_less_pp[code]:
  "xs < (ys :: 'a :: linorder \<Rightarrow>\<^sub>0 'b :: {zero, linorder}) \<longleftrightarrow>
    (\<exists>i\<in>keys xs \<union> keys ys. lookup xs i < lookup ys i \<and>
    (\<forall>j\<in>keys xs \<union> keys ys. j < i \<longrightarrow> lookup xs j = lookup ys j))"
proof transfer
  fix f g :: "'a \<Rightarrow> 'b"
  let ?dom = "{i. f i \<noteq> 0} \<union> {i. g i \<noteq> 0}"
  have "less_fun f g \<longleftrightarrow> (\<exists>k. f k < g k \<and> (\<forall>k'<k. f k' = g k'))"
    unfolding less_fun_def ..
  also have "\<dots> \<longleftrightarrow> (\<exists>i. f i < g i \<and> (i \<in> ?dom \<and> (\<forall>j\<in>?dom. j < i \<longrightarrow> f j = g j)))"
  proof (intro iff_exI conj_cong refl)
    fix k assume "f k < g k"
    hence k: "k \<in> ?dom" by auto
    have "(\<forall>k'<k. f k' = g k') = (\<forall>k'\<in>{..<k}. f k' = g k')"
      by auto
    also have "\<dots> \<longleftrightarrow> (\<forall>j\<in>({k. f k \<noteq> 0} \<union> {k. g k \<noteq> 0}) \<inter> {..<k}. f j = g j)"
      by (intro Ball_subset_right) auto
    also have "\<dots> \<longleftrightarrow> (\<forall>j\<in>({k. f k \<noteq> 0} \<union> {k. g k \<noteq> 0}). j < k \<longrightarrow> f j = g j)"
      by auto
    finally show "(\<forall>k'<k. f k' = g k') \<longleftrightarrow> k \<in> ?dom \<and> (\<forall>j\<in>?dom. j < k \<longrightarrow> f j = g j)"
      using k by simp
  qed
  also have "\<dots> \<longleftrightarrow> (\<exists>i\<in>?dom. f i < g i \<and> (\<forall>j\<in>?dom. j < i \<longrightarrow> f j = g j))"
    by (simp add: Bex_def conj_ac)
  finally show "less_fun f g \<longleftrightarrow> (\<exists>i\<in>?dom. f i < g i \<and> (\<forall>j\<in>?dom. j < i \<longrightarrow> f j = g j))" .
qed

lemma compute_le_pp[code]:
  "xs \<le> ys \<longleftrightarrow> xs = ys \<or> xs < (ys :: _ \<Rightarrow>\<^sub>0 _)"
  by (auto simp: order.order_iff_strict)

lemma vars_code [code]:
  "vars (MPoly p) = (\<Union>m\<in>keys p. keys m)"
  unfolding vars_def by transfer' simp

lemma mpoly_coeff_code [code]: "coeff (MPoly p) = lookup p"
  by transfer' simp

lemma sym_mpoly_code [code]:
  "sym_mpoly (set xs) k = (\<Sum>X\<in>Set.filter (\<lambda>X. card X = k) (Pow (set xs)). monom (monom_of_set X) 1)"
  by (simp add: sym_mpoly_altdef Set.filter_def)

lemma monom_of_set_code [code]:
  "monom_of_set (set xs) = Pm_fmap (fmap_of_list (map (\<lambda>x. (x, 1)) xs))"
    (is "?lhs = ?rhs")
proof (intro poly_mapping_eqI)
  fix k
  show "lookup ?lhs k = lookup ?rhs k"
    by (induction xs) (auto simp: lookup_monom_of_set fmlookup_default_def)
qed

lemma restrictpm_code [code]:
  "restrictpm A (Pm_fmap m) = Pm_fmap (fmrestrict_set A m)"
  by (intro poly_mapping_eqI) (auto simp: lookup_restrictpm fmlookup_default_def)

lemmas [code] = check_symmetric_mpoly_correct [symmetric]

notepad
begin
  define X Y Z :: "int mpoly" where "X = Var 1" "Y = Var 2" "Z = Var 3"
  define e1 e2 :: "int mpoly mpoly" where "e1 = Var 1" "e2 = Var 2"
  have "sym_mpoly {1, 2, 3} 2 = X * Y + X * Z + Y * Z"
    unfolding X_Y_Z_def by eval
  have "symmetric_mpoly {1, 2} (X ^ 3 + Y ^ 3)"
    unfolding X_Y_Z_def by eval
  have "fund_sym_poly_wit {1, 2} (X ^ 3 + Y ^ 3) = e1 ^ 3 - 3 * e1 * e2"
    unfolding X_Y_Z_def e1_e2_def by eval
end

end