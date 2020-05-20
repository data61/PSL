(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Fundamental Theorem of Network Capacity\<close>

theory DL_Fundamental_Theorem_Network_Capacity
  imports DL_Rank_CP_Rank DL_Deep_Model_Poly Lebesgue_Zero_Set 
  Jordan_Normal_Form.DL_Rank_Submatrix "HOL-Analysis.Complete_Measure" DL_Shallow_Model
begin

context deep_model_correct_params_y
begin

definition "polynomial_f w = det (submatrix (matricize {n. even n} (A w)) rows_with_1 rows_with_1)"


lemma polyfun_polynomial:
  shows "polyfun {..<weight_space_dim} polynomial_f"
unfolding polynomial_f_def using polyfun_det_deep_model unfolding witness_submatrix_def A'_def .

definition "polynomial_p = (SOME p. vars p \<subseteq> {..<weight_space_dim} \<and> (\<forall>x. insertion x p = polynomial_f x))"

lemma
polynomial_p_not_0: "polynomial_p\<noteq>0" and
vars_polynomial_p: "vars polynomial_p \<subseteq> {..<weight_space_dim}" and
polynomial_pf: "\<And>w. insertion w polynomial_p = polynomial_f w"
proof -
  have "vars polynomial_p \<subseteq> {..<weight_space_dim} \<and> (\<forall>x. insertion x polynomial_p = polynomial_f x)" unfolding polynomial_p_def
    using someI_ex[OF polyfun_polynomial[unfolded polyfun_def]] .
  then show "vars polynomial_p \<subseteq> {..<weight_space_dim}" "\<And>w. insertion w polynomial_p = polynomial_f w" by auto
  show "polynomial_p\<noteq>0" using A'_def Aw'_def' \<open>\<And>w. insertion w polynomial_p = polynomial_f w\<close> polynomial_f_def witness_det by auto
qed

lemma  if_polynomial_0_rank:
assumes "polynomial_f w \<noteq> 0"
shows "r ^ N_half \<le> cprank (A w)"
proof -
  have "r ^ N_half = dim_row (submatrix (matricize {n. even n} (A w)) rows_with_1 rows_with_1)"
      by (metis (full_types) Aw'_def card_rows_with_1 dim_submatrix(1) dims_A dims_Aw dims_matricize(1) set_le_in)
  also have "... \<le> mrank (matricize {n. even n} (A w))"
    using assms vec_space.rank_gt_minor[OF carrier_matI[OF dims_A'_pow, unfolded weight_space_dim_def]]
      by (metis (full_types) A'_def dim_submatrix(1) dims_A'_pow(1) polynomial_f_def)
  also have "... \<le> cprank (A w)" using matrix_rank_le_cp_rank by blast
  finally show ?thesis .
qed

lemma  if_polynomial_0_evaluate:
assumes "polynomial_f wd \<noteq> 0"
assumes "\<forall>inputs. input_sizes (deep_model_l rs) = map dim_vec inputs \<longrightarrow> evaluate_net (insert_weights shared_weights (deep_model_l rs) wd) inputs
 = evaluate_net (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) ws) inputs"
shows "Z \<ge> r ^ N_half"
proof -
  have valid1:"valid_net' (insert_weights shared_weights (deep_model_l rs) wd)"
    using remove_insert_weights valid_deep_model by presburger
  have valid2:"valid_net' (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) ws)"
    by (simp add: remove_insert_weights valid_shallow_model)
  have input_sizes: "input_sizes (insert_weights shared_weights (deep_model_l rs) wd)
    = input_sizes (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2 * N_half - 1)) ws)"
    using input_sizes_remove_weights input_sizes_deep_model remove_insert_weights 
    by (simp add: N_half_def input_sizes_shallow_model)
  have 0:"tensors_from_net (insert_weights shared_weights (deep_model_l rs) wd)
        = tensors_from_net (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half -1)) ws)"
    using tensors_from_net_eqI[OF valid1 valid2 input_sizes, unfolded input_sizes_remove_weights remove_insert_weights]
    using assms by blast
  have "cprank (tensors_from_net (insert_weights shared_weights (deep_model_l rs) wd) $ y) \<le> Z"
    unfolding 0 using y_valid cprank_shallow_model by blast
  then show ?thesis
   using if_polynomial_0_rank assms
   using A_def assms(1)  less_le_trans not_le remove_insert_weights
   by fastforce
qed

lemma  if_polynomial_0_evaluate_notex:
assumes "polynomial_f wd \<noteq> 0"
shows "\<not>(\<exists>weights_shallow Z. Z < r ^ N_half \<and> (\<forall>inputs. input_sizes (deep_model_l rs) = map dim_vec inputs \<longrightarrow>
evaluate_net (insert_weights shared_weights (deep_model_l rs) wd) inputs
 = evaluate_net (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) ws) inputs))"
  using assms if_polynomial_0_evaluate not_le by blast

theorem fundamental_theorem_network_capacity:
"AE x in lborel_f weight_space_dim. r ^ N_half \<le> cprank (A x)"
using AE_I'[OF lebesgue_mpoly_zero_set[OF polynomial_p_not_0 vars_polynomial_p]]
  by (metis (mono_tags, lifting) Collect_mono if_polynomial_0_rank polynomial_pf)

theorem fundamental_theorem_network_capacity_v2:
shows "AE wd in lborel_f weight_space_dim.
   \<not>(\<exists>ws Z. Z < r ^ N_half \<and>  (\<forall>inputs. input_sizes (deep_model_l rs) = map dim_vec inputs \<longrightarrow>
evaluate_net (insert_weights shared_weights (deep_model_l rs) wd) inputs
 = evaluate_net (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) ws) inputs))"
  apply (rule AE_I'[OF lebesgue_mpoly_zero_set[OF polynomial_p_not_0 vars_polynomial_p], unfolded polynomial_pf])
  apply (rule subsetI) unfolding mem_Collect_eq
  using if_polynomial_0_evaluate_notex by metis

abbreviation lebesgue_f where "lebesgue_f n \<equiv> completion (lborel_f n)"

lemma space_lebesgue_f: "space (lebesgue_f n) = Pi\<^sub>E {..<n} (\<lambda>_. UNIV)"
  by (simp add: space_lborel_f)

theorem fundamental_theorem_network_capacity_v3:
  assumes
    "S = {wd \<in> space (lebesgue_f weight_space_dim).
      \<exists>ws Z. Z < r ^ N_half \<and>  (\<forall>inputs. input_sizes (deep_model_l rs) = map dim_vec inputs \<longrightarrow>
        evaluate_net (insert_weights shared_weights (deep_model_l rs) wd) inputs
      = evaluate_net (insert_weights shared_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) ws) inputs)}"
  shows "S \<in> null_sets (completion (lborel_f weight_space_dim))"
  unfolding assms
  using fundamental_theorem_network_capacity_v2[unfolded completion.AE_iff_null_sets[unfolded AE_completion_iff], unfolded not_not]
  by blast

end
end
