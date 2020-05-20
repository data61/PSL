(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Size Bounds\<close>

text \<open>We prove an exponential upper bound for the normalisation procedure. Moreover, we show that 
  the number of proper subformulas, which correspond to states very-weak alternating automata 
  (A1W), is only linear for each disjunct.\<close>

theory Normal_Form_Complexity imports
  Normal_Form
begin

subsection \<open>Inequalities and Identities\<close>

lemma inequality_1: 
  "y > 0 \<Longrightarrow> y + 3 \<le> (2 :: nat) ^ (y + 1)"
  by (induction y) (simp, fastforce)

lemma inequality_2: 
  "x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> ((2 :: nat) ^ (x + 1)) + (2 ^ (y + 1)) \<le> (2 ^ (x + y + 1))"
  by (induction x; simp; induction y; simp; fastforce)

lemma size_gr_0: 
  "size (\<phi> :: 'a ltln) > 0" 
  by (cases \<phi>) simp_all

lemma sum_associative:
  "finite X \<Longrightarrow> (\<Sum>x \<in> X. f x + c) = (\<Sum>x \<in> X. f x) + card X * c"
  by (induction rule: finite_induct) simp_all

subsection \<open>Length\<close>

text \<open>We prove that the length (size) of the resulting formula in normal form is at most exponential.\<close>

lemma flatten_sigma_1_length: 
  "size (\<phi>[N]\<^sub>\<Sigma>\<^sub>1) \<le> size \<phi>"
  by (induction \<phi>) simp_all

lemma flatten_pi_1_length: 
  "size (\<phi>[M]\<^sub>\<Pi>\<^sub>1) \<le> size \<phi>"
  by (induction \<phi>) simp_all

lemma flatten_sigma_2_length: 
  "size (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<le> 2 ^ (size \<phi> + 1)"
proof (induction \<phi>)
  case (And_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 and\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 and\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Or_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 or\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 or\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Next_ltln \<phi>)
  then show ?case 
    using le_Suc_eq by fastforce
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 W\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2 \<le> 2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1) + size \<phi>1 + 4"
    by (simp, simp add: add.commute add_mono flatten_pi_1_length)
  also
  have "\<dots> \<le> 2 ^ (size \<phi>2 + 1) + 2 * 2 ^ (size \<phi>1 + 1) + 1"
    using inequality_1[OF size_gr_0, of \<phi>1] by simp
  also
  have "\<dots> \<le> 2 * (2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1))"
    by simp
  also
  have "\<dots> \<le> 2 * 2 ^ (size \<phi>1 + size \<phi>2 + 1)"
    using inequality_2[OF size_gr_0 size_gr_0] mult_le_mono2 by blast 
  also
  have "\<dots> = 2 ^ (size (\<phi>1 W\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 M\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 M\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Until_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 U\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 U\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Release_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 R\<^sub>n \<phi>2)[M]\<^sub>\<Sigma>\<^sub>2 \<le> 2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1) + size \<phi>2 + 4"
    by (simp, simp add: add.commute add_mono flatten_pi_1_length)
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + 1) + 2 * 2 ^ (size \<phi>2 + 1) + 1"
    using inequality_1[OF size_gr_0, of \<phi>2] by simp
  also
  have "\<dots> \<le> 2 * (2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1))"
    by simp
  also
  have "\<dots> \<le> 2 * 2 ^ (size \<phi>1 + size \<phi>2 + 1)"
    using inequality_2[OF size_gr_0 size_gr_0] mult_le_mono2 by blast 
  also
  have "\<dots> = 2 ^ (size (\<phi>1 R\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case .
qed auto

lemma flatten_pi_2_length: 
  "size (\<phi>[N]\<^sub>\<Pi>\<^sub>2) \<le> 2 ^ (size \<phi> + 1)"
proof (induction \<phi>)
  case (And_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 and\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 and\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Or_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 or\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 or\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Next_ltln \<phi>)
  then show ?case 
    using le_Suc_eq by fastforce
next
  case (Until_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 U\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2 \<le> 2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1) + size \<phi>2 + 4"
    by (simp, simp add: add.commute add_mono flatten_sigma_1_length)
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + 1) + 2 * 2 ^ (size \<phi>2 + 1) + 1"
    using inequality_1[OF size_gr_0, of \<phi>2] by simp
  also
  have "\<dots> \<le> 2 * (2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1))"
    by simp
  also
  have "\<dots> \<le> 2 * 2 ^ (size \<phi>1 + size \<phi>2 + 1)"
    using inequality_2[OF size_gr_0 size_gr_0] mult_le_mono2 by blast 
  also
  have "\<dots> = 2 ^ (size (\<phi>1 U\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (Release_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 R\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 R\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 W\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2  \<le> (2 ^ (size \<phi>1 + 1)) + (2 ^ (size \<phi>2 + 1)) + 1"
    by simp
  also
  have "\<dots> \<le> 2 ^ (size \<phi>1 + size \<phi>2 + 1) + 1 "
    using inequality_2[OF size_gr_0 size_gr_0] by simp
  also
  have "\<dots> \<le> 2 ^ (size (\<phi>1 W\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case.
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  hence "size (\<phi>1 M\<^sub>n \<phi>2)[N]\<^sub>\<Pi>\<^sub>2 \<le> 2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1) + size \<phi>1 + 4"
    by (simp, simp add: add.commute add_mono flatten_sigma_1_length)
  also
  have "\<dots> \<le> 2 ^ (size \<phi>2 + 1) + 2 * 2 ^ (size \<phi>1 + 1) + 1"
    using inequality_1[OF size_gr_0, of \<phi>1] by simp
  also
  have "\<dots> \<le> 2 * (2 ^ (size \<phi>1 + 1) + 2 ^ (size \<phi>2 + 1))"
    by simp
  also
  have "\<dots> \<le> 2 * 2 ^ (size \<phi>1 + size \<phi>2 + 1)"
    using inequality_2[OF size_gr_0 size_gr_0] mult_le_mono2 by blast 
  also
  have "\<dots> = 2 ^ (size (\<phi>1 M\<^sub>n \<phi>2) + 1)"
    by simp
  finally
  show ?case .
qed auto

definition "normal_form_length_upper_bound"
  where "normal_form_length_upper_bound \<phi>
    \<equiv> (2 :: nat) ^ (size \<phi>) * (2 ^ (size \<phi> + 1) + 2 * (size \<phi> + 2) ^ 2)"

definition "normal_form_disjunct_with_flatten_pi_2_length"
  where "normal_form_disjunct_with_flatten_pi_2_length \<phi> M N
    \<equiv> size (\<phi>[N]\<^sub>\<Pi>\<^sub>2) + (\<Sum>\<psi> \<in> M. size (\<psi>[N]\<^sub>\<Sigma>\<^sub>1) + 2) + (\<Sum>\<psi> \<in> N. size (\<psi>[M]\<^sub>\<Pi>\<^sub>1) + 2)" 

definition "normal_form_with_flatten_pi_2_length"
  where "normal_form_with_flatten_pi_2_length \<phi> 
    \<equiv> \<Sum>(M, N) \<in> {(M, N) | M N. M \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> N \<subseteq> subformulas\<^sub>\<nu> \<phi>}. normal_form_disjunct_with_flatten_pi_2_length \<phi> M N"

definition "normal_form_disjunct_with_flatten_sigma_2_length"
  where "normal_form_disjunct_with_flatten_sigma_2_length \<phi> M N 
    \<equiv> size (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) + (\<Sum>\<psi> \<in> M. size (\<psi>[N]\<^sub>\<Sigma>\<^sub>1) + 2) + (\<Sum>\<psi> \<in> N. size (\<psi>[M]\<^sub>\<Pi>\<^sub>1) + 2)" 

definition "normal_form_with_flatten_sigma_2_length"
  where "normal_form_with_flatten_sigma_2_length \<phi> 
    \<equiv> \<Sum>(M, N) \<in> {(M, N) | M N. M \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> N \<subseteq> subformulas\<^sub>\<nu> \<phi>}. normal_form_disjunct_with_flatten_sigma_2_length \<phi> M N"

lemma normal_form_disjunct_length_upper_bound:
  assumes 
    "M \<subseteq> subformulas\<^sub>\<mu> \<phi>" 
    "N \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  shows 
    "normal_form_disjunct_with_flatten_sigma_2_length \<phi> M N \<le> 2 ^ (size \<phi> + 1) + 2 * (size \<phi> + 2) ^ 2" (is "?thesis1")
    "normal_form_disjunct_with_flatten_pi_2_length \<phi> M N \<le> 2 ^ (size \<phi> + 1) + 2 * (size \<phi> + 2) ^ 2" (is "?thesis2")
proof -
  let ?n = "size \<phi>"
  let ?b = "2 ^ (?n + 1) + ?n * (?n + 2) + ?n * (?n + 2)"

  have finite_M: "finite M" and card_M: "card M \<le> ?n"
    by (metis assms(1) finite_subset subformulas\<^sub>\<mu>_finite)
       (meson assms(1) card_mono order_trans subformulas\<^sub>\<mu>_subfrmlsn subfrmlsn_card subfrmlsn_finite) 

  have finite_N: "finite N" and card_N: "card N \<le> ?n"
    by (metis assms(2) finite_subset subformulas\<^sub>\<nu>_finite)
       (meson assms(2) card_mono order_trans subformulas\<^sub>\<nu>_subfrmlsn subfrmlsn_card subfrmlsn_finite) 

  have size_M: "\<And>\<psi>. \<psi> \<in> M \<Longrightarrow> size \<psi> \<le> size \<phi>"
    and size_N: "\<And>\<psi>. \<psi> \<in> N \<Longrightarrow> size \<psi> \<le> size \<phi>"
    by (metis assms(1) eq_iff in_mono less_imp_le subformulas\<^sub>\<mu>_subfrmlsn subfrmlsn_size)
       (metis assms(2) eq_iff in_mono less_imp_le subformulas\<^sub>\<nu>_subfrmlsn subfrmlsn_size)

  hence size_M': "\<And>\<psi>. \<psi> \<in> M \<Longrightarrow> size (\<psi>[N]\<^sub>\<Sigma>\<^sub>1) \<le> size \<phi>"
    and size_N': "\<And>\<psi>. \<psi> \<in> N \<Longrightarrow> size (\<psi>[M]\<^sub>\<Pi>\<^sub>1) \<le> size \<phi>"
    using flatten_sigma_1_length flatten_pi_1_length order_trans by blast+

  have "(\<Sum>\<psi> \<in> M. size (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<le> ?n * ?n"
    and "(\<Sum>\<psi> \<in> N. size (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> ?n * ?n"
    using sum_bounded_above[of M, OF size_M'] sum_bounded_above[of N, OF size_N']
    using mult_le_mono[OF card_M] mult_le_mono[OF card_N] by fastforce+
     
  hence "(\<Sum>\<psi> \<in> M. (size (\<psi>[N]\<^sub>\<Sigma>\<^sub>1) + 2)) \<le> ?n * (?n + 2)"
    and "(\<Sum>\<psi> \<in> N. (size (\<psi>[M]\<^sub>\<Pi>\<^sub>1) + 2)) \<le> ?n * (?n + 2)"
    unfolding sum_associative[OF finite_M] sum_associative[OF finite_N]
    using card_M card_N by simp_all

  hence "normal_form_disjunct_with_flatten_sigma_2_length \<phi> M N \<le> ?b"
    and "normal_form_disjunct_with_flatten_pi_2_length \<phi> M N \<le> ?b"
    unfolding normal_form_disjunct_with_flatten_sigma_2_length_def normal_form_disjunct_with_flatten_pi_2_length_def 
    by (metis (no_types, lifting) flatten_sigma_2_length flatten_pi_2_length add_le_mono)+

  thus ?thesis1 and ?thesis2
    by (simp_all add: power2_eq_square)
qed

theorem normal_form_length_upper_bound:
  "normal_form_with_flatten_sigma_2_length \<phi> \<le> normal_form_length_upper_bound \<phi>" (is "?thesis1")
  "normal_form_with_flatten_pi_2_length \<phi> \<le> normal_form_length_upper_bound \<phi>" (is "?thesis2")
proof -
  let ?n = "size \<phi>"
  let ?b = "2 ^ (size \<phi> + 1) + 2 * (size \<phi> + 2) ^ 2"

  have "{(M, N) | M N. M \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> N \<subseteq> subformulas\<^sub>\<nu> \<phi>} = {M. M \<subseteq> subformulas\<^sub>\<mu> \<phi>} \<times> {N. N \<subseteq> subformulas\<^sub>\<nu> \<phi>}" (is "?choices = _")
    by simp
  
  moreover
  
  have "card {M. M \<subseteq> subformulas\<^sub>\<mu> \<phi>} = (2 :: nat) ^ (card (subformulas\<^sub>\<mu> \<phi>))"
    and "card {N. N \<subseteq> subformulas\<^sub>\<nu> \<phi>} = (2 :: nat) ^ (card (subformulas\<^sub>\<nu> \<phi>))"
    using card_Pow unfolding Pow_def using subformulas\<^sub>\<mu>_finite subformulas\<^sub>\<nu>_finite by auto
  
  ultimately
  
  have "card ?choices \<le> 2 ^ (card (subfrmlsn \<phi>))" (is "?f \<le> _")
    by (metis subformulas\<^sub>\<mu>\<^sub>\<nu>_card card_cartesian_product subformulas\<^sub>\<mu>\<^sub>\<nu>_subfrmlsn subfrmlsn_finite Suc_1 card_mono lessI power_add power_increasing_iff)
  
  moreover
  
  have "(2 :: nat) ^ (card (subfrmlsn \<phi>)) \<le> 2 ^ ?n"
    using power_increasing[of _ _ "2 :: nat"] by (simp add: subfrmlsn_card)
  
  ultimately
  
  have bar: "of_nat (card ?choices) \<le> (2 :: nat) ^ ?n"
    using of_nat_id by presburger

  moreover

  have "normal_form_with_flatten_sigma_2_length \<phi> \<le> of_nat (card ?choices) * ?b"
    unfolding normal_form_with_flatten_sigma_2_length_def
    by (rule sum_bounded_above) (insert normal_form_disjunct_length_upper_bound, auto)

  moreover

  have "normal_form_with_flatten_pi_2_length \<phi> \<le> of_nat (card ?choices) * ?b"
    unfolding normal_form_with_flatten_pi_2_length_def
    by (rule sum_bounded_above) (insert normal_form_disjunct_length_upper_bound, auto)

  ultimately

  show ?thesis1 and ?thesis2
    unfolding normal_form_length_upper_bound_def 
    using mult_le_mono1 order_trans by blast+
qed

subsection \<open>Proper Subformulas\<close>

text \<open>We prove that the number of (proper) subformulas (sf) in a disjunct is linear and not exponential.\<close>

fun sf :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "sf (\<phi> and\<^sub>n \<psi>) = sf \<phi> \<union> sf \<psi>"
| "sf (\<phi> or\<^sub>n \<psi>) = sf \<phi> \<union> sf \<psi>"
| "sf (X\<^sub>n \<phi>) = {X\<^sub>n \<phi>} \<union> sf \<phi>"
| "sf (\<phi> U\<^sub>n \<psi>) = {\<phi> U\<^sub>n \<psi>} \<union> sf \<phi> \<union> sf \<psi>"
| "sf (\<phi> R\<^sub>n \<psi>) = {\<phi> R\<^sub>n \<psi>} \<union> sf \<phi> \<union> sf \<psi>"
| "sf (\<phi> W\<^sub>n \<psi>) = {\<phi> W\<^sub>n \<psi>} \<union> sf \<phi> \<union> sf \<psi>"
| "sf (\<phi> M\<^sub>n \<psi>) = {\<phi> M\<^sub>n \<psi>} \<union> sf \<phi> \<union> sf \<psi>"
| "sf \<phi> = {}"

lemma sf_finite: 
  "finite (sf \<phi>)"
  by (induction \<phi>) auto

lemma sf_subset_subfrmlsn: 
  "sf \<phi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma sf_size:
  "\<psi> \<in> sf \<phi> \<Longrightarrow> size \<psi> \<le> size \<phi>"
  by (induction \<phi>) auto

lemma sf_sf_subset: 
  "\<psi> \<in> sf \<phi> \<Longrightarrow> sf \<psi> \<subseteq> sf \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsn_sf_subset: 
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> sf \<psi> \<subseteq> sf \<phi>"
  by (induction \<phi>) auto

lemma sf_subset_insert:
  assumes "sf \<phi> \<subseteq> insert \<phi> X"
  assumes "\<psi> \<in> subfrmlsn \<phi>"
  assumes "\<phi> \<noteq> \<psi>" 
  shows "sf \<psi> \<subseteq> X" 
proof -
  have "sf \<psi> \<subseteq> sf \<phi> - {\<phi>}"
    using assms(2,3) subfrmlsn_sf_subset sf_size subfrmlsn_size by fastforce
  thus "?thesis"
    using assms(1) by auto
qed

lemma flatten_pi_1_sf_subset: 
  "sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1) \<subseteq> (\<Union>\<phi>\<in>sf \<phi>. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1))"
  by (induction \<phi>) auto

lemma flatten_sigma_1_sf_subset: 
  "sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>1) \<subseteq> (\<Union>\<phi>\<in>sf \<phi>. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>1))"
  by (induction \<phi>) auto

lemma flatten_sigma_2_sf_subset: 
  "sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<subseteq> (\<Union>\<psi>\<in>sf \<phi>. sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2))"
  by (induction \<phi>) auto

lemma sf_set1: 
  "sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1) \<subseteq> (\<Union>\<psi> \<in> (sf \<phi>). (sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)))"
  by (induction \<phi>) auto

(* TODO: could be moved *)
lemma ltln_not_idempotent [simp]:
  "\<phi> and\<^sub>n \<psi> \<noteq> \<phi>" "\<psi> and\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> and\<^sub>n \<psi>" "\<phi> \<noteq> \<psi> and\<^sub>n \<phi>"
  "\<phi> or\<^sub>n \<psi> \<noteq> \<phi>" "\<psi> or\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> or\<^sub>n \<psi>" "\<phi> \<noteq> \<psi> or\<^sub>n \<phi>"
  "X\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> X\<^sub>n \<phi>"
  "\<phi> U\<^sub>n \<psi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> U\<^sub>n \<psi>" "\<psi> U\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<psi> U\<^sub>n \<phi>"
  "\<phi> R\<^sub>n \<psi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> R\<^sub>n \<psi>" "\<psi> R\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<psi> R\<^sub>n \<phi>"
  "\<phi> W\<^sub>n \<psi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> W\<^sub>n \<psi>" "\<psi> W\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<psi> W\<^sub>n \<phi>"
  "\<phi> M\<^sub>n \<psi> \<noteq> \<phi>" "\<phi> \<noteq> \<phi> M\<^sub>n \<psi>" "\<psi> M\<^sub>n \<phi> \<noteq> \<phi>" "\<phi> \<noteq> \<psi> M\<^sub>n \<phi>"
  by (induction \<phi>; force)+

lemma flatten_card_sf_induct:
  assumes "finite X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> sf x \<subseteq> X"
  shows "card (\<Union>\<phi>\<in>X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<le> card X 
   \<and> card (\<Union>\<phi>\<in>X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> card X 
   \<and> card (\<Union>\<phi>\<in>X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> 3 * card X"
  using assms(2)
proof (induction rule: finite_ranking_induct[where f = size, OF \<open>finite X\<close>])
  case (2 \<psi> X)
    {
      assume "\<psi> \<notin> X"
      hence "\<And>\<chi>. \<chi> \<in> X \<Longrightarrow> sf \<chi> \<subseteq> X"
        using 2(2,4) sf_subset_subfrmlsn subfrmlsn_size by fastforce
      hence "card (\<Union>\<phi>\<in>X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<le> card X"
        and "card (\<Union>\<phi>\<in>X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> card X"        
        and "card (\<Union>\<phi>\<in>X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> 3 * card X"
        using 2(3) by simp+
      
      moreover

      let ?lower1 = "\<Union>\<phi> \<in> insert \<psi> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)"
      let ?upper1 = "(\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"

      let ?lower2 = "\<Union>\<phi> \<in> insert \<psi> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)"
      let ?upper2 = "(\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"

      let ?lower3 = "\<Union>\<phi> \<in> insert \<psi> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)"
      let ?upper3_cases = "{\<psi>[M]\<^sub>\<Sigma>\<^sub>2, \<psi>[M]\<^sub>\<Pi>\<^sub>1} \<union> (case \<psi> of (\<phi>1 W\<^sub>n \<phi>2) \<Rightarrow> {G\<^sub>n (\<phi>1[M]\<^sub>\<Pi>\<^sub>1)} | (\<phi>1 R\<^sub>n \<phi>2) \<Rightarrow> {G\<^sub>n (\<phi>2[M]\<^sub>\<Pi>\<^sub>1)} | _ \<Rightarrow> {})"
      let ?upper3 = "(\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> ?upper3_cases"

      have finite_upper1: "finite (?upper1)"
        and finite_upper2: "finite (?upper2)" 
        and finite_upper3: "finite (?upper3)" 
        using 2(1) sf_finite by auto (cases \<psi>, auto)

      have "\<And>x y. card {x, y} \<le> 3"
        and "\<And>x y z. card {x, y, z} \<le> 3"
        by (simp add: card_insert_if le_less)+
      hence card_leq_3: "card (?upper3_cases) \<le> 3"
        by (cases \<psi>) (simp_all, fast)

      note card_subset_split_rule = le_trans[OF card_mono card_Un_le]

      have sf_in_X: "sf \<psi> \<subseteq> insert \<psi> X"
        using 2 by blast

      have "?lower1 \<subseteq> ?upper1 \<and> ?lower2 \<subseteq> ?upper2 \<and> ?lower3 \<subseteq> ?upper3" 
      proof (cases \<psi>)
        case (And_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X" 
          by (rule sf_subset_insert[OF sf_in_X, unfolded And_ltln]; simp)+

        have "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2))"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1))"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1))"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: And_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: And_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: And_ltln)
          done
        
        thus ?thesis 
          by blast
      next
        case (Or_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X"
          by (rule sf_subset_insert[OF sf_in_X, unfolded Or_ltln]; simp)+

        have "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2))"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1))"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1))"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: Or_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: Or_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: Or_ltln)
          done
          
        thus ?thesis 
          by blast
      next
        case (Next_ltln \<psi>\<^sub>1)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" 
          by (rule sf_subset_insert[OF sf_in_X, unfolded Next_ltln]) simp_all
  
        have "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<union> {\<psi>[M]\<^sub>\<Sigma>\<^sub>2}"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: Next_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: Next_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: Next_ltln)
          done
        
        thus ?thesis
          by blast
      next
        case (Until_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X"
          by (rule sf_subset_insert[OF sf_in_X, unfolded Until_ltln]; simp)+
  
        hence "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<union> {\<psi>[M]\<^sub>\<Sigma>\<^sub>2}"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: Until_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: Until_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: Until_ltln)
          done
  
        thus ?thesis
          by blast
      next
        case (Release_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X"
          by (rule sf_subset_insert[OF sf_in_X, unfolded Release_ltln]; simp)+
  
        have "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<union> {\<psi>[M]\<^sub>\<Sigma>\<^sub>2, G\<^sub>n \<psi>\<^sub>2[M]\<^sub>\<Pi>\<^sub>1} \<union> sf (\<psi>\<^sub>2[M]\<^sub>\<Pi>\<^sub>1)"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: Release_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: Release_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: Release_ltln)
          done
  
        moreover 
        have "sf (\<psi>\<^sub>2[M]\<^sub>\<Pi>\<^sub>1) \<subseteq> (\<Union>\<phi>\<in>X. sf \<phi>[M]\<^sub>\<Sigma>\<^sub>2 \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}" 
          using \<open>(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}\<close> 
          by (auto simp: Release_ltln)
          
        ultimately
        show ?thesis
          by (simp add: Release_ltln) blast 
      next
        case (WeakUntil_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X"
          by (rule sf_subset_insert[OF sf_in_X, unfolded WeakUntil_ltln]; simp)+
  
        have "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<union> {\<psi>[M]\<^sub>\<Sigma>\<^sub>2, G\<^sub>n \<psi>\<^sub>1[M]\<^sub>\<Pi>\<^sub>1} \<union> sf (\<psi>\<^sub>1[M]\<^sub>\<Pi>\<^sub>1)"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: WeakUntil_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: WeakUntil_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: WeakUntil_ltln)
          done
  
        moreover 
        have "sf (\<psi>\<^sub>1[M]\<^sub>\<Pi>\<^sub>1) \<subseteq> (\<Union>\<phi>\<in>X. sf \<phi>[M]\<^sub>\<Sigma>\<^sub>2 \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}" 
          using \<open>(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}\<close> 
          by (auto simp: WeakUntil_ltln)
          
        ultimately
        show ?thesis
          by (simp add: WeakUntil_ltln) blast 
      next 
        case (StrongRelease_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)
        have *: "sf \<psi>\<^sub>1 \<subseteq> X" "sf \<psi>\<^sub>2 \<subseteq> X"
          by (rule sf_subset_insert[OF sf_in_X, unfolded StrongRelease_ltln]; simp)+
          
        hence "(sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<union> {\<psi>[M]\<^sub>\<Sigma>\<^sub>2}"
          and "(sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<union> {\<psi>[M]\<^sub>\<Pi>\<^sub>1}"
          and "(sf (\<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<subseteq> (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) \<union> {\<psi>[N]\<^sub>\<Sigma>\<^sub>1}"
          subgoal
            using flatten_sigma_2_sf_subset[of _ M] * by (force simp: StrongRelease_ltln)
          subgoal
            using flatten_pi_1_sf_subset[of _ M] * by (force simp: StrongRelease_ltln)
          subgoal 
            using flatten_sigma_1_sf_subset * by (force simp: StrongRelease_ltln)
          done
          
        thus ?thesis 
          by blast
      qed auto

      hence "card ?lower1 \<le> card (\<Union>\<phi> \<in> X. sf (\<phi>[N]\<^sub>\<Sigma>\<^sub>1)) + 1"
        and "card ?lower2 \<le> card (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) + 1"
        and "card ?lower3 \<le> card (\<Union>\<phi> \<in> X. sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) + 3" 
        using card_subset_split_rule[OF finite_upper1, of ?lower1] 
        using card_subset_split_rule[OF finite_upper2, of ?lower2]
        using card_subset_split_rule[OF finite_upper3, of ?lower3]
        using card_leq_3 by simp+
  
      moreover
      have "card (insert \<psi> X) = card X + 1"
        using \<open>\<psi> \<notin> X\<close> \<open>finite X\<close> by simp
      ultimately
      have ?case
        by linarith
    }
  moreover
  have "\<psi> \<in> X \<Longrightarrow> ?case"
    using 2 by (simp add: insert_absorb)
  ultimately
  show ?case 
    by meson
qed simp
      
theorem flatten_card_sf: 
  "card (\<Union>\<psi> \<in> sf \<phi>. sf (\<psi>[M]\<^sub>\<Sigma>\<^sub>1)) \<le> card (sf \<phi>)" (is "?t1") 
  "card (\<Union>\<psi> \<in> sf \<phi>. sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> card (sf \<phi>)" (is "?t2")
  "card (sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> 3 * card (sf \<phi>)" (is "?t3")
proof -
  have "card (\<Union>\<psi> \<in> sf \<phi>. sf \<psi>[M]\<^sub>\<Sigma>\<^sub>2 \<union> sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> 3 * card (sf \<phi>)"
    using flatten_card_sf_induct[OF sf_finite sf_sf_subset] by auto
  moreover
  have "card (sf \<phi>[M]\<^sub>\<Sigma>\<^sub>2 \<union> sf (\<phi>[M]\<^sub>\<Pi>\<^sub>1)) \<le> card (\<Union>\<psi> \<in> sf \<phi>. sf \<psi>[M]\<^sub>\<Sigma>\<^sub>2 \<union> sf (\<psi>[M]\<^sub>\<Pi>\<^sub>1))"
    using card_mono[OF _ sf_set1] sf_finite by blast
  ultimately
  show ?t1 ?t2 ?t3
    using flatten_card_sf_induct[OF sf_finite sf_sf_subset] by auto
qed

corollary flatten_sigma_2_card_sf: 
  "card (sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)) \<le> 3 * (card (sf \<phi>))"
  by (metis sf_finite order.trans[OF _ flatten_card_sf(3), of "card (sf (\<phi>[M]\<^sub>\<Sigma>\<^sub>2))", OF card_mono] finite_UnI Un_upper1)

end