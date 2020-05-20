section \<open>Partial and total correctness\<close>

theory Quantum_Hoare
  imports Quantum_Program
begin

context state_sig
begin

definition density_states :: "state set" where
  "density_states = {\<rho> \<in> carrier_mat d d. partial_density_operator \<rho>}"

lemma denote_density_states:
  "\<rho> \<in> density_states \<Longrightarrow> well_com S \<Longrightarrow> denote S \<rho> \<in> density_states"
  by (simp add: denote_dim_pdo density_states_def)

definition is_quantum_predicate :: "complex mat \<Rightarrow> bool" where
  "is_quantum_predicate P \<longleftrightarrow> P \<in> carrier_mat d d \<and> positive P \<and> P \<le>\<^sub>L 1\<^sub>m d"

lemma trace_measurement2:
  assumes m: "measurement n 2 M" and dA: "A \<in> carrier_mat n n"
  shows "trace ((M 0) * A * adjoint (M 0)) + trace ((M 1) * A * adjoint (M 1)) = trace A"
proof -
  from m have dM0: "M 0 \<in> carrier_mat n n" and dM1: "M 1 \<in> carrier_mat n n" and id: "adjoint (M 0) * (M 0) + adjoint (M 1) * (M 1) = 1\<^sub>m n" 
    using measurement_def measurement_id2 by auto
  have "trace (M 1 * A * adjoint (M 1)) + trace (M 0 * A * adjoint (M 0))
    = trace ((adjoint (M 0) * M 0 + adjoint (M 1) * M 1) * A)"
    using dM0 dM1 dA by (mat_assoc n)
  also have "\<dots> = trace (1\<^sub>m n * A)" using id by auto
  also have "\<dots> = trace A" using dA by auto
  finally show ?thesis
    using dA dM0 dM1 local.id state_sig.trace_measure2_id by blast
qed

lemma qp_close_under_unitary_operator:
  fixes U P :: "complex mat"
  assumes dU: "U \<in> carrier_mat d d"
    and u: "unitary U"
    and qp: "is_quantum_predicate P"
  shows "is_quantum_predicate (adjoint U * P * U)"
  unfolding is_quantum_predicate_def
proof (auto)
  have dP: "P \<in> carrier_mat d d" using qp is_quantum_predicate_def by auto
  show "adjoint U * P * U \<in> carrier_mat d d" using dU dP by fastforce
  have "positive P" using qp is_quantum_predicate_def by auto
  then show "positive (adjoint U * P * U)" 
    using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dU] dP, simplified adjoint_adjoint] by fastforce
  have "adjoint U * U = 1\<^sub>m d" apply (subgoal_tac "inverts_mat (adjoint U) U")
    subgoal unfolding inverts_mat_def using dU by auto
    using u unfolding unitary_def using inverts_mat_symm[OF dU adjoint_dim[OF dU]] by auto
  then have u': "adjoint U * 1\<^sub>m d * U = 1\<^sub>m d" using dU by auto
  have le: "P \<le>\<^sub>L 1\<^sub>m d" using qp is_quantum_predicate_def by auto
  show "adjoint U * P * U \<le>\<^sub>L 1\<^sub>m d" 
    using lowner_le_keep_under_measurement[OF dU dP one_carrier_mat le] u' by auto
qed

lemma qps_after_measure_is_qp:
  assumes m: "measurement d n M " and qpk: "\<And>k. k < n \<Longrightarrow> is_quantum_predicate (P k)"
  shows "is_quantum_predicate (matrix_sum d (\<lambda>k. adjoint (M k) * P k  * M k) n)"
  unfolding is_quantum_predicate_def 
proof (auto)
  have dMk: "k < n \<Longrightarrow> M k \<in> carrier_mat d d" for k using m measurement_def by auto
  moreover have dPk: "k < n \<Longrightarrow> P k \<in> carrier_mat d d" for k using qpk is_quantum_predicate_def by auto
  ultimately have dk: "k < n \<Longrightarrow> adjoint (M k) * P k  * M k \<in> carrier_mat d d" for k by fastforce
  then show d: "matrix_sum d (\<lambda>k. adjoint (M k) * P k  * M k) n \<in> carrier_mat d d" 
    using matrix_sum_dim[of n "\<lambda>k. adjoint (M k) * P k  * M k"] by auto
  have "k < n \<Longrightarrow> positive (P k)" for k using qpk is_quantum_predicate_def by auto
  then have "k < n \<Longrightarrow> positive (adjoint (M k) * P k * M k)" for k 
    using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dMk] dPk, simplified adjoint_adjoint] by fastforce
  then show "positive (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n)" using matrix_sum_positive dk by auto
  have "k < n \<Longrightarrow> P k \<le>\<^sub>L 1\<^sub>m d" for k using qpk is_quantum_predicate_def by auto
  then have "k < n \<Longrightarrow> positive (1\<^sub>m d - P k)" for k using lowner_le_def by auto
  then have p: "k < n \<Longrightarrow> positive (adjoint (M k) * (1\<^sub>m d - P k) * M k)" for k 
    using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dMk], simplified adjoint_adjoint, of _ "1\<^sub>m d - P k"] dPk by fastforce
  {
    fix k assume k: "k < n"
    have "adjoint (M k) * (1\<^sub>m d - P k) * M k = adjoint (M k) * M k - adjoint (M k) * P k * M k"
      apply (mat_assoc d) using dMk dPk k by auto
  }
  note split = this
  have dk': "k < n \<Longrightarrow> adjoint (M k) * M k - adjoint (M k) * P k * M k \<in> carrier_mat d d" for k using dMk dPk by fastforce
  have "k < n \<Longrightarrow> positive (adjoint (M k) * M k - adjoint (M k) * P k * M k)" for k using p split by auto
  then have p': "positive (matrix_sum d (\<lambda>k. adjoint (M k) * M k - adjoint (M k) * P k * M k) n)" 
    using matrix_sum_positive[OF dk', of n id, simplified] by auto
  have daMMk: "k < n \<Longrightarrow> adjoint (M k) * M k \<in> carrier_mat d d" for k using dMk by fastforce
  have daMPMk: "k < n \<Longrightarrow> adjoint (M k) * P k * M k \<in> carrier_mat d d" for k using dMk dPk by fastforce
  have "matrix_sum d (\<lambda>k. adjoint (M k) * M k - adjoint (M k) * P k * M k) n 
    = matrix_sum d (\<lambda>k. adjoint (M k) * M k) n - matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n"
    using matrix_sum_minus_distrib[OF daMMk daMPMk] by auto
  also have "\<dots> = 1\<^sub>m d - matrix_sum d (\<lambda>k. adjoint (M k) * P k  * M k) n" using m measurement_def by auto
  finally have "positive (1\<^sub>m d - matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n)" using p' by auto
  then show "matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n \<le>\<^sub>L 1\<^sub>m d" using lowner_le_def d by auto
qed

definition hoare_total_correct :: "complex mat \<Rightarrow> com \<Rightarrow> complex mat \<Rightarrow> bool" ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile>\<^sub>t {P} S {Q} \<longleftrightarrow> (\<forall>\<rho>\<in>density_states. trace (P * \<rho>) \<le> trace (Q * denote S \<rho>))"

definition hoare_partial_correct :: "complex mat \<Rightarrow> com \<Rightarrow> complex mat \<Rightarrow> bool" ("\<Turnstile>\<^sub>p {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile>\<^sub>p {P} S {Q} \<longleftrightarrow> (\<forall>\<rho>\<in>density_states. trace (P * \<rho>) \<le> trace (Q * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>)))"

(* Proposition 6.1 (1) *)
lemma total_implies_partial:
  assumes S: "well_com S"
    and total: "\<Turnstile>\<^sub>t {P} S {Q}"
  shows "\<Turnstile>\<^sub>p {P} S {Q}"
proof -
  have "trace (P * \<rho>) \<le> trace (Q * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>))" if \<rho>: "\<rho> \<in> density_states" for \<rho>
  proof -
    have "trace (P * \<rho>) \<le> trace (Q * denote S \<rho>)"
      using total hoare_total_correct_def \<rho> by auto
    moreover have "trace (denote S \<rho>) \<le> trace \<rho>"
      using denote_trace[OF S] \<rho> density_states_def by auto
    ultimately show ?thesis by auto
  qed
  then show ?thesis
    using hoare_partial_correct_def by auto
qed

lemma predicate_prob_positive:
  assumes "0\<^sub>m d d \<le>\<^sub>L P"
    and "\<rho> \<in> density_states"
  shows "0 \<le> trace (P * \<rho>)"
proof -
  have "trace (0\<^sub>m d d * \<rho>) \<le> trace (P * \<rho>)"
    apply (rule lowner_le_traceD)
    using assms unfolding lowner_le_def density_states_def by auto
  then show ?thesis
    using assms(2) density_states_def by auto
qed

(* Proposition 6.1 (2a) *)
lemma total_pre_zero:
  assumes S: "well_com S"
    and Q: "is_quantum_predicate Q"
  shows "\<Turnstile>\<^sub>t {0\<^sub>m d d} S {Q}"
proof -
  have "trace (0\<^sub>m d d * \<rho>) \<le> trace (Q * denote S \<rho>)" if \<rho>: "\<rho> \<in> density_states" for \<rho>
  proof -
    have 1: "trace (0\<^sub>m d d * \<rho>) = 0"
      using \<rho> unfolding density_states_def by auto
    show ?thesis
      apply (subst 1)
      apply (rule predicate_prob_positive)
      subgoal apply (simp add: lowner_le_def, subgoal_tac "Q - 0\<^sub>m d d = Q") using Q is_quantum_predicate_def[of Q] by auto
      subgoal using denote_density_states \<rho> S by auto
      done
  qed
  then show ?thesis
    using hoare_total_correct_def by auto
qed

(* Proposition 6.1 (2b) *)
lemma partial_post_identity:
  assumes S: "well_com S"
    and P: "is_quantum_predicate P"
  shows "\<Turnstile>\<^sub>p {P} S {1\<^sub>m d}"
proof -
  have "trace (P * \<rho>) \<le> trace (1\<^sub>m d * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>))" if \<rho>: "\<rho> \<in> density_states" for \<rho>
  proof -
    have "denote S \<rho> \<in> carrier_mat d d"
      using S denote_dim \<rho> density_states_def by auto
    then have "trace (1\<^sub>m d * denote S \<rho>) = trace (denote S \<rho>)"
      by auto
    moreover have "trace (P * \<rho>) \<le> trace (1\<^sub>m d * \<rho>)"
      apply (rule lowner_le_traceD)
      using \<rho> unfolding density_states_def apply auto
      using P is_quantum_predicate_def by auto
    ultimately show ?thesis
      using density_states_def that by auto
  qed
  then show ?thesis
    using hoare_partial_correct_def by auto
qed

subsection \<open>Weakest liberal preconditions\<close>

definition is_weakest_liberal_precondition :: "complex mat \<Rightarrow> com \<Rightarrow> complex mat \<Rightarrow> bool"  where
  "is_weakest_liberal_precondition W S P \<longleftrightarrow>
    is_quantum_predicate W \<and> \<Turnstile>\<^sub>p {W} S {P} \<and> (\<forall>Q. is_quantum_predicate Q \<longrightarrow> \<Turnstile>\<^sub>p {Q} S {P} \<longrightarrow> Q \<le>\<^sub>L W)"

definition wlp_measure :: "nat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> ((complex mat \<Rightarrow> complex mat) list) \<Rightarrow> complex mat \<Rightarrow> complex mat" where
"wlp_measure n M WS P = matrix_sum d (\<lambda>k. adjoint (M k) * ((WS!k) P) * (M k)) n"

fun wlp_while_n :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (complex mat \<Rightarrow> complex mat) \<Rightarrow> nat \<Rightarrow> complex mat \<Rightarrow> complex mat" where
  "wlp_while_n M0 M1 WS 0 P = 1\<^sub>m d"
| "wlp_while_n M0 M1 WS (Suc n) P = adjoint M0 * P * M0 + adjoint M1 * (WS (wlp_while_n M0 M1 WS n P)) * M1"

lemma measurement2_leq_one_mat:
  assumes dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d"
    and leP: "P \<le>\<^sub>L 1\<^sub>m d" and leQ: "Q \<le>\<^sub>L 1\<^sub>m d" and m: "measurement d 2 M"
  shows "(adjoint (M 0) * P * (M 0) + adjoint (M 1) * Q * (M 1)) \<le>\<^sub>L 1\<^sub>m d"
proof -
  define M0 where "M0 = M 0" 
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using m M0_def M1_def measurement_def by auto

  have "adjoint M1 * Q * M1 \<le>\<^sub>L adjoint M1 * 1\<^sub>m d * M1"
    using lowner_le_keep_under_measurement[OF dM1 dQ _ leQ] by auto
  then have le1: "adjoint M1 * Q * M1 \<le>\<^sub>L adjoint M1 * M1" using dM1 dQ by fastforce
  have "adjoint M0 * P * M0 \<le>\<^sub>L adjoint M0 * 1\<^sub>m d * M0"
    using lowner_le_keep_under_measurement[OF dM0 dP _ leP] by auto
  then have le0: "adjoint M0 * P * M0 \<le>\<^sub>L adjoint M0 * M0"
    using dM0 dP by fastforce
  have "adjoint M0 * P * M0 + adjoint M1 * Q * M1 \<le>\<^sub>L adjoint M0 * M0 + adjoint M1 * M1"
    apply (rule lowner_le_add[of "adjoint M0 * P * M0" d "adjoint M0 * M0" "adjoint M1 * Q * M1" "adjoint M1 * M1"])
    using dM0 dP dM1 dQ le0 le1 by auto
  also have "\<dots> = 1\<^sub>m d" using m M0_def M1_def measurement_id2 by auto
  finally show "adjoint M0 * P * M0 + adjoint M1 * Q * M1 \<le>\<^sub>L 1\<^sub>m d".
qed

lemma wlp_while_n_close:
  assumes close: "\<And>P. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (WS P)"
    and m: "measurement d 2 M" and qpP: "is_quantum_predicate P"
  shows "is_quantum_predicate (wlp_while_n (M 0) (M 1) WS k P)"
proof (induct k)
  case 0
  then show ?case 
    unfolding wlp_while_n.simps is_quantum_predicate_def using positive_one[of d] lowner_le_refl[of "1\<^sub>m d"] by fastforce
next
  case (Suc k)
  define M0 where "M0 = M 0" 
  define M1 where "M1 = M 1"
  define W where "W k = wlp_while_n M0 M1 WS k P" for k
  show ?case unfolding wlp_while_n.simps is_quantum_predicate_def
  proof (fold M0_def M1_def, fold W_def, auto)
    have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using m M0_def M1_def measurement_def by auto
    have dP:  "P \<in> carrier_mat d d" using qpP is_quantum_predicate_def by auto
    have qpWk: "is_quantum_predicate (W k)" using Suc M0_def M1_def W_def by auto
    then have qpWWk: "is_quantum_predicate (WS (W k))" using close by auto
    from qpWk have dWk: "W k \<in> carrier_mat d d" using is_quantum_predicate_def by auto
    from qpWWk have dWWk: "WS (W k) \<in> carrier_mat d d" using is_quantum_predicate_def by auto
    show "adjoint M0 * P * M0 + adjoint M1 * WS (W k) * M1 \<in> carrier_mat d d" using dM0 dP dM1 dWWk by auto

    have pP: "positive P" using qpP is_quantum_predicate_def by auto
    then have pM0P: "positive (adjoint M0 * P * M0)" 
      using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dM0]] dM0 dP adjoint_adjoint[of M0] by auto
    have pWWk: "positive (WS (W k))" using qpWWk is_quantum_predicate_def by auto
    then have pM1WWk: "positive (adjoint M1 * WS (W k) * M1)"
      using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dM1]] dM1 dWWk adjoint_adjoint[of M1] by auto
    then show "positive (adjoint M0 * P * M0 + adjoint M1 * WS (W k) * M1)"
      using positive_add[OF pM0P pM1WWk] dM0 dP dM1 dWWk by fastforce

    have leWWk: "WS (W k) \<le>\<^sub>L 1\<^sub>m d" using qpWWk is_quantum_predicate_def by auto
    have leP: "P \<le>\<^sub>L 1\<^sub>m d" using qpP is_quantum_predicate_def by auto
    show "(adjoint M0 * P * M0 + adjoint M1 * WS (W k) * M1) \<le>\<^sub>L 1\<^sub>m d " 
      using measurement2_leq_one_mat[OF dP dWWk leP leWWk m] M0_def M1_def by auto
  qed
qed

lemma wlp_while_n_mono:
  assumes "\<And>P. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (WS P)"
    and "\<And>P Q. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q \<Longrightarrow> WS P \<le>\<^sub>L WS Q"
    and "measurement d 2 M"
    and "is_quantum_predicate P"
    and "is_quantum_predicate Q"
    and "P \<le>\<^sub>L Q"
  shows "(wlp_while_n (M 0) (M 1) WS k P) \<le>\<^sub>L (wlp_while_n (M 0) (M 1) WS k Q)"
proof (induct k)
  case 0
  then show ?case unfolding wlp_while_n.simps using lowner_le_refl[of "1\<^sub>m d"] by fastforce
next
  case (Suc k)
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using assms M0_def M1_def measurement_def by auto
  define W where "W P k = wlp_while_n M0 M1 WS k P" for k P

  have dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d" using assms is_quantum_predicate_def by auto

  have eq1: "W P (Suc k) = adjoint M0 * P * M0 + adjoint M1 * (WS (W P k)) * M1" unfolding W_def wlp_while_n.simps by auto
  have eq2: "W Q (Suc k) = adjoint M0 * Q * M0 + adjoint M1 * (WS (W Q k)) * M1" unfolding W_def wlp_while_n.simps by auto
  have le1: "adjoint M0 * P * M0 \<le>\<^sub>L adjoint M0 * Q * M0" using lowner_le_keep_under_measurement dM0 dP dQ assms by auto
  have leWk: "(W P k) \<le>\<^sub>L (W Q k)" unfolding W_def M0_def M1_def using Suc by auto
  have qpWPk: "is_quantum_predicate (W P k)" unfolding W_def M0_def M1_def using wlp_while_n_close assms by auto
  then have "is_quantum_predicate (WS (W P k))" unfolding W_def M0_def M1_def using assms by auto
  then have dWWPk: "(WS (W P k)) \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  have qpWQk: "is_quantum_predicate (W Q k)" unfolding W_def M0_def M1_def using wlp_while_n_close assms by auto
  then have "is_quantum_predicate (WS (W Q k))" unfolding W_def M0_def M1_def using assms by auto
  then have dWWQk: "(WS (W Q k)) \<in> carrier_mat d d" using is_quantum_predicate_def by auto

  have "(WS (W P k)) \<le>\<^sub>L (WS (W Q k))" using qpWPk qpWQk leWk assms by auto
  then have le2: "adjoint M1 * (WS (W P k)) * M1 \<le>\<^sub>L adjoint M1 * (WS (W Q k)) * M1"
    using lowner_le_keep_under_measurement dM1 dWWPk dWWQk by auto

  have "(adjoint M0 * P * M0 + adjoint M1 * (WS (W P k)) * M1) \<le>\<^sub>L (adjoint M0 * Q * M0 + adjoint M1 * (WS (W Q k)) * M1)"
    using lowner_le_add[OF _ _ _ _ le1 le2] dM0 dP dM1 dQ dWWPk dWWQk le1 le2 by fastforce

  then have "W P (Suc k) \<le>\<^sub>L W Q (Suc k)" using eq1 eq2 by auto
  then show ?case unfolding W_def M0_def M1_def by auto
qed

definition wlp_while :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (complex mat \<Rightarrow> complex mat) \<Rightarrow> complex mat \<Rightarrow> complex mat" where
  "wlp_while M0 M1 WS P = (THE Q. limit_mat (\<lambda>n. wlp_while_n M0 M1 WS n P) Q d)"

lemma wlp_while_exists:
  assumes "\<And>P. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (WS P)"
    and "\<And>P Q. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q \<Longrightarrow> WS P \<le>\<^sub>L WS Q"
    and m: "measurement d 2 M"
    and qpP: "is_quantum_predicate P"
  shows "is_quantum_predicate (wlp_while (M 0) (M 1) WS P) 
    \<and> (\<forall>n. (wlp_while (M 0) (M 1) WS P) \<le>\<^sub>L (wlp_while_n (M 0) (M 1) WS n P))
    \<and> (\<forall>W'. (\<forall>n. W' \<le>\<^sub>L (wlp_while_n (M 0) (M 1) WS n P)) \<longrightarrow> W' \<le>\<^sub>L (wlp_while (M 0) (M 1) WS P))
    \<and> limit_mat (\<lambda>n. wlp_while_n (M 0) (M 1) WS n P) (wlp_while (M 0) (M 1) WS P) d"
proof (auto)
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using assms M0_def M1_def measurement_def by auto
  define W where "W k = wlp_while_n M0 M1 WS k P" for k
  have leP: "P \<le>\<^sub>L 1\<^sub>m d" and dP: "P \<in> carrier_mat d d" and pP: "positive P" using qpP is_quantum_predicate_def by auto
  have pM0P: "positive (adjoint M0 * P * M0)" 
    using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dM0]] adjoint_adjoint[of "M0"] dP pP by  auto

  have le_qp: "W (Suc k) \<le>\<^sub>L W k \<and> is_quantum_predicate (W k)" for k
  proof (induct k)
    case 0
    have "is_quantum_predicate (1\<^sub>m d)" 
      unfolding is_quantum_predicate_def using positive_one lowner_le_refl[of "1\<^sub>m d"] by fastforce
    then have "is_quantum_predicate (WS (1\<^sub>m d))" using assms by auto
    then have "(WS (1\<^sub>m d)) \<in> carrier_mat d d" and "(WS (1\<^sub>m d)) \<le>\<^sub>L 1\<^sub>m d" using is_quantum_predicate_def by auto
    then have "W 1 \<le>\<^sub>L W 0" unfolding W_def wlp_while_n.simps M0_def M1_def
      using measurement2_leq_one_mat[OF dP _ leP _ m] by auto
    moreover have "is_quantum_predicate (W 0)" unfolding W_def wlp_while_n.simps is_quantum_predicate_def
      using positive_one lowner_le_refl[of "1\<^sub>m d"] by fastforce
    ultimately show ?case by auto
  next
    case (Suc k)
    then have leWSk: "W (Suc k) \<le>\<^sub>L W k" and qpWk: "is_quantum_predicate (W k)"  by auto
    then have "is_quantum_predicate (WS (W k))" using assms by auto
    then have dWWk: "WS (W k) \<in> carrier_mat d d" and leWWk1: "(WS (W k)) \<le>\<^sub>L 1\<^sub>m d" and pWWk: "positive (WS (W k))"
      using is_quantum_predicate_def by auto
    then have leWSk1: "W (Suc k) \<le>\<^sub>L 1\<^sub>m d" using measurement2_leq_one_mat[OF dP dWWk leP leWWk1 m]
      unfolding W_def wlp_while_n.simps M0_def M1_def by auto
    then have dWSk: "W (Suc k) \<in> carrier_mat d d" using lowner_le_def by fastforce
    have pM1WWk: "positive (adjoint M1 * (WS (W k)) * M1)" 
      using positive_close_under_left_right_mult_adjoint[OF adjoint_dim[OF dM1] dWWk pWWk] adjoint_adjoint[of "M1"] by auto
    have pWSk: "positive (W (Suc k))" unfolding W_def wlp_while_n.simps apply (fold W_def)
      using positive_add[OF pM0P pM1WWk] dM0 dP dM1 by fastforce
    have qpWSk:"is_quantum_predicate (W (Suc k))" unfolding is_quantum_predicate_def using dWSk pWSk leWSk1 by auto
    then have qpWWSk: "is_quantum_predicate (WS (W (Suc k)))" using assms(1) by auto
    then have dWWSk: "(WS (W (Suc k))) \<in> carrier_mat d d" using is_quantum_predicate_def by auto

    have "WS (W (Suc k)) \<le>\<^sub>L WS (W k)" using assms(2)[OF qpWSk qpWk] leWSk by auto
    then have "adjoint M1 * WS (W (Suc k)) * M1 \<le>\<^sub>L adjoint M1 * WS (W k) * M1"
      using lowner_le_keep_under_measurement[OF dM1 dWWSk dWWk] by auto
    then have "(adjoint M0 * P * M0 + adjoint M1 * WS (W (Suc k)) * M1)
              \<le>\<^sub>L (adjoint M0 * P * M0 + adjoint M1 * WS (W k) * M1)"
      using lowner_le_add[of _ d _ "adjoint M1 * WS (W (Suc k)) * M1" "adjoint M1 * WS (W k) * M1", 
            OF _ _ _ _ lowner_le_refl[of "adjoint M0 * P * M0"]] dM0 dM1 dP dWWSk dWWk by fastforce
    then have "W (Suc (Suc k)) \<le>\<^sub>L W (Suc k)" unfolding W_def wlp_while_n.simps by auto
    with qpWSk show ?case by auto
  qed
  then have dWk: "W k \<in> carrier_mat d d" for k using is_quantum_predicate_def by auto
  then have dmWk: "- W k \<in> carrier_mat d d" for k by auto
  have incmWk: "- (W k) \<le>\<^sub>L - (W (Suc k))" for k using lowner_le_swap[of "W (Suc k)" d "W k"] dWk le_qp by auto
  have pWk: "positive (W k)" for k using le_qp is_quantum_predicate_def by auto
  have ubmWk: "- W k \<le>\<^sub>L 0\<^sub>m d d" for k
  proof -
    have "0\<^sub>m d d \<le>\<^sub>L W k" for k using zero_lowner_le_positiveI dWk pWk by auto
    then have "- W k \<le>\<^sub>L - 0\<^sub>m d d" for k using lowner_le_swap[of "0\<^sub>m d d" d "W k"] dWk by auto
    moreover have "(- 0\<^sub>m d d :: complex mat) = (0\<^sub>m d d)" by auto
    ultimately show ?thesis by auto
  qed

  have "\<exists>B. lowner_is_lub (\<lambda>k. - W k) B \<and> limit_mat (\<lambda>k. - W k) B d" 
    using mat_inc_seq_lub[of "\<lambda>k. - W k" d "0\<^sub>m d d"] dmWk incmWk ubmWk by auto
  then obtain B where lubB: "lowner_is_lub (\<lambda>k. - W k) B" and limB: "limit_mat (\<lambda>k. - W k) B d" by auto
  then have dB: "B \<in> carrier_mat d d" using limit_mat_def by auto
  define A where "A = - B"
  then have dA: "A \<in> carrier_mat d d" using dB by auto
  have "limit_mat (\<lambda>k. (-1) \<cdot>\<^sub>m (- W k)) (-1 \<cdot>\<^sub>m B) d" using limit_mat_scale[OF limB] by auto
  moreover have "W k = -1 \<cdot>\<^sub>m (- W k)" for k using dWk by auto
  moreover have "-1 \<cdot>\<^sub>m B = - B" by auto
  ultimately have limA: "limit_mat W A d" using A_def by auto
  moreover have "(limit_mat W A' d \<Longrightarrow> A' = A)" for A' using limit_mat_unique[of W A d] limA by auto
  ultimately have eqA: "(wlp_while (M 0) (M 1) WS P) = A" unfolding wlp_while_def W_def M0_def M1_def 
    using the_equality[of "\<lambda>X. limit_mat (\<lambda>n. wlp_while_n (M 0) (M 1) WS n P) X d" A] by fastforce

  show "limit_mat (\<lambda>n. wlp_while_n (M 0) (M (Suc 0)) WS n P) (wlp_while (M 0) (M (Suc 0)) WS P) d" 
    using limA eqA unfolding W_def M0_def M1_def by auto

  have "- W k \<le>\<^sub>L B" for k using lubB lowner_is_lub_def by auto
  then have glbA: "A \<le>\<^sub>L W k" for k unfolding A_def using lowner_le_swap[of "- W k" d] dB dWk by fastforce
  then show "\<And>n. wlp_while (M 0) (M (Suc 0)) WS P \<le>\<^sub>L wlp_while_n (M 0) (M (Suc 0)) WS n P" using eqA unfolding W_def M0_def M1_def by auto

  have "W k \<le>\<^sub>L 1\<^sub>m d" for k using le_qp unfolding is_quantum_predicate_def by auto
  then have "positive (1\<^sub>m d - W k)" for k using lowner_le_def by auto
  moreover have "limit_mat (\<lambda>k. 1\<^sub>m d - W k) (1\<^sub>m d - A) d" using mat_minus_limit limA by auto
  ultimately have "positive (1\<^sub>m d - A)" using pos_mat_lim_is_pos by auto
  then have leA1: "A \<le>\<^sub>L 1\<^sub>m d" using dA lowner_le_def by auto

  have pA: "positive A" using pos_mat_lim_is_pos limA pWk by auto

  show "is_quantum_predicate (wlp_while (M 0) (M (Suc 0)) WS P)" unfolding is_quantum_predicate_def using pA dA leA1 eqA by auto

  {
    fix W' assume asmW': "\<forall>k. W' \<le>\<^sub>L W k"  
    then have dW': "W' \<in> carrier_mat d d" unfolding lowner_le_def using carrier_matD[OF dWk] by auto
    then have "- W k \<le>\<^sub>L - W'" for k using lowner_le_swap dWk asmW' by auto
    then have "B \<le>\<^sub>L - W'" using lubB unfolding lowner_is_lub_def by auto
    then have "W' \<le>\<^sub>L A" unfolding A_def 
      using lowner_le_swap[of "B" d "- W'"] dB dW'  by auto
    then have "W' \<le>\<^sub>L wlp_while (M 0) (M 1) WS P" using eqA by auto
  }
  then show "\<And>W'. \<forall>n. W' \<le>\<^sub>L wlp_while_n (M 0) (M (Suc 0)) WS n P \<Longrightarrow> W' \<le>\<^sub>L wlp_while (M 0) (M (Suc 0)) WS P"
    unfolding W_def M0_def M1_def by auto
qed

lemma wlp_while_mono:
  assumes "\<And>P. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (WS P)"
    and "\<And>P Q. is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q \<Longrightarrow> WS P \<le>\<^sub>L WS Q"
    and "measurement d 2 M"
    and "is_quantum_predicate P"
    and "is_quantum_predicate Q"
    and "P \<le>\<^sub>L Q"
  shows "wlp_while (M 0) (M 1) WS P \<le>\<^sub>L wlp_while (M 0) (M 1) WS Q"
proof -
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using assms M0_def M1_def measurement_def by auto
  define Wn where "Wn P k = wlp_while_n M0 M1 WS k P" for P k
  define W where "W P = wlp_while M0 M1 WS P" for P
  have lePQk: "Wn P k \<le>\<^sub>L Wn Q k" for k unfolding Wn_def M0_def M1_def 
    using wlp_while_n_mono assms by auto
  have "is_quantum_predicate (Wn P k)" for k unfolding Wn_def M0_def M1_def using wlp_while_n_close assms by auto
  then have dWPk: "Wn P k \<in> carrier_mat d d" for k using is_quantum_predicate_def by auto
  have "is_quantum_predicate (Wn Q k)" for k unfolding Wn_def M0_def M1_def using wlp_while_n_close assms by auto
  then have dWQk:"Wn Q k \<in> carrier_mat d d" for k using is_quantum_predicate_def by auto
  have "is_quantum_predicate (W P)" and lePk: "(W P) \<le>\<^sub>L (Wn P k)" and "limit_mat (Wn P) (W P) d" for k
    unfolding W_def Wn_def M0_def M1_def using wlp_while_exists assms by auto
  then have dWP: "W P \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  have "is_quantum_predicate (W Q)" and "(W Q) \<le>\<^sub>L (Wn Q k)" 
    and glb:"(\<forall>k. W' \<le>\<^sub>L (Wn Q k)) \<longrightarrow> W' \<le>\<^sub>L (W Q)" and "limit_mat (Wn Q) (W Q) d" for k W'
    unfolding W_def Wn_def M0_def M1_def using wlp_while_exists assms by auto

  have "W P \<le>\<^sub>L Wn Q k" for k using lowner_le_trans[of "W P" d "Wn P k" "Wn Q k"] lePk lePQk dWPk dWQk dWP by auto
  then show "W P \<le>\<^sub>L W Q" using glb by auto
qed

fun wlp :: "com \<Rightarrow> complex mat \<Rightarrow> complex mat" where
  "wlp SKIP P = P"
| "wlp (Utrans U) P = adjoint U * P * U"
| "wlp (Seq S1 S2) P = wlp S1 (wlp S2 P)"
| "wlp (Measure n M S) P = wlp_measure n M (map wlp S) P"
| "wlp (While M S) P = wlp_while (M 0) (M 1) (wlp S) P"

lemma wlp_measure_expand_m:
  assumes m: "m \<le> n" and wc: "well_com (Measure n M S)"  
  shows "wlp (Measure m M S) P = matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * (M k)) m"
  unfolding wlp.simps wlp_measure_def
proof -
  have "k < m \<Longrightarrow> map wlp S ! k = wlp (S!k)" for k using wc m by auto
  then have "k < m \<Longrightarrow> (map wlp S ! k) P = wlp (S!k) P" for k by auto
  then show "matrix_sum d (\<lambda>k. adjoint (M k) * ((map wlp S ! k) P) * (M k)) m
    = matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * (M k)) m" 
    using matrix_sum_cong[of m "\<lambda>k. adjoint (M k) * ((map wlp S ! k) P) * (M k)" "\<lambda>k. adjoint (M k) * (wlp (S!k) P) * (M k)"] by auto
qed

lemma wlp_measure_expand:
  assumes wc: "well_com (Measure n M S)"  
  shows "wlp (Measure n M S) P = matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * (M k)) n"
  using wlp_measure_expand_m[OF Nat.le_refl[of n]] wc by auto

lemma wlp_mono_and_close:
  shows "well_com S \<Longrightarrow> is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q 
        \<Longrightarrow> is_quantum_predicate (wlp S P) \<and> wlp S P \<le>\<^sub>L wlp S Q"
proof (induct S arbitrary: P Q)
  case SKIP
  then show ?case by auto
next
  case (Utrans U)
  then have dU: "U \<in> carrier_mat d d" and u: "unitary U" and qp: "is_quantum_predicate P"  and le: "P \<le>\<^sub>L Q"
    and dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  then have qp': "is_quantum_predicate (wlp (Utrans U) P)" using qp_close_under_unitary_operator by auto
  moreover have "adjoint U * P * U \<le>\<^sub>L adjoint U * Q * U" using lowner_le_keep_under_measurement[OF dU dP dQ le] by auto
  ultimately show ?case by auto
next
  case (Seq S1 S2)
  then have qpP: "is_quantum_predicate P" and qpQ: "is_quantum_predicate Q" and wc1: "well_com S1" and wc2: "well_com S2" 
    and dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d" and le: "P \<le>\<^sub>L Q"using is_quantum_predicate_def by auto
  have qpP2: "is_quantum_predicate (wlp S2 P)" using Seq qpP wc2 by auto
  have qpQ2: "is_quantum_predicate (wlp S2 Q)" using Seq(2)[OF wc2 qpQ qpQ] lowner_le_refl dQ by blast
  have qpP1: "is_quantum_predicate (wlp S1 (wlp S2 P))" 
    using Seq(1)[OF wc1 qpP2 qpP2] qpP2 is_quantum_predicate_def[of "wlp S2 P"] lowner_le_refl by auto
  have "wlp S2 P \<le>\<^sub>L wlp S2 Q" using Seq(2) wc2 qpP qpQ le by auto
  then have "wlp S1 (wlp S2 P) \<le>\<^sub>L wlp S1 (wlp S2 Q)" using Seq(1) wc1 qpP2 qpQ2 by auto
  then show ?case using qpP1 by auto
next
  case (Measure n M S)
  then have wc: "well_com (Measure n M S)" and wck: "k < n \<Longrightarrow> well_com (S!k)" and l: "length S = n"
    and m: "measurement d n M" and le: "P \<le>\<^sub>L Q"
    and qpP: "is_quantum_predicate P" and dP: "P \<in> carrier_mat d d" 
    and qpQ: "is_quantum_predicate Q" and dQ: "Q \<in> carrier_mat d d"
    for k using measure_well_com is_quantum_predicate_def by auto
  have dMk: "k < n \<Longrightarrow> M k \<in> carrier_mat d d" for k using m measurement_def by auto
  have set: "k < n \<Longrightarrow> S!k \<in> set S" for k using l by auto
  have qpk: "k < n \<Longrightarrow> is_quantum_predicate (wlp (S!k) P)" for k 
    using Measure(1)[OF set wck qpP qpP] lowner_le_refl[of P] dP by auto
  then have dWkP: "k < n \<Longrightarrow> wlp (S!k) P \<in> carrier_mat d d" for k using is_quantum_predicate_def by auto
  then have dMkP: "k < n \<Longrightarrow> adjoint (M k) * (wlp (S!k) P) * (M k) \<in> carrier_mat d d" for k using dMk by fastforce
  have "k < n \<Longrightarrow> is_quantum_predicate (wlp (S!k) Q)" for k 
    using Measure(1)[OF set wck qpQ qpQ] lowner_le_refl[of Q] dQ by auto
  then have dWkQ: "k < n \<Longrightarrow> wlp (S!k) Q \<in> carrier_mat d d" for k using is_quantum_predicate_def by auto
  then have dMkQ: "k < n \<Longrightarrow> adjoint (M k) * (wlp (S!k) Q) * (M k) \<in> carrier_mat d d" for k using dMk by fastforce
  have "k < n \<Longrightarrow> wlp (S!k) P \<le>\<^sub>L wlp (S!k) Q" for k 
    using Measure(1)[OF set wck qpP qpQ le] by auto
  then have "k < n \<Longrightarrow> adjoint (M k) * (wlp (S!k) P) * (M k) \<le>\<^sub>L adjoint (M k) * (wlp (S!k) Q) * (M k)" for k
    using lowner_le_keep_under_measurement[OF dMk dWkP dWkQ] by auto
  then have le': "wlp (Measure n M S) P \<le>\<^sub>L wlp (Measure n M S) Q" unfolding wlp_measure_expand[OF wc]
    using lowner_le_matrix_sum dMkP dMkQ by auto
  have qp': "is_quantum_predicate (wlp (Measure n M S) P)" unfolding wlp_measure_expand[OF wc]
    using qps_after_measure_is_qp[OF m] qpk by auto
  show ?case using le' qp' by auto
next
  case (While M S)
  then have m: "measurement d 2 M" and wcs: "well_com S" 
    and qpP: "is_quantum_predicate P"
    by auto
  have closeWS: "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (wlp S P)" for P
  proof -
    assume asm: "is_quantum_predicate P"
    then have dP: "P \<in> carrier_mat d d" using is_quantum_predicate_def by auto
    then show "is_quantum_predicate (wlp S P)" using While(1)[OF wcs asm asm lowner_le_refl] dP by auto
  qed
  have monoWS: "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q \<Longrightarrow> wlp S P \<le>\<^sub>L wlp S Q" for P Q
    using While(1)[OF wcs] by auto
  have "is_quantum_predicate (wlp (While M S) P)"
    using wlp_while_exists[of "wlp S" M P] closeWS monoWS m qpP by auto
  moreover have "wlp (While M S) P \<le>\<^sub>L wlp (While M S) Q"
    using wlp_while_mono[of "wlp S" M P Q] closeWS monoWS m While by auto
  ultimately show ?case by auto
qed

lemma wlp_close:
  assumes wc: "well_com S" and qp: "is_quantum_predicate P"
  shows "is_quantum_predicate (wlp S P)" 
  using wlp_mono_and_close[OF wc qp qp] is_quantum_predicate_def[of P] qp lowner_le_refl by auto

lemma wlp_soundness:
  "well_com S \<Longrightarrow> 
    (\<And>P. (is_quantum_predicate P \<Longrightarrow> 
      (\<forall>\<rho> \<in> density_states. trace (wlp S P * \<rho>) = trace (P * (denote S \<rho>)) + trace \<rho> - trace (denote S \<rho>))))"
proof (induct S)
  case SKIP
then show ?case by auto
next
  case (Utrans U)
  then have dU: "U \<in> carrier_mat d d" and u: "unitary U" and wc: "well_com (Utrans U)" 
    and qp: "is_quantum_predicate P" and dP: "P \<in> carrier_mat d d"  using is_quantum_predicate_def by auto
  have qp': "is_quantum_predicate (wlp (Utrans U) P)" using wlp_close[OF wc qp] by auto
  have eq1: "trace (adjoint U * P * U * \<rho>) = trace (P * (U * \<rho> * adjoint U))" if dr: "\<rho> \<in> carrier_mat d d" for \<rho>
    using dr dP apply (mat_assoc d) using wc by auto
  have eq2: "trace (U * \<rho> * adjoint U) = trace \<rho>" if dr: "\<rho> \<in> carrier_mat d d" for \<rho>
    using unitary_operator_keep_trace[OF adjoint_dim[OF dU] dr unitary_adjoint[OF dU u]] adjoint_adjoint[of U] by auto
  show ?case using qp' eq1 eq2 density_states_def by auto
next
  case (Seq S1 S2)
  then have qp: "is_quantum_predicate P" and wc1: "well_com S1" and wc2: "well_com S2" by auto
  then have qp2: "is_quantum_predicate (wlp S2 P)" using wlp_close by auto
  then have qp1: "is_quantum_predicate (wlp S1 (wlp S2 P))" using wlp_close wc1 by auto
  have eq1: "trace (wlp S2 P * \<rho>) = trace (P * denote S2 \<rho>) + trace \<rho> - trace (denote S2 \<rho>)" 
    if ds: "\<rho> \<in> density_states" for \<rho> using Seq(2) wc2 qp ds by auto
  have eq2: "trace (wlp S1 (wlp S2 P) * \<rho>) = trace ((wlp S2 P) * denote S1 \<rho>) + trace \<rho> - trace (denote S1 \<rho>)" 
    if ds: "\<rho> \<in> density_states" for \<rho> using Seq(1) wc1 qp2 ds by auto
  have eq3: "trace (wlp S1 (wlp S2 P) * \<rho>) = trace (P * (denote S2 (denote S1 \<rho>))) + trace \<rho> - trace (denote S2 (denote S1 \<rho>))" 
    if ds: "\<rho> \<in> density_states" for \<rho>
  proof -
    have "denote S1 \<rho> \<in> density_states"
      using ds denote_density_states wc1  by auto
    then have  "trace ((wlp S2 P) * denote S1 \<rho>) = trace (P * denote S2 (denote S1 \<rho>)) + trace (denote S1 \<rho>) - trace (denote S2 (denote S1 \<rho>))"
      using eq1 by auto
    then show "trace (wlp S1 (wlp S2 P) * \<rho>) = trace (P * (denote S2 (denote S1 \<rho>))) + trace \<rho> - trace (denote S2 (denote S1 \<rho>))"
      using eq2 ds by auto
  qed
  then show ?case using qp1 by auto
next
  case (Measure n M S)
  then have wc: "well_com (Measure n M S)"
    and wck: "k < n \<Longrightarrow> well_com (S!k)"
    and qpP: "is_quantum_predicate P"
    and dP: "P \<in> carrier_mat d d"
    and qpWk: "k < n \<Longrightarrow> is_quantum_predicate (wlp (S!k) P)"
    and dWk: "k < n \<Longrightarrow> (wlp (S!k) P) \<in> carrier_mat d d"
    and c: "k < n \<Longrightarrow> \<rho> \<in> density_states \<Longrightarrow> trace (wlp (S!k) P * \<rho>) = trace (P * denote (S!k) \<rho>) + trace \<rho> - trace (denote (S!k) \<rho>)" 
    and m: "measurement d n M"
    and aMMkleq: "k < n \<Longrightarrow> adjoint (M k) * M k \<le>\<^sub>L 1\<^sub>m d"
    and dMk: "k < n \<Longrightarrow> M k \<in> carrier_mat d d"
    for k \<rho> using is_quantum_predicate_def measurement_def measure_well_com measurement_le_one_mat wlp_close by auto
    {
    fix \<rho> assume \<rho>: "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
    have dsr: "k < n \<Longrightarrow> (M k) * \<rho> * adjoint (M k) \<in> density_states" for k unfolding density_states_def 
      using dMk pdo_close_under_measurement[OF dMk dr pdor aMMkleq] dr by fastforce
    then have leqk: "k < n \<Longrightarrow> trace (wlp (S!k) P * ((M k) * \<rho> * adjoint (M k))) = 
      trace (P * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
      (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))" for k 
      using c by auto
    have "k < n \<Longrightarrow> M k * \<rho> * adjoint (M k) \<in> carrier_mat d d" for k using dMk dr by fastforce
    then have dsMrk: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. (M k * \<rho> * adjoint (M k))) k \<in> carrier_mat d d" for k 
      using matrix_sum_dim[of k "\<lambda>k. (M k * \<rho> * adjoint (M k))" d] by fastforce
    have "k < n \<Longrightarrow> adjoint (M k) * (wlp (S!k) P) * M k \<in> carrier_mat d d" for k using dMk by fastforce
    then have dsMW: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) k \<in> carrier_mat d d" for k 
      using matrix_sum_dim[of k "\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k" d] by fastforce
    have dSMrk: "k < n \<Longrightarrow> denote (S ! k) (M k * \<rho> * adjoint (M k)) \<in> carrier_mat d d" for k 
      using denote_dim[OF wck, of k "M k * \<rho> * adjoint (M k)"] dsr density_states_def by fastforce
    have dsSMrk: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k \<in> carrier_mat d d" for k
      using matrix_sum_dim[of k "\<lambda>k. denote (S ! k) (M k * \<rho> * adjoint (M k))" d, OF dSMrk] by fastforce
    have "k \<le> n \<Longrightarrow> 
        trace (matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) k * \<rho>)
       = trace (P * (denote (Measure k M S) \<rho>)) + (trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) k) - trace (denote (Measure k M S) \<rho>))" for k 
      unfolding denote_measure_expand[OF _ wc]
    proof (induct k)
      case 0
      then show ?case unfolding matrix_sum.simps using dP dr by auto
    next
      case (Suc k)
      then have k: "k < n" by auto
      have eq1: "trace (matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) (Suc k) * \<rho>) 
        = trace (adjoint (M k) * (wlp (S!k) P) * M k * \<rho>) + trace (matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) k * \<rho>)"
        unfolding matrix_sum.simps
        using dMk[OF k] dWk[OF k] dr dsMW[OF k] by (mat_assoc d)

      have "trace (adjoint (M k) * (wlp (S!k) P) * M k * \<rho>) = trace ((wlp (S!k) P) * (M k * \<rho> * adjoint (M k)))" 
        using dMk[OF k] dWk[OF k] dr by (mat_assoc d)
      also have "\<dots> = trace (P * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
        (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))" using leqk k by auto
      finally have eq2: "trace (adjoint (M k) * (wlp (S!k) P) * M k * \<rho>) = trace (P * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
        (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))" .

      have eq3: "trace (P * matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) (Suc k)) 
        = trace (P * (denote (S!k) (M k * \<rho> * adjoint (M k)))) + trace (P * matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)"
        unfolding matrix_sum.simps
        using dP dSMrk[OF k] dsSMrk[OF k] by (mat_assoc d)

      have eq4: "trace (denote (S ! k) (M k * \<rho> * adjoint (M k)) + matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)
        = trace (denote (S ! k) (M k * \<rho> * adjoint (M k))) + trace (matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)"
        using dSMrk[OF k] dsSMrk[OF k] by (mat_assoc d)

      show ?case
        apply (subst eq1) apply (subst eq3) 
        apply (simp del: less_eq_complex_def) 
        apply (subst trace_add_linear[of "M k * \<rho> * adjoint (M k)" d "matrix_sum d (\<lambda>k. M k * \<rho> * adjoint (M k)) k"])
          apply (simp add: dMk adjoint_dim[OF dMk] dr mult_carrier_mat[of _ d d _ d] k)
         apply (simp add: dsMrk k)
        apply (subst eq4)
        apply (insert eq2 Suc(1) k, fastforce)
        done
    qed
    then have leq: "trace (matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) n * \<rho>)
       = trace (P * denote (Measure n M S) \<rho>) + 
          (trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) n) - trace (denote (Measure n M S) \<rho>))"
      by auto
    have "trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) n) = trace \<rho>" using trace_measurement m dr by auto

    with leq have "trace (matrix_sum d (\<lambda>k. adjoint (M k) * (wlp (S!k) P) * M k) n * \<rho>)
       = trace (P * denote (Measure n M S) \<rho>) + (trace \<rho> - trace (denote (Measure n M S) \<rho>))"
      unfolding denote_measure_def by auto
  }
  then show ?case unfolding wlp_measure_expand[OF wc] by auto
next
  case (While M S)
  then have qpP: "is_quantum_predicate P" and dP: "P \<in> carrier_mat d d" 
    and wcS: "well_com S" and m: "measurement d 2 M" and wc: "well_com (While M S)"
    using is_quantum_predicate_def by auto
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using m measurement_def M0_def M1_def by auto
  have leM1: "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat m M1_def by auto
  define W where "W k = wlp_while_n M0 M1 (wlp S) k P" for k
  define DS where "DS = denote S"
  define D0 where "D0 = denote_while_n M0 M1 DS"
  define D1 where "D1 = denote_while_n_comp M0 M1 DS"
  define D where "D = denote_while_n_iter M0 M1 DS"

  have eqk: "\<rho> \<in> density_states \<Longrightarrow> trace ((W k) * \<rho>) = (\<Sum>k=0..<k. trace (P * (D0 k \<rho>))) + trace \<rho> - (\<Sum>k=0..<k. trace (D0 k \<rho>))" for k \<rho> 
  proof (induct k arbitrary: \<rho>)
    case 0
    then have dsr: "\<rho> \<in> density_states" by auto
    show ?case unfolding W_def wlp_while_n.simps using dsr density_states_def by auto 
  next
    case (Suc k)
    then have dsr: "\<rho> \<in> density_states" and dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
    then have dsM1r: "M1 * \<rho> * adjoint M1 \<in> density_states" unfolding density_states_def using pdo_close_under_measurement[OF dM1 dr pdor leM1] dr dM1 by auto
    then have dsDSM1r: "(DS (M1 * \<rho> * adjoint M1)) \<in> density_states" unfolding density_states_def DS_def 
      using denote_dim[OF wcS] denote_partial_density_operator[OF wcS] dsM1r by auto
    have qpWk: "is_quantum_predicate (W k)" 
      using wlp_while_n_close[OF _ m qpP, folded M0_def M1_def, of "wlp S", folded W_def] wlp_close[OF wcS] by auto
    then have "is_quantum_predicate (wlp S (W k))" using wlp_close[OF wcS] by auto
    then have dWWk: "wlp S (W k) \<in> carrier_mat d d" using is_quantum_predicate_def by auto

    have "trace (P * (M0 * \<rho> * adjoint M0)) + (\<Sum>k=0..<k. trace (P * (D0 k (DS (M1 * \<rho> * adjoint M1)))))
      = trace (P * (D0 0 \<rho>)) + (\<Sum>k=0..<k. trace (P * (D0 (Suc k) \<rho>)))"
      unfolding D0_def by auto
    also have "\<dots> = trace (P * (D0 0 \<rho>)) + (\<Sum>k=1..<(Suc k). trace (P * (D0 k \<rho>)))"
      using sum.shift_bounds_Suc_ivl[symmetric, of "\<lambda>k. trace (P * (D0 k \<rho>))"] by auto
    also have "\<dots> = (\<Sum>k=0..<(Suc k). trace (P * (D0 k \<rho>)))" using sum.atLeast_Suc_lessThan[of 0 "Suc k" "\<lambda>k. trace (P * (D0 k \<rho>))"] by auto
    finally have eq1: "trace (P * (M0 * \<rho> * adjoint M0)) + (\<Sum>k=0..<k. trace (P * (D0 k (DS (M1 * \<rho> * adjoint M1))))) 
      = (\<Sum>k=0..<(Suc k). trace (P * (D0 k \<rho>)))".

    have eq2: "trace (M1 * \<rho> * adjoint M1) = trace \<rho> - trace (M0 * \<rho> * adjoint M0)" 
      unfolding M0_def M1_def using m trace_measurement2[OF m dr] dr by (simp add: algebra_simps)

    have "trace (M0 * \<rho> * adjoint M0) + (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1))))
       = trace (D0 0 \<rho>) + (\<Sum>k=0..<k. trace (D0 (Suc k) \<rho>))" unfolding D0_def by auto
    also have "\<dots> = trace (D0 0 \<rho>) + (\<Sum>k=1..<(Suc k). trace (D0 k \<rho>))"
      using sum.shift_bounds_Suc_ivl[symmetric, of "\<lambda>k. trace (D0 k \<rho>)"] by auto
    also have "\<dots> = (\<Sum>k=0..<(Suc k). trace (D0 k \<rho>))"
      using sum.atLeast_Suc_lessThan[of 0 "Suc k" "\<lambda>k. trace (D0 k \<rho>)"] by auto
    finally have eq3: "trace (M0 * \<rho> * adjoint M0) + (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1)))) = (\<Sum>k=0..<(Suc k). trace (D0 k \<rho>))".

    then have "trace (M1 * \<rho> * adjoint M1) - (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1))))
      = trace \<rho> - (trace (M0 * \<rho> * adjoint M0) + (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1)))))"
      by (simp add: algebra_simps eq2)
    then have eq4: "trace (M1 * \<rho> * adjoint M1) - (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1)))) = trace \<rho> - (\<Sum>k=0..<(Suc k). trace (D0 k \<rho>))"
      by (simp add: eq3)

    have "trace ((W (Suc k)) * \<rho>) = trace (P * (M0 * \<rho> * adjoint M0)) + trace ((wlp S (W k)) * (M1 * \<rho> * adjoint M1))"
      unfolding W_def wlp_while_n.simps
      apply (fold W_def) using dM0 dP dM1 dWWk dr by (mat_assoc d)
    also have "\<dots> = trace (P * (M0 * \<rho> * adjoint M0)) + trace ((W k) * (DS (M1 * \<rho> * adjoint M1))) + trace (M1 * \<rho> * adjoint M1) - trace (DS (M1 * \<rho> * adjoint M1))"
      using While(1)[OF wcS, of "W k"] qpWk dsM1r DS_def by auto
    also have "\<dots> = trace (P * (M0 * \<rho> * adjoint M0))
      + (\<Sum>k=0..<k. trace (P * (D0 k (DS (M1 * \<rho> * adjoint M1))))) + trace (DS (M1 * \<rho> * adjoint M1)) - (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1))))
      + trace (M1 * \<rho> * adjoint M1) - trace (DS (M1 * \<rho> * adjoint M1))"
      using Suc(1)[OF dsDSM1r] by auto
    also have "\<dots> = trace (P * (M0 * \<rho> * adjoint M0)) + (\<Sum>k=0..<k. trace (P * (D0 k (DS (M1 * \<rho> * adjoint M1))))) 
      + trace (M1 * \<rho> * adjoint M1) - (\<Sum>k=0..<k. trace (D0 k (DS (M1 * \<rho> * adjoint M1))))"
      by auto
    also have "\<dots> = (\<Sum>k=0..<(Suc k). trace (P * (D0 k \<rho>))) + trace \<rho> - (\<Sum>k=0..<(Suc k). trace (D0 k \<rho>))"
      by (simp add: eq1 eq4)
    finally show ?case.
  qed

  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
    have limDW: "limit_mat (\<lambda>n. matrix_sum d (\<lambda>k. D0 k \<rho>) (n)) (denote (While M S) \<rho>) d"
      using limit_mat_denote_while_n[OF wc dr pdor] unfolding D0_def M0_def M1_def DS_def by auto
    then have "limit_mat (\<lambda>n. (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n)))) (P * (denote (While M S) \<rho>)) d"
      using mat_mult_limit[OF dP] unfolding mat_mult_seq_def by auto
    then have limtrPm: "(\<lambda>n. trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n)))) \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>))"
      using mat_trace_limit by auto

    with limDW have limtrDW:"(\<lambda>n. trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n))) \<longlonglongrightarrow> trace (denote (While M S) \<rho>)"
      using mat_trace_limit by auto

    have limm: "(\<lambda>n. trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n))) \<longlonglongrightarrow> trace (denote (While M S) \<rho>)"
      using mat_trace_limit limDW by auto

    have closeWS: "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate (wlp S P)" for P
    proof -
      assume asm: "is_quantum_predicate P"
      then have dP: "P \<in> carrier_mat d d" using is_quantum_predicate_def by auto
      then show "is_quantum_predicate (wlp S P)" using wlp_mono_and_close[OF wcS asm asm] lowner_le_refl by auto
    qed
    have monoWS: "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> P \<le>\<^sub>L Q \<Longrightarrow> wlp S P \<le>\<^sub>L wlp S Q" for P Q
      using wlp_mono_and_close[OF wcS] by auto
  
    have "is_quantum_predicate (wlp (While M S) P)"
      using wlp_while_exists[of "wlp S" M P] closeWS monoWS m qpP by auto
                                                                        
    have "limit_mat W (wlp_while M0 M1 (wlp S) P) d" unfolding W_def M0_def M1_def 
      using wlp_while_exists[of "wlp S" M P] closeWS monoWS m qpP by auto
    then have "limit_mat (\<lambda>k. (W k) * \<rho>) ((wlp_while M0 M1 (wlp S) P) * \<rho>) d" using mult_mat_limit dr by auto
    then have lim1: "(\<lambda>k. trace ((W k) * \<rho>)) \<longlonglongrightarrow> trace ((wlp_while M0 M1 (wlp S) P) * \<rho>)" 
      using mat_trace_limit by auto

    have dD0kr: "D0 k \<rho> \<in> carrier_mat d d" for k unfolding D0_def 
      using denote_while_n_dim[OF dr dM0 dM1 pdor] denote_positive_trace_dim[OF wcS, folded DS_def] by auto
    then have "(P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n))) = matrix_sum d (\<lambda>k. P * (D0 k \<rho>)) n" for n
      using matrix_sum_distrib_left[OF dP] by auto
    moreover have "trace (matrix_sum d (\<lambda>k. P * (D0 k \<rho>)) n) = (\<Sum>k=0..<n. trace (P * (D0 k \<rho>)))" for n
      using trace_matrix_sum_linear dD0kr dP by auto
    ultimately have eqPsD0kr: "trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n))) = (\<Sum>k=0..<n. trace (P * (D0 k \<rho>)))" for n by auto
    with limtrPm have lim2: "(\<lambda>k. (\<Sum>k=0..<k. trace (P * (D0 k \<rho>)))) \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>))" by auto

    have "trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n)) = (\<Sum>k=0..<n. trace (D0 k \<rho>))" for n
      using trace_matrix_sum_linear dD0kr by auto
    with limtrDW have lim3: "(\<lambda>k. (\<Sum>k=0..<k. trace (D0 k \<rho>))) \<longlonglongrightarrow> trace (denote (While M S) \<rho>)" by auto

    have "(\<lambda>k. (\<Sum>k=0..<k. trace (P * (D0 k \<rho>))) + trace \<rho>) \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>)) + trace \<rho>"
      using tendsto_add[of "\<lambda>k. (\<Sum>k=0..<k. trace (P * (D0 k \<rho>)))"] lim2 by auto
    then have "(\<lambda>k. (\<Sum>k=0..<k. trace (P * (D0 k \<rho>))) + trace \<rho> - (\<Sum>k=0..<k. trace (D0 k \<rho>)))
       \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>)) + trace \<rho> -  trace (denote (While M S) \<rho>)"
      using tendsto_diff[of _ _ _ "\<lambda>k. (\<Sum>k=0..<k. trace (D0 k \<rho>))"] lim3 by auto
    then have lim4: "(\<lambda>k. trace ((W k) * \<rho>)) \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>)) + trace \<rho> -  trace (denote (While M S) \<rho>)"
      using eqk[OF dsr] by auto

    then have "trace ((wlp_while M0 M1 (wlp S) P) * \<rho>) = trace (P * (denote (While M S) \<rho>)) + trace \<rho> -  trace (denote (While M S) \<rho>)"
      using eqk[OF dsr] tendsto_unique[OF _ lim1 lim4] by auto
  }
  then show ?case unfolding M0_def M1_def DS_def wlp.simps by auto
qed

lemma denote_while_split:
  assumes wc: "well_com (While M S)" and dsr: "\<rho> \<in> density_states"
  shows "denote (While M S) \<rho> = (M 0) * \<rho> * adjoint (M 0) + denote (While M S) (denote S (M 1 * \<rho> * adjoint (M 1)))"
proof -
  have m: "measurement d 2 M" using wc by auto
  have wcs: "well_com S" using wc by auto
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using m measurement_def M0_def M1_def by auto
  have M1leq: "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat m M1_def by auto
  define DS where "DS = denote S"
  define D0 where "D0 = denote_while_n M0 M1 DS"
  define D1 where "D1 = denote_while_n_comp M0 M1 DS"
  define D where "D = denote_while_n_iter M0 M1 DS"
  define DW where "DW \<rho> = denote (While M S) \<rho>" for \<rho>

  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
    have pdoDkr: "\<And>k. partial_density_operator (D k \<rho>)" unfolding D_def
    using pdo_denote_while_n_iter[OF dr pdor dM1 M1leq]
      denote_partial_density_operator[OF wcs] denote_dim[OF wcs, folded DS_def] 
    apply (fold DS_def) by auto
    then have pDkr: "\<And>k. positive (D k \<rho>)" unfolding partial_density_operator_def by auto
    have dDkr: "\<And>k. D k \<rho> \<in> carrier_mat d d" 
      using denote_while_n_iter_dim[OF dr pdor dM1 M1leq denote_dim_pdo[OF wcs, folded DS_def], of id M0, simplified, folded D_def] by auto
    then have dD0kr: "\<And>k. D0 k \<rho> \<in> carrier_mat d d" unfolding D0_def denote_while_n.simps apply (fold D_def) using dM0 by auto
  }
  note dD0k = this
  have "matrix_sum d (\<lambda>k. D0 k \<rho>) k \<in> carrier_mat d d" if dsr: "\<rho> \<in> density_states" for \<rho> k 
    using matrix_sum_dim[OF dD0k, of _ "\<lambda>k. \<rho>" id, OF dsr] dsr by auto
  {
    fix k
    have "matrix_sum d (\<lambda>k. D0 k \<rho>) (Suc k) = (D0 0 \<rho>) + matrix_sum d (\<lambda>k. D0 (Suc k) \<rho>) k"
      using matrix_sum_shift_Suc[of _ "\<lambda>k. D0 k \<rho>"] dD0k[OF dsr] by fastforce
    also have "\<dots> = M0 * \<rho> * adjoint M0 + matrix_sum d (\<lambda>k. D0 k (DS (M1 * \<rho> * adjoint M1))) k"
      unfolding D0_def by auto
    finally have "matrix_sum d (\<lambda>k. D0 k \<rho>) (Suc k) = M0 * \<rho> * adjoint M0 + matrix_sum d (\<lambda>k. D0 k (DS (M1 * \<rho> * adjoint M1))) k".
  }
  note eqk = this

  have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def dsr by auto 
  then have "M1 * \<rho> * adjoint M1 \<in> carrier_mat d d" and "partial_density_operator (M1 * \<rho> * adjoint M1)"
    using dM1 dr pdo_close_under_measurement[OF dM1 dr pdor M1leq] by auto
  then have dSM1r: "(DS (M1 * \<rho> * adjoint M1)) \<in> carrier_mat d d" and pdoSM1r: "partial_density_operator (DS (M1 * \<rho> * adjoint M1))"
    unfolding DS_def using denote_dim_pdo[OF wcs] by auto

  have "limit_mat (matrix_sum d (\<lambda>k. D0 k \<rho>)) (DW \<rho>) d" unfolding M0_def M1_def D0_def DS_def DW_def
    using limit_mat_denote_while_n[OF wc dr pdor] by auto
  then have liml: "limit_mat (\<lambda>k. matrix_sum d (\<lambda>k. D0 k \<rho>) (Suc k)) (DW \<rho>) d"
    using limit_mat_ignore_initial_segment[of "matrix_sum d (\<lambda>k. D0 k \<rho>)" "DW \<rho>" d 1] by auto

  have dM0r: "M0 * \<rho> * adjoint M0 \<in> carrier_mat d d" using dM0 dr by fastforce
  have "limit_mat (matrix_sum d (\<lambda>k. D0 k (DS (M1 * \<rho> * adjoint M1)))) (DW (DS (M1 * \<rho> * adjoint M1))) d"
    using limit_mat_denote_while_n[OF wc dSM1r pdoSM1r] unfolding M0_def M1_def D0_def DS_def DW_def by auto
  then have 
    limr: "limit_mat 
      (mat_add_seq (M0 * \<rho> * adjoint M0) (matrix_sum d (\<lambda>k. D0 k (DS (M1 * \<rho> * adjoint M1)))))
      (M0 * \<rho> * adjoint M0 + (DW (DS (M1 * \<rho> * adjoint M1))))
      d"
    using mat_add_limit[OF dM0r] by auto
  moreover have 
    "(\<lambda>k. matrix_sum d (\<lambda>k. D0 k \<rho>) (Suc k))
     = (mat_add_seq (M0 * \<rho> * adjoint M0) (matrix_sum d (\<lambda>k. D0 k (DS (M1 * \<rho> * adjoint M1)))))"
    using eqk mat_add_seq_def by auto
  ultimately have 
    "limit_mat
      (\<lambda>k. matrix_sum d (\<lambda>k. D0 k \<rho>) (Suc k))
      (M0 * \<rho> * adjoint M0 + (DW (DS (M1 * \<rho> * adjoint M1))))
      d" by auto
  with liml limit_mat_unique have 
    "DW \<rho> = (M0 * \<rho> * adjoint M0 + (DW (DS (M1 * \<rho> * adjoint M1))))" by auto
  then show ?thesis unfolding DW_def M0_def M1_def DS_def by auto
qed

lemma wlp_while_split:
  assumes wc: "well_com (While M S)" and qpP: "is_quantum_predicate P"
  shows "wlp (While M S) P = adjoint (M 0) * P * (M 0) + adjoint (M 1) * (wlp S (wlp (While M S) P)) * (M 1)"
proof -
  have m: "measurement d 2 M" using wc by auto
  have wcs: "well_com S" using wc by auto
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  have dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" using m measurement_def M0_def M1_def by auto
  have M1leq: "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat m M1_def by auto
  define DS where "DS = denote S"
  define D0 where "D0 = denote_while_n M0 M1 DS"
  define D1 where "D1 = denote_while_n_comp M0 M1 DS"
  define D where "D = denote_while_n_iter M0 M1 DS"
  define DW where "DW \<rho> = denote (While M S) \<rho>" for \<rho>

  have dP: "P \<in> carrier_mat d d" using qpP is_quantum_predicate_def by auto
  have qpWP: "is_quantum_predicate (wlp (While M S) P)" using qpP wc wlp_close[OF wc qpP] by auto
  then have "is_quantum_predicate (wlp S (wlp (While M S) P))" using wc wlp_close[OF wcs] by auto
  then have dWWP: "(wlp S (wlp (While M S) P)) \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  have dWP: "(wlp (While M S) P) \<in> carrier_mat d d" using qpWP is_quantum_predicate_def by auto
  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
    have dsM1r: "M1 * \<rho> * adjoint M1 \<in> density_states" unfolding density_states_def
      using pdo_close_under_measurement[OF dM1 dr pdor] M1leq dM1 dr by fastforce
    then have dsDSM1r: "DS (M1 * \<rho> * adjoint M1) \<in> density_states" unfolding density_states_def DS_def
      using denote_dim_pdo[OF wcs] by auto
    have dM0r: "M0 * \<rho> * adjoint M0 \<in> carrier_mat d d" using dM0 dr by fastforce
    have dDWDSM1r: "DW (DS (M1 * \<rho> * adjoint M1)) \<in> carrier_mat d d" 
      unfolding DW_def using denote_dim[OF wc] dsDSM1r density_states_def by auto
    
    have eq2: "trace ((wlp (While M S) P) * DS (M1 * \<rho> * adjoint M1))
          = trace (P * (DW (DS (M1 * \<rho> * adjoint M1)))) + trace (DS (M1 * \<rho> * adjoint M1)) - trace (DW (DS (M1 * \<rho> * adjoint M1)))"
      unfolding DW_def using wlp_soundness[OF wc qpP] dsDSM1r by auto
    have eq3: "trace (M1 * \<rho> * adjoint M1) = trace \<rho> - trace (M0 * \<rho> * adjoint M0)" 
      unfolding M0_def M1_def using m trace_measurement2[OF m dr] dr by (simp add: algebra_simps)
  
    have "trace (adjoint M1 * (wlp S (wlp (While M S) P)) * M1 * \<rho>)
          = trace ((wlp S (wlp (While M S) P)) * (M1 * \<rho> * adjoint M1))" using dWWP dM1 dr by (mat_assoc d)
    also have "\<dots> = trace ((wlp (While M S) P) * DS (M1 * \<rho> * adjoint M1)) 
                  + trace (M1 * \<rho> * adjoint M1) - trace (DS (M1 * \<rho> * adjoint M1))"
      unfolding DS_def using wlp_soundness[OF wcs qpWP] dsM1r by auto
    also have "\<dots> = trace (P * (DW (DS (M1 * \<rho> * adjoint M1)))) 
                  + trace (M1 * \<rho> * adjoint M1)  - trace (DW (DS (M1 * \<rho> * adjoint M1)))"
      using eq2 by auto
    also have "\<dots> = trace (P * (DW (DS (M1 * \<rho> * adjoint M1)))) + trace \<rho> - (trace (M0 * \<rho> * adjoint M0) + trace (DW (DS (M1 * \<rho> * adjoint M1))))" 
      using eq3 by auto
    finally have eq4: "trace (adjoint M1 * (wlp S (wlp (While M S) P)) * M1 * \<rho>) 
      = trace (P * (DW (DS (M1 * \<rho> * adjoint M1)))) + trace \<rho> - (trace (M0 * \<rho> * adjoint M0) + trace (DW (DS (M1 * \<rho> * adjoint M1))))".
  
    have "trace (adjoint M0 * P * M0 * \<rho>) + trace (P * (DW (DS (M1 * \<rho> * adjoint M1))))
      = trace (P * ((M0 * \<rho> * adjoint M0) + (DW (DS (M1 * \<rho> * adjoint M1)))))"
      using dP dr dM0 dDWDSM1r by (mat_assoc d)
    also have "\<dots> = trace (P * (DW \<rho>))" unfolding DW_def M0_def M1_def DS_def using denote_while_split[OF wc dsr] by auto
    finally have eq5: "trace (adjoint M0 * P * M0 * \<rho>) + trace (P * (DW (DS (M1 * \<rho> * adjoint M1)))) = trace (P * (DW \<rho>))".
  
    have "trace (M0 * \<rho> * adjoint M0) + trace (DW (DS (M1 * \<rho> * adjoint M1)))
      = trace (M0 * \<rho> * adjoint M0 + (DW (DS (M1 * \<rho> * adjoint M1))))"
      using dr dM0 dDWDSM1r by (mat_assoc d)
    also have "\<dots> = trace (DW \<rho>)"
      unfolding DW_def DS_def M0_def M1_def denote_while_split[OF wc dsr] by auto
    finally have eq6: "trace (M0 * \<rho> * adjoint M0) + trace (DW (DS (M1 * \<rho> * adjoint M1))) = trace (DW \<rho>)".
  
    from eq5 eq4 eq6 have
      eq7: "trace (adjoint M0 * P * M0 * \<rho>) + trace (adjoint M1 * wlp S (wlp (While M S) P) * M1 * \<rho>)
      = trace (P * DW \<rho>) + trace \<rho> - trace (DW \<rho>)" by auto
    have eq8: "trace (adjoint M0 * P * M0 * \<rho>) + trace (adjoint M1 * wlp S (wlp (While M S) P) * M1 * \<rho>)
      = trace ((adjoint M0 * P * M0 + adjoint M1 * wlp S (wlp (While M S) P) * M1) * \<rho>)"
      using dM0 dM1 dr dP dWWP by (mat_assoc d)
    from eq7 eq8 have 
      eq9: "trace ((adjoint M0 * P * M0 + adjoint M1 * wlp S (wlp (While M S) P) * M1) * \<rho>) = trace (P * DW \<rho>) + trace \<rho> - trace (DW \<rho>)" by auto
    have eq10: "trace ((wlp (While M S) P) * \<rho>) = trace (P * DW \<rho>) + trace \<rho> - trace (DW \<rho>)" 
      unfolding DW_def using wlp_soundness[OF wc qpP] dsr by auto
    with eq9 have "trace ((wlp (While M S) P) * \<rho>) = trace ((adjoint M0 * P * M0 + adjoint M1 * wlp S (wlp (While M S) P) * M1) * \<rho>)" by auto
  }
  then have "(wlp (While M S) P) = (adjoint M0 * P * M0 + adjoint M1 * wlp S (wlp (While M S) P) * M1)"
    using trace_pdo_eq_imp_eq[OF dWP, of "adjoint M0 * P * M0 + adjoint M1 * wlp S (wlp (While M S) P) * M1"] 
      dM0 dP dM1 dWWP density_states_def by fastforce
  then show ?thesis using M0_def M1_def by auto
qed

lemma wlp_is_weakest_liberal_precondition:
  assumes "well_com S" and "is_quantum_predicate P"
  shows "is_weakest_liberal_precondition (wlp S P) S P"
  unfolding is_weakest_liberal_precondition_def
proof (auto)
  show qpWP: "is_quantum_predicate (wlp S P)" using wlp_close assms by auto
  have eq: "trace (wlp S P * \<rho>) = trace (P * (denote S \<rho>)) + trace \<rho> - trace (denote S \<rho>)" if dsr: "\<rho> \<in> density_states" for \<rho> 
    using wlp_soundness assms dsr by auto
  then show "\<Turnstile>\<^sub>p {wlp S P} S {P}" unfolding hoare_partial_correct_def by auto
  fix Q assume qpQ: "is_quantum_predicate Q" and p: "\<Turnstile>\<^sub>p {Q} S {P}"
  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have "trace (Q * \<rho>) \<le> trace (P * (denote S \<rho>)) + trace \<rho> - trace (denote S \<rho>)" 
      using hoare_partial_correct_def p by auto
    then have "trace (Q * \<rho>) \<le> trace (wlp S P * \<rho>)" using eq[symmetric] dsr by auto
  }
  then show "Q \<le>\<^sub>L wlp S P" using lowner_le_trace density_states_def qpQ qpWP is_quantum_predicate_def by auto
qed

subsection \<open>Hoare triples for partial correctness\<close>

inductive hoare_partial :: "complex mat \<Rightarrow> com \<Rightarrow> complex mat \<Rightarrow> bool" ("\<turnstile>\<^sub>p ({(1_)}/ (_)/ {(1_)})" 50) where
  "is_quantum_predicate P \<Longrightarrow> \<turnstile>\<^sub>p {P} SKIP {P}"
| "is_quantum_predicate P \<Longrightarrow> \<turnstile>\<^sub>p {adjoint U * P * U} Utrans U {P}"
| "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> is_quantum_predicate R \<Longrightarrow>
   \<turnstile>\<^sub>p {P} S1 {Q} \<Longrightarrow> \<turnstile>\<^sub>p {Q} S2 {R} \<Longrightarrow>
   \<turnstile>\<^sub>p {P} Seq S1 S2 {R}"
| "(\<And>k. k < n \<Longrightarrow> is_quantum_predicate (P k)) \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow>
   (\<And>k. k < n \<Longrightarrow> \<turnstile>\<^sub>p {P k} S ! k {Q}) \<Longrightarrow>
   \<turnstile>\<^sub>p {matrix_sum d (\<lambda>k. adjoint (M k) * P k  * M k) n} Measure n M S {Q}"
| "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow>
   \<turnstile>\<^sub>p {Q} S {adjoint (M 0) * P * M 0 + adjoint (M 1) * Q * M 1} \<Longrightarrow>
   \<turnstile>\<^sub>p {adjoint (M 0) * P * M 0 + adjoint (M 1) * Q * M 1} While M S {P}"
| "is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> is_quantum_predicate P' \<Longrightarrow> is_quantum_predicate Q' \<Longrightarrow>
   P \<le>\<^sub>L P' \<Longrightarrow> \<turnstile>\<^sub>p {P'} S {Q'} \<Longrightarrow> Q' \<le>\<^sub>L Q \<Longrightarrow> \<turnstile>\<^sub>p {P} S {Q}"

theorem hoare_partial_sound:
  "\<turnstile>\<^sub>p {P} S {Q} \<Longrightarrow> well_com S \<Longrightarrow> \<Turnstile>\<^sub>p {P} S {Q}"
proof (induction rule: hoare_partial.induct)
  case (1 P)
  then show ?case
    unfolding hoare_partial_correct_def by auto
next
  case (2 P U) (*utrans*)
  then have dU: "U \<in> carrier_mat d d" and "unitary U" and dP: "P \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  then have uU: "adjoint U * U = 1\<^sub>m d" using unitary_def by auto
  show ?case
    unfolding hoare_partial_correct_def denote.simps(2)
  proof 
    fix \<rho> assume "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" using density_states_def by auto
    have e1: "trace (U * \<rho> * adjoint U) = trace ((adjoint U * U) * \<rho>)"
      using dr dU by (mat_assoc d)
    also have "\<dots> = trace \<rho>"
      using uU dr by auto
    finally have e1: "trace (U * \<rho> * adjoint U) = trace \<rho>" .
    have e2: "trace (P * (U * \<rho> * adjoint U)) = trace (adjoint U * P * U * \<rho>)"
      using dU dP dr by (mat_assoc d)
    with e1 have "trace (P * (U * \<rho> * adjoint U)) + (trace \<rho> - trace (U * \<rho> * adjoint U)) = trace (adjoint U * P * U * \<rho>)"
      using e1 by auto
    then show "trace (adjoint U * P * U * \<rho>) \<le> trace (P * (U * \<rho> * adjoint U)) + (trace \<rho> - trace (U * \<rho> * adjoint U))" by auto
  qed
next
  case (3 P Q R S1 S2) (*seq*)
  then have wc1: "\<Turnstile>\<^sub>p {P} S1 {Q}" and wc2: "\<Turnstile>\<^sub>p {Q} S2 {R}" by auto
  show ?case
    unfolding hoare_partial_correct_def denote.simps(3)
  proof clarify
    fix \<rho> assume \<rho>: "\<rho> \<in> density_states"
    have 1: "trace (P * \<rho>) \<le> trace (Q * denote S1 \<rho>) + (trace \<rho> - trace (denote S1 \<rho>))"
      using wc1 hoare_partial_correct_def \<rho> by auto
    have \<rho>': "denote S1 \<rho> \<in> density_states"
      using 3(8) denote_density_states \<rho> by auto
    have 2: "trace (Q * denote S1 \<rho>) \<le> trace (R * denote S2 (denote S1 \<rho>)) + (trace (denote S1 \<rho>) - trace (denote S2 (denote S1 \<rho>)))"
      using wc2 hoare_partial_correct_def \<rho>' by auto
    show "trace (P * \<rho>) \<le> trace (R * denote S2 (denote S1 \<rho>)) + (trace \<rho> - trace (denote S2 (denote S1 \<rho>)))"
      using 1 2 by auto
  qed
next
  case (4 n P Q S M) (*if*)
  then have wc: "k < n \<Longrightarrow> well_com (S!k)"
    and c: "k < n \<Longrightarrow> \<Turnstile>\<^sub>p {P k} (S!k) {Q}" and m: "measurement d n M"
    and dMk: "k < n \<Longrightarrow> M k \<in> carrier_mat d d"
    and aMMkleq: "k < n \<Longrightarrow> adjoint (M k) * M k \<le>\<^sub>L 1\<^sub>m d"
    and dPk: "k < n \<Longrightarrow> P k \<in> carrier_mat d d"
    and dQ: "Q \<in> carrier_mat d d"
    for k using is_quantum_predicate_def measurement_def measure_well_com measurement_le_one_mat by auto

    {
      fix \<rho> assume \<rho>: "\<rho> \<in> density_states"
      then have dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>" using density_states_def by auto
      have dsr: "k < n \<Longrightarrow> (M k) * \<rho> * adjoint (M k) \<in> density_states" for k unfolding density_states_def 
        using dMk pdo_close_under_measurement[OF dMk dr pdor aMMkleq] dr by fastforce
      then have leqk: "k < n \<Longrightarrow> trace ((P k) * ((M k) * \<rho> * adjoint (M k))) \<le> 
        trace (Q * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
        (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))" for k 
        using c unfolding hoare_partial_correct_def by auto
      have "k < n \<Longrightarrow> M k * \<rho> * adjoint (M k) \<in> carrier_mat d d" for k using dMk dr by fastforce
      then have dsMrk: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. (M k * \<rho> * adjoint (M k))) k \<in> carrier_mat d d" for k 
        using matrix_sum_dim[of k "\<lambda>k. (M k * \<rho> * adjoint (M k))" d] by fastforce
      have "k < n \<Longrightarrow> adjoint (M k) * P k * M k \<in> carrier_mat d d" for k using dMk dPk by fastforce
      then have dsMP: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) k \<in> carrier_mat d d" for k 
        using matrix_sum_dim[of k "\<lambda>k. adjoint (M k) * P k * M k" d] by fastforce
      have dSMrk: "k < n \<Longrightarrow> denote (S ! k) (M k * \<rho> * adjoint (M k)) \<in> carrier_mat d d" for k 
        using denote_dim[OF wc, of k "M k * \<rho> * adjoint (M k)"] dsr density_states_def by fastforce
      have dsSMrk: "k < n \<Longrightarrow> matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k \<in> carrier_mat d d" for k
        using matrix_sum_dim[of k "\<lambda>k. denote (S ! k) (M k * \<rho> * adjoint (M k))" d, OF dSMrk] by fastforce
      have "k \<le> n \<Longrightarrow> 
          trace (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) k * \<rho>)
         \<le> trace (Q * (denote (Measure k M S) \<rho>)) + (trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) k) - trace (denote (Measure k M S) \<rho>))" for k 
        unfolding denote_measure_expand[OF _ 4(5)]
      proof (induct k)
        case 0
        then show ?case using dQ dr pdor partial_density_operator_def positive_trace by auto
      next
        case (Suc k)
        then have k: "k < n" by auto
        have eq1: "trace (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) (Suc k) * \<rho>) 
          = trace (adjoint (M k) * P k * M k * \<rho>) + trace (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) k * \<rho>)"
          unfolding matrix_sum.simps
          using dMk[OF k] dPk[OF k] dr dsMP[OF k] by (mat_assoc d)
  
        have "trace (adjoint (M k) * P k * M k * \<rho>) = trace (P k * (M k * \<rho> * adjoint (M k)))" 
          using dMk[OF k] dPk[OF k] dr by (mat_assoc d)
        also have "\<dots> \<le> trace (Q * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
          (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))" using leqk k by auto
        finally have eq2: "trace (adjoint (M k) * P k * M k * \<rho>) \<le> trace (Q * (denote (S!k) ((M k) * \<rho> * adjoint (M k)))) + 
          (trace ((M k) * \<rho> * adjoint (M k)) - trace (denote (S ! k) ((M k) * \<rho> * adjoint (M k))))".
  
        have eq3: "trace (Q * matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) (Suc k)) 
          = trace (Q * (denote (S!k) (M k * \<rho> * adjoint (M k)))) + trace (Q * matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)"
          unfolding matrix_sum.simps 
          using dQ dSMrk[OF k] dsSMrk[OF k] by (mat_assoc d)
  
        have eq4: "trace (denote (S ! k) (M k * \<rho> * adjoint (M k)) + matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)
          = trace (denote (S ! k) (M k * \<rho> * adjoint (M k))) + trace (matrix_sum d (\<lambda>k. denote (S!k) (M k * \<rho> * adjoint (M k))) k)"
          using dSMrk[OF k] dsSMrk[OF k] by (mat_assoc d)
  
        show ?case
          apply (subst eq1) apply (subst eq3) 
          apply (simp del: less_eq_complex_def) 
          apply (subst trace_add_linear[of "M k * \<rho> * adjoint (M k)" d "matrix_sum d (\<lambda>k. M k * \<rho> * adjoint (M k)) k"])
            apply (simp add: dMk adjoint_dim[OF dMk] dr mult_carrier_mat[of _ d d _ d] k)
           apply (simp add: dsMrk k)
          apply (subst eq4)
          apply (insert eq2 Suc(1) k, fastforce)
          done
      qed
      then have leq: "trace (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n * \<rho>)
         \<le> trace (Q * denote (Measure n M S) \<rho>) + 
            (trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) n) - trace (denote (Measure n M S) \<rho>))"
        by auto
      have "trace (matrix_sum d (\<lambda>k. (M k) * \<rho> * adjoint (M k)) n) = trace \<rho>" using trace_measurement m dr by auto
  
      with leq have "trace (matrix_sum d (\<lambda>k. adjoint (M k) * P k * M k) n * \<rho>)
         \<le> trace (Q * denote (Measure n M S) \<rho>) + (trace \<rho> - trace (denote (Measure n M S) \<rho>))"
        unfolding denote_measure_def by auto
    }
    then show ?case unfolding hoare_partial_correct_def by auto
next
  case (5 P Q S M) (*while*)
  define M0 where "M0 = M 0"
  define M1 where "M1 = M 1"
  from 5 have wcs: "well_com S" and c: "\<Turnstile>\<^sub>p {Q} S {adjoint M0 * P * M0 + adjoint M1 * Q * M1}" 
    and m: "measurement d 2 M"
    and dM0: "M0 \<in> carrier_mat d d" and dM1: "M1 \<in> carrier_mat d d" 
    and dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d" 
    and qpQ: "is_quantum_predicate Q"
    and wc: "well_com (While M S)"
    using measurement_def is_quantum_predicate_def M0_def M1_def by auto
  then have M0leq: "adjoint M0 * M0 \<le>\<^sub>L 1\<^sub>m d" and M1leq: "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat[OF m] M0_def M1_def by auto
  define DS where "DS = denote S"

  have "\<forall>\<rho> \<in> density_states. trace (Q * \<rho>) \<le> trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * DS \<rho>) + trace \<rho> - trace (DS \<rho>)" 
    using hoare_partial_correct_def[of Q S "adjoint M0 * P * M0 + adjoint M1 * Q * M1"] c DS_def by auto
  define D0 where "D0 = denote_while_n M0 M1 DS"
  define D1 where "D1 = denote_while_n_comp M0 M1 DS"
  define D where "D = denote_while_n_iter M0 M1 DS"
  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have dr: "\<rho> \<in> carrier_mat d d" and pr: "positive \<rho>" and pdor: "partial_density_operator \<rho>" 
      using density_states_def partial_density_operator_def by auto
    have pdoDkr: "\<And>k. partial_density_operator (D k \<rho>)" unfolding D_def
      using pdo_denote_while_n_iter[OF dr pdor dM1 M1leq]
        denote_partial_density_operator[OF wcs] denote_dim[OF wcs, folded DS_def] 
      apply (fold DS_def) by auto
    then have pDkr: "\<And>k. positive (D k \<rho>)" unfolding partial_density_operator_def by auto
    have dDkr: "\<And>k. D k \<rho> \<in> carrier_mat d d" 
      using denote_while_n_iter_dim[OF dr pdor dM1 M1leq denote_dim_pdo[OF wcs, folded DS_def], of id M0, simplified, folded D_def] by auto
    then have dD0kr: "\<And>k. D0 k \<rho> \<in> carrier_mat d d" unfolding D0_def denote_while_n.simps apply (fold D_def) using dM0 by auto
    then have dPD0kr: "\<And>k. P * (D0 k \<rho>) \<in> carrier_mat d d" using dP by auto
    have "\<And>k. positive (D0 k \<rho>)" unfolding D0_def denote_while_n.simps 
      by (fold D_def, rule positive_close_under_left_right_mult_adjoint[OF dM0 dDkr pDkr])
    then have trge0: "\<And>k. trace (D0 k \<rho>) \<ge> 0" using positive_trace dD0kr by blast
    have DSr: "\<rho> \<in> density_states \<Longrightarrow> DS \<rho> \<in> density_states" for "\<rho>" unfolding DS_def density_states_def
      using denote_partial_density_operator denote_dim wcs by auto
    have dsD1nr: "D1 n \<rho> \<in> density_states" for n unfolding D1_def denote_while_n_comp.simps 
      apply (fold D_def) unfolding density_states_def
      apply (auto)
       apply (insert dDkr dM1 adjoint_dim[OF dM1], auto)
      apply (rule pdo_close_under_measurement[OF dM1 spec[OF allI[OF dDkr], of "\<lambda>x. n"] spec[OF allI[OF pdoDkr], of "\<lambda>x. n"] M1leq])
      done
  
    have leQn: "trace (Q * D1 n \<rho>) 
          \<le> trace (P * D0 (Suc n) \<rho>) + trace (Q * D1 (Suc n) \<rho>)
          + trace (D1 n \<rho>) - trace (D (Suc n) \<rho>)" for n
    proof -
      have "(\<forall>\<rho>\<in>density_states. trace (Q * \<rho>) \<le> trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>)))"
        using c hoare_partial_correct_def by auto
      then have leQn': "trace (Q * (D1 n \<rho>)) 
          \<le> trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * (DS (D1 n \<rho>))) 
          + (trace (D1 n \<rho>) - trace (DS (D1 n \<rho>)))"
        using dsD1nr[of n] DS_def by auto
      have "(DS (D1 n \<rho>)) \<in> carrier_mat d d" unfolding DS_def using denote_dim[OF wcs] dsD1nr density_states_def by auto
      then have "trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * (DS (D1 n \<rho>)))
        = trace (P * (M0 * (DS (D1 n \<rho>)) * adjoint M0))
        + trace (Q * (M1 * (DS (D1 n \<rho>)) * adjoint M1))" using dP dQ dM0 dM1 by (mat_assoc d)
      moreover have "trace (P * (M0 * (DS (D1 n \<rho>)) * adjoint M0)) = trace (P * D0 (Suc n) \<rho>)" 
        unfolding D0_def denote_while_n.simps
        apply (subst denote_while_n_iter_assoc)
        by (fold denote_while_n_comp.simps D1_def, auto)
      moreover have "trace (Q * (M1 * (DS (D1 n \<rho>)) * adjoint M1)) = trace (Q * D1 (Suc n) \<rho>)"
        apply (subst (2) D1_def) unfolding denote_while_n_comp.simps
        apply (subst denote_while_n_iter_assoc)
        by (fold denote_while_n_comp.simps D1_def, auto)
      ultimately have "trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * (DS (D1 n \<rho>))) 
        = trace (P * D0 (Suc n) \<rho>) + trace (Q * D1 (Suc n) \<rho>)" by auto
      moreover have "trace (DS (D1 n \<rho>)) = trace (D (Suc n) \<rho>)"
        unfolding D_def 
        apply (subst denote_while_n_iter_assoc)
        by (fold denote_while_n_comp.simps D1_def, auto)
      ultimately show ?thesis using leQn' by auto
    qed
  
    have 12: "trace (P * (M0 * \<rho> * adjoint M0)) + trace (Q * (M1 * \<rho> * adjoint M1))
    \<le> (\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace (Q * (D1 (n+1) \<rho>))
      + (\<Sum>k=0..<(n+1). trace (D1 k \<rho>) - trace (D (k+1) \<rho>))" for n
    proof (induct n)
      case 0
      show ?case apply (simp del: less_eq_complex_def) 
        unfolding D0_def D1_def D_def  denote_while_n_comp.simps denote_while_n.simps denote_while_n_iter.simps 
        using leQn[of 0] unfolding D1_def D0_def D_def denote_while_n.simps denote_while_n_comp.simps denote_while_n_iter.simps by auto
    next
      case (Suc n)
      have "trace (Q * D1 (n + 1) \<rho>) 
          \<le> trace (P * D0 (Suc (Suc n)) \<rho>) + trace (Q * D1 (Suc (Suc n)) \<rho>)
          + trace (D1 (Suc n) \<rho>) - trace (D (Suc (Suc n)) \<rho>)" using leQn[of "n + 1"] by auto
      with Suc show ?case apply (simp del: less_eq_complex_def) by auto
    qed
  
    have tr_measurement: "\<rho> \<in> carrier_mat d d
      \<Longrightarrow> trace (M0 * \<rho> * adjoint M0) + trace (M1 * \<rho> * adjoint M1) = trace \<rho>" for \<rho>
      using trace_measurement2[OF m, folded M0_def M1_def] by auto
  
    have 14: "(\<Sum>k=0..<(n+1). trace (D1 k \<rho>) - trace (D (k+1) \<rho>)) = trace \<rho> - trace (D (n+1) \<rho>) - (\<Sum>k=0..<(n+1). trace (D0 k \<rho>))" for n
    proof (induct n)
      case 0
      show ?case apply (simp) unfolding D1_def D0_def denote_while_n_comp.simps denote_while_n.simps denote_while_n_iter.simps
        using tr_measurement[OF dr] by (auto simp add: algebra_simps)
    next
      case (Suc n)
      have "trace (D0 (Suc n) \<rho>) + trace (D1 (Suc n) \<rho>) = trace (D (Suc n) \<rho>)" 
        unfolding D0_def D1_def denote_while_n.simps denote_while_n_comp.simps apply (fold D_def)
        using tr_measurement dDkr by auto
      then have "trace (D1 (Suc n) \<rho>) = trace (D (Suc n) \<rho>) - trace (D0 (Suc n) \<rho>)"
        by (auto simp add: algebra_simps)
      then show ?case using Suc by simp
    qed  
  
    have 15: "trace (Q * (D1 n \<rho>)) \<le> trace (D n \<rho>) - trace (D0 n \<rho>)" for n
    proof -
      have QleId: "Q \<le>\<^sub>L 1\<^sub>m d" using is_quantum_predicate_def qpQ by auto
      then have "trace (Q * (D1 n \<rho>)) \<le> trace (1\<^sub>m d * (D1 n \<rho>))" using 
          dsD1nr[of n] unfolding density_states_def lowner_le_trace[OF dQ one_carrier_mat] by auto
      also have "\<dots> = trace (D1 n \<rho>)" using dsD1nr[of n] unfolding density_states_def by auto
      also have "\<dots> = trace (M1 * (D n \<rho>) * adjoint M1)" unfolding D1_def denote_while_n_comp.simps D_def by auto
      also have "\<dots> = trace (D n \<rho>) - trace (M0 * (D n \<rho>) * adjoint M0)" 
        using tr_measurement[OF dDkr[of n]] by (simp add: algebra_simps)
      also have "\<dots> = trace (D n \<rho>) - trace (D0 n \<rho>)" unfolding D0_def denote_while_n.simps by (fold D_def, auto)
      finally show ?thesis.
    qed
  
    have tmp: "\<And>a b c. 0 \<le> a \<Longrightarrow> b \<le> c - a \<Longrightarrow> b \<le> (c::complex)" by simp
    then have 151: "\<And>n. trace (Q * (D1 n \<rho>)) \<le> trace (D n \<rho>)" 
      by (auto simp add: tmp[OF trge0 15] simp del: less_eq_complex_def)
  
    have main_leq: "\<And>n. trace (P * (M0 * \<rho> * adjoint M0)) + trace (Q * (M1 * \<rho> * adjoint M1))
          \<le> trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))) + trace \<rho> - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))"
    proof -
      fix n
      have "(\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace (Q * (D1 (n+1) \<rho>))
            + (\<Sum>k=0..<(n+1). trace (D1 k \<rho>) - trace (D (k+1) \<rho>))
            \<le> (\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace (Q * (D1 (n+1) \<rho>))
            + trace \<rho> - trace (D (n+1) \<rho>) - (\<Sum>k=0..<(n+1). trace (D0 k \<rho>))"
        by (subst 14, auto)
      also have 
        "\<dots> \<le> (\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace (D (n+1) \<rho>) - trace (D0 (n+1) \<rho>)
            + trace \<rho> - trace (D (n+1) \<rho>) - (\<Sum>k=0..<(n+1). trace (D0 k \<rho>))"
        using 15[of "n+1"] by auto
      also have "\<dots> = (\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace \<rho> - (\<Sum>k=0..<(n+2). trace (D0 k \<rho>))" by auto
      also have "\<dots> = trace (matrix_sum d (\<lambda>k. (P * (D0 k \<rho>))) (n+2)) + trace \<rho> - (\<Sum>k=0..<(n+2). trace (D0 k \<rho>))"
        using trace_matrix_sum_linear[of "n+2" "\<lambda>k. (P * (D0 k \<rho>))" d, symmetric] dPD0kr by auto
      also have "\<dots> = trace (matrix_sum d (\<lambda>k. (P * (D0 k \<rho>))) (n+2)) + trace \<rho> - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))"
        using trace_matrix_sum_linear[of "n+2" "\<lambda>k. D0 k \<rho>" d, symmetric] dD0kr by auto
      also have "\<dots> = trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))) + trace \<rho> - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))"
        using matrix_sum_distrib_left[OF dP dD0kr, of id "n+2"] by auto
      finally have 
        "(\<Sum>k=0..<(n+2). trace (P * (D0 k \<rho>))) + trace (Q * (D1 (n+1) \<rho>))
         + (\<Sum>k=0..<(n+1). trace (D1 k \<rho>) - trace (D (k+1) \<rho>))
        \<le> trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))) + trace \<rho> - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))" .
      then show "trace (P * (M0 * \<rho> * adjoint M0)) + trace (Q * (M1 * \<rho> * adjoint M1))
          \<le> trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))) + trace \<rho> - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))" using 12[of n] by auto
    qed
  
    have "limit_mat (\<lambda>n. matrix_sum d (\<lambda>k. D0 k \<rho>) (n)) (denote (While M S) \<rho>) d"
      using limit_mat_denote_while_n[OF wc dr pdor] unfolding D0_def M0_def M1_def DS_def by auto
    then have limp2: "limit_mat (\<lambda>n. matrix_sum d (\<lambda>k. D0 k \<rho>) (n + 2)) (denote (While M S) \<rho>) d"
      using limit_mat_ignore_initial_segment[of "\<lambda>n. matrix_sum d (\<lambda>k. D0 k \<rho>) (n)" "(denote (While M S) \<rho>)" d 2] by auto
    then have "limit_mat (\<lambda>n. (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2)))) (P * (denote (While M S) \<rho>)) d"
      using mat_mult_limit[OF dP] unfolding mat_mult_seq_def by auto
    then have limPm: "(\<lambda>n. trace (P * (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2)))) \<longlonglongrightarrow> trace (P * (denote (While M S) \<rho>))"
      using mat_trace_limit by auto
  
    have limm: "(\<lambda>n. trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n+2))) \<longlonglongrightarrow> trace (denote (While M S) \<rho>)"
      using mat_trace_limit limp2 by auto
  
    have leq_lim: "trace (P * (M0 * \<rho> * adjoint M0)) + trace (Q * (M1 * \<rho> * adjoint M1)) 
      \<le> trace (P * (denote (While M S) \<rho>)) + trace \<rho> - trace (denote (While M S) \<rho>)" (is "?lhs \<le> ?rhs")
      using main_leq
    proof -
      define seq where "seq n = trace (P * matrix_sum d (\<lambda>k. D0 k \<rho>) (n + 2)) - trace (matrix_sum d (\<lambda>k. D0 k \<rho>) (n + 2)) " for n
      define seqlim where "seqlim = trace (P * (denote (While M S) \<rho>)) - trace (denote (While M S) \<rho>)"
      have main_leq': "?lhs \<le> trace \<rho> + seq n" for n 
        unfolding seq_def using main_leq by (simp add: algebra_simps)
      have limseq: "seq \<longlonglongrightarrow> seqlim"
        unfolding seq_def seqlim_def using tendsto_diff[OF limPm limm]  by auto
      have limrs: "(\<lambda>n. trace \<rho> + seq n) \<longlonglongrightarrow> (trace \<rho> + seqlim)" using tendsto_add[OF _ limseq] by auto
  
      have limrsRe: "(\<lambda>n. Re (trace \<rho> + seq n)) \<longlonglongrightarrow> Re (trace \<rho> + seqlim)" using tendsto_Re[OF limrs] by auto
      have main_leq_Re: "Re ?lhs \<le> Re (trace \<rho> + seq n)" for n using main_leq' by auto
      have Re: "Re ?lhs \<le> Re (trace \<rho> + seqlim)" 
        using Lim_bounded2[OF limrsRe ]  main_leq_Re by auto
  
      have limrsIm: "(\<lambda>n. Im (trace \<rho> + seq n)) \<longlonglongrightarrow> Im (trace \<rho> + seqlim)" using tendsto_Im[OF limrs] by auto
      have main_leq_Im: "Im ?lhs = Im (trace \<rho> + seq n)" for n using main_leq' unfolding less_eq_complex_def by auto
      then have limIm: "(\<lambda>n. Im (trace \<rho> + seq n)) \<longlonglongrightarrow> Im ?lhs" using tendsto_intros(1) by auto
      have Im: "Im ?lhs = Im (trace \<rho> + seqlim)" 
        using tendsto_unique[OF _ limIm limrsIm] by auto
  
      have "?lhs \<le> trace \<rho> + seqlim" using Re Im by auto
      then show "?lhs \<le> ?rhs" unfolding seqlim_def by auto
    qed
  
    have "trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * \<rho>) =
      trace (P * (M0 * \<rho> * adjoint M0)) + trace (Q * (M1 * \<rho> * adjoint M1))"
      using dr dM0 dM1 dP dQ by (mat_assoc d)
    then have "trace ((adjoint M0 * P * M0 + adjoint M1 * Q * M1) * \<rho>) \<le> 
      trace (P * (denote (While M S) \<rho>)) + (trace \<rho> - trace (denote (While M S) \<rho>))"
      using leq_lim by auto
  }
  then show ?case unfolding hoare_partial_correct_def denote.simps(5) 
    apply (fold M0_def M1_def DS_def D0_def D1_def) by auto
next
  case (6 P Q P' Q' S)
  then have wcs: "well_com S" and c: "\<Turnstile>\<^sub>p {P'} S {Q'}" 
    and dP: "P \<in> carrier_mat d d" and dQ: "Q \<in> carrier_mat d d"
    and dP': "P' \<in> carrier_mat d d" and dQ': "Q' \<in> carrier_mat d d"
    using is_quantum_predicate_def by auto
  show ?case unfolding hoare_partial_correct_def
  proof 
    fix \<rho> assume pds: "\<rho> \<in> density_states"
    then have pdor: "partial_density_operator \<rho>" and dr: "\<rho> \<in> carrier_mat d d" 
      using density_states_def by auto
    have pdoSr: "partial_density_operator (denote S \<rho>)" 
      using denote_partial_density_operator pdor dr wcs by auto
    have dSr: "denote S \<rho> \<in> carrier_mat d d"  
      using denote_dim pdor dr wcs by auto
    have "trace (P * \<rho>) \<le> trace (P' * \<rho>)" using lowner_le_trace[OF dP dP'] 6 dr pdor by auto
    also have "\<dots> \<le> trace (Q' * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>))"
      using c unfolding hoare_partial_correct_def using pds by auto
    also have "\<dots> \<le> trace (Q * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>))" using lowner_le_trace[OF dQ' dQ] 6 dSr pdoSr by auto
    finally show "trace (P * \<rho>) \<le> trace (Q * denote S \<rho>) + (trace \<rho> - trace (denote S \<rho>)) ".
  qed
qed

lemma wlp_complete:
  "well_com S \<Longrightarrow> is_quantum_predicate P \<Longrightarrow> \<turnstile>\<^sub>p {wlp S P} S {P}"
proof (induct S arbitrary: P)
  case SKIP
  then show ?case unfolding wlp.simps using hoare_partial.intros by auto
next
  case (Utrans U)
  then show ?case unfolding wlp.simps using hoare_partial.intros by auto
next
  case (Seq S1 S2)
  then have wc1: "well_com S1" and wc2: "well_com S2" and qpP: "is_quantum_predicate P" 
    and p2: "\<turnstile>\<^sub>p {wlp S2 P} S2 {P}" by auto
  have qpW2P: "is_quantum_predicate (wlp S2 P)" using wlp_close[OF wc2 qpP] by auto
  then have p1: "\<turnstile>\<^sub>p {wlp S1 (wlp S2 P)} S1 {wlp S2 P}" using Seq by auto
  have qpW1W2P: "is_quantum_predicate (wlp S1 (wlp S2 P))" using wlp_close[OF wc1 qpW2P] by auto
  then show ?case unfolding wlp.simps using hoare_partial.intros qpW1W2P qpW2P qpP p1 p2 by auto
next
  case (Measure n M S)
  then have wc: "well_com (Measure n M S)" and qpP: "is_quantum_predicate P" by auto
  have set: "k < n \<Longrightarrow> (S!k) \<in> set S" for k using wc by auto
  have wck: "k < n \<Longrightarrow> well_com (S!k)" for k using wc measure_well_com by auto
  then have qpWkP: "k < n \<Longrightarrow> is_quantum_predicate (wlp (S!k) P)" for k using wlp_close qpP by auto
  have pk: "k < n \<Longrightarrow> \<turnstile>\<^sub>p {(wlp (S!k) P)} (S!k) {P}" for k using Measure(1) set wck qpP by auto
  show ?case unfolding wlp_measure_expand[OF wc] using hoare_partial.intros qpWkP qpP pk  by auto
next
  case (While M S)
  then have wc: "well_com (While M S)" and wcS: "well_com S" and qpP: "is_quantum_predicate P " by auto
  have qpWP: "is_quantum_predicate (wlp (While M S) P)" using wlp_close[OF wc qpP] by auto
  then have qpWWP: "is_quantum_predicate (wlp S (wlp (While M S) P))" using wlp_close wcS by auto
  have "\<turnstile>\<^sub>p {wlp S (wlp (While M S) P)} S {wlp (While M S) P}" using While(1) wcS qpWP by auto
  moreover have eq: "wlp (While M S) P = adjoint (M 0) * P * M 0 + adjoint (M 1) * wlp S (wlp (While M S) P) * M 1"
    using wlp_while_split wc qpP by auto
  ultimately have p: "\<turnstile>\<^sub>p {wlp S (wlp (While M S) P)} S {adjoint (M 0) * P * M 0 + adjoint (M 1) * wlp S (wlp (While M S) P) * M 1}" by auto    
  then show ?case using hoare_partial.intros(5)[OF qpP qpWWP p] eq by auto 
qed

theorem hoare_partial_complete:
  "\<Turnstile>\<^sub>p {P} S {Q} \<Longrightarrow> well_com S \<Longrightarrow> is_quantum_predicate P \<Longrightarrow> is_quantum_predicate Q \<Longrightarrow> \<turnstile>\<^sub>p {P} S {Q}"
proof -
  assume p: "\<Turnstile>\<^sub>p {P} S {Q}" and wc: "well_com S" and qpP: "is_quantum_predicate P" and qpQ: "is_quantum_predicate Q"
  then have dQ: "Q \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  have qpWP: "is_quantum_predicate (wlp S Q)" using wlp_close wc qpQ by auto
  then have dWP: "wlp S Q \<in> carrier_mat d d" using is_quantum_predicate_def by auto
  have eq: "trace (wlp S Q * \<rho>) = trace (Q * (denote S \<rho>)) + trace \<rho> - trace (denote S \<rho>)" if dsr: "\<rho> \<in> density_states" for \<rho> 
    using wlp_soundness wc qpQ dsr by auto
  then have "\<Turnstile>\<^sub>p {wlp S Q} S {Q}" unfolding hoare_partial_correct_def by auto
  {
    fix \<rho> assume dsr: "\<rho> \<in> density_states"
    then have "trace (P * \<rho>) \<le> trace (Q * (denote S \<rho>)) + trace \<rho> - trace (denote S \<rho>)" 
      using hoare_partial_correct_def p by auto
    then have "trace (P * \<rho>) \<le> trace (wlp S Q * \<rho>)" using eq[symmetric] dsr by auto
  }
  then have le: "P \<le>\<^sub>L wlp S Q" using lowner_le_trace density_states_def qpP qpWP is_quantum_predicate_def by auto
  moreover have wlp: "\<turnstile>\<^sub>p {wlp S Q} S {Q}" using wlp_complete wc qpQ by auto
  ultimately show "\<turnstile>\<^sub>p {P} S {Q}" using hoare_partial.intros(6)[OF qpP qpQ qpWP qpQ] lowner_le_refl[OF dQ] by auto
qed

subsection \<open>Consequences of completeness\<close>

lemma hoare_patial_seq_assoc_sem:
  shows "\<Turnstile>\<^sub>p {A} (S1 ;; S2) ;; S3 {B} \<longleftrightarrow> \<Turnstile>\<^sub>p {A} S1 ;; (S2 ;; S3) {B}"
  unfolding hoare_partial_correct_def denote.simps by auto

lemma hoare_patial_seq_assoc:
  assumes "well_com S1" and "well_com S2" and "well_com S3"
    and "is_quantum_predicate A" and "is_quantum_predicate B"
  shows "\<turnstile>\<^sub>p {A} (S1 ;; S2) ;; S3 {B} \<longleftrightarrow> \<turnstile>\<^sub>p {A} S1 ;; (S2 ;; S3) {B}"
proof 
  assume "\<turnstile>\<^sub>p {A} S1;; S2;; S3 {B}"
  then have "\<Turnstile>\<^sub>p {A} (S1 ;; S2) ;; S3 {B}" using hoare_partial_sound assms by auto
  then have "\<Turnstile>\<^sub>p {A} S1 ;; (S2 ;; S3) {B}" using hoare_patial_seq_assoc_sem by auto
  then show "\<turnstile>\<^sub>p {A} S1 ;; (S2 ;; S3) {B}" using hoare_partial_complete assms by auto
next
  assume "\<turnstile>\<^sub>p {A} S1;; (S2;; S3) {B}"
  then have "\<Turnstile>\<^sub>p {A} S1;; (S2;; S3) {B}" using hoare_partial_sound assms by auto
  then have "\<Turnstile>\<^sub>p {A} S1;; S2;; S3 {B}" using hoare_patial_seq_assoc_sem by auto
  then show "\<turnstile>\<^sub>p {A} S1;; S2;; S3 {B}" using hoare_partial_complete assms by auto
qed

end

end
