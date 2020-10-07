section \<open>Quantum programs\<close>

theory Quantum_Program
  imports Matrix_Limit
begin

subsection \<open>Syntax\<close>

text \<open>Datatype for quantum programs\<close>
datatype com = 
  SKIP
| Utrans "complex mat"
| Seq com com  ("_;;/ _" [60, 61] 60)
| Measure nat "nat \<Rightarrow> complex mat" "com list" 
| While "nat \<Rightarrow> complex mat" com 

text \<open>A state corresponds to the density operator\<close>
type_synonym state = "complex mat"

text \<open>List of dimensions of quantum states\<close>
locale state_sig =
  fixes dims :: "nat list"
begin

definition d :: nat where
  "d = prod_list dims"

text \<open>Wellformedness of commands\<close>

fun well_com :: "com \<Rightarrow> bool" where
  "well_com SKIP = True"
| "well_com (Utrans U) = (U \<in> carrier_mat d d \<and> unitary U)"
| "well_com (Seq S1 S2) = (well_com S1 \<and> well_com S2)"
| "well_com (Measure n M S) = 
    (measurement d n M \<and> length S = n \<and> list_all well_com S)"
| "well_com (While M S) =
    (measurement d 2 M \<and> well_com S)"

subsection \<open>Denotational semantics\<close>

text \<open>Denotation of going through the while loop n times\<close>
fun denote_while_n_iter :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "denote_while_n_iter M0 M1 DS 0 \<rho> = \<rho>"
| "denote_while_n_iter M0 M1 DS (Suc n) \<rho> = denote_while_n_iter M0 M1 DS n (DS (M1 * \<rho> * adjoint M1))"

fun denote_while_n :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "denote_while_n M0 M1 DS n \<rho> = M0 * denote_while_n_iter M0 M1 DS n \<rho> * adjoint M0"

fun denote_while_n_comp :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "denote_while_n_comp M0 M1 DS n \<rho> = M1 * denote_while_n_iter M0 M1 DS n \<rho> * adjoint M1"

lemma denote_while_n_iter_assoc:
  "denote_while_n_iter M0 M1 DS (Suc n) \<rho> = DS (M1 * (denote_while_n_iter M0 M1 DS n \<rho>) * adjoint M1)"
proof (induct n arbitrary: \<rho>)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case
    apply (subst denote_while_n_iter.simps)
    apply (subst Suc, auto)
    done
qed

lemma denote_while_n_iter_dim:
  "\<rho> \<in> carrier_mat m m \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> M1 \<in> carrier_mat m m \<Longrightarrow> adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m m
  \<Longrightarrow> (\<And>\<rho>. \<rho> \<in> carrier_mat m m \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> DS \<rho> \<in> carrier_mat m m \<and> partial_density_operator (DS \<rho>))
  \<Longrightarrow> denote_while_n_iter M0 M1 DS n \<rho> \<in> carrier_mat m m \<and> partial_density_operator (denote_while_n_iter M0 M1 DS n \<rho>)"
proof (induct n arbitrary: \<rho>)
  case 0
  then show ?case unfolding denote_while_n_iter.simps by auto
next
  case (Suc n)
  then have dr: "\<rho> \<in> carrier_mat m m" and dM1: "M1 \<in> carrier_mat m m" by auto
  have dMr: "M1 * \<rho> * adjoint M1 \<in> carrier_mat m m" using dr dM1 by fastforce
  have pdoMr: "partial_density_operator (M1 * \<rho> * adjoint M1)" using pdo_close_under_measurement Suc by auto
  from Suc dMr pdoMr have d: "DS (M1 * \<rho> * adjoint M1) \<in> carrier_mat m m" and "partial_density_operator (DS (M1 * \<rho> * adjoint M1))" by auto
  then show ?case unfolding denote_while_n_iter.simps
    using Suc by auto
qed

lemma pdo_denote_while_n_iter:
  "\<rho> \<in> carrier_mat m m \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> M1 \<in> carrier_mat m m \<Longrightarrow> adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m m
  \<Longrightarrow> (\<And>\<rho>. \<rho> \<in> carrier_mat m m \<and> partial_density_operator \<rho> \<Longrightarrow> partial_density_operator (DS \<rho>))
  \<Longrightarrow> (\<And>\<rho>. \<rho> \<in> carrier_mat m m \<and> partial_density_operator \<rho> \<Longrightarrow> DS \<rho> \<in> carrier_mat m m)
  \<Longrightarrow> partial_density_operator (denote_while_n_iter M0 M1 DS n \<rho>)"
proof (induct n arbitrary: \<rho>)
  case 0
  then show ?case unfolding denote_while_n_iter.simps by auto
next
  case (Suc n)
  have "partial_density_operator (M1 * \<rho> * adjoint M1)" using Suc pdo_close_under_measurement by auto
  moreover have "M1 * \<rho> * adjoint M1 \<in> carrier_mat m m" using Suc by auto
  ultimately have p: "partial_density_operator (DS (M1 * \<rho> * adjoint M1))" and d: "DS (M1 * \<rho> * adjoint M1) \<in> carrier_mat m m "using Suc by auto
  show ?case unfolding denote_while_n_iter.simps using Suc(1)[OF d p Suc(4) Suc(5)] Suc by auto
qed


text \<open>Denotation of while is simply the infinite sum of denote\_while\_n\<close>
definition denote_while :: "complex mat \<Rightarrow> complex mat \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> state \<Rightarrow> state" where
  "denote_while M0 M1 DS \<rho> = matrix_inf_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)"

lemma denote_while_n_dim:
  assumes "\<rho> \<in> carrier_mat d d"
    "M0 \<in> carrier_mat d d"
    "M1 \<in> carrier_mat d d"
    "partial_density_operator \<rho>"
    "\<And>\<rho>'. \<rho>' \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho>'  \<Longrightarrow> positive (DS \<rho>') \<and> trace (DS \<rho>') \<le> trace \<rho>' \<and> DS \<rho>' \<in> carrier_mat d d"
   shows "denote_while_n M0 M1 DS n \<rho>  \<in> carrier_mat d d"
proof (induction n arbitrary: \<rho>)
  case 0
  then show ?case 
  proof -
    have "M0 * \<rho> * adjoint M0 \<in> carrier_mat d d"
      using assms assoc_mult_mat by auto
    then show ?thesis by auto
  qed
next
  case (Suc n)
  then show ?case 
  proof -
    have "denote_while_n M0 M1 DS n (DS (M1 * \<rho> * adjoint M1)) \<in> carrier_mat d d"
      using Suc assms by auto
    then show ?thesis by auto
  qed
qed
 
lemma denote_while_n_sum_dim:
  assumes "\<rho> \<in> carrier_mat d d"
    "M0 \<in> carrier_mat d d"
    "M1 \<in> carrier_mat d d"
    "partial_density_operator \<rho>"
    "\<And>\<rho>'. \<rho>' \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho>'  \<Longrightarrow> positive (DS \<rho>') \<and> trace (DS \<rho>') \<le> trace \<rho>' \<and> DS \<rho>' \<in> carrier_mat d d"
  shows "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<in> carrier_mat d d"
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
  proof -
    have " denote_while_n M0 M1 DS n \<rho> \<in> carrier_mat d d"
      using denote_while_n_dim assms by auto
    then have "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n) \<in> carrier_mat d d"
      using Suc by auto
    then show ?thesis by auto
  qed
qed

lemma trace_decrease_mul_adj:
  assumes pdo: "partial_density_operator \<rho>" and dimr: "\<rho> \<in> carrier_mat d d" 
    and dimx: "x \<in> carrier_mat d d" and un: "adjoint x * x \<le>\<^sub>L   1\<^sub>m d "
  shows "trace (x * \<rho> * adjoint x) \<le> trace \<rho>"
proof -
  have ad: "adjoint x * x \<in> carrier_mat d d" using adjoint_dim index_mult_mat dimx by auto
  have "trace (x * \<rho> * adjoint x) = trace ((adjoint x * x) * \<rho>)" using dimx dimr by (mat_assoc d)
  also have "\<dots> \<le> trace (1\<^sub>m d * \<rho>)" using lowner_le_trace un ad dimr pdo by auto
  also have "\<dots> = trace \<rho>" using dimr by auto
  ultimately show ?thesis by auto
qed

lemma denote_while_n_positive: 
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and un: "adjoint M1 * M1 \<le>\<^sub>L   1\<^sub>m d"
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
  shows "partial_density_operator \<rho> \<and> \<rho> \<in> carrier_mat d d \<Longrightarrow> positive (denote_while_n M0 M1 DS n \<rho>)"
proof (induction n arbitrary: \<rho>)
  case 0
  then show ?case using positive_close_under_left_right_mult_adjoint dim0 unfolding partial_density_operator_def by auto
next
  case (Suc n)
  then show ?case 
  proof -
    have pdoM: "partial_density_operator (M1 * \<rho> * adjoint M1)" using pdo_close_under_measurement Suc dim1 un by auto
    moreover have cM: "M1 * \<rho> * adjoint M1 \<in> carrier_mat d d" using Suc dim1 adjoint_dim index_mult_mat by auto
    ultimately have DSM1: "positive (DS (M1 * \<rho> * adjoint M1)) \<and> trace (DS (M1 * \<rho> * adjoint M1)) \<le> trace (M1 * \<rho> * adjoint M1) \<and> DS (M1 * \<rho> * adjoint M1) \<in> carrier_mat d d"
      using DS by auto
    moreover have "trace (M1 * \<rho> * adjoint M1) \<le> trace \<rho>" using trace_decrease_mul_adj Suc dim1 un by auto
    ultimately have "partial_density_operator (DS (M1 * \<rho> * adjoint M1))" using Suc unfolding partial_density_operator_def by auto
    then have "positive (M0 * denote_while_n_iter M0 M1 DS n (DS (M1 * \<rho> * adjoint M1)) * adjoint M0)" using Suc DSM1 by auto
    then have "positive (denote_while_n M0 M1 DS (Suc n) \<rho>)" by auto
    then show ?thesis by auto      
  qed
qed

lemma denote_while_n_sum_positive:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and un: "adjoint M1 * M1 \<le>\<^sub>L   1\<^sub>m d" 
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and pdo: "partial_density_operator \<rho>" and r: " \<rho> \<in> carrier_mat d d" 
    shows "positive (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)"
proof -
  have "\<And>k. k < n \<Longrightarrow> positive (denote_while_n M0 M1 DS k \<rho>)"  using assms denote_while_n_positive by auto
  moreover have "\<And>k. k < n \<Longrightarrow> denote_while_n M0 M1 DS k \<rho> \<in> carrier_mat d d" using denote_while_n_dim assms by auto
  ultimately show ?thesis using matrix_sum_positive by auto
qed

lemma trace_measure2_id:
  assumes dM0: "M0 \<in> carrier_mat n n" and dM1: "M1 \<in> carrier_mat n n" 
    and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m n"
    and dA: "A \<in> carrier_mat n n"
  shows "trace (M0 * A * adjoint M0) + trace (M1 * A * adjoint M1) = trace A"
proof -
  have "trace (M0 * A * adjoint M0) + trace (M1 * A * adjoint M1) = trace ((adjoint M0 * M0 + adjoint M1 * M1) * A)"
    using assms by (mat_assoc n)
  also have "\<dots> = trace (1\<^sub>m n * A)" using id by auto
  also have "\<dots> = trace A" using dA by auto
  finally show ?thesis.
qed

lemma measurement_lowner_le_one1:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d"
  shows "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d"
proof -
  have paM0: "positive (adjoint M0 * M0)"
    apply (subgoal_tac "adjoint M0 * adjoint (adjoint M0) = adjoint M0 * M0")
    subgoal using positive_if_decomp[of "adjoint M0 * M0"] dim0 adjoint_dim[OF dim0] by fastforce
    using adjoint_adjoint[of M0] by auto
  have le1: "adjoint M0 * M0 + adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using id lowner_le_refl[of "1\<^sub>m d"] by fastforce
  show "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" 
    using add_positive_le_reduce2[OF _ _ _ paM0 le1] dim0 dim1 by fastforce
qed

lemma denote_while_n_sum_trace:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d" 
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and r: " \<rho> \<in> carrier_mat d d"
      and pdor: "partial_density_operator \<rho>"
    shows "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> trace \<rho>"
proof -
  have un: "adjoint M1 * M1 \<le>\<^sub>L 1\<^sub>m d" using measurement_lowner_le_one1 using dim0 dim1 id by auto
  have DS': "(DS \<rho> \<in> carrier_mat d d) \<and> partial_density_operator (DS \<rho>)" if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
  proof -
    have res: "positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d" using DS that by auto
    moreover have "trace \<rho> \<le> 1" using that partial_density_operator_def by auto
    ultimately have "trace (DS \<rho>) \<le> 1" by auto
    with res show ?thesis unfolding partial_density_operator_def by auto
  qed
  have dWk: "denote_while_n_iter M0 M1 DS k \<rho> \<in> carrier_mat d d" for k 
    using denote_while_n_iter_dim[OF r pdor dim1 un] DS' dim0 dim1 by auto
  have pdoWk: "partial_density_operator (denote_while_n_iter M0 M1 DS k \<rho>)" for k 
    using pdo_denote_while_n_iter[OF r pdor dim1 un] DS' dim0 dim1 by auto
  have dW0k: "denote_while_n M0 M1 DS k \<rho> \<in> carrier_mat d d" for k using denote_while_n_dim r dim0 dim1 pdor by auto
  then have dsW0k: "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) k \<in> carrier_mat d d" for k
    using matrix_sum_dim[of k "\<lambda>k. denote_while_n M0 M1 DS k \<rho>"] by auto

  have "(denote_while_n_comp M0 M1 DS n \<rho>) \<in> carrier_mat d d" for n unfolding denote_while_n_comp.simps using dim1 dWk by auto
  moreover have 
    pdoW1k: "partial_density_operator (denote_while_n_comp M0 M1 DS n \<rho>)" for n unfolding denote_while_n_comp.simps
    using pdo_close_under_measurement[OF dim1 dWk pdoWk un] by auto
  ultimately have "trace (DS (denote_while_n_comp M0 M1 DS n \<rho>)) \<le> trace (denote_while_n_comp M0 M1 DS n \<rho>)" for n
    using DS by auto
  moreover have "trace (denote_while_n_iter M0 M1 DS (Suc n) \<rho>) = trace (DS (denote_while_n_comp M0 M1 DS n \<rho>))" for n
    using denote_while_n_iter_assoc[folded denote_while_n_comp.simps] by auto
  ultimately have leq3: "trace (denote_while_n_iter M0 M1 DS (Suc n) \<rho>) \<le> trace (denote_while_n_comp M0 M1 DS n \<rho>)" for n by auto

  have mainleq: "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)) + trace (denote_while_n_comp M0 M1 DS n \<rho>) \<le> trace \<rho>" for n
  proof (induct n)
    case 0
    then show ?case unfolding matrix_sum.simps denote_while_n.simps denote_while_n_comp.simps denote_while_n_iter.simps 
      apply (subgoal_tac "M0 * \<rho> * adjoint M0 + 0\<^sub>m d d = M0 * \<rho> * adjoint M0")
      using trace_measure2_id[OF dim0 dim1 id r] dim0 apply simp
      using dim0 by auto
  next
    case (Suc n)

    have eq1: "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc (Suc n))) 
      = trace (denote_while_n M0 M1 DS (Suc n) \<rho>) + trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n))"
      unfolding matrix_sum.simps
      using trace_add_linear dW0k[of "Suc n"] dsW0k[of "Suc n"] by auto

    have eq2: "trace (denote_while_n M0 M1 DS (Suc n) \<rho>) + trace (denote_while_n_comp M0 M1 DS (Suc n) \<rho>) 
      = trace (denote_while_n_iter M0 M1 DS (Suc n) \<rho>)"
      unfolding denote_while_n.simps denote_while_n_comp.simps using trace_measure2_id[OF dim0 dim1 id dWk[of "Suc n"]] by auto

    have "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc (Suc n))) + trace (denote_while_n_comp M0 M1 DS (Suc n) \<rho>)
    = trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)) + trace (denote_while_n M0 M1 DS (Suc n) \<rho>) + trace (denote_while_n_comp M0 M1 DS (Suc n) \<rho>)"
      using eq1 by auto
    also have "\<dots> = trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)) + trace (denote_while_n_iter M0 M1 DS (Suc n) \<rho>)"
      using eq2 by auto
    also have "\<dots> \<le> trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)) + trace (denote_while_n_comp M0 M1 DS n \<rho>)"
      using leq3 by auto
    also have "\<dots> \<le> trace \<rho>" using Suc by auto
    finally show ?case.
  qed

  have reduce_le_complex: "(b::complex) \<ge> 0 \<Longrightarrow> a + b \<le> c \<Longrightarrow> a \<le> c" for a b c by simp
  have "positive (denote_while_n_comp M0 M1 DS n \<rho>)" for n using pdoW1k unfolding partial_density_operator_def by auto
  then have "trace (denote_while_n_comp M0 M1 DS n \<rho>) \<ge> 0" for n using positive_trace
    using \<open>\<And>n. denote_while_n_comp M0 M1 DS n \<rho> \<in> carrier_mat d d\<close> by blast
  then have "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)) \<le> trace \<rho>" for n 
    using mainleq reduce_le_complex[of "trace (denote_while_n_comp M0 M1 DS n \<rho>)"] by auto
  moreover have "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) 0) \<le> trace \<rho>"
    unfolding matrix_sum.simps
    using trace_zero positive_trace pdor unfolding partial_density_operator_def
    using r by auto
  ultimately show "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> trace \<rho>" for n 
    apply (induct n) by auto
qed
 
lemma denote_while_n_sum_partial_density:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d"
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and pdo: "partial_density_operator \<rho>" and r: " \<rho> \<in> carrier_mat d d" 
  shows "(partial_density_operator (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n))"
proof -
  have "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> trace \<rho>" 
    using denote_while_n_sum_trace assms by auto
  then have "trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> 1" 
    using pdo unfolding partial_density_operator_def  by auto
  moreover have "positive (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)" 
    using assms DS denote_while_n_sum_positive measurement_lowner_le_one1[OF dim0 dim1 id] by auto
  ultimately show ?thesis unfolding partial_density_operator_def by auto
qed

lemma denote_while_n_sum_lowner_le:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d"
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and pdo: "partial_density_operator \<rho>" and dimr: " \<rho> \<in> carrier_mat d d" 
  shows "(matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<le>\<^sub>L matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n))"
proof auto
  have whilenc: "denote_while_n M0 M1 DS n \<rho> \<in> carrier_mat d d" using denote_while_n_dim assms by auto
  have sumc: "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<in> carrier_mat d d"
    using denote_while_n_sum_dim assms by auto
  have "denote_while_n M0 M1 DS n \<rho> + matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n - matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n
         = denote_while_n M0 M1 DS n \<rho>  + matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n + (- matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)" 
    using  minus_add_uminus_mat[of "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n" d d "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n"] by auto
  also have "\<dots> = denote_while_n M0 M1 DS n \<rho>  + 0\<^sub>m d d" 
    by (smt assoc_add_mat minus_add_uminus_mat minus_r_inv_mat sumc uminus_carrier_mat whilenc)
  also have "\<dots> = denote_while_n M0 M1 DS n \<rho>" using whilenc by auto
  finally have simp: "denote_while_n M0 M1 DS n \<rho> + matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n -  matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n =
                denote_while_n M0 M1 DS n \<rho> " by auto
  have "positive (denote_while_n M0 M1 DS n \<rho>)" using denote_while_n_positive assms measurement_lowner_le_one1[OF dim0 dim1 id] by auto
  then have "matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<le>\<^sub>L (denote_while_n M0 M1 DS n \<rho> + matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)"
    unfolding lowner_le_def using simp by auto
  then show "matrix_sum d (\<lambda>n. M0 * denote_while_n_iter M0 M1 DS n \<rho> * adjoint M0) n \<le>\<^sub>L
             (M0 * denote_while_n_iter M0 M1 DS n \<rho> * adjoint M0 + matrix_sum d (\<lambda>n. M0 * denote_while_n_iter M0 M1 DS n \<rho> * adjoint M0) n)" by auto
qed

lemma lowner_is_lub_matrix_sum: 
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d"
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and pdo: "partial_density_operator \<rho>" and dimr: " \<rho> \<in> carrier_mat d d" 
  shows  "matrix_seq.lowner_is_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)) (matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)))"
proof-
  have sumdd: "\<forall>n. matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<in> carrier_mat d d"
    using  denote_while_n_sum_dim assms by auto
  have sumtr: "\<forall>n. trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> trace \<rho>"
    using denote_while_n_sum_trace assms by auto
  have sumpar: "\<forall>n. partial_density_operator (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)"
    using denote_while_n_sum_partial_density assms by auto
  have sumle:"\<forall>n. matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<le>\<^sub>L matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)"
    using denote_while_n_sum_lowner_le assms by auto
  have seqd: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>))"
    using matrix_seq_def sumdd sumpar sumle by auto
  then show ?thesis  using matrix_seq.lowner_lub_prop[of d "(matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>))"] by auto
qed
  
lemma denote_while_dim_positive:
  assumes dim0: "M0 \<in> carrier_mat d d" and dim1: "M1 \<in> carrier_mat d d" and id: "adjoint M0 * M0 + adjoint M1 * M1 = 1\<^sub>m d"
      and DS: "\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (DS \<rho>) \<and> trace (DS \<rho>) \<le> trace \<rho> \<and> DS \<rho> \<in> carrier_mat d d"
      and pdo: "partial_density_operator \<rho>" and dimr: " \<rho> \<in> carrier_mat d d" 
  shows
    "denote_while M0 M1 DS \<rho> \<in> carrier_mat d d \<and> positive (denote_while M0 M1 DS \<rho>) \<and> trace (denote_while M0 M1 DS \<rho>) \<le> trace \<rho>"
proof -
  have sumdd: "\<forall>n. matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<in> carrier_mat d d"
    using denote_while_n_sum_dim assms by auto
  have sumtr: "\<forall>n. trace (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n) \<le> trace \<rho>"
    using denote_while_n_sum_trace assms by auto
  have sumpar: "\<forall>n. partial_density_operator (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n)"
    using denote_while_n_sum_partial_density assms by auto
  have sumle:"\<forall>n. matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) n \<le>\<^sub>L matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>) (Suc n)"
    using denote_while_n_sum_lowner_le assms by auto
  have seqd: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>))"
    using matrix_seq_def sumdd sumpar sumle by auto
  have "matrix_seq.lowner_is_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)) (matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)))"
    using lowner_is_lub_matrix_sum assms by auto
  then have "matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)) \<in> carrier_mat d d
            \<and> positive (matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>)))
            \<and> trace (matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n M0 M1 DS n \<rho>))) \<le> trace \<rho>"
    using matrix_seq.lowner_is_lub_dim seqd matrix_seq.lowner_lub_is_positive matrix_seq.lowner_lub_trace sumtr by auto
  then show ?thesis unfolding denote_while_def matrix_inf_sum_def by auto 
qed 

definition denote_measure :: "nat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> ((state \<Rightarrow> state) list) \<Rightarrow> state \<Rightarrow> state" where
  "denote_measure n M DS \<rho> = matrix_sum d (\<lambda>k. (DS!k) ((M k) * \<rho> * adjoint (M k))) n"

lemma denote_measure_dim:
  assumes "\<rho> \<in> carrier_mat d d"
    "measurement d n M"
    "\<And>\<rho>' k. \<rho>' \<in> carrier_mat d d \<Longrightarrow> k < n \<Longrightarrow> (DS!k) \<rho>' \<in> carrier_mat d d"
  shows
    "denote_measure n M DS \<rho> \<in> carrier_mat d d"
proof -
  have dMk: "k < n \<Longrightarrow> M k \<in> carrier_mat d d" for k using assms measurement_def by auto
  have d: "k < n \<Longrightarrow> (M k) * \<rho> * adjoint (M k) \<in> carrier_mat d d" for k 
    using mult_carrier_mat[OF mult_carrier_mat[OF dMk assms(1)] adjoint_dim[OF dMk]] by auto
  then have "k < n \<Longrightarrow> (DS!k) ((M k) * \<rho> * adjoint (M k)) \<in> carrier_mat d d" for k using assms(3) by auto
  then show ?thesis unfolding denote_measure_def using matrix_sum_dim[of n "\<lambda>k. (DS!k) ((M k) * \<rho> * adjoint (M k))"] by auto
qed

lemma measure_well_com:
  assumes "well_com (Measure n M S)"
  shows "\<And>k. k < n \<Longrightarrow> well_com (S ! k)"
  using assms unfolding well_com.simps using list_all_length by auto


text \<open>Semantics of commands\<close>
fun denote :: "com \<Rightarrow> state \<Rightarrow> state" where
  "denote SKIP \<rho> = \<rho>"
| "denote (Utrans U) \<rho> = U * \<rho> * adjoint U"
| "denote (Seq S1 S2) \<rho> = denote S2 (denote S1 \<rho>)"
| "denote (Measure n M S) \<rho> = denote_measure n M (map denote S) \<rho>"
| "denote (While M S) \<rho> = denote_while (M 0) (M 1) (denote S) \<rho>"


lemma denote_measure_expand:
  assumes m: "m \<le> n" and wc: "well_com (Measure n M S)"  
  shows "denote (Measure m M S) \<rho> = matrix_sum d (\<lambda>k. denote (S!k) ((M k) * \<rho> * adjoint (M k))) m"
  unfolding denote.simps denote_measure_def
proof -
  have "k < m \<Longrightarrow> map denote S ! k = denote (S!k)" for k using wc m by auto
  then have "k < m \<Longrightarrow> (map denote S ! k) (M k * \<rho> * adjoint (M k)) = denote (S!k) ((M k) * \<rho> * adjoint (M k))" for k by auto
  then show "matrix_sum d (\<lambda>k. (map denote S ! k) (M k * \<rho> * adjoint (M k))) m
    = matrix_sum d (\<lambda>k. denote (S ! k) (M k * \<rho> * adjoint (M k))) m" 
    using matrix_sum_cong[of m "\<lambda>k. (map denote S ! k) (M k * \<rho> * adjoint (M k))" "\<lambda>k. denote (S ! k) (M k * \<rho> * adjoint (M k))"] by auto
qed

lemma matrix_sum_trace_le:
  fixes f :: "nat \<Rightarrow> complex mat" and g :: "nat \<Rightarrow> complex mat"
  assumes "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d d)" 
    "(\<And>k. k < n \<Longrightarrow> g k \<in> carrier_mat d d)"
    "(\<And>k. k < n \<Longrightarrow> trace (f k) \<le> trace (g k))"
  shows "trace (matrix_sum d f n) \<le> trace (matrix_sum d g n)"
proof -
  have "sum (\<lambda>k. trace (f k)) {0..<n} \<le>  sum (\<lambda>k. trace (g k)) {0..<n}"
    using assms by (meson atLeastLessThan_iff sum_mono)
  then show ?thesis using trace_matrix_sum_linear assms by auto
qed

lemma map_denote_positive_trace_dim:
  assumes "well_com (Measure x1 x2a x3a)"
    "x4 \<in> carrier_mat d d"
    "partial_density_operator x4"
    "\<And>x3aa \<rho>. x3aa \<in> set x3a \<Longrightarrow> well_com x3aa \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
      \<Longrightarrow> positive (denote x3aa \<rho>) \<and> trace (denote x3aa \<rho>) \<le> trace \<rho> \<and> denote x3aa \<rho> \<in> carrier_mat d d"
  shows "\<forall>k < x1. positive ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) 
               \<and> ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<in> carrier_mat d d
               \<and> trace ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<le> trace (x2a k * x4 * adjoint (x2a k))"
proof -
  have x2ak: "\<forall> k < x1. x2a k \<in> carrier_mat d d" using assms(1) measurement_dim by auto
  then have x2aa:"\<forall> k < x1. (x2a k * x4 * adjoint (x2a k)) \<in> carrier_mat d d" using assms(2) by fastforce
  have posct: "positive ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) 
               \<and> ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<in> carrier_mat d d
               \<and> trace ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<le> trace (x2a k * x4 * adjoint (x2a k))"
    if k: "k < x1" for k
  proof -
    have lea: "adjoint (x2a k) * x2a k \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat assms(1) k by auto
    have "(x2a k * x4 * adjoint (x2a k)) \<in> carrier_mat d d" using k x2aa assms(2) by fastforce
    moreover have "(x3a ! k) \<in> set x3a" using k assms(1) by simp
    moreover have "well_com (x3a ! k)"  using k assms(1) using measure_well_com by blast
    moreover have "partial_density_operator (x2a k * x4 * adjoint (x2a k))" 
      using pdo_close_under_measurement x2ak assms(2,3) lea  k by blast 
    ultimately have "positive (denote (x3a ! k) (x2a k * x4 * adjoint (x2a k)))
         \<and> (denote (x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<in> carrier_mat d d
         \<and> trace (denote (x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<le> trace (x2a k * x4 * adjoint (x2a k))" 
      using assms(4) by auto
    then show ?thesis using assms(1) k by auto          
  qed
  then show ?thesis by auto
qed

lemma denote_measure_positive_trace_dim:
  assumes "well_com (Measure x1 x2a x3a)"
    "x4 \<in> carrier_mat d d"
    "partial_density_operator x4"
    "\<And>x3aa \<rho>. x3aa \<in> set x3a \<Longrightarrow> well_com x3aa \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
      \<Longrightarrow> positive (denote x3aa \<rho>) \<and> trace (denote x3aa \<rho>) \<le> trace \<rho> \<and> denote x3aa \<rho> \<in> carrier_mat d d"
  shows "positive (denote (Measure x1 x2a x3a) x4) \<and> trace (denote (Measure x1 x2a x3a) x4) \<le> trace x4
        \<and> (denote (Measure x1 x2a x3a) x4) \<in> carrier_mat d d"
proof -
  have x2ak: "\<forall> k < x1. x2a k \<in> carrier_mat d d" using assms(1) measurement_dim by auto
  then have x2aa:"\<forall> k < x1. (x2a k * x4 * adjoint (x2a k)) \<in> carrier_mat d d" using assms(2) by fastforce
  have posct:"\<forall> k < x1. positive ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) 
               \<and> ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<in> carrier_mat d d
               \<and> trace ((map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) \<le> trace (x2a k * x4 * adjoint (x2a k))"
    using map_denote_positive_trace_dim assms by auto
  
  have "trace (matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) x1)
       \<le> trace (matrix_sum d (\<lambda>k. (x2a k * x4 * adjoint (x2a k))) x1)"
    using posct matrix_sum_trace_le[of x1 "(\<lambda>k. (map denote x3a ! k) (x2a k * x4 * adjoint (x2a k)))" "(\<lambda>k. x2a k * x4 * adjoint (x2a k)) "]
         x2aa by auto
  also have "\<dots> = trace x4"  using trace_measurement[of d "x1" "x2a" x4] assms(1,2) by auto
  finally have " trace (matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * x4 * adjoint (x2a k))) x1) \<le> trace x4" by auto
  then have "trace (denote_measure x1 x2a (map denote x3a) x4) \<le> trace x4"
    unfolding denote_measure_def by auto
  then have "trace (denote (Measure x1 x2a x3a) x4) \<le> trace x4" by auto
  moreover from posct have "positive (denote (Measure x1 x2a x3a) x4)"
    apply auto
    unfolding denote_measure_def using matrix_sum_positive by auto
  moreover have "(denote (Measure x1 x2a x3a) x4) \<in> carrier_mat d d" 
    apply auto  
    unfolding denote_measure_def using matrix_sum_dim posct 
    by (simp add: matrix_sum_dim)
  ultimately show ?thesis by auto
qed
  
lemma denote_positive_trace_dim:
  "well_com S \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
   \<Longrightarrow> (positive (denote S \<rho>) \<and> trace (denote S \<rho>) \<le> trace \<rho> \<and> denote S \<rho> \<in> carrier_mat d d)"
proof (induction arbitrary: \<rho>)
  case SKIP
then show ?case unfolding partial_density_operator_def by auto
next
case (Utrans x)
  then show ?case  
  proof -
    assume wc: "well_com (Utrans x)" and r: "\<rho> \<in> carrier_mat d d" and pdo: "partial_density_operator \<rho>"
    show "positive (denote (Utrans x) \<rho>) \<and> trace (denote (Utrans x) \<rho>) \<le> trace \<rho> \<and> denote (Utrans x) \<rho> \<in> carrier_mat d d"
    proof -
     have "trace (x * \<rho> * adjoint x) = trace ((adjoint x * x) * \<rho>)"
       using r apply (mat_assoc d) using wc by auto
     also have "\<dots> = trace (1\<^sub>m d * \<rho>)" using wc inverts_mat_def inverts_mat_symm adjoint_dim by auto
     also have "\<dots> = trace \<rho>"  using r by auto
     finally have fst: "trace (x * \<rho> * adjoint x) = trace \<rho>" by auto
     moreover have "positive (x * \<rho> * adjoint x)" using positive_close_under_left_right_mult_adjoint r pdo wc unfolding partial_density_operator_def by auto
     moreover have "x * \<rho> * adjoint x \<in> carrier_mat d d" using r wc adjoint_dim index_mult_mat by auto
     ultimately show ?thesis by auto
    qed
  qed
next
  case (Seq x1 x2a)
  then show ?case
  proof -
    assume dx1: "(\<And>\<rho>. well_com x1 \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (denote x1 \<rho>) \<and> trace (denote x1 \<rho>) \<le> trace \<rho> \<and> denote x1 \<rho> \<in> carrier_mat d d)"
       and dx2a: "(\<And>\<rho>. well_com x2a \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive (denote x2a \<rho>) \<and> trace (denote x2a \<rho>) \<le> trace \<rho> \<and> denote x2a \<rho> \<in> carrier_mat d d)"
       and wc: "well_com (Seq x1 x2a)" and r: "\<rho> \<in> carrier_mat d d" and pdo: "partial_density_operator \<rho>"
    show "positive (denote (Seq x1 x2a) \<rho>) \<and> trace (denote (Seq x1 x2a) \<rho>) \<le> trace \<rho> \<and> denote (Seq x1 x2a) \<rho> \<in> carrier_mat d d"
    proof -
      have ptc: "positive (denote x1 \<rho>) \<and> trace (denote x1 \<rho>) \<le> trace \<rho> \<and> denote x1 \<rho> \<in> carrier_mat d d"
        using wc r pdo dx1 by auto
      then have "partial_density_operator (denote x1 \<rho>)" using pdo unfolding partial_density_operator_def by auto
      then show ?thesis using ptc dx2a wc  dual_order.trans by auto
    qed
  qed
next
  case (Measure x1 x2a x3a)
  then show ?case using denote_measure_positive_trace_dim by auto
next
  case (While x1 x2a)
  then show ?case
  proof -
    have "adjoint (x1 0) * (x1 0) + adjoint (x1 1) * (x1 1) = 1\<^sub>m d"
      using measurement_id2 While by auto
    moreover have "(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> 
      positive (denote x2a \<rho>) \<and> trace (denote x2a \<rho>) \<le> trace \<rho> \<and> denote x2a \<rho> \<in> carrier_mat d d)"
      using While by fastforce
    moreover have "x1 0 \<in> carrier_mat d d \<and> x1 1 \<in> carrier_mat d d"
      using measurement_dim While by fastforce
    ultimately have "denote_while (x1 0) (x1 1) (denote x2a) \<rho> \<in> carrier_mat d d \<and> 
               positive (denote_while (x1 0) (x1 1) (denote x2a) \<rho>) \<and> 
               trace (denote_while (x1 0) (x1 1) (denote x2a) \<rho>) \<le> trace \<rho>"
      using denote_while_dim_positive[of "x1 0" "x1 1" "denote x2a" "\<rho>"] While by fastforce
    then show ?thesis by auto
  qed 
qed

lemma denote_dim_pdo:
  "well_com S \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
   \<Longrightarrow> (denote S \<rho> \<in> carrier_mat d d) \<and> (partial_density_operator (denote S \<rho>))"
  using denote_positive_trace_dim unfolding partial_density_operator_def by fastforce

lemma denote_dim:
  "well_com S \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
   \<Longrightarrow> (denote S \<rho> \<in> carrier_mat d d)"
  using denote_positive_trace_dim by auto

lemma denote_trace:
  "well_com S \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
   \<Longrightarrow> trace (denote S \<rho>) \<le> trace \<rho>"
  using denote_positive_trace_dim by auto

lemma denote_partial_density_operator:
  assumes "well_com S" "partial_density_operator \<rho>" "\<rho> \<in> carrier_mat d d"
  shows "partial_density_operator (denote S \<rho>)"
  using assms denote_positive_trace_dim unfolding partial_density_operator_def
  using dual_order.trans by blast


lemma denote_while_n_sum_mat_seq:
  assumes "\<rho> \<in> carrier_mat d d" and
    "x1 0 \<in> carrier_mat d d" and
    "x1 1 \<in> carrier_mat d d" and
    "partial_density_operator \<rho>" and
    wc: "well_com x2" and mea: "measurement d 2 x1"  
  shows "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>))"   
proof -
  let ?A = "x1 0" and ?B = "x1 1"
  have dx2:"\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow>
            positive ((denote x2) \<rho>) \<and> trace ((denote x2) \<rho>) \<le> trace \<rho> \<and> (denote x2) \<rho> \<in> carrier_mat d d"
    using denote_positive_trace_dim wc by auto
  have lo1: "adjoint ?A * ?A + adjoint ?B * ?B = 1\<^sub>m d" using measurement_id2 assms by auto
  have "\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n \<in> carrier_mat d d"
    using assms dx2 
    by (metis denote_while_n_dim matrix_sum_dim)
  moreover have "(\<forall>n. partial_density_operator (matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n))"
    using assms dx2 lo1
    by (metis denote_while_n_sum_partial_density)
  moreover have "(\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n \<le>\<^sub>L matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) (Suc n))"
    using assms dx2 lo1
    by (metis denote_while_n_sum_lowner_le)
  ultimately show ?thesis
    unfolding matrix_seq_def by auto
qed 

lemma denote_while_n_add:
  assumes M0: "x1 0 \<in> carrier_mat d d" and
    M1: "x1 1 \<in> carrier_mat d d" and
    wc: "well_com x2" and mea: "measurement d 2 x1" and
    DS: "(\<And>\<rho>\<^sub>1 \<rho>\<^sub>2. \<rho>\<^sub>1 \<in> carrier_mat d d \<Longrightarrow> \<rho>\<^sub>2 \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho>\<^sub>1 \<Longrightarrow> 
      partial_density_operator \<rho>\<^sub>2 \<Longrightarrow> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<le> 1 \<Longrightarrow> denote x2 (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote x2 \<rho>\<^sub>1 + denote x2 \<rho>\<^sub>2)"
  shows "\<rho>\<^sub>1 \<in> carrier_mat d d \<Longrightarrow> \<rho>\<^sub>2 \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho>\<^sub>1 \<Longrightarrow> partial_density_operator \<rho>\<^sub>2 \<Longrightarrow> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<le> 1 \<Longrightarrow> 
    denote_while_n (x1 0) (x1 1) (denote x2) k (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>1 + denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>2"
proof (auto, induct k arbitrary: \<rho>\<^sub>1 \<rho>\<^sub>2)
  case 0
  then show ?case
    apply auto using M0 by (mat_assoc d)
next
  case (Suc k)
  then show ?case 
  proof -
    let ?A = "x1 0" and ?B = "x1 1"
    have dx2:"(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive ((denote x2) \<rho>) \<and> trace ((denote x2) \<rho>) \<le> trace \<rho> \<and> (denote x2) \<rho> \<in> carrier_mat d d) "
      using denote_positive_trace_dim wc by auto
    have lo1: "adjoint ?B * ?B \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat assms by auto
    have dim1: "x1 1 * \<rho>\<^sub>1 * adjoint (x1 1) \<in> carrier_mat d d" using assms Suc 
      by (metis adjoint_dim mult_carrier_mat)
    moreover have pdo1: "partial_density_operator (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))"
      using pdo_close_under_measurement assms(2) Suc(2,4) lo1 by auto
    ultimately have dimr1: "denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) \<in> carrier_mat d d"
      using dx2 by auto
    have dim2: "x1 1 * \<rho>\<^sub>2 * adjoint (x1 1) \<in> carrier_mat d d" using assms Suc 
      by (metis adjoint_dim mult_carrier_mat)
    moreover have pdo2: "partial_density_operator (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"
      using pdo_close_under_measurement assms(2) Suc lo1 by auto
    ultimately have dimr2: "denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1)) \<in> carrier_mat d d"
      using dx2 by auto
    have pdor1: "partial_density_operator (denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)))"
      using denote_partial_density_operator assms dim1 pdo1 by auto
    have pdor2: "partial_density_operator (denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1)))"
      using denote_partial_density_operator assms dim2 pdo2 by auto
    have "trace (denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))) \<le> trace (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))"
      using dx2 dim1 pdo1 by auto
    also have tr1: "\<dots> \<le> trace \<rho>\<^sub>1" using trace_decrease_mul_adj assms Suc lo1 by auto
    finally have trr1:" trace (denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))) \<le> trace \<rho>\<^sub>1" by auto
    have "trace (denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> trace (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"
      using dx2 dim2 pdo2 by auto
    also have tr2: "\<dots> \<le> trace \<rho>\<^sub>2" using trace_decrease_mul_adj assms Suc lo1 by auto
    finally have trr2:" trace (denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> trace \<rho>\<^sub>2" by auto
    from tr1 tr2 Suc have "trace ( (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) +  (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2)"
      using trace_add_linear trace_add_linear[of "(x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))" d "(x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"]
            trace_add_linear[of \<rho>\<^sub>1 d \<rho>\<^sub>2]
      using dim1 dim2 by auto
    then have trless1: "trace ( (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) +  (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> 1" using Suc by auto
    from trr1 trr2 Suc have "trace (denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) + denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2)"
      using trace_add_linear[of "denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1))" d "denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"]
            trace_add_linear[of \<rho>\<^sub>1 d \<rho>\<^sub>2]
      using dimr1 dimr2 by auto
    then have trless2: "trace (denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) + denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))) \<le> 1"
      using Suc by auto
    have "x1 1 * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x1 1) = (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) + (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"
      using M1 Suc by (mat_assoc d)
    then have deadd: "denote x2 (x1 1 * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x1 1)) =
        denote x2 (x1 1 * \<rho>\<^sub>1 * adjoint (x1 1)) + denote x2 (x1 1 * \<rho>\<^sub>2 * adjoint (x1 1))"
      using assms(5) dim1 dim2 pdo1 pdo2 trless1 by auto
    from dimr1 dimr2 pdor1 pdor2 trless2 Suc(1) deadd show ?thesis by auto
  qed
qed

lemma denote_while_add:
  assumes r1: "\<rho>\<^sub>1 \<in> carrier_mat d d" and
    r2: "\<rho>\<^sub>2 \<in> carrier_mat d d" and
    M0: "x1 0 \<in> carrier_mat d d" and
    M1: "x1 1 \<in> carrier_mat d d" and
    pdo1: "partial_density_operator \<rho>\<^sub>1" and
    pdo2: "partial_density_operator \<rho>\<^sub>2" and tr12: "trace (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<le> 1" and
    wc: "well_com x2" and mea: "measurement d 2 x1" and
    DS: "(\<And>\<rho>\<^sub>1 \<rho>\<^sub>2. \<rho>\<^sub>1 \<in> carrier_mat d d \<Longrightarrow> \<rho>\<^sub>2 \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho>\<^sub>1 \<Longrightarrow> 
      partial_density_operator \<rho>\<^sub>2 \<Longrightarrow> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<le> 1 \<Longrightarrow> denote x2 (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote x2 \<rho>\<^sub>1 + denote x2 \<rho>\<^sub>2)"
    shows
    "denote_while (x1 0) (x1 1) (denote x2) (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote_while (x1 0) (x1 1) (denote x2) \<rho>\<^sub>1 + denote_while (x1 0) (x1 1) (denote x2) \<rho>\<^sub>2"
proof -
  let ?A = "x1 0" and ?B = "x1 1"
  have dx2:"(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive ((denote x2) \<rho>) \<and> trace ((denote x2) \<rho>) \<le> trace \<rho> \<and> (denote x2) \<rho> \<in> carrier_mat d d) "
    using denote_positive_trace_dim wc by auto
  have lo1: "adjoint ?A * ?A + adjoint ?B * ?B = 1\<^sub>m d" using measurement_id2 assms by auto
  have pdo12: "partial_density_operator (\<rho>\<^sub>1 + \<rho>\<^sub>2)" using pdo1 pdo2 unfolding partial_density_operator_def using tr12 positive_add assms by auto
  have ms1: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1))"   
    using denote_while_n_sum_mat_seq assms by auto
  have ms2: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2))"   
    using denote_while_n_sum_mat_seq assms by auto
  have dim1: "(\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>\<^sub>1) n \<in> carrier_mat d d)"   
    using assms dx2 
    by (metis denote_while_n_dim matrix_sum_dim)
  have dim2: "(\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>\<^sub>2) n \<in> carrier_mat d d)"   
    using assms dx2 
    by (metis denote_while_n_dim matrix_sum_dim)
  have "trace (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1) n +
               matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2) n) \<le> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2)"
    for n
  proof -
    have "trace (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1) n) \<le> trace \<rho>\<^sub>1"
      using denote_while_n_sum_trace dx2 lo1 assms by auto
    moreover have "trace (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2) n) \<le> trace \<rho>\<^sub>2"
      using denote_while_n_sum_trace dx2 lo1 assms by auto
    ultimately show ?thesis
      using trace_add_linear dim1 dim2
      by (metis add_mono_thms_linordered_semiring(1) r1 r2)
  qed
  then have "\<forall>n. trace (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1) n + matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2) n) \<le> 1"
    using assms(7) dual_order.trans by blast
  then have lladd: "matrix_seq.lowner_lub  (\<lambda>n. (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1)) n + (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2)) n) = matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1))
    + matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2))"
    using lowner_lub_add ms1 ms2 by auto
 
  have "matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (\<rho>\<^sub>1 + \<rho>\<^sub>2)) m =
    matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1) m + matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2) m"
    for m
  proof -
    have "(\<And>k. k < m \<Longrightarrow> denote_while_n (x1 0) (x1 1) (denote x2) k (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<in> carrier_mat d d)"
      using denote_while_n_dim dx2 pdo12 assms measurement_dim by auto
    moreover have "(\<And>k. k < m \<Longrightarrow> denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>1 \<in> carrier_mat d d)" 
      using denote_while_n_dim dx2  assms measurement_dim by auto
    moreover have "(\<And>k. k < m \<Longrightarrow> denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>2 \<in> carrier_mat d d)"
      using denote_while_n_dim dx2  assms measurement_dim by auto
    moreover have "(\<forall>  k < m.
      denote_while_n (x1 0) (x1 1) (denote x2) k (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>1 + denote_while_n (x1 0) (x1 1) (denote x2) k \<rho>\<^sub>2)"
      using denote_while_n_add assms by auto
    ultimately show ?thesis
      using matrix_sum_add[of m "(\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (\<rho>\<^sub>1 + \<rho>\<^sub>2))" d "(\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>\<^sub>1)"
        "(\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>\<^sub>2)"] by auto
  qed
  then have "matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (\<rho>\<^sub>1 + \<rho>\<^sub>2))) = 
    matrix_seq.lowner_lub (\<lambda>n. (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>1)) n + (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>\<^sub>2)) n)"
    using lladd by presburger
  then show ?thesis unfolding denote_while_def matrix_inf_sum_def using lladd by auto
qed

lemma denote_add:
  "well_com S \<Longrightarrow> \<rho>\<^sub>1 \<in> carrier_mat d d \<Longrightarrow> \<rho>\<^sub>2 \<in> carrier_mat d d \<Longrightarrow>
   partial_density_operator \<rho>\<^sub>1 \<Longrightarrow> partial_density_operator \<rho>\<^sub>2 \<Longrightarrow> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2) \<le> 1 \<Longrightarrow>
   denote S (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote S \<rho>\<^sub>1 + denote S \<rho>\<^sub>2"
proof (induction arbitrary: \<rho>\<^sub>1 \<rho>\<^sub>2)
  case SKIP
  then show ?case by auto
next
  case (Utrans U)
  then show ?case by (clarsimp, mat_assoc d)
next
  case (Seq x1 x2a)
  then show ?case
  proof -
    have dim1: "denote x1 \<rho>\<^sub>1 \<in> carrier_mat d d" using denote_positive_trace_dim Seq by auto
    have dim2: "denote x1 \<rho>\<^sub>2 \<in> carrier_mat d d" using denote_positive_trace_dim Seq by auto
    have "trace (denote x1  \<rho>\<^sub>1) \<le> trace \<rho>\<^sub>1" using denote_positive_trace_dim Seq by auto
    moreover have "trace (denote x1 \<rho>\<^sub>2) \<le> trace \<rho>\<^sub>2" using denote_positive_trace_dim Seq by auto
    ultimately have tr: "trace (denote x1 \<rho>\<^sub>1 + denote x1 \<rho>\<^sub>2) \<le> 1" using Seq(4,5,8) trace_add_linear dim1 dim2
      by (smt add_mono order_trans)

    have "denote (Seq x1 x2a) (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote x2a (denote x1 (\<rho>\<^sub>1 + \<rho>\<^sub>2))" by auto
    moreover have "denote x1 (\<rho>\<^sub>1 + \<rho>\<^sub>2) = denote x1 \<rho>\<^sub>1 + denote x1 \<rho>\<^sub>2" using Seq by auto
    moreover have "partial_density_operator (denote x1 \<rho>\<^sub>1)" using denote_partial_density_operator Seq by auto
    moreover have "partial_density_operator (denote x1 \<rho>\<^sub>2)" using denote_partial_density_operator Seq by auto
    ultimately show ?thesis using Seq dim1 dim2 tr by auto
  qed
next
  case (Measure x1 x2a x3a)
  then show ?case
  proof -
    have ptc: "\<And>x3aa \<rho>. x3aa \<in> set x3a \<Longrightarrow> well_com x3aa \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
      \<Longrightarrow> positive (denote x3aa \<rho>) \<and> trace (denote x3aa \<rho>) \<le> trace \<rho> \<and> denote x3aa \<rho> \<in> carrier_mat d d"
      using denote_positive_trace_dim Measure by auto
    then have map:"\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> \<forall> k < x1. positive ((map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))) 
               \<and> ((map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))) \<in> carrier_mat d d
               \<and> trace ((map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))) \<le> trace (x2a k * \<rho> * adjoint (x2a k))"
      using Measure map_denote_positive_trace_dim by auto

    from map have mapd1: "\<And>k. k < x1 \<Longrightarrow> (map denote x3a ! k) (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) \<in> carrier_mat d d"
      using Measure by auto
    from map have mapd2: "\<And>k. k < x1 \<Longrightarrow> (map denote x3a ! k) (x2a k * \<rho>\<^sub>2 * adjoint (x2a k)) \<in> carrier_mat d d"
      using Measure by auto
    have dim1:"\<And>k. k < x1 \<Longrightarrow> x2a k * \<rho>\<^sub>1 * adjoint (x2a k) \<in> carrier_mat d d" 
      using well_com.simps(5) measurement_dim Measure by fastforce
    have dim2: "\<And>k. k < x1 \<Longrightarrow> x2a k * \<rho>\<^sub>2 * adjoint (x2a k) \<in> carrier_mat d d"
      using well_com.simps(5) measurement_dim Measure by fastforce
    have "\<And>k. k < x1 \<Longrightarrow> (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) \<in> carrier_mat d d"
      using well_com.simps(5) measurement_dim Measure by fastforce
    have lea: "\<And>k. k < x1 \<Longrightarrow> adjoint (x2a k) * x2a k \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat Measure by auto
    moreover have dimx: "\<And>k. k < x1 \<Longrightarrow> x2a k \<in> carrier_mat d d" using Measure measurement_dim by auto
    ultimately have pdo12:"\<And>k. k < x1 \<Longrightarrow> partial_density_operator (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) \<and> partial_density_operator (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))"
      using pdo_close_under_measurement Measure measurement_dim by blast

    have trless: "trace (x2a k * \<rho>\<^sub>1 * adjoint (x2a k) + x2a k * \<rho>\<^sub>2 * adjoint (x2a k)) \<le> 1"
      if k: "k < x1" for k
    proof -
      have "trace (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) \<le> trace \<rho>\<^sub>1" using trace_decrease_mul_adj dimx Measure lea k by auto
      moreover have "trace (x2a k * \<rho>\<^sub>2 * adjoint (x2a k)) \<le> trace \<rho>\<^sub>2" using trace_decrease_mul_adj dimx Measure lea k by auto
      ultimately have "trace (x2a k * \<rho>\<^sub>1 * adjoint (x2a k) + x2a k * \<rho>\<^sub>2 * adjoint (x2a k)) \<le> trace (\<rho>\<^sub>1 + \<rho>\<^sub>2)"
        using trace_add_linear dim1 dim2 Measure k 
        by (metis add_mono_thms_linordered_semiring(1))
      then show ?thesis using Measure(7) by auto
    qed
 
    have dist: "(x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) = (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))"
      if k: "k < x1" for k
    proof -
      have "(x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) = ((x2a k * \<rho>\<^sub>1 + x2a k * \<rho>\<^sub>2) * adjoint (x2a k))"
        using mult_add_distrib_mat Measure well_com.simps(4) measurement_dim by (metis k)
      also have "\<dots> = (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))"
        apply (mat_assoc d) using Measure k well_com.simps(4) measurement_dim by auto
      finally show ?thesis by auto
    qed

    have mapadd: "(map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) =
        (map denote x3a ! k) (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + (map denote x3a ! k) (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))"
      if k: "k < x1" for k
    proof -
      have "(map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) = denote (x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k))"
        using Measure.prems(1) k by auto
      then have mapx: "(map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) =  denote (x3a ! k) ((x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + (x2a k * \<rho>\<^sub>2 * adjoint (x2a k)))"
        using dist k by auto
      have "denote (x3a ! k) ((x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))) 
           = denote (x3a ! k) (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)) + denote (x3a ! k) (x2a k * \<rho>\<^sub>2  * adjoint (x2a k))"
        using Measure(1,2) dim1 dim2 pdo12 trless k
        by (simp add: list_all_length)
      then show ?thesis  
        using Measure.prems(1) mapx k by auto
    qed
    then have mapd12:"(\<And>k. k < x1 \<Longrightarrow> (map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)) \<in> carrier_mat d d)"
      using mapd1 mapd2 by auto

    have "matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k))) x1 =
          matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * \<rho>\<^sub>1 * adjoint (x2a k))) x1 + 
          matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * \<rho>\<^sub>2 * adjoint (x2a k))) x1"
      using matrix_sum_add[of x1 "(\<lambda>k. (map denote x3a ! k) (x2a k * (\<rho>\<^sub>1 + \<rho>\<^sub>2) * adjoint (x2a k)))" d "(\<lambda>k. (map denote x3a ! k) (x2a k * \<rho>\<^sub>1 * adjoint (x2a k)))" "(\<lambda>k. (map denote x3a ! k) (x2a k * \<rho>\<^sub>2 * adjoint (x2a k)))"]
      using mapd12 mapd1 mapd2 mapadd by auto
    then show ?thesis  using denote.simps(4) unfolding denote_measure_def by auto
  qed
next
  case (While x1 x2)
  then show ?case
    apply auto using denote_while_add measurement_dim by auto     
qed 


lemma mulfact:
  fixes c:: real and a:: complex and b:: complex
  assumes "c\<ge>0" "a \<le> b"
  shows "c * a \<le> c * b"
  using assms Im_complex_of_real Re_complex_of_real less_eq_complex_def mult_eq_0_iff real_mult_le_cancel_iff2 times_complex.simps
  using eq_iff by fastforce 

lemma denote_while_n_scale:
  fixes c:: real
  assumes "c\<ge>0"
    "measurement d 2 x1" "well_com x2"
    "(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (c \<cdot>\<^sub>m \<rho>) \<le> 1 \<Longrightarrow> 
      denote x2 (c \<cdot>\<^sub>m \<rho>) =  c \<cdot>\<^sub>m denote x2 \<rho>)"
  shows "\<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (c \<cdot>\<^sub>m \<rho>) \<le> 1 \<Longrightarrow> 
    denote_while_n (x1 0) (x1 1) (denote x2) n (complex_of_real c \<cdot>\<^sub>m \<rho>) = c \<cdot>\<^sub>m (denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>)"
proof (auto, induct n arbitrary: \<rho>)
  case 0
  then show ?case 
    apply auto apply (mat_assoc d) using assms measurement_dim by auto
next
  case (Suc n)
  then show ?case
  proof -
    let ?A = "x1 0" and ?B = "x1 1"
    have dx2:"(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive ((denote x2) \<rho>) \<and> trace ((denote x2) \<rho>) \<le> trace \<rho> \<and> (denote x2) \<rho> \<in> carrier_mat d d) "
      using denote_positive_trace_dim assms by auto
    have lo1: "adjoint ?B * ?B \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat assms by auto
    have dim1: "x1 1 * \<rho> * adjoint (x1 1) \<in> carrier_mat d d" using assms(2) Suc(2) measurement_dim 
      by (meson adjoint_dim mult_carrier_mat one_less_numeral_iff semiring_norm(76))
    moreover have pdo1: "partial_density_operator (x1 1 * \<rho> * adjoint (x1 1))"
      using pdo_close_under_measurement assms  Suc lo1 measurement_dim 
      by (metis One_nat_def lessI numeral_2_eq_2)
    ultimately have dimr: "denote x2 (x1 1 * \<rho> * adjoint (x1 1)) \<in> carrier_mat d d"
      using dx2 by auto
    have pdor: "partial_density_operator (denote x2 (x1 1 * \<rho> * adjoint (x1 1)))"
      using denote_partial_density_operator assms dim1 pdo1 by auto
    have "trace (denote x2 (x1 1 * \<rho> * adjoint (x1 1))) \<le> trace (x1 1 * \<rho> * adjoint (x1 1))"
      using dx2 dim1 pdo1 by auto
    also have trr1: "\<dots> \<le> trace \<rho>" using trace_decrease_mul_adj assms Suc lo1 measurement_dim by auto
    finally have trr: "trace (denote x2 (x1 1 * \<rho> * adjoint (x1 1))) \<le> trace \<rho>" by auto
    moreover have "trace (c \<cdot>\<^sub>m denote x2 (x1 1 * \<rho> * adjoint (x1 1))) = c * trace (denote x2 (x1 1 * \<rho> * adjoint (x1 1)))"
      using trace_smult dimr by auto
    moreover have trcr: "trace (c \<cdot>\<^sub>m \<rho>) = c * trace \<rho>" using trace_smult Suc by auto
    ultimately have "trace (c \<cdot>\<^sub>m denote x2 (x1 1 * \<rho> * adjoint (x1 1))) \<le> trace (c \<cdot>\<^sub>m \<rho>)"
      using assms(1) state_sig.mulfact by auto
    then have trrc: "trace (c \<cdot>\<^sub>m denote x2 (x1 1 * \<rho> * adjoint (x1 1))) \<le>  1" using Suc by auto
    have "trace (c \<cdot>\<^sub>m (x1 1 * \<rho> * adjoint (x1 1))) = c * trace (x1 1 * \<rho> * adjoint (x1 1))"
      using trace_smult dim1 by auto
    then have "trace (c \<cdot>\<^sub>m (x1 1 * \<rho> * adjoint (x1 1))) \<le> trace (c \<cdot>\<^sub>m \<rho>)"  using trcr trr1 assms(1) 
      using state_sig.mulfact by auto
    then have trrle: "trace (c \<cdot>\<^sub>m (x1 1 * \<rho> * adjoint (x1 1))) \<le> 1" using Suc by auto
    have "x1 1 * (complex_of_real c \<cdot>\<^sub>m \<rho>) * adjoint (x1 1) = complex_of_real c \<cdot>\<^sub>m (x1 1 * \<rho> * adjoint (x1 1))"
      apply (mat_assoc d) using Suc.prems(1) assms measurement_dim by auto
    then have "denote x2 (x1 1 * (complex_of_real c \<cdot>\<^sub>m \<rho>) * adjoint (x1 1)) =  (denote x2 (c \<cdot>\<^sub>m (x1 1 * (\<rho>) * adjoint (x1 1))))"
      by auto
    moreover have "denote x2 (c \<cdot>\<^sub>m (x1 1 * \<rho> * adjoint (x1 1))) = c \<cdot>\<^sub>m denote x2 (x1 1 * \<rho> * adjoint (x1 1))"
      using assms(4) dim1 pdo1 trrle by auto
    ultimately have "denote x2 (x1 1 * (complex_of_real c \<cdot>\<^sub>m \<rho>) * adjoint (x1 1)) = c \<cdot>\<^sub>m denote x2 (x1 1 * \<rho> * adjoint (x1 1))"
      using assms by auto
    then show ?thesis using Suc dimr pdor trrc by auto
  qed
qed
  
lemma denote_while_scale:
  fixes c:: real
  assumes "\<rho> \<in> carrier_mat d d"
    "partial_density_operator \<rho>"
    "trace (c \<cdot>\<^sub>m \<rho>) \<le> 1" "c \<ge> 0"
    "measurement d 2 x1" "well_com x2"
    "(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> trace (c \<cdot>\<^sub>m \<rho>) \<le> 1 \<Longrightarrow> 
      denote x2 (c \<cdot>\<^sub>m \<rho>) =  c \<cdot>\<^sub>m denote x2 \<rho>)"
  shows "denote_while (x1 0) (x1 1) (denote x2) (c \<cdot>\<^sub>m \<rho>) = c \<cdot>\<^sub>m denote_while (x1 0) (x1 1) (denote x2) \<rho>"
proof -
  let ?A = "x1 0" and ?B = "x1 1"
  have dx2:"(\<And>\<rho>. \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow> positive ((denote x2) \<rho>) \<and> trace ((denote x2) \<rho>) \<le> trace \<rho> \<and> (denote x2) \<rho> \<in> carrier_mat d d) "
    using denote_positive_trace_dim assms by auto
  have lo1: "adjoint ?A * ?A + adjoint ?B * ?B = 1\<^sub>m d" using measurement_id2 assms by auto
  have ms: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>))"   
    using denote_while_n_sum_mat_seq assms measurement_dim by auto

  have trcless: "trace (c \<cdot>\<^sub>m matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n) \<le> 1" for n
  proof -
    have dimr: "matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n \<in> carrier_mat d d"   
      using assms dx2 denote_while_n_dim matrix_sum_dim 
      using matrix_seq.dim ms by auto 
    have "trace (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>) n) \<le> trace \<rho>"
      using denote_while_n_sum_trace dx2 lo1 assms measurement_dim by auto
    moreover have "trace (c \<cdot>\<^sub>m matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n) = c * trace (matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n)"
      using trace_smult dimr by auto
    moreover have "trace (c \<cdot>\<^sub>m \<rho>) =  c * trace \<rho>"  using trace_smult assms by auto        
    ultimately have "trace (c \<cdot>\<^sub>m matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>) n) \<le> trace (c \<cdot>\<^sub>m \<rho>)"
      using  assms(4) by (simp add: ordered_comm_semiring_class.comm_mult_left_mono)
    then show ?thesis
      using assms by auto
  qed

  have llscale: "matrix_seq.lowner_lub  (\<lambda>n. c \<cdot>\<^sub>m (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>)) n) 
    = c \<cdot>\<^sub>m matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>))"
    using lowner_lub_scale[of d "(matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>))" c] ms trcless assms(4) by auto
  have "matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (complex_of_real c \<cdot>\<^sub>m \<rho>)) m 
    = c \<cdot>\<^sub>m (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>)) m"
    for m
  proof -
    have  dim:"(\<And>k. k < m \<Longrightarrow> denote_while_n (x1 0) (x1 1) (denote x2) k \<rho> \<in> carrier_mat d d)" 
      using denote_while_n_dim dx2  assms measurement_dim by auto
    then have dimr: "(\<And>k. k < m \<Longrightarrow> c \<cdot>\<^sub>m denote_while_n (x1 0) (x1 1) (denote x2) k \<rho> \<in> carrier_mat d d)"
      using smult_carrier_mat by auto
    have "\<forall> n<m. denote_while_n (x1 0) (x1 1) (denote x2) n (complex_of_real c \<cdot>\<^sub>m \<rho>) = c \<cdot>\<^sub>m (denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>)"
      using denote_while_n_scale assms by auto
    then have "(matrix_sum d (\<lambda>n. c \<cdot>\<^sub>m denote_while_n ?A ?B (denote x2) n \<rho>)) m = 
      matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (complex_of_real c \<cdot>\<^sub>m \<rho>)) m "
      using matrix_sum_cong[of m "\<lambda>n. complex_of_real c \<cdot>\<^sub>m denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>"] dimr 
      by fastforce
    moreover have "(matrix_sum d (\<lambda>n. c \<cdot>\<^sub>m denote_while_n ?A ?B (denote x2) n \<rho>)) m = c \<cdot>\<^sub>m (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>)) m"
      using matrix_sum_smult[of m "(\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n \<rho>)" d c] dim by auto
    ultimately show ?thesis by auto
  qed
  then have "matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n (x1 0) (x1 1) (denote x2) n (complex_of_real c \<cdot>\<^sub>m \<rho>))) =
    matrix_seq.lowner_lub (\<lambda>n. c \<cdot>\<^sub>m (matrix_sum d (\<lambda>n. denote_while_n ?A ?B (denote x2) n \<rho>)) n)"
    by meson
  then show ?thesis
    unfolding denote_while_def matrix_inf_sum_def using llscale by auto
qed
 
lemma denote_scale:
  fixes c :: real
  assumes "c\<ge>0"
  shows "well_com S \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> \<Longrightarrow>
         trace (c  \<cdot>\<^sub>m \<rho>) \<le> 1 \<Longrightarrow> denote S (c  \<cdot>\<^sub>m \<rho>) = c  \<cdot>\<^sub>m denote S \<rho>"
proof (induction arbitrary: \<rho>)
  case SKIP
  then show ?case by auto
next
  case (Utrans x)
  then show ?case
    unfolding denote.simps apply (mat_assoc d) using Utrans by auto
next
  case (Seq x1 x2a)
  then show ?case
  proof -
    have cd: "denote x1 (c \<cdot>\<^sub>m \<rho>) = c \<cdot>\<^sub>m denote x1 \<rho>" using Seq by auto
    have x1: "denote x1 \<rho> \<in> carrier_mat d d \<and> partial_density_operator (denote x1 \<rho>) \<and> trace (denote x1 \<rho>) \<le> trace \<rho>" 
      using denote_positive_trace_dim Seq denote_partial_density_operator by auto
    have "trace (c \<cdot>\<^sub>m denote x1 \<rho>) = c * trace (denote x1 \<rho>)" using trace_smult x1 by auto
    also have "\<dots> \<le> c * trace \<rho>" using x1 assms 
      by (metis Seq.prems cd denote_positive_trace_dim partial_density_operator_def positive_scale smult_carrier_mat trace_smult well_com.simps(3))
    also have "\<dots> \<le> 1" using Seq(6) trace_smult Seq(4) 
      by (simp add: trace_smult)
    finally have "trace (c \<cdot>\<^sub>m denote x1 \<rho>) \<le>1" by auto
    then have "denote x2a (c \<cdot>\<^sub>m denote x1 \<rho>) = c \<cdot>\<^sub>m denote x2a ( denote x1 \<rho>)" using x1 Seq by auto
    then show ?thesis using denote.simps(4) cd by auto
  qed
next
  case (Measure x1 x2a x3a)
  then show ?case
  proof -
    have ptc: "\<And>x3aa \<rho>. x3aa \<in> set x3a \<Longrightarrow> well_com x3aa \<Longrightarrow> \<rho> \<in> carrier_mat d d \<Longrightarrow> partial_density_operator \<rho> 
      \<Longrightarrow> positive (denote x3aa \<rho>) \<and> trace (denote x3aa \<rho>) \<le> trace \<rho> \<and> denote x3aa \<rho> \<in> carrier_mat d d"
      using denote_positive_trace_dim Measure by auto
    have cad: "x2a k * (c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k) = c \<cdot>\<^sub>m (x2a k * \<rho> * adjoint (x2a k))"
      if k: "k < x1" for k
      apply (mat_assoc d) using well_com.simps Measure measurement_dim k by auto
    have "\<forall>k<x1. x2a k * \<rho> * adjoint (x2a k) \<in> carrier_mat d d"
      using Measure(2) measurement_dim Measure(3) by fastforce
    have lea: "\<forall>k<x1. adjoint (x2a k) * x2a k \<le>\<^sub>L 1\<^sub>m d" using measurement_le_one_mat Measure(2) by auto
    then have pdox: "\<forall> k<x1. partial_density_operator (x2a k * \<rho> * adjoint (x2a k))"
      using pdo_close_under_measurement Measure(2,3,4) measurement_dim  
      by (meson state_sig.well_com.simps(4))
    have x2aa:"\<forall> k < x1. (x2a k * \<rho> * adjoint (x2a k)) \<in> carrier_mat d d" using Measure(2,3) measurement_dim by fastforce
    have dimm: "(\<And>k. k < x1 \<Longrightarrow> (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k)) \<in> carrier_mat d d)"
      using map_denote_positive_trace_dim Measure(2,3,4) ptc by auto
    then have dimcm: "(\<And>k. k < x1 \<Longrightarrow> c \<cdot>\<^sub>m (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k)) \<in> carrier_mat d d)"
      using smult_carrier_mat by auto
    
    have tra: "\<forall> k < x1. trace ((x2a k * \<rho> * adjoint (x2a k))) \<le> trace \<rho>"
      using trace_decrease_mul_adj Measure lea measurement_dim by auto

    have tra1: "trace (c \<cdot>\<^sub>m (x2a k * \<rho> * adjoint (x2a k))) \<le> 1" if k: "k < x1" for k
    proof -
      have trle: "trace (x2a k * \<rho> * adjoint (x2a k)) \<le> trace \<rho>" using tra k by auto
      have "trace (c \<cdot>\<^sub>m (x2a k * \<rho> * adjoint (x2a k))) = c * trace ((x2a k * \<rho> * adjoint (x2a k)))"
        using trace_smult x2aa k by auto
      also have "\<dots> \<le> c * trace \<rho>" 
        using trle assms mulfact  by auto
      also have "\<dots> \<le> 1" using Measure(3,5) trace_smult  by metis
      finally show ?thesis by auto
    qed

    have "(map denote x3a ! k) (x2a k * (c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k)) 
        = c \<cdot>\<^sub>m (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))" if k: "k < x1" for k
    proof -
      have "denote (x3a ! k) (x2a k * (c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k)) = denote (x3a ! k) (c \<cdot>\<^sub>m (x2a k * \<rho> * adjoint (x2a k)))"
        using cad k by auto
      also have "\<dots> = c \<cdot>\<^sub>m denote (x3a ! k) ( (x2a k * \<rho> * adjoint (x2a k)))"
        using Measure(1,2) pdox x2aa tra1 k using measure_well_com by auto
      finally have "denote (x3a ! k) (x2a k * (complex_of_real c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k)) = complex_of_real c \<cdot>\<^sub>m denote (x3a ! k) (x2a k * \<rho> * adjoint (x2a k))"
        by auto
      then show ?thesis using Measure.prems(1) k by auto
    qed

    then have "matrix_sum d (\<lambda>k. c \<cdot>\<^sub>m (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))) x1 =
      matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * (c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k))) x1"
      using matrix_sum_cong[of x1 "(\<lambda>k. complex_of_real c \<cdot>\<^sub>m (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k)))" 
        "(\<lambda>k. (map denote x3a ! k) (x2a k * (complex_of_real c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k)))"] dimcm by auto
    then have "matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * (c \<cdot>\<^sub>m \<rho>) * adjoint (x2a k))) x1 =
       c \<cdot>\<^sub>m matrix_sum d (\<lambda>k. (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k))) x1"
      using matrix_sum_smult[of x1 "(\<lambda>k. (map denote x3a ! k) (x2a k * \<rho> * adjoint (x2a k)))" d c] dimm by auto
    then have "denote (Measure x1 x2a x3a) (c \<cdot>\<^sub>m \<rho>) = c \<cdot>\<^sub>m denote (Measure x1 x2a x3a) \<rho>"
    using denote.simps(4)[of x1 x2a x3a "c \<cdot>\<^sub>m \<rho>"] 
    using denote.simps(4)[of x1 x2a x3a "\<rho>"] unfolding denote_measure_def by auto
  then show ?thesis by auto
qed     
next
  case (While x1 x2a)
  then show ?case
    apply auto
    using denote_while_scale assms by auto
qed

lemma limit_mat_denote_while_n:
  assumes wc: "well_com (While M S)" and dr: "\<rho> \<in> carrier_mat d d" and pdor: "partial_density_operator \<rho>"
  shows "limit_mat (matrix_sum d (\<lambda>k. denote_while_n (M 0) (M 1) (denote S) k \<rho>)) (denote (While M S) \<rho>) d"
proof -
  have m: "measurement d 2 M" using wc by auto
  then have dM0: "M 0 \<in> carrier_mat d d" and dM1: "M 1 \<in> carrier_mat d d" and id: "adjoint (M 0) * (M 0) + adjoint (M 1) * (M 1) = 1\<^sub>m d" 
    using measurement_id2 m measurement_def by auto
  have wcs: "well_com S" using wc by auto
  have DS: "positive (denote S \<rho>) \<and> trace (denote S \<rho>) \<le> trace \<rho> \<and> denote S \<rho> \<in> carrier_mat d d" 
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using wcs that denote_positive_trace_dim by auto

  have sumdd: "(\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>) n \<in> carrier_mat d d)" 
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using denote_while_n_sum_dim dM0 dM1 DS that by auto
  have sumtr: "\<forall> n. trace (matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>) n) \<le> trace \<rho>"
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using denote_while_n_sum_trace[OF dM0 dM1 id DS] that by auto
  have sumpar: "(\<forall>n. partial_density_operator (matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>) n))"
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using denote_while_n_sum_partial_density[OF dM0 dM1 id DS] that by auto
  have sumle:"(\<forall>n. matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>) n \<le>\<^sub>L matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>) (Suc n))"
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using denote_while_n_sum_lowner_le[OF dM0 dM1 id DS] that by auto
  have seqd: "matrix_seq d (matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>))"
    if "\<rho> \<in> carrier_mat d d" and "partial_density_operator \<rho>" for \<rho>
    using matrix_seq_def sumdd sumpar sumle that by auto

  have "matrix_seq.lowner_is_lub (matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>))
    (matrix_seq.lowner_lub (matrix_sum d (\<lambda>n. denote_while_n (M 0) (M 1) (denote S) n \<rho>)))"
    using DS lowner_is_lub_matrix_sum dM0 dM1 id pdor dr by auto
  then show "limit_mat (matrix_sum d (\<lambda>k. denote_while_n (M 0) (M 1) (denote S) k \<rho>)) (denote (While M S) \<rho>) d"
    unfolding denote.simps denote_while_def matrix_inf_sum_def using matrix_seq.lowner_lub_is_limit[OF seqd[OF dr pdor]]  by auto
qed

end

end
