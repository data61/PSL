(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Tensor CP-Rank\<close>

theory Tensor_Rank
imports Tensor_Unit_Vec
begin

inductive cprank_max1::"'a::ring_1 tensor \<Rightarrow> bool" where
order1: "order A \<le> 1 \<Longrightarrow> cprank_max1 A" |
higher_order: "order A = 1 \<Longrightarrow> cprank_max1 B \<Longrightarrow> cprank_max1 (A \<otimes> B)"

lemma cprank_max1_order0: "cprank_max1 B \<Longrightarrow> order A = 0 \<Longrightarrow> cprank_max1 (A \<otimes> B)"
proof (induction B rule:cprank_max1.induct)
  case order1
  then show ?case by (simp add: cprank_max1.order1)
next
  case (higher_order A' B)
  then have "order (A \<otimes> A') = 1" by simp
  then show ?case using higher_order cprank_max1.higher_order by (metis mult.assoc)
qed

lemma cprank_max1_order_le1: "order A \<le> 0 \<Longrightarrow> cprank_max1 B \<Longrightarrow> cprank_max1 (A \<otimes> B)"
by (simp add: cprank_max1_order0)

lemma cprank_max1_prod: "cprank_max1 A \<Longrightarrow> cprank_max1 B \<Longrightarrow> cprank_max1 (A \<otimes> B)"
  apply(induction A rule: cprank_max1.induct)
 apply (meson higher_order le_neq_trans less_one cprank_max1_order0)
by (simp add: higher_order mult.assoc)

lemma cprank_max1_prod_list:
assumes "\<And>B. B\<in>set Bs \<Longrightarrow> cprank_max1 B"
shows "cprank_max1 (prod_list Bs)"
  using assms by (induction Bs, metis dims_smult dims_tensor0 list.size(3) prod_list.Nil order1 order_0_multiple_of_one zero_le_one, simp add: cprank_max1_prod)

lemma cprank_max1_prod_listE:
  fixes A::"'a::comm_ring_1 tensor"
  assumes "cprank_max1 A"
  obtains Bs a where "\<And>B. B\<in>set Bs \<Longrightarrow> order B = 1" "a \<cdot> prod_list Bs = A"
using assms proof (induction A arbitrary:thesis rule:cprank_max1.induct)
  case (order1 A)
  then show ?case
  proof (cases "order A = 0")
    case True
    then obtain a where "A = a \<cdot> prod_list []" using order_0_multiple_of_one using prod_list.Nil by auto
    then show ?thesis using length_pos_if_in_set order1.prems by fastforce
  next
    case False
    then have "order A = 1" using order1 by linarith
    then have "A = 1 \<cdot> prod_list [A]" by (simp add: smult_1)
    then show ?thesis by (metis \<open>order A = 1\<close> length_greater_0_conv length_pos_if_in_set order1.prems set_ConsD)
  qed
next
  case (higher_order A B)
  then obtain Bs b where "(\<And>B'. B' \<in> set Bs \<Longrightarrow> order B' = 1)" "b \<cdot> prod_list Bs = B" by metis
  then have "(\<And>B. B \<in> set (A # Bs) \<Longrightarrow> order B = 1)" using higher_order by auto
  have "A \<otimes> B = b \<cdot> (A \<otimes> prod_list Bs)" using smult_prod_extract2  `b \<cdot> prod_list Bs = B` by metis
  then show ?case by (metis \<open>\<And>Ba. Ba \<in> set (A # Bs) \<Longrightarrow> order Ba = 1\<close> higher_order.prems prod_list.Cons)
qed

inductive cprank_max :: "nat \<Rightarrow> 'a::ring_1 tensor \<Rightarrow> bool" where
cprank_max0: "cprank_max 0 (tensor0 ds)" |
cprank_max_Suc: "dims A = dims B \<Longrightarrow> cprank_max1 A \<Longrightarrow> cprank_max j B \<Longrightarrow> cprank_max (Suc j) (A+B)"

lemma cprank_max1: "cprank_max1 A \<Longrightarrow> cprank_max 1 A"
  by (metis One_nat_def dims_tensor0 cprank_max.simps cprank_max0 tensor_add_0_right)

lemma cprank_max_plus: "cprank_max i A \<Longrightarrow> cprank_max j B \<Longrightarrow> dims A = dims B \<Longrightarrow> cprank_max (i+j) (A+B)"
apply (induction A rule:cprank_max.induct)
 apply auto[1]
by (metis add_Suc plus_assoc plus_dim1 cprank_max.intros(2))

lemma cprank_max_listsum:
assumes "\<And>A. A\<in>set As \<Longrightarrow> dims A = ds"
and "\<And>A. A\<in>set As \<Longrightarrow> cprank_max n A"
shows "cprank_max (n*length As) (listsum ds As)"
using assms proof (induction As)
  case Nil
  then show ?case using listsum_Nil cprank_max.simps by fastforce
next
  case (Cons A As)
  then show ?case using cprank_max_plus[of n A "n * length As" "listsum ds As"]
    by (simp add: length_Cons list.set_intros(1) listsum_Cons listsum_dims set_subset_Cons subsetCE)
qed

lemma cprank_maxE:
assumes "cprank_max n A"
obtains BS where "(\<And>B. B\<in>set BS \<Longrightarrow> cprank_max1 B)" and "(\<And>B. B\<in>set BS \<Longrightarrow> dims A = dims B)" and "listsum (dims A) BS = A" and "length BS = n"
using assms proof (induction arbitrary:thesis rule:cprank_max.induct)
  case (cprank_max0 ds)
  have "Tensor_Plus.listsum (dims (tensor0 ds)) [] = tensor0 ds" by (simp add: listsum_Nil)
  then show ?case using cprank_max0.prems by fastforce
next
  case (cprank_max_Suc A B j)
  then obtain BS where BS_def:"(\<And>B. B \<in> set BS \<Longrightarrow> cprank_max1 B)" "(\<And>B'. B' \<in> set BS \<Longrightarrow> dims B' = dims B)"
                       "listsum (dims B) BS = B" "length BS = j" by metis
  then have "listsum (dims (A + B)) (A # BS) = A + B"
    by (simp add: listsum_Cons cprank_max_Suc.hyps(1))
  then show ?case using BS_def length_Cons cprank_max_Suc.hyps(2) cprank_max_Suc.prems set_ConsD
    by (metis plus_dim1 cprank_max_Suc.hyps(1))
qed

lemma cprank_maxI:
assumes "\<And>B. B\<in>set BS \<Longrightarrow> cprank_max1 B"
and "\<And>B. B\<in>set BS \<Longrightarrow> dims B = ds"
shows "cprank_max (length BS) (listsum ds BS)"
using assms proof (induction BS)
  case Nil
  then show ?case by (simp add: listsum_Nil cprank_max0)
next
  case (Cons B BS)
  then show ?case
    by (simp add: length_Cons list.set_intros(1) list.set_intros(2) listsum_Cons listsum_dims cprank_max_Suc)
qed

lemma cprank_max_0E: "cprank_max 0 A \<Longrightarrow> A = tensor0 (dims A)" by (metis dims_tensor0 length_0_conv cprank_max0 cprank_maxE)

lemma listsum_prod_distr_right:
assumes "(\<And>C. C\<in>set CS \<Longrightarrow> dims C = ds)"
shows "A \<otimes> listsum ds CS = listsum (dims A @ ds) (map (\<lambda>C. A \<otimes> C) CS)"
using assms proof (induction CS)
  case Nil
  then show ?case by (simp add:listsum_Nil)
next
  case (Cons C CS)
  then have "dims C = dims (listsum ds CS)" by (simp add: list.set_intros(1) list.set_intros(2) listsum_dims)
  then show ?case unfolding listsum_Cons list.map(2)
    using tensor_prod_distr_right Cons.IH Cons.prems list.set_intros(2) by fastforce
qed

lemma cprank_max_prod_order1:
assumes "order A = 1"
and "cprank_max n B"
shows "cprank_max n (A\<otimes>B)"
proof -
  obtain CS where "(\<And>C. C\<in>set CS \<Longrightarrow> cprank_max1 C)"
              and "(\<And>C. C\<in>set CS \<Longrightarrow> dims C = dims B)"
              and "listsum (dims B) CS = B"
              and "length CS = n"
    using assms(2) cprank_maxE by metis
  define CS' where "CS' = map (\<lambda>C. A\<otimes>C) CS"
  then have "\<And>C'. C'\<in>set CS' \<Longrightarrow> cprank_max1 C'"
    using assms(1) higher_order \<open>\<And>C. C \<in> set CS \<Longrightarrow> cprank_max1 C\<close> imageE set_map by auto
  have "listsum (dims A @ dims B) CS' = A\<otimes>B" using CS'_def \<open>Tensor_Plus.listsum (dims B) CS = B\<close>
    using \<open>\<And>Ca. Ca \<in> set CS \<Longrightarrow> dims Ca = dims B\<close> listsum_prod_distr_right by fastforce
  then show ?thesis by (metis (mono_tags, lifting) CS'_def \<open>\<And>C'. C' \<in> set CS' \<Longrightarrow> cprank_max1 C'\<close> \<open>\<And>Ca. Ca \<in> set CS \<Longrightarrow> dims Ca = dims B\<close> \<open>length CS = n\<close> dims_tensor_prod imageE length_map cprank_maxI set_map)
qed

lemma cprank_max_upper_bound: (* Stronger bound is possible, one of the factors in prod_list can be dropped. *)
shows "cprank_max (prod_list (dims A)) A"
proof (induction A rule:subtensor_induct)
  case (order_0 A)
  then have "cprank_max 1 A" using order1 cprank_max1 by force
  then show ?case using order_0 by auto
next
  case (order_step A)
  define Bs where "Bs = map (\<lambda>i. unit_vec (hd (dims A)) i \<otimes> subtensor A i) [0..<hd (dims A)]"
  have "\<And>B. B \<in> set Bs \<Longrightarrow> dims A = dims B"
  proof -
    fix B assume "B \<in> set Bs"
    obtain i where "i<hd (dims A)" "Bs!i=B" using Bs_def \<open>B \<in> set Bs\<close> by auto
    then have "dims (unit_vec (hd (dims A)) i \<otimes> subtensor A i) = dims A"
      using dims_unit_vec order_step.hyps
      by (metis append_Cons dims_subtensor dims_tensor_prod list.exhaust_sel self_append_conv2)
    then show "dims A = dims B" using Bs_def \<open>Bs ! i = B\<close> \<open>i < hd (dims A)\<close> by auto
  qed
  have "\<And>B. B \<in> set Bs \<Longrightarrow> cprank_max (prod_list (tl (dims A))) B"
  proof -
    fix B assume "B \<in> set Bs"
    obtain i where "i<hd (dims A)" "Bs!i=B" using Bs_def \<open>B \<in> set Bs\<close> by auto
    then have "cprank_max (prod_list (tl (dims A))) (unit_vec (hd (dims A)) i \<otimes> subtensor A i)"
      by (metis One_nat_def dims_subtensor dims_unit_vec length_Cons list.size(3) order_step.IH order_step.hyps cprank_max_prod_order1)
    then show "cprank_max (prod_list (tl (dims A))) B" using Bs_def \<open>Bs ! i = B\<close> \<open>i < hd (dims A)\<close> by auto
  qed
  then show ?case using subtensor_decomposition[OF order_step.hyps] cprank_max_listsum
    by (metis (no_types, lifting) Bs_def \<open>\<And>Ba. Ba \<in> set Bs \<Longrightarrow> dims A = dims Ba\<close> diff_zero length_map length_upt list.exhaust_sel prod_list.Cons mult.commute order_step.hyps)
qed

definition cprank :: "'a::ring_1 tensor \<Rightarrow> nat" where
"cprank A = (LEAST n. cprank_max n A)"

lemma cprank_upper_bound: "cprank A \<le> prod_list (dims A)"
unfolding cprank_def using cprank_max_upper_bound Least_le by fastforce

lemma cprank_max_cprank: "cprank_max (cprank A) A"
  unfolding cprank_def using cprank_max_upper_bound by (metis LeastI)

end
