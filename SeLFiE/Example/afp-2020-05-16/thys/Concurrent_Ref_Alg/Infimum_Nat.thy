section \<open>Infimum nat lemmas \label{S:infimum-nat}\<close>

theory Infimum_Nat
imports 
  Refinement_Lattice
begin

locale infimum_nat
begin

lemma INF_partition_nat3: 
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Sqinter>j. f i j) =
    (\<Sqinter>j\<in>{j. i = j}. f i j) \<sqinter>
    (\<Sqinter>j\<in>{j. i < j}. f i j) \<sqinter>
    (\<Sqinter>j\<in>{j. j < i}. f i j)"
proof -
  have univ_part: "UNIV = {j. i = j} \<union> {j. i < j} \<union> {j. j < i}" by auto
  have "(\<Sqinter>j \<in> {j. i = j} \<union> {j. i < j} \<union> {j. j < i}. f i j) =
          (\<Sqinter>j\<in>{j. i = j}. f i j) \<sqinter>
          (\<Sqinter>j\<in>{j. i < j}. f i j) \<sqinter>
          (\<Sqinter>j\<in>{j. j < i}. f i j)" by (metis INF_union)
  with univ_part show ?thesis by simp
qed

lemma INF_INF_partition_nat3: 
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Sqinter>i. \<Sqinter>j. f i j) =
    (\<Sqinter>i. \<Sqinter>j\<in>{j. i = j}. f i j) \<sqinter>
    (\<Sqinter>i. \<Sqinter>j\<in>{j. i < j}. f i j) \<sqinter>
    (\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f i j)"
proof -
  have "(\<Sqinter>i. \<Sqinter>j. f i j) = (\<Sqinter>i. ((\<Sqinter>j\<in>{j. i = j}. f i j) \<sqinter>
                                  (\<Sqinter>j\<in>{j. i < j}. f i j) \<sqinter>
                                  (\<Sqinter>j\<in>{j. j < i}. f i j)))"
    by (simp add: INF_partition_nat3)
  also have "... = (\<Sqinter>i. \<Sqinter>j\<in>{j. i = j}. f i j) \<sqinter>
                   (\<Sqinter>i. \<Sqinter>j\<in>{j. i < j}. f i j) \<sqinter>
                   (\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f i j)"
    by (simp add: INF_inf_distrib)
  finally show ?thesis .
qed

lemma INF_nat_shift: "(\<Sqinter>i\<in>{i. 0 < i}. f i) = (\<Sqinter>i. f (Suc i))"
  by (metis greaterThan_0 greaterThan_def range_composition)

lemma INF_nat_minus:
  fixes f :: "nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Sqinter>j\<in>{j. i < j}. f (j - i)) = (\<Sqinter>k\<in>{k. 0 < k}. f k)"
  apply (rule antisym)
  apply (rule INF_mono, simp)
  apply (metis add.right_neutral add_diff_cancel_left' add_less_cancel_left order_refl)
  apply (rule INF_mono, simp)
  by (meson order_refl zero_less_diff)

(* TODO: generalise to P j i? *)
lemma INF_INF_guarded_switch:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> 'a::refinement_lattice"
  shows "(\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j)) = (\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j))"
proof (rule antisym)
  have "\<And>jj ii. jj < ii \<Longrightarrow> \<exists>i. \<exists>j<i. f j (i - j) \<sqsubseteq> f jj (ii - jj)"
    by blast
  then have "\<And>jj ii. jj < ii \<Longrightarrow> \<exists>i. (\<Sqinter>j\<in>{j. j < i}. f j (i - j)) \<sqsubseteq> f jj (ii - jj)"
    by (meson INF_lower mem_Collect_eq)
  then have "\<And>jj ii. jj < ii \<Longrightarrow> (\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j)) \<sqsubseteq> f jj (ii - jj)"
    by (meson UNIV_I INF_lower dual_order.trans)
  then have "\<And>jj. (\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>ii\<in>{ii. jj < ii}. f jj (ii - jj))"
    by (metis (mono_tags, lifting) INF_greatest mem_Collect_eq)
  then have "(\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>jj. \<Sqinter>ii\<in>{ii. jj < ii}. f jj (ii - jj))"
    by (simp add: INF_greatest)
  then show "(\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j))"
    by simp
next
  have "\<And>ii jj. jj < ii \<Longrightarrow> \<exists>j. \<exists>i>j. f j (i - j) \<sqsubseteq> f jj (ii - jj)"
    by blast
  then have "\<And>ii jj. jj < ii \<Longrightarrow> \<exists>j. (\<Sqinter>i\<in>{i. j < i}. f j (i - j)) \<sqsubseteq> f jj (ii - jj)"
    by (meson INF_lower mem_Collect_eq)
  then have "\<And>ii jj. jj < ii \<Longrightarrow> (\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j)) \<sqsubseteq> f jj (ii - jj)"
    by (meson UNIV_I INF_lower dual_order.trans)
  then have "\<And>ii. (\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>jj\<in>{jj. jj < ii}. f jj (ii - jj))"
    by (metis (mono_tags, lifting) INF_greatest mem_Collect_eq)
  then have "(\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>ii. \<Sqinter>jj\<in>{jj. jj < ii}. f jj (ii - jj))"
    by (simp add: INF_greatest)
  then show "(\<Sqinter>j. \<Sqinter>i\<in>{i. j < i}. f j (i - j)) \<sqsubseteq> (\<Sqinter>i. \<Sqinter>j\<in>{j. j < i}. f j (i - j))"
    by simp
qed

end

end
