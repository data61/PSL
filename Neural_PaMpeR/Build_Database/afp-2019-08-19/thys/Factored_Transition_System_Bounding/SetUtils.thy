theory SetUtils
  imports Main
begin

\<comment> \<open>TODO use Inf instead of Min where necessary.\<close>

\<comment> \<open>TODO can be replaced by @{term "card_Un_disjoint (\<lbrakk>finite A; finite B; A \<inter> B = {}\<rbrakk> 
  \<Longrightarrow> card (A \<union> B) = card A + card B)"} ?\<close>
lemma card_union': "(finite s) \<and> (finite t) \<and> (disjnt s t) \<Longrightarrow> (card (s \<union> t) = card s + card t)"
  by (simp add: card_Un_disjoint disjnt_def)

lemma CARD_INJ_IMAGE_2: 
  fixes f s
  assumes "finite s" "(\<forall>x y. ((x \<in> s) \<and> (y \<in> s)) \<longrightarrow> ((f x = f y) \<longleftrightarrow> (x = y)))"
  shows "(card (f ` s) = card s)"
proof -
  {
    fix x y
    assume "x \<in> s" "y \<in> s" 
    then have "f x = f y \<longrightarrow> x = y"
      using assms(2)
      by blast
  }
  then have "inj_on f s"
    by (simp add: inj_onI)
  then show ?thesis
    using assms(1) inj_on_iff_eq_card
    by blast
qed

lemma scc_main_lemma_x: "\<And>s t x. (x \<in> s) \<and> \<not>(x \<in> t) \<Longrightarrow> \<not>(s = t)"
  by blast

lemma neq_funs_neq_images:
  fixes s 
  assumes "\<forall>x. x \<in> s \<longrightarrow> (\<forall>y. y \<in> s \<longrightarrow> f1 x \<noteq> f2 y)" "\<exists>x. x \<in> s" 
  shows "f1 ` s \<noteq> f2 ` s"
  using assms 
  by blast 

subsection "Sets of Numbers"

\<comment> \<open>TODO 
  Is '<=' natural number lte or overloaded? 
  If it's overloaded for reals, this might be wrong (e.g. the real set s = [0; 1] is not finite even 
though @{term "\<forall> x \<in> s. x \<le> 1"} holds).\<close>
lemma mems_le_finite_i: 
  fixes s :: "nat set" and k :: nat
  shows "(\<forall> x. x \<in> s \<longrightarrow> x \<le> k) \<Longrightarrow> finite s"
proof -
  assume P: "(\<forall> x. x \<in> s \<longrightarrow> x \<le> k)"
  let ?f = "id :: nat \<Rightarrow> nat"
  let ?S = "{i. i \<le> k}"
  have "s \<subseteq> ?S" using P by blast
  moreover have "?f ` ?S = ?S" by auto
  moreover have "finite ?S" using nat_seg_image_imp_finite by auto
  moreover have "finite s" using calculation finite_subset by auto
  ultimately show ?thesis by auto
qed
lemma mems_le_finite: 
  fixes s :: "nat set" and k :: nat
  shows "\<And>(s :: nat set) k. (\<forall> x. x \<in> s \<longrightarrow> x \<le> k) \<Longrightarrow> finite s"  
  using mems_le_finite_i by auto

\<comment> \<open>NOTE translated `s` to `nat set` (more generality wasn't required.).\<close> 
lemma mem_le_imp_MIN_le: 
  fixes s :: "nat set" and k :: nat 
  assumes "\<exists>x. (x \<in> s) \<and> (x \<le> k)" 
  shows "(Inf s \<le> k)" 
proof -
  from assms obtain x where 1: "x \<in> s" "x \<le> k"
    by blast
  {
    assume C: "Inf s > k"
    then have "Inf s > x" using 1(2)
      by fastforce
    then have False 
      using 1(1) cInf_lower leD
      by fast
  }
  then show ?thesis
    by fastforce
qed

\<comment> \<open>NOTE 
  nat --> bool is the type of a HOL4 set and was translated to 'nat set'.\<close>
\<comment> \<open>NOTE 
  We cannot use 'Min' instead of 'Inf' because there is no indication that '{n. s n}' will be
finite. Without that @{term "Min {n. s n} \<in> {n. s n}"} is not necessarily true.\<close>
lemma mem_lt_imp_MIN_lt: 
  fixes s :: "nat set" and k :: nat
  assumes "(\<exists>x. x \<in> s \<and> x < k)"
  shows "(Inf s) < k" 
proof -
  obtain x where 1: "x \<in> s" "x < k"
    using assms
    by blast
  then have 2: "s \<noteq> {}" 
    by blast
  then have "Inf s \<in> s" 
    using Inf_nat_def LeastI
    by force
  moreover have "\<forall>x\<in>s. Inf s \<le> x"
    by (simp add: cInf_lower)
  ultimately show "(Inf s) < k"
    using assms leD 
    by force
qed

\<comment> \<open>NOTE type for 'k' had to be fixed (type unordered error; also not true for e.g. real sets).\<close>
lemma bound_child_parent_neq_mems_state_set_neq_len: 
  fixes s and k :: nat
  assumes "(\<forall>x. x \<in> s \<longrightarrow> x < k)"
  shows "finite s"
  using assms bounded_nat_set_is_finite 
  by blast 

lemma bound_main_lemma_2: "\<And>(s :: nat set) k. (s \<noteq> {}) \<and> (\<forall>x. x \<in> s \<longrightarrow> x \<le> k) \<Longrightarrow> Sup s \<le> k"
proof -
  fix s :: "nat set" and k
  {
    assume P1: "s \<noteq> {}"
    assume P2: "(\<forall>x. x \<in> s \<longrightarrow> x \<le> k)"
    have "finite s" using P2 mems_le_finite by auto
    moreover have "Max s \<in> s" using P1 calculation Max_in by auto
    moreover have "Max s \<le> k" using P2 calculation by auto 
  }
  then show "(s \<noteq> {}) \<and> (\<forall>x. x \<in> s \<longrightarrow> x \<le> k) \<Longrightarrow> Sup s \<le> k"
    by (simp add: Sup_nat_def)
qed

\<comment> \<open>NOTE type of 'k' fixed to nat to be able to use 'bound\_child\_parent\_neq\_mems\_state\_set\_neq\_len'.\<close>
lemma bound_child_parent_not_eq_last_diff_paths: "\<And>s (k :: nat).
  (s \<noteq> {}) 
  \<Longrightarrow> (\<forall>x. x \<in> s \<longrightarrow> x < k) 
  \<Longrightarrow> Sup s < k
"
  by (simp add: Sup_nat_def bound_child_parent_neq_mems_state_set_neq_len)

lemma FINITE_ALL_DISTINCT_LISTS_i:
  fixes P
  assumes "finite P"
  shows "
    {p. distinct p \<and> set p \<subseteq> P} 
    = {[]} \<union> (\<Union> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) ` P))"
proof -
  let ?A="{p. distinct p \<and> set p \<subseteq> P }"
  let ?B="{[]} \<union> (\<Union> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) ` P))"
  {
    {
      fix a
      assume P: "a \<in> ?A"
      then have "a \<in> ?B" 
      proof (cases a)
        text \<open> The empty list is distinct and its corresponding set is the empty set which is a 
            trivial subset of `?B`. The `Nil` case can therefore be derived by automation. \<close>
        case (Cons h list)
        {
          let ?b'="h"
          {
            from P have "set a \<subseteq> P"
              by simp
            then have "set list \<subseteq> (P - {h})"
              using P dual_order.trans local.Cons 
              by auto
          }
          moreover from P Cons 
          have "distinct list"
            by force
          ultimately have "a \<in> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) ?b')"
            using Cons
            by blast
          moreover {
            from P Cons have "?b' \<in> set a"
              by simp
            moreover from P have "set a \<subseteq> P"
              by simp
            ultimately have "?b' \<in> P" 
              by auto
          }
          ultimately have 
            "\<exists>b' \<in> P. a \<in> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) b')"
            by meson 
        }
        then obtain b' where
          "b' \<in> P" "a \<in> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) b')"
          by blast
        then show ?thesis 
          by blast
      qed blast
    }
    then have "?A \<subseteq> ?B"
      by auto
  }
  moreover {
    {
      fix b
      assume P: "b \<in> ?B"
      have "b \<in> ?A" 
        text \<open> The empty list is in `?B` by construction. The `Nil` case can therefore be derived  
          straightforwardly.\<close>
      proof (cases b)
        case (Cons a list)
        from P Cons obtain b' where a: 
          "b' \<in> P" "b \<in> {b' # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {b'})}"
          by fast
        then obtain p0 where b: "b = b' # p0" "distinct p0" "set p0 \<subseteq> (P - {b'})"
          by blast
        then have "distinct (b' # p0)"
          by (simp add: subset_Diff_insert)
        moreover have "set (b' # p0) \<subseteq> P"
          using a(1) b(3)
          by auto
        ultimately show ?thesis 
          using b(1)
          by fast
      qed simp
    }
    then have "?B \<subseteq> ?A"
      by blast
  }
  ultimately show ?thesis
    using set_eq_subset 
    by blast
qed

lemma FINITE_ALL_DISTINCT_LISTS:
  fixes P
  assumes "finite P"
  shows "finite {p. distinct p \<and> set p \<subseteq> P}"
  using assms 
proof (induction "card P" arbitrary: P)
  case 0
  then have "P = {}"
    by force
  then show ?case 
    using 0
    by simp
next
  case (Suc x)
  {
    text \<open> Proof the finiteness of the union by proving both sets of the union are finite. The 
      singleton set `{[]}` is trivially finite. \<close>
    {
      {
        fix e
        assume P: "e \<in> P" 
        have "
          {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> P - {e}} 
          = (\<lambda>p. e # p) ` { p. distinct p \<and> set p \<subseteq> P - {e}}" 
          by blast
        moreover {
          let ?P'="P - {e}"
          from Suc.prems 
          have "finite ?P'"
            by blast
          text \<open> The finiteness can now be shown using the induction hypothesis. However `e` might
            already be contained in `?P`, so we have to split cases first. \<close>
          have "finite ((\<lambda>p. e # p) ` {p. distinct p \<and> set p \<subseteq> ?P'})" 
          proof (cases "e \<in> P")
            case True
            then have "x = card ?P'" using Suc.prems Suc(2) 
              by fastforce
            moreover from Suc.prems 
            have "finite ?P'" 
              by blast
            ultimately show ?thesis 
              using Suc(1) 
              by blast
          next
            case False
            then have "?P' = P" 
              by simp
            then have "finite {p. distinct p \<and> set p \<subseteq> ?P'}"
              using False P by linarith 
            then show ?thesis
              using finite_imageI
              by blast
          qed
        }
        ultimately have "finite {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}"
          by argo
      }
      then have "finite (\<Union> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) ` P))"
        using Suc.prems
        by blast
    }
    then have 
      "finite ({[]} \<union> (\<Union> ((\<lambda>e. {e # p0 | p0. distinct p0 \<and> set p0 \<subseteq> (P - {e})}) ` P)))" 
      using finite_Un
      by blast    
  }
  then show ?case 
    using FINITE_ALL_DISTINCT_LISTS_i[OF Suc.prems]
    by force
qed

lemma subset_inter_diff_empty: 
  assumes "s \<subseteq> t" 
  shows "(s \<inter> (u - t) = {})" 
  using assms
  by auto

end