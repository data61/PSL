theory TheoremD9
imports TheoremD8
begin

context LocalLexing begin

definition items_le :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "items_le k I = { x . x \<in> I \<and> item_end x \<le> k }"

definition items_eq :: "nat \<Rightarrow> items \<Rightarrow> items"
where
  "items_eq k I = { x . x \<in> I \<and> item_end x = k }"

definition paths_le :: "nat \<Rightarrow> tokens set \<Rightarrow> tokens set"
where 
  "paths_le k P = { p . p \<in> P \<and> charslength p \<le> k }"

definition paths_eq :: "nat \<Rightarrow> tokens set \<Rightarrow> tokens set"
where
  "paths_eq k P = { p . p \<in> P \<and> charslength p = k }"

lemma items_le_pointwise: "pointwise (items_le k)"
  by (auto simp add: pointwise_def items_le_def)

lemma items_le_is_filter: "items_le k I \<subseteq> I"
  by (auto simp add: items_le_def)

lemma items_eq_pointwise: "pointwise (items_eq k)"
  by (auto simp add: pointwise_def items_eq_def)

lemma items_eq_is_filter: "items_eq k I \<subseteq> I"
  by (auto simp add: items_eq_def)

lemma paths_le_pointwise: "pointwise (paths_le k)"
  by (auto simp add: pointwise_def paths_le_def)

lemma paths_le_continuous: "continuous (paths_le k)"
  by (simp add: paths_le_pointwise pointbased_implies_continuous pointwise_implies_pointbased)

lemma paths_le_mono: "mono (paths_le k)"
  by (simp add: continuous_imp_mono paths_le_continuous)
   
lemma paths_le_is_filter: "paths_le k P \<subseteq> P"
  by (auto simp add: paths_le_def)

lemma paths_eq_pointwise: "pointwise (paths_eq k)"
  by (auto simp add: pointwise_def paths_eq_def)

lemma paths_eq_is_filter: "paths_eq k P \<subseteq> P"
  by (auto simp add: paths_eq_def)

lemma Predict_item_end: "x \<in> Predict k Y \<Longrightarrow> item_end x = k \<or> x \<in> Y"
  using Predict_def by auto
  
lemma Complete_item_end: "x \<in> Complete k Y \<Longrightarrow> item_end x = k \<or> x \<in> Y"
  using Complete_def by auto

lemma \<J>_0_0_item_end: "x \<in> \<J> 0 0 \<Longrightarrow> item_end x = 0"
  apply (simp add: \<pi>_def)
  proof (induct rule: limit_induct)
    case (Init x) thus ?case by (auto simp add: Init_def)
  next
    case (Iterate x Y) 
    then have "x \<in> Complete 0 (Predict 0 Y)" by (simp add: Scan_empty)
    then have "item_end x = 0 \<or> x \<in> Predict 0 Y" using Complete_item_end by blast
    then have "item_end x = 0 \<or> x \<in> Y" using Predict_item_end by blast 
    then show ?case using Iterate by blast
  qed

lemma items_le_\<J>_0_0: "items_le 0 (\<J> 0 0) = \<J> 0 0"
  using LocalLexing.\<J>_0_0_item_end LocalLexing.items_le_def LocalLexing_axioms by blast

lemma paths_le_\<P>_0_0: "paths_le 0 (\<P> 0 0) = \<P> 0 0"
  by (auto simp add: paths_le_def)

definition empty_tokens :: "token set \<Rightarrow> token set"
where
  "empty_tokens T = { t . t \<in> T \<and> chars_of_token t = [] }"

lemma items_le_Predict: "items_le k (Predict k I) = Predict k (items_le k I)"
  by (auto simp add: items_le_def Predict_def bin_def)

lemma items_le_Complete: 
  "wellformed_items I \<Longrightarrow> items_le k (Complete k I) = Complete k (items_le k I)"
  by (auto simp add: items_le_def Complete_def bin_def is_complete_def wellformed_items_def 
    wellformed_item_def)

lemma items_le_Scan:
  "items_le k (Scan T k I) = Scan (empty_tokens T) k (items_le k I)"
  by (auto simp add: items_le_def Scan_def bin_def empty_tokens_def)

lemma wellformed_items_Gen: "wellformed_items (Gen P)"
  using Gen_implies_pvalid pvalid_def wellformed_items_def by blast
  
lemma wellformed_\<J>_0_0: "wellformed_items (\<J> 0 0)"
  using thmD8 wellformed_items_Gen by auto

lemma wellformed_items_Predict: 
  "wellformed_items I \<Longrightarrow> wellformed_items (Predict k I)"
  by (auto simp add: wellformed_items_def wellformed_item_def Predict_def bin_def)

lemma wellformed_items_Complete:
  "wellformed_items I \<Longrightarrow> wellformed_items (Complete k I)"
  apply (auto simp add: wellformed_items_def wellformed_item_def Complete_def bin_def)
  apply (metis dual_order.trans)
  using is_complete_def next_symbol_not_complete not_less_eq_eq by blast

lemma \<X>_length_bound: "(t, c) \<in> \<X> k \<Longrightarrow> k + length c \<le> length Doc"
  using \<X>_is_prefix is_prefix_length not_le by fastforce

lemma wellformed_items_Scan:
  "wellformed_items I \<Longrightarrow> T \<subseteq> \<X> k \<Longrightarrow> wellformed_items (Scan T k I)"
  apply (auto simp add: wellformed_items_def wellformed_item_def Scan_def bin_def \<X>_length_bound)
  using is_complete_def next_symbol_not_complete not_less_eq_eq by blast

lemma wellformed_items_\<pi>:
  assumes "wellformed_items I"
  assumes "T \<subseteq> \<X> k"
  shows "wellformed_items (\<pi> k T I)"
proof -
  {
    fix x :: item
    have "x \<in> \<pi> k T I \<Longrightarrow> wellformed_item x"
    proof (simp add: \<pi>_def, induct rule: limit_induct)
      case (Init x) thus ?case using assms(1) by (simp add: wellformed_items_def) 
    next
      case (Iterate x Y)
      have "wellformed_items Y" by (simp add: Iterate.hyps(1) wellformed_items_def)
      then have "wellformed_items (Scan T k (Complete k (Predict k Y)))"
        by (simp add: assms(2) wellformed_items_Complete wellformed_items_Predict 
          wellformed_items_Scan)
      then show ?case by (simp add: Iterate.hyps(2) wellformed_items_def) 
    qed
  }
  then show ?thesis using wellformed_items_def by auto  
qed   

lemma \<J>_subset_Suc_u: "\<J> k u \<subseteq> \<J> k (Suc u)"
  by (metis Complete_\<pi>_fix Complete_subset_\<pi> \<J>.simps(1) \<J>.simps(2) \<J>.simps(3) not0_implies_Suc)

lemma mono_TokensAt: "mono (TokensAt k)"
  by (auto simp add: mono_def TokensAt_def bin_def)
    
lemma \<T>_subset_TokensAt: "\<T> k u \<subseteq> TokensAt k (\<J> k u)"
proof (induct u)
  case 0 thus ?case by simp
next
  case (Suc u)
    have 1: "Tokens k (\<T> k u) (\<J> k u) = Sel (\<T> k u) (TokensAt k (\<J> k u))"
      by (simp add: Tokens_def)
    have 2: "Sel (\<T> k u) (TokensAt k (\<J> k u)) \<subseteq> TokensAt k (\<J> k u)"
      by (simp add: Sel_upper_bound Suc.hyps)
    have "\<T> k (Suc u) \<subseteq> TokensAt k (\<J> k u)"
      by (simp add: 1 2)
    then show ?case
      by (meson \<J>_subset_Suc_u mono_TokensAt mono_subset_elem subset_iff)
qed      

lemma TokensAt_subset_\<X>: "TokensAt k I \<subseteq> \<X> k"
  using TokensAt_def \<X>_def is_terminal_def by auto
  
lemma wellformed_items_\<J>_induct_u: 
  assumes "wellformed_items (\<J> k u)"
  shows "wellformed_items (\<J> k (Suc u))"
proof -
  {
    fix x :: item
    have "x \<in> \<J> k (Suc u) \<Longrightarrow> wellformed_item x"
    proof (simp add: \<pi>_def, induct rule: limit_induct)
      case (Init x)
        with assms show ?case by (auto simp add: wellformed_items_def)
    next
      case (Iterate p Y)
        from Iterate(1) have wellformed_Y: "wellformed_items Y"
          by (auto simp add: wellformed_items_def)
        then have "wellformed_items (Complete k (Predict k Y))"
          by (simp add: wellformed_items_Complete wellformed_items_Predict)
        then have "wellformed_items (Scan (Tokens k (\<T> k u) (\<J> k u)) k (Complete k (Predict k Y)))"
          apply (rule_tac wellformed_items_Scan)
          apply simp
          apply (simp add: Tokens_def)
          by (meson Sel_upper_bound TokensAt_subset_\<X> \<T>_subset_TokensAt subset_trans)
        then show ?case
          using Iterate.hyps(2) wellformed_items_def by blast
    qed
  }
  then show ?thesis
    using wellformed_items_def by blast 
qed      

lemma wellformed_items_\<J>_k_u_if_0: "wellformed_items (\<J> k 0) \<Longrightarrow> wellformed_items (\<J> k u)"
  apply (induct u)
  apply (simp)
  using wellformed_items_\<J>_induct_u by blast

lemma wellformed_items_natUnion: "(\<And> k. wellformed_items (I k)) \<Longrightarrow> wellformed_items (natUnion I)"
  by (auto simp add: natUnion_def wellformed_items_def) 

lemma wellformed_items_\<I>_k_if_0: "wellformed_items (\<J> k 0) \<Longrightarrow> wellformed_items (\<I> k)" 
  apply (simp)
  apply (rule wellformed_items_natUnion)
  using wellformed_items_\<J>_k_u_if_0 by blast
 
lemma wellformed_items_\<J>_\<I>: "wellformed_items (\<J> k u) \<and> wellformed_items (\<I> k)"
proof (induct k arbitrary: u)
  case 0
    show ?case
      using wellformed_\<J>_0_0 wellformed_items_\<I>_k_if_0 wellformed_items_\<J>_k_u_if_0 by blast 
next
  case (Suc k)
    have 0: "wellformed_items (\<J> (Suc k) 0)"
      apply simp
      using Suc.hyps wellformed_items_\<pi> by auto      
    then show ?case
      using wellformed_items_\<I>_k_if_0 wellformed_items_\<J>_k_u_if_0 by blast
qed

lemma wellformed_items_\<J>: "wellformed_items (\<J> k u)"
by (simp add: wellformed_items_\<J>_\<I>)

lemma wellformed_items_\<I>: "wellformed_items (\<I> k)"
using wellformed_items_\<J>_\<I> by blast

lemma funpower_consume_function:
  assumes law: "\<And> X. P X \<Longrightarrow> f (g X) = h (f X) \<and> P (g X)"
  shows "P I \<Longrightarrow> P (funpower g n I) \<and> f (funpower g n I) = funpower h n (f I)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have S1: "P (funpower g n I)" and S2: "f (funpower g n I) = funpower h n (f I)"
    by auto
  have law1: "\<And> X. P X \<Longrightarrow> f (g X) = h (f X)" using law by auto
  have law2: "\<And> X. P X \<Longrightarrow> P (g X)" using law by auto
  show ?case
    apply simp
    apply (subst law1[where X="funpower g n I"])
    apply (simp add: S1)
    apply (subst S2) 
    apply auto
    apply (rule law2)
    apply (simp add: S1)
    done
qed
    
lemma limit_consume_function:
  assumes continuous: "continuous f"
  assumes law: "\<And> X. P X \<Longrightarrow> f (g X) = h (f X) \<and> P (g X)"
  assumes setmonotone: "setmonotone g"
  shows "P I \<Longrightarrow> f (limit g I) = limit h (f I)"
proof -
  have 1: "f (limit g I) = f (natUnion (\<lambda>n. funpower g n I))"
    by (simp add: limit_def)
  have "chain (\<lambda>n. funpower g n I)" by (simp add: setmonotone setmonotone_implies_chain_funpower)
  from continuous_apply[OF continuous this]
  have swap: "f (natUnion (\<lambda>n. funpower g n I)) = natUnion (f \<circ> (\<lambda>n. funpower g n I))" by blast
  have "f o (\<lambda>n. funpower g n I) = (\<lambda> n. f (funpower g n I))" by auto
  also have "P I \<Longrightarrow> (\<lambda> n. f (funpower g n I)) = (\<lambda> n. funpower h n (f I))"
    by (metis funpower_consume_function[where P=P and f=f and g=g and h=h, OF law, simplified])
  ultimately have "P I \<Longrightarrow> f o (\<lambda>n. funpower g n I) = (\<lambda> n. funpower h n (f I))" by auto
  with swap have 2: "P I \<Longrightarrow> f (natUnion (\<lambda>n. funpower g n I)) = natUnion (\<lambda> n. funpower h n (f I))"
    by auto
  have 3: "natUnion (\<lambda> n. funpower h n (f I)) = limit h (f I)"
    by (simp add: limit_def)
  assume "P I"
  with 1 2 3 show ?thesis by auto
qed

lemma items_le_\<pi>_swap: 
  assumes wellformed_I: "wellformed_items I"
  assumes T: "T \<subseteq> \<X> k"
  shows "items_le k (\<pi> k T I) = \<pi> k (empty_tokens T) (items_le k I)"
proof -
  let ?g = "(Scan T k) o (Complete k) o (Predict k)"
  let ?h = "(Scan (empty_tokens T) k) o (Complete k) o (Predict k)" 
  have law1: "\<And> I. wellformed_items I \<Longrightarrow> items_le k (?g I) = ?h (items_le k I)"
    using LocalLexing.wellformed_items_Predict LocalLexing_axioms items_le_Complete 
      items_le_Predict items_le_Scan by auto
  have law2: "\<And> I. wellformed_items I \<Longrightarrow> wellformed_items (?g I)"
    by (simp add: T wellformed_items_Complete wellformed_items_Predict wellformed_items_Scan)
  show ?thesis
    apply (subst \<pi>_functional)
    apply (subst limit_consume_function[where P="wellformed_items" and h="?h"])
    apply (simp add: items_le_pointwise pointbased_implies_continuous pointwise_implies_pointbased)
    using law1 law2 apply blast
    apply (simp add: \<pi>_step_regular regular_implies_setmonotone)
    apply (rule wellformed_I)
    apply (subst \<pi>_functional)
    apply blast
    done
qed
    
lemma items_le_idempotent: "items_le k (items_le k I) = items_le k I"
  using items_le_def by auto 

lemma paths_le_idempotent: "paths_le k (paths_le k P) = paths_le k P"
  using paths_le_def by auto

lemma items_le_fix_D:
  assumes items_le_fix: "items_le k I = I"
  assumes x_dom: "x \<in> I" 
  shows "item_end x \<le> k"
using items_le_def items_le_fix x_dom by blast

lemma remove_paths_le_in_subset_Gen:
  assumes "items_le k I = I"
  assumes "I \<subseteq> Gen P"
  shows "I \<subseteq> Gen (paths_le k P)"
proof -
  {
    fix x :: item
    assume x_dom: "x \<in> I"
    then have x_item_end:  "item_end x \<le> k" using assms items_le_fix_D by auto 
    have "x \<in> Gen P" using assms x_dom by auto 
    then obtain p where p: "p \<in> P \<and> pvalid p x" using Gen_implies_pvalid by blast 
    have charslength_p: "charslength p \<le> k" using p pvalid_item_end x_item_end by auto 
    then have "p \<in> paths_le k P" by (simp add: p paths_le_def) 
    then have "x \<in> Gen (paths_le k P)" using Gen_def p by blast 
  }
  then show ?thesis by blast 
qed

lemma mono_Gen: "mono Gen"
  by (auto simp add: mono_def Gen_def)

lemma empty_tokens_idempotent: "empty_tokens (empty_tokens T) = empty_tokens T"
  by (auto simp add: empty_tokens_def)

lemma empty_tokens_is_filter: "empty_tokens T \<subseteq> T"
  by (auto simp add: empty_tokens_def)

lemma items_le_paths_le: "items_le k (Gen P) = Gen (paths_le k P)"
  using LocalLexing.Gen_def LocalLexing.items_le_def LocalLexing_axioms paths_le_def 
  pvalid_item_end by auto      

lemma bin_items_le[symmetric]: "bin I k = bin (items_le k I) k"
  by (auto simp add: bin_def items_le_def)

lemma TokensAt_items_le[symmetric]: "TokensAt k I = TokensAt k (items_le k I)"
  using TokensAt_def bin_items_le by blast

lemma by_length_paths_le[symmetric]: "by_length k P = by_length k (paths_le k P)"
  using by_length.simps paths_le_def by auto

lemma \<W>_paths_le[symmetric]: "\<W> P k = \<W> (paths_le k P) k"
  using \<W>_def by_length_paths_le by blast

theorem \<T>_equals_\<Z>_induct_step: 
  assumes induct: "items_le k (\<J> k u) = Gen (paths_le k (\<P> k u))"
  assumes induct_tokens: "\<T> k u = \<Z> k u"
  shows "\<T> k (Suc u) = \<Z> k (Suc u)"
proof -
  have "TokensAt k (\<J> k u) = TokensAt k (items_le k (\<J> k u))"
    using TokensAt_items_le by blast
  also have "TokensAt k (items_le k (\<J> k u)) = TokensAt k (Gen (paths_le k (\<P> k u)))"
    using induct by auto
  ultimately have TokensAt_le: "TokensAt k (\<J> k u) = TokensAt k (Gen (paths_le k (\<P> k u)))"
    by auto
  have "TokensAt k (\<J> k u) = \<W> (\<P> k u) k"
    apply (subst TokensAt_le)
    apply (subst \<W>_paths_le[symmetric])
    apply (rule_tac thmD4[symmetric])
    using \<PP>_covers_\<P> paths_le_is_filter by blast
  then show ?thesis
    by (simp add: induct_tokens Tokens_def \<Y>_def)
qed 

theorem thmD9:
  assumes induct: "items_le k (\<J> k u) = Gen (paths_le k (\<P> k u))"
  assumes induct_tokens: "\<T> k u = \<Z> k u"
  assumes k: "k \<le> length Doc"
  shows "items_le k (\<J> k (Suc u)) \<subseteq> Gen (paths_le k (\<P> k (Suc u)))"
proof -
  have t1: "items_le k (\<J> k (Suc u)) = items_le k (\<pi> k (\<T> k (Suc u)) (\<J> k u))"
    by auto
  have t2: "items_le k (\<pi> k (\<T> k (Suc u)) (\<J> k u)) = 
    \<pi> k (empty_tokens (\<T> k (Suc u))) (items_le k (\<J> k u))"
    apply (subst items_le_\<pi>_swap)
    apply (simp add: wellformed_items_\<J>)
    using TokensAt_subset_\<X> \<T>_subset_TokensAt apply blast
    by blast
  have t3: "\<pi> k (empty_tokens (\<T> k (Suc u))) (items_le k (\<J> k u)) =
    \<pi> k (empty_tokens (\<T> k (Suc u))) (Gen (paths_le k (\<P> k u)))"
    using induct by auto
  have \<P>_subset: "\<P> k u \<subseteq> \<P> k (Suc u)" using subset_\<P>Suc by blast
  then have "paths_le k (\<P> k u) \<subseteq> paths_le k (\<P> k (Suc u))"
    by (simp add: mono_subset_elem paths_le_mono subsetI)
  with mono_Gen have "Gen (paths_le k (\<P> k u)) \<subseteq> Gen (paths_le k (\<P> k (Suc u)))"
    by (simp add: mono_subset_elem subsetI)
  then have t4: "\<pi> k (empty_tokens (\<T> k (Suc u))) (Gen (paths_le k (\<P> k u))) \<subseteq>
    \<pi> k (empty_tokens (\<T> k (Suc u))) (Gen (paths_le k (\<P> k (Suc u))))"
    by (rule monoD[OF mono_\<pi>]) 
  have \<T>_eq_\<Z>: "\<T> k (Suc u) = \<Z> k (Suc u)"
    using \<T>_equals_\<Z>_induct_step assms(1) induct_tokens by blast  
  have t5: "\<pi> k (empty_tokens (\<T> k (Suc u))) (Gen (paths_le k (\<P> k (Suc u)))) \<subseteq> 
    Gen (paths_le k (\<P> k (Suc u)))"
    apply (rule_tac remove_paths_le_in_subset_Gen)
    apply (subst items_le_\<pi>_swap)
    using wellformed_items_Gen apply blast
    using \<T>_eq_\<Z> \<Z>_subset_\<X> empty_tokens_is_filter apply blast    
    apply (simp only: empty_tokens_idempotent paths_le_idempotent items_le_paths_le)
    apply (rule_tac thmD5)
    using items_le_is_filter items_le_paths_le apply blast
    apply (rule k)
    using \<T>_eq_\<Z> empty_tokens_is_filter by blast
  from t1 t2 t3 t4 t5 show ?thesis using subset_trans by blast
qed      
  
end

end
