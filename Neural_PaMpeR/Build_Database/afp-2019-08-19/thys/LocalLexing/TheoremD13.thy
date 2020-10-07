theory TheoremD13
imports TheoremD12
begin

context LocalLexing begin

lemma pointwise_natUnion_swap:
  assumes pointwise_f: "pointwise f"
  shows "f (natUnion G) = natUnion (\<lambda> u. f (G u))"
proof -
  note f_simp = pointwise_simp[OF pointwise_f]
  have h1: "f (natUnion G) = \<Union> {f {x} |x. x \<in> (natUnion G)}" using f_simp by blast
  have h2: "\<And> x. f (G x) =  \<Union> {f {y} |y. y \<in> G x}" using f_simp by metis
  show ?thesis
    apply (subst h1)
    apply (subst h2)
    apply (simp add: natUnion_def)
    by blast
qed    

lemma pointwise_Gen: "pointwise Gen"
  by (simp add: pointwise_def Gen_def, blast)
    
lemma thmD13_part1:
  assumes start: "items_le k (\<J> k 0) = Gen (paths_le k (\<P> k 0))"
  assumes valid_k: "k \<le> length Doc"
  shows "items_le k (\<J> k u) = Gen (paths_le k (\<P> k u)) \<and> \<T> k u = \<Z> k u"
proof (induct u)
  case 0 
    then show ?case using start by auto
next
  case (Suc u) 
    from Suc have sub: "items_le k (\<J> k (Suc u)) \<subseteq> Gen (paths_le k (\<P> k (Suc u)))"
      using thmD9 valid_k by blast
    from Suc have sup: "items_le k (\<J> k (Suc u)) \<supseteq> Gen (paths_le k (\<P> k (Suc u)))"
      using thmD12 by blast
    from Suc have tokens: "\<T> k (Suc u) = \<Z> k (Suc u)"
      using \<T>_equals_\<Z>_induct_step by blast
    from sub sup tokens show ?case by blast
qed

lemma thmD13_part2:      
  assumes start: "items_le k (\<J> k 0) = Gen (paths_le k (\<P> k 0))"
  assumes valid_k: "k \<le> length Doc"
  shows "items_le k (\<I> k) = Gen (paths_le k (\<Q> k))"
proof -
  note part1 = thmD13_part1[OF start valid_k]
  have e1: "items_le k (\<I> k) = natUnion (\<lambda> u. items_le k (\<J> k u))"
    using items_le_pointwise pointwise_natUnion_swap by auto 
  have e2: "natUnion (\<lambda> u. items_le k (\<J> k u)) = natUnion  (\<lambda> u. Gen (paths_le k (\<P> k u)))"
    using part1 by auto
  have e3: "natUnion (\<lambda> u. Gen (paths_le k (\<P> k u))) = Gen (natUnion (\<lambda> u. paths_le k (\<P> k u)))"
    using pointwise_Gen pointwise_natUnion_swap by fastforce 
  have e4: "natUnion (\<lambda> u. paths_le k (\<P> k u)) = paths_le k (natUnion (\<lambda> u. \<P> k u))"
    using paths_le_pointwise pointwise_natUnion_swap by fastforce   
  from e1 e2 e3 e4 show ?thesis by simp
qed
    
theorem thmD13:      
  assumes start: "items_le k (\<J> k 0) = Gen (paths_le k (\<P> k 0))"
  assumes valid_k: "k \<le> length Doc"
  shows "items_le k (\<J> k u) = Gen (paths_le k (\<P> k u)) \<and> \<T> k u = \<Z> k u 
    \<and> items_le k (\<I> k) = Gen (paths_le k (\<Q> k))"
using thmD13_part1[OF start valid_k] thmD13_part2[OF start valid_k] by blast

end

end
