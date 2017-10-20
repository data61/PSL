section {* Recoverable Data Types *}

theory RDR
imports Main Sequences
begin

subsection {* The pre-RDR locale contains definitions later used in the RDR locale 
  to state the properties of RDRs *}

locale pre_RDR = Sequences +
  fixes \<delta>::"'a \<Rightarrow> ('b \<times> 'c) \<Rightarrow> 'a" (infix "\<bullet>" 65)
  and \<gamma>::"'a \<Rightarrow> ('b \<times> 'c) \<Rightarrow> 'd"
  and bot::'a ("\<bottom>")
begin

fun exec::"'a \<Rightarrow> ('b\<times>'c)list \<Rightarrow> 'a" (infix "\<star>" 65) where 
  "exec s Nil = s"
| "exec s (rs#r) = (exec s rs) \<bullet> r"

definition less_eq (infix "\<preceq>" 50) where
  "less_eq s s' \<equiv> \<exists> rs . s' = (s\<star>rs)"

definition less (infix "\<prec>" 50) where
  "less s s' \<equiv> less_eq s s' \<and> s \<noteq> s'"

definition is_lb where
  "is_lb s s1 s2 \<equiv> s \<preceq> s2 \<and> s \<preceq> s1"

definition is_glb where
  "is_glb s s1 s2 \<equiv> is_lb s s1 s2 \<and> (\<forall> s' . is_lb s' s1 s2 \<longrightarrow> s' \<preceq> s)"
  
definition contains where
  "contains s r \<equiv> \<exists> rs . r \<in> set rs \<and> s = (\<bottom> \<star> rs)"

definition inf  (infix "\<sqinter>" 65) where
  "inf s1 s2 \<equiv> THE s . is_glb s s1 s2"

subsection {* Useful Lemmas in the pre-RDR locale *}

lemma exec_cons: 
  "s \<star> (rs # r)= (s \<star> rs) \<bullet> r" by simp

lemma exec_append: 
  "(s \<star> rs) \<star> rs'  = s \<star> (rs@rs')"
proof (induct rs')
  show "(s \<star> rs) \<star> []  = s \<star> (rs@[])" by simp
next
  fix rs' r
  assume ih:"(s \<star> rs) \<star> rs'  = s \<star> (rs@rs')"
  thus "(s \<star> rs) \<star> (rs'#r)  = s \<star> (rs @ (rs'#r))"
    by (metis append_Cons exec_cons)
qed

lemma trans:
  assumes "s1 \<preceq> s2" and "s2 \<preceq> s3"
  shows "s1 \<preceq> s3" using assms
    by (auto simp add:less_eq_def, metis exec_append)

lemma contains_star:
  fixes s r rs
  assumes "contains s r"
  shows "contains (s \<star> rs) r"
proof (induct rs)
  case Nil
  show "contains (s \<star> []) r" using assms by auto
next
  case (Cons r' rs)
  with this obtain rs' where 1:"s \<star> rs = \<bottom> \<star> rs'" and 2:"r \<in> set rs'" 
    by (auto simp add:contains_def)
  have 3:"s \<star> (rs#r') = \<bottom>\<star>(rs'#r')" using 1 by fastforce
  show "contains (s \<star> (rs#r')) r" using 2 3 
    by (auto simp add:contains_def) (metis exec_cons set_rev_mp set_subset_Cons)
qed

lemma preceq_star: "s \<star> (rs#r) \<preceq> s' \<Longrightarrow> s \<star> rs \<preceq> s'"
by (metis pre_RDR.exec.simps(1) pre_RDR.exec.simps(2) pre_RDR.less_eq_def trans)

end

subsection {* The RDR locale *}

locale RDR = pre_RDR +
  assumes idem1:"contains s r \<Longrightarrow> s \<bullet> r = s"
  and idem2:"\<And> s r r' . fst r \<noteq> fst r' \<Longrightarrow> \<gamma> s r = \<gamma> ((s \<bullet> r) \<bullet> r') r"
  and antisym:"\<And> s1 s2 . s1 \<preceq> s2 \<and> s2 \<preceq> s1 \<Longrightarrow> s1 = s2"
  and glb_exists:"\<And> s1 s2 . \<exists> s . is_glb s s1 s2"
  and consistency:"\<And>s1 s2 s3 rs . s1 \<preceq> s2 \<Longrightarrow> s2 \<preceq> s3 \<Longrightarrow> s3 = s1 \<star> rs 
    \<Longrightarrow> \<exists> rs' rs'' . s2 = s1 \<star> rs' \<and> s3 = s2 \<star> rs'' 
      \<and> set rs' \<subseteq> set rs \<and> set rs'' \<subseteq> set rs"
  and bot:"\<And> s . \<bottom> \<preceq> s"
begin

lemma inf_glb:"is_glb (s1 \<sqinter> s2) s1 s2"
proof -
  { fix s s'
    assume "is_glb s s1 s2" and "is_glb s' s1 s2"
    hence "s = s'" using antisym by (auto simp add:is_glb_def is_lb_def) }
    from this and glb_exists show ?thesis
      by (auto simp add:inf_def, metis (lifting) theI')
qed

sublocale ordering less_eq less
proof
  fix s
  show "s \<preceq> s"
  by (metis exec.simps(1) less_eq_def)
next
  fix s s'
  show "s \<prec> s' = (s \<preceq> s' \<and> s \<noteq> s')" 
  by (auto simp add:less_def)
next
  fix s s'
  assume "s \<preceq> s'" and "s' \<preceq> s"
  thus "s = s'"
  using antisym by auto
next
  fix s1 s2 s3
  assume "s1 \<preceq> s2" and "s2 \<preceq> s3"
  thus "s1 \<preceq> s3"
  using trans by blast
qed

sublocale semilattice_set inf
proof
  fix s
  show "s \<sqinter> s = s" 
    using inf_glb
    by (metis antisym is_glb_def is_lb_def refl) 
next
  fix s1 s2
  show "s1 \<sqinter> s2 = (s2 \<sqinter> s1)"
    using inf_glb 
    by (smt antisym is_glb_def pre_RDR.is_lb_def)
next
  fix s1 s2 s3
  show "(s1 \<sqinter> s2) \<sqinter> s3 = (s1 \<sqinter> (s2 \<sqinter> s3))"
    using inf_glb 
    by(auto simp add:is_glb_def is_lb_def, smt antisym trans)
qed

sublocale semilattice_order_set inf less_eq less
proof 
  fix s s'
  show "s \<preceq> s' = (s = s \<sqinter> s')"
  by (metis antisym idem inf_glb pre_RDR.is_glb_def pre_RDR.is_lb_def)
next
  fix s s'
  show "s \<prec> s' = (s = s \<sqinter> s' \<and> s \<noteq> s')"
  by (metis inf_glb local.antisym local.refl pre_RDR.is_glb_def pre_RDR.is_lb_def pre_RDR.less_def)
qed

notation F ("\<Sqinter> _" [99])

subsection {* Some useful lemmas *}

lemma idem_star: 
fixes r s rs
assumes "contains s r"
shows "s \<star> rs = s \<star> (filter (\<lambda> x . x \<noteq> r) rs)"
proof (induct rs)
  case Nil
  show "s \<star> [] = s \<star> (filter (\<lambda> x . x \<noteq> r) [])" 
    using assms by auto
next
  case (Cons r' rs)
  have 1:"contains (s \<star> rs) r" using assms and contains_star by auto
  show "s \<star> (rs#r') = s \<star> (filter (\<lambda> x . x \<noteq> r) (rs#r'))"
  proof (cases "r' = r")
    case True
    hence "s \<star> (rs#r') = s \<star> rs" using idem1 1 by auto
    thus ?thesis using Cons by simp
  next
    case False
    thus ?thesis using Cons by auto
  qed
qed

lemma idem_star2: 
  fixes s rs' 
  shows "\<exists> rs' . s \<star> rs = s \<star> rs' \<and> set rs' \<subseteq> set rs 
    \<and> (\<forall> r \<in> set rs' . \<not> contains s r)"
proof (induct rs)
  case Nil
  thus "\<exists> rs' . s \<star> [] = s \<star> rs' \<and> set rs' \<subseteq> set [] 
    \<and> (\<forall> r \<in> set rs' . \<not> contains s r)" by force
next
  case (Cons r rs)
  obtain rs' where 1:"s \<star> rs = s \<star> rs'" and 2:"set rs' \<subseteq> set rs"
  and 3:"\<forall> r \<in> set rs' . \<not> contains s r" using Cons(1) by blast
  show "\<exists> rs' . s \<star> (rs#r) = s \<star> rs' \<and> set rs' \<subseteq> set (rs#r)
    \<and> (\<forall> r \<in> set rs' . \<not> contains s r)"
  proof (cases "contains s r")
    case True
    have "s\<star>(rs#r) = s\<star>rs'"
    proof -
      have "s \<star> (rs#r) = s\<star>rs" using True
        by (metis contains_star exec_cons idem1)
      moreover
      have "s \<star> (rs'#r) = s\<star>rs'" using True
        by (metis contains_star exec_cons idem1) 
      ultimately show ?thesis using 1 by simp
    qed
    moreover have "set rs' \<subseteq> set (rs#r)" using 2 
      by (simp, metis subset_insertI2) 
    moreover have "\<forall> r \<in> set rs' . \<not> contains s r" 
      using 3 by assumption
    ultimately show ?thesis by blast
  next
    case False
    have "s\<star>(rs#r) = s\<star>(rs'#r)" using 1 by simp
    moreover
    have "set (rs'#r) \<subseteq> set (rs#r)" using 2 by auto
    moreover have "\<forall> r \<in> set (rs'#r) . \<not> contains s r" 
      using 3 False by auto
    ultimately show ?thesis by blast
  qed 
qed

lemma idem2_star:
assumes "contains s r" 
and "\<And> r' . r' \<in> set rs \<Longrightarrow> fst r' \<noteq> fst r"
shows "\<gamma> s r = \<gamma> (s \<star> rs) r" using assms
proof (induct rs)  
  case Nil
  show "\<gamma> s r = \<gamma> (s \<star> []) r" by simp
next
  case (Cons r' rs)
  thus "\<gamma> s r = \<gamma> (s \<star> (rs#r')) r"
    using assms by auto
      (metis contains_star fst_conv idem1 idem2 prod.exhaust) 
qed

lemma glb_common:
fixes s1 s2 s rs1 rs2
assumes "s1 = s \<star> rs1" and "s2 = s \<star> rs2"
shows "\<exists> rs . s1 \<sqinter> s2 = s \<star> rs \<and> set rs \<subseteq> set rs1 \<union> set rs2"
proof -
  have 1:"s \<preceq> s1" and 2:"s \<preceq> s2" using assms by (auto simp add:less_eq_def)
  hence 3:"s \<preceq> s1 \<sqinter> s2" by (metis inf_glb is_lb_def pre_RDR.is_glb_def)
  have 4:"s1 \<sqinter> s2 \<preceq> s1" by (metis cobounded1) 
  show ?thesis using 3 4 assms(1) and consistency by blast
qed

lemma glb_common_set:
fixes ss s0 rset
assumes "finite ss"  and "ss \<noteq> {}"
and "\<And> s . s \<in> ss \<Longrightarrow> \<exists> rs . s = s0 \<star> rs \<and> set rs \<subseteq> rset"
shows "\<exists> rs . \<Sqinter> ss = s0 \<star> rs \<and> set rs \<subseteq> rset"
using assms
proof (induct ss rule:finite_ne_induct)
  case (singleton s)
  obtain rs where "s = s0 \<star> rs \<and> set rs \<subseteq> rset" using singleton by force
  moreover have "\<Sqinter> {s} = s" using singleton by auto
  ultimately show "\<exists> rs . \<Sqinter> {s} = s0 \<star> rs \<and> set rs \<subseteq> rset" by blast
next
  case (insert s ss)
  have 1:"\<And> s' . s' \<in> ss \<Longrightarrow> \<exists> rs . s' = s0 \<star> rs \<and> set rs \<subseteq> rset"
    using insert(5) by force
  obtain rs where 2:"\<Sqinter> ss = s0 \<star> rs" and 3:"set rs \<subseteq> rset" 
    using insert(4) 1 by blast
  obtain rs' where 4:"s = s0 \<star> rs'"and 5:"set rs' \<subseteq> rset"
    using insert(5) by blast
  have 6:"\<Sqinter> (insert s ss) = s \<sqinter> (\<Sqinter> ss)"
    by (metis insert.hyps(1-3) insert_not_elem) 
  obtain rs'' where 7:"\<Sqinter> (insert s ss) = s0 \<star> rs''" 
    and 8:"set rs'' \<subseteq> set rs' \<union> set rs"
    using glb_common 2 4 6 by force
  have 9:"set rs'' \<subseteq> rset" using 3 5 8 by blast
  show "\<exists> rs . \<Sqinter> (insert s ss) = s0 \<star> rs \<and> set rs \<subseteq> rset"
    using 7 9 by blast
qed

end 

end
