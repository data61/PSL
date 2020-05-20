(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

section "Summation Over Lists"

theory ListSum
imports ListAux
begin

primrec ListSum :: "'b list \<Rightarrow> ('b \<Rightarrow> 'a::comm_monoid_add) \<Rightarrow> 'a::comm_monoid_add"  where
  "ListSum [] f = 0"
| "ListSum (l#ls) f = f l + ListSum ls f"

syntax "_ListSum" :: "idt \<Rightarrow> 'b list \<Rightarrow> ('a::comm_monoid_add) \<Rightarrow> 
  ('a::comm_monoid_add)"    ("\<Sum>\<^bsub>_\<in>_\<^esub> _" [0, 0, 10] 10)
translations "\<Sum>\<^bsub>x\<in>xs\<^esub> f" == "CONST ListSum xs (\<lambda>x. f)" 

lemma [simp]: "(\<Sum>\<^bsub>v \<in> V\<^esub> 0) = (0::nat)" by (induct V) simp_all

lemma ListSum_compl1: 
  "(\<Sum>\<^bsub>x \<in> [x\<leftarrow>xs. \<not> P x]\<^esub> f x) + (\<Sum>\<^bsub>x \<in> [x\<leftarrow>xs. P x]\<^esub> f x) = (\<Sum>\<^bsub>x \<in> xs\<^esub> (f x::nat))" 
 by (induct xs) simp_all

lemma ListSum_compl2: 
  "(\<Sum>\<^bsub>x \<in>  [x\<leftarrow>xs. P x]\<^esub> f x) + (\<Sum>\<^bsub>x \<in>  [x\<leftarrow>xs. \<not> P x]\<^esub> f x) = (\<Sum>\<^bsub>x \<in> xs\<^esub> (f x::nat))" 
 by (induct xs) simp_all

lemmas ListSum_compl = ListSum_compl1 ListSum_compl2


lemma ListSum_conv_sum:
 "distinct xs \<Longrightarrow> ListSum xs f =  sum f (set xs)"
by(induct xs) simp_all


lemma listsum_cong:
 "\<lbrakk> xs = ys; \<And>y. y \<in> set ys \<Longrightarrow> f y = g y \<rbrakk>
  \<Longrightarrow> ListSum xs f = ListSum ys g"
apply simp
apply(erule thin_rl)
by (induct ys) simp_all


lemma strong_listsum_cong[cong]:
 "\<lbrakk> xs = ys; \<And>y. y \<in> set ys =simp=> f y = g y \<rbrakk>
  \<Longrightarrow> ListSum xs f = ListSum ys g"
by(auto simp:simp_implies_def intro!:listsum_cong)


lemma ListSum_eq [trans]: 
  "(\<And>v. v \<in> set V \<Longrightarrow> f v = g v) \<Longrightarrow> (\<Sum>\<^bsub>v \<in> V\<^esub> f v) = (\<Sum>\<^bsub>v \<in> V\<^esub> g v)" 
by(auto intro!:listsum_cong)


lemma ListSum_disj_union: 
  "distinct A \<Longrightarrow> distinct B \<Longrightarrow> distinct C \<Longrightarrow> 
  set C = set A \<union> set B  \<Longrightarrow> 
  set A \<inter> set B = {} \<Longrightarrow>
  (\<Sum>\<^bsub>a \<in> C\<^esub> (f a)) = (\<Sum>\<^bsub>a \<in> A\<^esub> f a) + (\<Sum>\<^bsub>a \<in> B\<^esub> (f a::nat))"
by (simp add: ListSum_conv_sum sum.union_disjoint)


lemma listsum_const[simp]: 
  "(\<Sum>\<^bsub>x \<in> xs\<^esub> k) = length xs * k"
by (induct xs) (simp_all add: ring_distribs)

lemma ListSum_add: 
  "(\<Sum>\<^bsub>x \<in> V\<^esub> f x) + (\<Sum>\<^bsub>x \<in> V\<^esub> g x) = (\<Sum>\<^bsub>x \<in> V\<^esub> (f x + (g x::nat)))" 
  by (induct V) auto

lemma ListSum_le: 
  "(\<And>v. v \<in> set V \<Longrightarrow> f v \<le> g v) \<Longrightarrow> (\<Sum>\<^bsub>v \<in> V\<^esub> f v) \<le> (\<Sum>\<^bsub>v \<in> V\<^esub> (g v::nat))"
proof (induct V)
  case Nil then show ?case by simp
next
  case (Cons v V) then have "(\<Sum>\<^bsub>v \<in> V\<^esub> f v) \<le> (\<Sum>\<^bsub>v \<in> V\<^esub> g v)" by simp
  moreover from Cons have "f v \<le> g v" by simp
  ultimately show ?case by simp
qed

lemma ListSum1_bound:
 "a \<in> set F \<Longrightarrow> (d a::nat)\<le> (\<Sum>\<^bsub>f \<in> F\<^esub> d f)"
by (induct F) auto

end
