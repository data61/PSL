theory Nondeterminism
imports Main
begin

  inductive foreach :: "('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    for f
    where
      empty: "foreach f {} a a" |
      insert: "foreach f S a\<^sub>0 a\<^sub>1 \<Longrightarrow> x \<notin> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> foreach f (insert x S) a\<^sub>0 a\<^sub>2"

  declare foreach.intros[intro]
  declare foreach.cases[elim]

  lemma foreach_mono:
    assumes "\<And> x a\<^sub>0 a\<^sub>1. f\<^sub>1 x a\<^sub>0 a\<^sub>1 \<Longrightarrow> f\<^sub>2 x a\<^sub>0 a\<^sub>1"
    assumes "foreach f\<^sub>1 S a\<^sub>0 a\<^sub>1"
    shows "foreach f\<^sub>2 S a\<^sub>0 a\<^sub>1"
    using assms(2, 1) by induct auto
  lemma foreach_mono_inductive[mono]:
    assumes "\<And> x a\<^sub>0 a\<^sub>1. f\<^sub>1 x a\<^sub>0 a\<^sub>1 \<longrightarrow> f\<^sub>2 x a\<^sub>0 a\<^sub>1"
    shows "foreach f\<^sub>1 S a\<^sub>0 a\<^sub>1 \<longrightarrow> foreach f\<^sub>2 S a\<^sub>0 a\<^sub>1"
    using foreach_mono assms by metis

  lemma foreach_reflexive_transitive:
    assumes "reflp r" "transp r"
    assumes "foreach f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> r a\<^sub>1 a\<^sub>2"
    shows "r a\<^sub>1 a\<^sub>2"
  using assms(3, 4)
  proof induct
    case (empty a)
    show ?case using reflpD assms(1) by this
  next
    case (insert S a\<^sub>0 a\<^sub>1 x a\<^sub>2)
    have 0: "r a\<^sub>0 a\<^sub>1" using insert(2) insert(5) by auto
    have 1: "r a\<^sub>1 a\<^sub>2" using insert(5) insert(4) by auto
    show ?case using transpD assms(2) 0 1 by this
  qed
  lemma foreach_preorder:
    fixes g :: "'a \<Rightarrow> 'b :: preorder"
    assumes "foreach f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> g a\<^sub>1 \<le> g a\<^sub>2"
    shows "g a\<^sub>1 \<le> g a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 \<le> g a\<^sub>2)" by (rule reflpI, rule order_refl)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 \<le> g a\<^sub>2)" by (rule transpI, rule order_trans)
    show ?thesis using foreach_reflexive_transitive 0 1 assms by this
  qed
  lemma foreach_equality:
    assumes "foreach f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> g a\<^sub>1 = g a\<^sub>2"
    shows "g a\<^sub>1 = g a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 = g a\<^sub>2)" by (rule reflpI, auto)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 = g a\<^sub>2)" by (rule transpI, auto)
    show "g a\<^sub>1 = g a\<^sub>2" using foreach_reflexive_transitive 0 1 assms by this
  qed
  lemma foreach_implication:
    assumes "foreach f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> P a\<^sub>1 \<Longrightarrow> P a\<^sub>2"
    shows "P a\<^sub>1 \<Longrightarrow> P a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. P a\<^sub>1 \<longrightarrow> P a\<^sub>2)" by (rule reflpI, auto)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. P a\<^sub>1 \<longrightarrow> P a\<^sub>2)" by (rule transpI, auto)
    show "P a\<^sub>1 \<Longrightarrow> P a\<^sub>2" using foreach_reflexive_transitive[OF 0 1] assms by blast
  qed

  inductive foreachc :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    ("foreach\<^sub>C")
    for c f
    where
      empty: "foreach\<^sub>C c f {} a a" |
      insert: "foreach\<^sub>C c f S a\<^sub>0 a\<^sub>1 \<Longrightarrow> c a\<^sub>1 \<Longrightarrow> x \<notin> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow>
        foreach\<^sub>C c f (insert x S) a\<^sub>0 a\<^sub>2" |
      abort: "foreach\<^sub>C c f S a\<^sub>0 a\<^sub>1 \<Longrightarrow> \<not> c a\<^sub>1 \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> foreach\<^sub>C c f S' a\<^sub>0 a\<^sub>1"

  declare foreachc.intros[intro]
  declare foreachc.cases[elim]

  lemma foreachc_mono:
    assumes "\<And> x a\<^sub>0 a\<^sub>1. f\<^sub>1 x a\<^sub>0 a\<^sub>1 \<Longrightarrow> f\<^sub>2 x a\<^sub>0 a\<^sub>1"
    assumes "foreach\<^sub>C c f\<^sub>1 S a\<^sub>0 a\<^sub>1"
    shows "foreach\<^sub>C c f\<^sub>2 S a\<^sub>0 a\<^sub>1"
    using assms(2, 1) by induct auto
  lemma foreachc_mono_inductive[mono]:
    assumes "\<And> x a\<^sub>0 a\<^sub>1. f\<^sub>1 x a\<^sub>0 a\<^sub>1 \<longrightarrow> f\<^sub>2 x a\<^sub>0 a\<^sub>1"
    shows "foreach\<^sub>C c f\<^sub>1 S a\<^sub>0 a\<^sub>1 \<longrightarrow> foreach\<^sub>C c f\<^sub>2 S a\<^sub>0 a\<^sub>1"
    using assms foreachc_mono by metis

  lemma foreachc_reflexive_transitive:
    assumes "reflp r" "transp r"
    assumes "foreach\<^sub>C c f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> r a\<^sub>1 a\<^sub>2"
    shows "r a\<^sub>1 a\<^sub>2"
  using assms(3, 4)
  proof induct
    case (empty a)
    show ?case using reflpD assms(1) by this
  next
    case (insert S a\<^sub>0 a\<^sub>1 x a\<^sub>2)
    have 0: "r a\<^sub>0 a\<^sub>1" using insert(2) insert(6) by auto
    have 1: "r a\<^sub>1 a\<^sub>2" using insert(6) insert(5) by auto
    show ?case using transpD assms(2) 0 1 by this
  next
    case (abort S a\<^sub>0 a\<^sub>1 S')
    have 0: "r a\<^sub>0 a\<^sub>1" using abort(2) abort(4) abort(5) by auto
    show ?case using 0 by this
  qed
  lemma foreachc_preorder:
    fixes g :: "'a \<Rightarrow> 'b :: preorder"
    assumes "foreach\<^sub>C c f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> g a\<^sub>1 \<le> g a\<^sub>2"
    shows "g a\<^sub>1 \<le> g a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 \<le> g a\<^sub>2)" by (rule reflpI, rule order_refl)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 \<le> g a\<^sub>2)" by (rule transpI, rule order_trans)
    show ?thesis using foreachc_reflexive_transitive 0 1 assms by this
  qed
  lemma foreachc_equality:
    assumes "foreach\<^sub>C c f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> g a\<^sub>1 = g a\<^sub>2"
    shows "g a\<^sub>1 = g a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 = g a\<^sub>2)" by (rule reflpI, auto)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. g a\<^sub>1 = g a\<^sub>2)" by (rule transpI, auto)
    show "g a\<^sub>1 = g a\<^sub>2" using foreachc_reflexive_transitive 0 1 assms by this
  qed
  lemma foreachc_implication:
    assumes "foreach\<^sub>C c f S a\<^sub>1 a\<^sub>2"
    assumes "\<And> x a\<^sub>1 a\<^sub>2. x \<in> S \<Longrightarrow> f x a\<^sub>1 a\<^sub>2 \<Longrightarrow> P a\<^sub>1 \<Longrightarrow> P a\<^sub>2"
    shows "P a\<^sub>1 \<Longrightarrow> P a\<^sub>2"
  proof -
    have 0: "reflp (\<lambda> a\<^sub>1 a\<^sub>2. P a\<^sub>1 \<longrightarrow> P a\<^sub>2)" by (rule reflpI, auto)
    have 1: "transp (\<lambda> a\<^sub>1 a\<^sub>2. P a\<^sub>1 \<longrightarrow> P a\<^sub>2)" by (rule transpI, auto)
    show "P a\<^sub>1 \<Longrightarrow> P a\<^sub>2" using foreachc_reflexive_transitive[OF 0 1] assms by blast
  qed

  lemma foreachc_success:
    assumes "foreach\<^sub>C c f S a\<^sub>0 a\<^sub>1"
    assumes "c a\<^sub>1"
    shows "foreach f S a\<^sub>0 a\<^sub>1"
    using assms by induct auto

  fun find :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool"
    where "find A P None \<longleftrightarrow> (\<forall> a \<in> A. \<not> P a)" | "find A P (Some a) \<longleftrightarrow> a \<in> A \<and> P a"

end