theory "Set-Cpo"
imports HOLCF
begin

default_sort type

instantiation set :: (type) below
begin
  definition below_set where "(\<sqsubseteq>) = (\<subseteq>)"
instance..  
end

instance set :: (type) po
  by standard (auto simp add: below_set_def)

lemma is_lub_set:
  "S <<| \<Union>S"
  by(auto simp add: is_lub_def below_set_def is_ub_def)

lemma lub_set: "lub S = \<Union>S"
  by (metis is_lub_set lub_eqI)
  
instance set  :: (type) cpo
  by standard (rule exI, rule is_lub_set)

lemma minimal_set: "{} \<sqsubseteq> S"
  unfolding below_set_def by simp

instance set  :: (type) pcpo
  by standard (rule+, rule minimal_set)

lemma set_contI:
  assumes  "\<And> Y. chain Y \<Longrightarrow> f (\<Squnion> i. Y i) = \<Union> (f ` range Y)"
  shows "cont f"
proof(rule contI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  hence "f (\<Squnion> i. Y i) = \<Union> (f ` range Y)" by (rule assms)
  also have "\<dots> = \<Union> (range (\<lambda>i. f (Y i)))" by simp
  finally
  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)" using is_lub_set by metis
qed

lemma set_set_contI:
  assumes  "\<And> S. f (\<Union>S) = \<Union> (f ` S)"
  shows "cont f"
  by (metis set_contI assms is_lub_set  lub_eqI)

lemma adm_subseteq[simp]:
  assumes "cont f"
  shows "adm (\<lambda>a. f a \<subseteq> S)"
by (rule admI)(auto simp add: cont2contlubE[OF assms] lub_set)

lemma adm_Ball[simp]: "adm (\<lambda>S. \<forall>x\<in>S. P x)"
  by (auto intro!: admI  simp add: lub_set)

lemma finite_subset_chain:
  fixes Y :: "nat \<Rightarrow> 'a set"
  assumes "chain Y"
  assumes "S \<subseteq> \<Union>(Y ` UNIV)"
  assumes "finite S"
  shows "\<exists>i. S \<subseteq> Y i"
proof-
  from assms(2)
  have "\<forall>x \<in> S. \<exists> i. x \<in> Y i" by auto
  then obtain f where f: "\<forall> x\<in> S. x \<in> Y (f x)" by metis

  define i where "i = Max (f ` S)"
  from \<open>finite S\<close>
  have "finite (f ` S)" by simp
  hence "\<forall> x\<in>S. f x \<le> i" unfolding i_def by auto
  with chain_mono[OF \<open>chain Y\<close>]
  have "\<forall> x\<in>S. Y (f x) \<subseteq> Y i" by (auto simp add: below_set_def)
  with f
  have "S \<subseteq> Y i" by auto
  thus ?thesis..
qed

lemma diff_cont[THEN cont_compose, simp, cont2cont]:
  fixes S' :: "'a set"
  shows  "cont (\<lambda>S. S - S')"
by (rule set_set_contI) simp


end
