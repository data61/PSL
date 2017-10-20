(*  Title:      Basis.thy
    Author:     Peter Gammie
*)

theory Basis
imports
  HOLCF
  "HOL-Library.Product_Order"
  "HOLCF-Library.Nat_Discrete"
  Dual_Lattice
begin

subsection{* Auxiliary lemmas *}

lemma cfun_map_below_ID:
  assumes e: "e \<sqsubseteq> ID"
  shows "cfun_map\<cdot>e\<cdot>e \<sqsubseteq> ID"
proof(intro cfun_belowI)
  fix f x
  from e have "cfun_map\<cdot>e\<cdot>e\<cdot>f\<cdot>x \<sqsubseteq> ID\<cdot>(f\<cdot>(ID\<cdot>x))"
    by (simp del: ID1) (fast intro: monofun_cfun)
  thus "cfun_map\<cdot>e\<cdot>e\<cdot>f\<cdot>x \<sqsubseteq> ID\<cdot>f\<cdot>x" by simp
qed

lemma cfun_below_ID:
  "\<lbrakk> f \<sqsubseteq> ID; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> f\<cdot>x \<sqsubseteq> y"
  by (auto simp: cfun_below_iff elim: below_trans)

lemma oo_below:
  "\<lbrakk> f \<sqsubseteq> f'; g \<sqsubseteq> g' \<rbrakk> \<Longrightarrow> f oo g \<sqsubseteq> f' oo g'"
  by (simp add: oo_def cfun_below_iff monofun_cfun)

lemma cont_case_nat[simp]:
  "\<lbrakk>cont (\<lambda>x. f x); \<And>n. cont (\<lambda>x. g x n) \<rbrakk> \<Longrightarrow> cont (\<lambda>x. case_nat (f x) (g x) n)"
  by (cases n, simp_all)

lemma cont2cont_if_below_const [cont2cont, simp]:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. if f x \<sqsubseteq> d then \<bottom> else g x)"
proof (rule cont_apply [OF f])
  show "\<And>x. cont (\<lambda>y. if y \<sqsubseteq> d then \<bottom> else g x)"
    unfolding cont_def is_lub_def is_ub_def ball_simps
    by (simp add: lub_below_iff)
  show "\<And>y. cont (\<lambda>x. if y \<sqsubseteq> d then \<bottom> else g x)"
    by (simp add: g)
qed

lemma cont2cont_foldl [simp, cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'c::cpo \<Rightarrow> 'b"
  fixes xs :: "'c list"
  fixes z :: "'a \<Rightarrow> 'b"
  assumes f: "cont (\<lambda>(x, y, z). f x y z)"
  assumes z: "cont z"
  shows "cont (\<lambda>x. foldl (f x) (z x) xs)"
apply (induct xs rule: rev_induct)
 apply (simp add: z)
using f
apply (simp add: prod_cont_iff)
by (rule cont_apply, simp_all)

lemma cont2cont_foldr [simp, cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'c::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'b"
  fixes xs :: "'c list"
  fixes z :: "'a \<Rightarrow> 'b"
  assumes f: "cont (\<lambda>(x, y, z). f x y z)"
  assumes z: "cont z"
  shows "cont (\<lambda>x. foldr (f x) xs (z x))"
apply (induct xs)
 apply (simp add: z)
using f
apply (simp add: prod_cont_iff)
by (rule cont_apply, simp_all)

text{*

The following proof is due to
\citet[Eqn~2.28]{DBLP:journals/siamcomp/Scott76}.

*}

lemma fix_argument_promote:
  assumes "cont g"
  shows "(\<Lambda> x. fix\<cdot>(g x)) = fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x))"
proof(rule below_antisym)
  have "(\<Lambda> x. g x\<cdot>(fix\<cdot>(g x))) = (\<Lambda> x. fix\<cdot>(g x))"
    by (subst fix_eq) simp
  with `cont g` show "fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x)) \<sqsubseteq> (\<Lambda> x. fix\<cdot>(g x))"
    by (simp add: fix_least cont2cont_LAM)
next
  show "(\<Lambda> x. fix\<cdot>(g x)) \<sqsubseteq> fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x))"
  proof(rule cfun_belowI)
    fix y
    from `cont g`
    have "g y\<cdot>(fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x))\<cdot>y) = fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x))\<cdot>y"
      by (subst fix_eq, simp add: cont2cont_LAM)
    with `cont g` show "(\<Lambda> x. fix\<cdot>(g x))\<cdot>y \<sqsubseteq> fix\<cdot>(\<Lambda> f x. g x\<cdot>(f\<cdot>x))\<cdot>y"
      by (simp add: fix_least)
  qed
qed

lemma fix_argument_promote_fun:
  fixes g :: "'a::type \<Rightarrow> 'b::pcpo \<rightarrow> 'b"
  shows "(\<lambda>x. fix\<cdot>(g x)) = (\<mu> f. (\<lambda>x. g x\<cdot>(f x)))"
proof(rule below_antisym)
  have "(\<lambda>x. g x\<cdot>(fix\<cdot>(g x))) = (\<lambda>x. fix\<cdot>(g x))"
    by (subst fix_eq) simp
  then show "(\<mu> f. (\<lambda>x. g x\<cdot>(f x))) \<sqsubseteq> (\<lambda>x. fix\<cdot>(g x))"
    by (simp add: fix_least cont_fun)
next
  show "(\<lambda>x. fix\<cdot>(g x)) \<sqsubseteq> (\<mu> f. (\<lambda>x. g x\<cdot>(f x)))"
  proof(rule fun_belowI)
    fix y
    have "g y\<cdot>((\<mu> f. (\<lambda>x. g x\<cdot>(f x))) y) = (\<mu> f. (\<lambda>x. g x\<cdot>(f x))) y"
      by (subst fix_eq, simp add: cont_fun)
    thus "fix\<cdot>(g y) \<sqsubseteq> (\<mu> f. (\<lambda>x. g x\<cdot>(f x))) y"
      by (simp add: fix_least)
  qed
qed

lemma adm_cart_prod [intro, simp]:
  assumes X: "adm (\<lambda>x. x \<in> X)"
  assumes Y: "adm (\<lambda>x. x \<in> Y)"
  shows "adm (\<lambda>x. x \<in> X \<times> Y)"
proof(rule admI)
  fix A assume A: "chain A" and Ai: "\<forall>i. A i \<in> X \<times> Y"
  from Ai have "\<forall>i. fst (A i) \<in> X" and "\<forall>i. snd (A i) \<in> Y"
    apply auto
    apply (erule_tac x=i in allE)
    apply (case_tac "A i")
    apply simp
    apply (erule_tac x=i in allE)
    apply (case_tac "A i")
    apply simp
    done
  with A X Y show "Lub A \<in> X \<times> Y"
    by (auto intro: admD intro!: adm_subst simp: lub_prod)
qed

lemma adm_exists_deterministic [intro, simp]:
  assumes Q: "\<And>y. adm (\<lambda>x. Q x y)"
  assumes P: "\<And>x x'. P x \<and> P x' \<longrightarrow> x = x'"
  shows "adm (\<lambda>x. \<exists>y. P y \<and> Q x y)"
proof(rule admI)
  fix Y assume Y: "chain Y" and Yi: "\<forall>i. \<exists>y. P y \<and> Q (Y i) y"
  then obtain y where Py: "P y" by blast
  with P Q Y Yi have "Q (Lub Y) y"
    by - (rule admD, fastforce+)
  with Py show "\<exists>y. P y \<and> Q (Lub Y) y" by blast
qed


subsubsection{* Order monics *}

text{*

Order monics are invertible with respect to the partial order. They
don't need to be continuous!

All domain data constructors are @{term "below_monic_cfun"}.

*}

definition
  below_monic :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool"
where
  "below_monic f \<equiv> \<forall>x y. f x \<sqsubseteq> f y \<longrightarrow> x \<sqsubseteq> y"

abbreviation
  below_monic_cfun :: "('a::cpo \<rightarrow> 'b::cpo) \<Rightarrow> bool"
where
  "below_monic_cfun f \<equiv> below_monic (Rep_cfun f)"

lemma below_monicI:
  "(\<And>x y. f x \<sqsubseteq> f y \<Longrightarrow> x \<sqsubseteq> y) \<Longrightarrow> below_monic f"
  unfolding below_monic_def by simp

lemma below_monicE:
  "\<lbrakk> below_monic f; f x \<sqsubseteq> f y \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
  unfolding below_monic_def by simp

lemma below_monic_inj:
  "below_monic (f :: 'a::cpo \<Rightarrow> 'b::cpo) \<Longrightarrow> inj f"
  by (auto intro!: below_antisym injI elim: below_monicE)

lemma below_monic_ID [iff]:
  "below_monic_cfun ID"
  by (rule below_monicI) simp

lemma below_monic_cfcomp [iff]:
  "below_monic_cfun f \<Longrightarrow> below_monic_cfun (cfcomp\<cdot>f)"
by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_K [iff]:
  "below_monic_cfun f \<Longrightarrow> below_monic_cfun (\<Lambda> c _. f\<cdot>c)"
by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_fun_K [iff]:
  "below_monic_cfun f \<Longrightarrow> below_monic_cfun (\<Lambda> c. (\<lambda>_. f\<cdot>c))"
by (rule below_monicI) (auto simp: fun_below_iff dest: below_monicE)

lemma below_monic_cfcomp2 [iff]:
  "\<lbrakk> below_monic_cfun f; below_monic_cfun g \<rbrakk> \<Longrightarrow> below_monic_cfun (f oo g)"
  by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_pair [iff]:
  "\<lbrakk> below_monic_cfun f; below_monic_cfun g \<rbrakk> \<Longrightarrow> below_monic_cfun (\<Lambda> x. (f\<cdot>x, g\<cdot>x))"
  by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_pair_split [iff]:
  "\<lbrakk> below_monic_cfun f; below_monic_cfun g \<rbrakk> \<Longrightarrow> below_monic_cfun (\<Lambda> x. (f\<cdot>(fst x), g\<cdot>(snd x)))"
  by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_sinl [iff]:
  "below_monic_cfun sinl"
  by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_sinr [iff]:
  "below_monic_cfun sinr"
  by (rule below_monicI) (auto simp: cfun_below_iff elim: below_monicE)

lemma below_monic_chain_inv:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes Y: "chain (Y :: nat \<Rightarrow> 'b::cpo)"
  assumes Yi: "\<forall>i. \<exists>y. Y i = f y \<and> P y"
  assumes f: "below_monic f"
  shows "\<exists>Y'. chain Y' \<and> (\<forall>i. Y i = f (Y' i) \<and> P (Y' i))"
proof -
  let ?Y' = "\<lambda>i. SOME y. Y i = f y \<and> P y"
  have "chain ?Y'"
  proof(rule chainI)
    fix i :: nat
    show "(SOME x. Y i = f x \<and> P x) \<sqsubseteq> (SOME y. Y (Suc i) = f y \<and> P y)"
      apply -
      using spec[OF Yi, where x=i] spec[OF Yi, where x="Suc i"]
      apply clarsimp
      apply (rule someI2)
       apply blast
      apply (rule someI2)
       apply blast
      apply (rule below_monicE[OF f])
      using chain_mono[OF Y, where i=i and j="Suc i"]
      apply simp
      done
  qed
  moreover
  { fix i
    from Yi have "Y i = f (?Y' i) \<and> P (?Y' i)"
      apply -
      apply (erule allE[where x=i])
      apply clarsimp
      apply (auto intro!: someI)
      done
  }
  ultimately show ?thesis by blast
qed

lemma adm_below_monic_exists:
  "\<lbrakk> adm P; below_monic (f::'a::cpo \<Rightarrow> 'b::cpo); cont f \<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<exists>y. x = f y \<and> P y)"
  apply (rule admI)
  apply (cut_tac Y=Y in below_monic_chain_inv)
  apply simp_all
  apply clarsimp
  apply (rule_tac x="Lub Y'" in exI)
  apply (auto iff: contlub_cfun_arg[symmetric] cont2contlubE[where f=f] elim!: admD)
  done

end
