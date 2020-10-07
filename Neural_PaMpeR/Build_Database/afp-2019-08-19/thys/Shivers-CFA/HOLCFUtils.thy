section \<open>HOLCF Utility lemmas\<close>
theory HOLCFUtils
imports HOLCF
begin

text \<open>
We use @{theory HOLCF} to define the denotational semantics. By default, HOLCF does not turn the regular \<open>set\<close> type into a partial order, so this is done here. Some of the lemmas here are contributed by Brian Huffman.

We start by making the type \<open>bool\<close> a pointed chain-complete partial order.
\<close>

instantiation bool :: po
begin
definition
  "x \<sqsubseteq> y \<longleftrightarrow> (x \<longrightarrow> y)"
instance by standard (unfold below_bool_def, fast+)
end

instance bool :: chfin
apply standard
apply (drule finite_range_imp_finch)
apply (rule finite)
apply (simp add: finite_chain_def)
done

instance bool :: pcpo
proof
  have "\<forall>y. False \<sqsubseteq> y" by (simp add: below_bool_def)
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

lemma is_lub_bool: "S <<| (True \<in> S)"
  unfolding is_lub_def is_ub_def below_bool_def by auto

lemma lub_bool: "lub S = (True \<in> S)"
  using is_lub_bool by (rule lub_eqI)

lemma bottom_eq_False[simp]: "\<bottom> = False"
by (rule below_antisym [OF minimal], simp add: below_bool_def)

text \<open>
To convert between the squared syntax used by @{theory HOLCF} and the regular, round syntax for sets, we state some of the equivalencies.
\<close>

instantiation set :: (type) po
begin
definition
  "A \<sqsubseteq> B \<longleftrightarrow> A \<subseteq> B"
instance by standard (unfold below_set_def, fast+)
end

lemma sqsubset_is_subset: "A \<sqsubseteq> B \<longleftrightarrow> A \<subseteq> B"
  by (fact below_set_def)

lemma is_lub_set: "S <<| \<Union>S"
  unfolding is_lub_def is_ub_def below_set_def by fast

lemma lub_is_union: "lub S = \<Union>S"
  using is_lub_set by (rule lub_eqI)

instance set :: (type) cpo
  by standard (fast intro: is_lub_set)

lemma emptyset_is_bot[simp]: "{} \<sqsubseteq> S"
  by (simp add:sqsubset_is_subset)

instance set :: (type) pcpo
  by standard (fast intro: emptyset_is_bot)

lemma bot_bool_is_emptyset[simp]: "\<bottom> = {}"
  using emptyset_is_bot by (rule bottomI [symmetric])

text \<open>
To actually use these instance in \<open>fixrec\<close> definitions or fixed-point inductions, we need continuity requrements for various boolean and set operations.
\<close>

lemma cont2cont_disj [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x \<or> g x)"
apply (rule cont_apply [OF f])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
apply (rule cont_compose [OF _ g])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
done

lemma cont2cont_imp[simp, cont2cont]:
  assumes f: "cont (\<lambda>x. \<not> f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x \<longrightarrow> g x)"
unfolding imp_conv_disj by (rule cont2cont_disj[OF f g])

lemma cont2cont_Collect [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. {y. f x y})"
apply (rule contI)
apply (subst cont2contlubE [OF assms], assumption)
apply (auto simp add: is_lub_def is_ub_def below_set_def lub_bool)
done

lemma cont2cont_mem [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. y \<in> f x)"
apply (rule cont_compose [OF _ assms])
apply (rule contI)
apply (auto simp add: is_lub_def is_ub_def below_bool_def lub_is_union)
done

lemma cont2cont_union [simp, cont2cont]:
  "cont (\<lambda>x. f x) \<Longrightarrow> cont (\<lambda>x. g x)
\<Longrightarrow> cont (\<lambda>x. f x \<union> g x)"
unfolding Un_def by simp

lemma cont2cont_insert [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. insert y (f x))"
unfolding insert_def using assms
by (intro cont2cont)

lemmas adm_subset = adm_below[where ?'b = "'a::type set", unfolded sqsubset_is_subset]

lemma cont2cont_UNION[cont2cont,simp]:
  assumes "cont f"
      and "\<And> y. cont (\<lambda>x. g x y)"
  shows "cont (\<lambda>x. \<Union>y\<in> f x. g x y)"
proof(induct rule: contI2[case_names Mono Limit])
case Mono
  show "monofun (\<lambda>x. \<Union>y\<in>f x. g x y)"
    by (rule monofunI)(auto iff:sqsubset_is_subset dest: monofunE[OF assms(1)[THEN cont2mono]] monofunE[OF assms(2)[THEN cont2mono]])
next
case (Limit Y)
  have "(\<Union>y\<in>f (\<Squnion> i. Y i). g (\<Squnion> j. Y j) y) \<subseteq> (\<Squnion> k. \<Union>y\<in>f (Y k). g (Y k) y)"
  proof
    fix x assume "x \<in> (\<Union>y\<in>f (\<Squnion> i. Y i). g (\<Squnion> j. Y j) y)"
    then obtain y where "y\<in>f (\<Squnion> i. Y i)" and "x\<in> g (\<Squnion> j. Y j) y" by auto
    hence "y \<in> (\<Squnion> i. f (Y i))" and "x\<in> (\<Squnion> j. g (Y j) y)" by (auto simp add: cont2contlubE[OF assms(1) Limit(1)] cont2contlubE[OF assms(2) Limit(1)])
    then obtain i and j where yi: "y\<in> f (Y i)" and xj: "x\<in> g (Y j) y" by (auto simp add:lub_is_union)
    obtain k where "i\<le>k" and "j\<le>k" by (erule_tac x = "max i j" in meta_allE)auto
    from yi and xj have "y \<in> f (Y k)" and "x\<in> g (Y k) y"
      using monofunE[OF assms(1)[THEN cont2mono], OF chain_mono[OF Limit(1) \<open>i\<le>k\<close>]]
        and monofunE[OF assms(2)[THEN cont2mono], OF chain_mono[OF Limit(1) \<open>j\<le>k\<close>]]
      by (auto simp add:sqsubset_is_subset)
    hence "x\<in> (\<Union>y\<in> f (Y k). g (Y k) y)" by auto
    thus "x\<in> (\<Squnion> k. \<Union>y\<in>f (Y k). g (Y k) y)" by (auto simp add:lub_is_union)
  qed
  thus ?case by (simp add:sqsubset_is_subset)
qed

lemma cont2cont_Let_simple[simp,cont2cont]:
  assumes "cont (\<lambda>x. g x t)"
  shows "cont (\<lambda>x. let y = t in g x y)"
unfolding Let_def using assms .


lemma cont2cont_case_list [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. case_list (f1 x) (f2 x) l)"
using assms
by (cases l) auto


text \<open>As with the continuity lemmas, we need admissibility lemmas.\<close>

lemma adm_not_mem:
  assumes "cont (\<lambda>x. f x)"
  shows "adm (\<lambda>x. y \<notin> f x)"
using assms
apply (erule_tac t = f in adm_subst)
proof (rule admI)
fix Y :: "nat \<Rightarrow> 'b set"
assume chain: "chain Y"
assume "\<forall>i. y \<notin> Y i" hence  "(\<Squnion> i. y \<in> Y i) = False"
  by auto
thus "y \<notin> (\<Squnion> i. Y i)"
  using chain unfolding lub_bool lub_is_union by auto
qed

lemma adm_id[simp]: "adm (\<lambda>x . x)"
by (rule adm_chfin)

lemma adm_Not[simp]: "adm Not"
by (rule adm_chfin)

lemma adm_prod_split:
  assumes "adm (\<lambda>p. f (fst p) (snd p))"
  shows "adm (\<lambda>(x,y). f x y)"
using assms unfolding split_def .

lemma adm_ball':
  assumes "\<And> y. adm (\<lambda>x. y \<in> A x \<longrightarrow> P x y)"
  shows "adm (\<lambda>x. \<forall>y \<in> A x . P x y)"
by (subst Ball_def, rule adm_all[OF assms])

lemma adm_not_conj:
  "\<lbrakk>adm (\<lambda>x. \<not> P x); adm (\<lambda>x. \<not> Q x)\<rbrakk> \<Longrightarrow> adm (\<lambda>x. \<not> (P x \<and> Q x))"
by simp

lemma adm_single_valued:
 assumes "cont (\<lambda>x. f x)"
 shows "adm (\<lambda>x. single_valued (f x))"
using assms
unfolding single_valued_def
by (intro adm_lemmas adm_not_mem cont2cont adm_subst[of f])

text \<open>
To match Shivers' syntax we introduce the power-syntax for iterated function application.
\<close>

abbreviation niceiterate ("(_\<^bsup>_\<^esup>)" [1000] 1000)
  where "niceiterate f i \<equiv> iterate i\<cdot>f"

end
