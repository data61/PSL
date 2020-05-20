theory "HOLCF-Meet"
imports HOLCF
begin

text \<open>
This theory defines the $\sqcap$ operator on HOLCF domains, and introduces a type class for domains
where all finite meets exist.
\<close>

subsubsection \<open>Towards meets: Lower bounds\<close>

context po
begin
definition is_lb :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix ">|" 55) where
  "S >| x \<longleftrightarrow> (\<forall>y\<in>S. x \<sqsubseteq> y)"

lemma is_lbI: "(!!x. x \<in> S ==> l \<sqsubseteq> x) ==> S >| l"
  by (simp add: is_lb_def)

lemma is_lbD: "[|S >| l; x \<in> S|] ==> l \<sqsubseteq> x"
  by (simp add: is_lb_def)

lemma is_lb_empty [simp]: "{} >| l"
  unfolding is_lb_def by fast

lemma is_lb_insert [simp]: "(insert x A) >| y = (y \<sqsubseteq> x \<and> A >| y)"
  unfolding is_lb_def by fast

lemma is_lb_downward: "[|S >| l; y \<sqsubseteq> l|] ==> S >| y"
  unfolding is_lb_def by (fast intro: below_trans)

subsubsection \<open>Greatest lower bounds\<close>

definition is_glb :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix ">>|" 55) where
  "S >>| x \<longleftrightarrow> S >| x \<and> (\<forall>u. S >| u --> u \<sqsubseteq> x)"

definition glb :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [60]60) where
  "glb S = (THE x. S >>| x)" 

text \<open>Access to the definition as inference rule\<close>

lemma is_glbD1: "S >>| x ==> S >| x"
  unfolding is_glb_def by fast

lemma is_glbD2: "[|S >>| x; S >| u|] ==> u \<sqsubseteq> x"
  unfolding is_glb_def by fast

lemma (in po) is_glbI: "[|S >| x; !!u. S >| u ==> u \<sqsubseteq> x|] ==> S >>| x"
  unfolding is_glb_def by fast

lemma is_glb_above_iff: "S >>| x ==> u \<sqsubseteq> x \<longleftrightarrow> S >| u"
  unfolding is_glb_def is_lb_def by (metis below_trans)

text \<open>glbs are unique\<close>

lemma is_glb_unique: "[|S >>| x; S >>| y|] ==> x = y"
  unfolding is_glb_def is_lb_def by (blast intro: below_antisym)

text \<open>technical lemmas about @{term glb} and @{term is_glb}\<close>

lemma is_glb_glb: "M >>| x ==> M >>| glb M"
  unfolding glb_def by (rule theI [OF _ is_glb_unique])

lemma glb_eqI: "M >>| l ==> glb M = l"
  by (rule is_glb_unique [OF is_glb_glb])

lemma is_glb_singleton: "{x} >>| x"
  by (simp add: is_glb_def)

lemma glb_singleton [simp]: "glb {x} = x"
  by (rule is_glb_singleton [THEN glb_eqI])

lemma is_glb_bin: "x \<sqsubseteq> y ==> {x, y} >>| x"
  by (simp add: is_glb_def)

lemma glb_bin: "x \<sqsubseteq> y ==> glb {x, y} = x"
  by (rule is_glb_bin [THEN glb_eqI])

lemma is_glb_maximal: "[|S >| x; x \<in> S|] ==> S >>| x"
  by (erule is_glbI, erule (1) is_lbD)

lemma glb_maximal: "[|S >| x; x \<in> S|] ==> glb S = x"
  by (rule is_glb_maximal [THEN glb_eqI])

lemma glb_above: "S >>| z \<Longrightarrow> x \<sqsubseteq> glb S \<longleftrightarrow> S >| x"
  by (metis glb_eqI is_glb_above_iff)
end

lemma (in cpo) Meet_insert: "S >>| l \<Longrightarrow> {x, l} >>| l2 \<Longrightarrow> insert x S >>| l2"
  apply (rule is_glbI)
  apply (metis is_glb_above_iff is_glb_def is_lb_insert)
  by (metis is_glb_above_iff is_glb_def is_glb_singleton is_lb_insert)

text \<open>Binary, hence finite meets.\<close>

class Finite_Meet_cpo = cpo +
  assumes binary_meet_exists: "\<exists> l. l \<sqsubseteq> x \<and> l \<sqsubseteq> y \<and> (\<forall> z. z \<sqsubseteq> x \<longrightarrow> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> l)"
begin

  lemma binary_meet_exists': "\<exists>l. {x, y} >>| l"
    using binary_meet_exists[of x y]
    unfolding is_glb_def is_lb_def
    by auto

  lemma finite_meet_exists:
    assumes "S \<noteq> {}"
    and "finite S"
    shows "\<exists>x. S >>| x"
  using \<open>S \<noteq> {}\<close>
  apply (induct rule: finite_induct[OF \<open>finite S\<close>])
  apply (erule notE, rule refl)[1]
  apply (case_tac "F = {}")
  apply (metis is_glb_singleton)
  apply (metis Meet_insert binary_meet_exists')
  done
end

definition meet :: "'a::cpo \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<sqinter>" 80) where
  "x \<sqinter> y = (if \<exists> z. {x, y} >>| z then glb {x, y} else x)"

lemma meet_def': "(x::'a::Finite_Meet_cpo) \<sqinter> y = glb {x, y}"
  unfolding meet_def by (metis binary_meet_exists')

lemma meet_comm: "(x::'a::Finite_Meet_cpo) \<sqinter> y = y \<sqinter> x" unfolding meet_def' by (metis insert_commute)

lemma meet_bot1[simp]:
  fixes y :: "'a :: {Finite_Meet_cpo,pcpo}"
  shows "(\<bottom> \<sqinter> y) = \<bottom>" unfolding meet_def' by (metis minimal po_class.glb_bin)
lemma meet_bot2[simp]:
  fixes x :: "'a :: {Finite_Meet_cpo,pcpo}"
  shows "(x \<sqinter> \<bottom>) = \<bottom>" by (metis meet_bot1 meet_comm)

lemma meet_below1[intro]:
  fixes x y :: "'a :: Finite_Meet_cpo"
  assumes "x \<sqsubseteq> z"
  shows "(x \<sqinter> y) \<sqsubseteq> z" unfolding meet_def' by (metis assms binary_meet_exists' below_trans glb_eqI is_glbD1 is_lb_insert)
lemma meet_below2[intro]:
  fixes x y :: "'a :: Finite_Meet_cpo"
  assumes "y \<sqsubseteq> z"
  shows "(x \<sqinter> y) \<sqsubseteq> z" unfolding meet_def' by (metis assms binary_meet_exists' below_trans glb_eqI is_glbD1 is_lb_insert)

lemma meet_above_iff:
  fixes x y z :: "'a :: Finite_Meet_cpo"
  shows "z \<sqsubseteq> x \<sqinter> y \<longleftrightarrow> z \<sqsubseteq> x \<and> z \<sqsubseteq> y"
proof-
  obtain g where "{x,y} >>| g" by (metis binary_meet_exists')
  thus ?thesis
  unfolding meet_def' by (simp add: glb_above)
qed

lemma below_meet[simp]:
  fixes x y :: "'a :: Finite_Meet_cpo"
  assumes "x \<sqsubseteq> z"
  shows "(x \<sqinter> z) = x" by (metis assms glb_bin meet_def')

lemma below_meet2[simp]:
  fixes x y :: "'a :: Finite_Meet_cpo"
  assumes "z \<sqsubseteq> x"
  shows "(x \<sqinter> z) = z" by (metis assms below_meet meet_comm)

lemma meet_aboveI:
  fixes x y z :: "'a :: Finite_Meet_cpo"
  shows "z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y" by (simp add: meet_above_iff)

lemma is_meetI:
  fixes x y z :: "'a :: Finite_Meet_cpo"
  assumes "z \<sqsubseteq> x"
  assumes "z \<sqsubseteq> y"
  assumes "\<And> a. \<lbrakk> a \<sqsubseteq> x ; a \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a \<sqsubseteq> z"
  shows "x \<sqinter> y = z"
by (metis assms below_antisym meet_above_iff below_refl)

lemma meet_assoc[simp]: "((x::'a::Finite_Meet_cpo) \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  apply (rule is_meetI)
  apply (metis below_refl meet_above_iff)
  apply (metis below_refl meet_below2)
  apply (metis meet_above_iff)
  done

lemma meet_self[simp]: "r \<sqinter> r = (r::'a::Finite_Meet_cpo)"
  by (metis below_refl is_meetI)

lemma [simp]: "(r::'a::Finite_Meet_cpo) \<sqinter> (r \<sqinter> x) = r \<sqinter> x"
  by (metis below_refl is_meetI meet_below1)

lemma meet_monofun1:
  fixes y :: "'a :: Finite_Meet_cpo"
  shows "monofun (\<lambda>x. (x \<sqinter> y))"
  by (rule monofunI)(auto simp add: meet_above_iff)

lemma chain_meet1:
  fixes y :: "'a :: Finite_Meet_cpo"
  assumes "chain Y"
  shows "chain (\<lambda> i. Y i \<sqinter> y)"
by (rule chainI) (auto simp add: meet_above_iff intro: chainI chainE[OF assms])

class cont_binary_meet = Finite_Meet_cpo +
  assumes meet_cont': "chain Y \<Longrightarrow> (\<Squnion> i. Y i) \<sqinter> y = (\<Squnion> i. Y i \<sqinter> y)"

lemma meet_cont1:
  fixes y :: "'a :: cont_binary_meet"
  shows "cont (\<lambda>x. (x \<sqinter> y))"
  by (rule contI2[OF meet_monofun1]) (simp add: meet_cont')

lemma meet_cont2: 
  fixes x :: "'a :: cont_binary_meet"
  shows "cont (\<lambda>y. (x \<sqinter> y))" by (subst meet_comm, rule meet_cont1)

lemma meet_cont[cont2cont,simp]:"cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. (f x \<sqinter> (g x::'a::cont_binary_meet)))"
  apply (rule cont2cont_case_prod[where g = "\<lambda> x. (f x, g x)" and f = "\<lambda> p x y . x \<sqinter> y", simplified])
  apply (rule meet_cont1)
  apply (rule meet_cont2)
  apply (metis cont2cont_Pair)
  done

end
