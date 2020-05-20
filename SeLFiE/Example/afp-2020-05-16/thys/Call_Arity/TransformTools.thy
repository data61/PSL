theory TransformTools
imports "Launchbury.Nominal-HOLCF" Launchbury.Terms Launchbury.Substitution Launchbury.Env
begin

default_sort type

fun lift_transform :: "('a::cont_pt \<Rightarrow> exp \<Rightarrow> exp) \<Rightarrow> ('a\<^sub>\<bottom> \<Rightarrow> exp \<Rightarrow> exp)"
  where "lift_transform t Ibottom  e = e"
  |     "lift_transform t (Iup a) e = t a e"

lemma lift_transform_simps[simp]:
  "lift_transform t \<bottom> e = e"
  "lift_transform t (up\<cdot>a) e = t a e"
  apply (metis inst_up_pcpo lift_transform.simps(1))
  apply (simp add: up_def cont_Iup)
  done

lemma lift_transform_eqvt[eqvt]: "\<pi> \<bullet>  lift_transform t a e = lift_transform (\<pi> \<bullet> t) (\<pi> \<bullet> a) (\<pi> \<bullet> e)"
  by (cases "a") simp_all

lemma lift_transform_fun_cong[fundef_cong]:
  "(\<And> a. t1 a e1 = t2 a e1) \<Longrightarrow> a1 = a2 \<Longrightarrow> e1 = e2 \<Longrightarrow> lift_transform t1 a1 e1 = lift_transform t2 a2 e2"
  by (cases "(t2,a2,e2)" rule: lift_transform.cases) auto

lemma subst_lift_transform: 
  assumes "\<And> a. (t a e)[x ::= y] = t a (e[x ::= y])"
  shows "(lift_transform t a e)[x ::=y] = lift_transform t a (e[x ::= y])"
  using assms by (cases a) auto

definition
  map_transform :: "('a::cont_pt \<Rightarrow> exp \<Rightarrow> exp) \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<Rightarrow> heap \<Rightarrow> heap"
  where "map_transform t ae = map_ran (\<lambda> x e . lift_transform t (ae x) e)"

lemma map_transform_eqvt[eqvt]: "\<pi> \<bullet> map_transform t ae = map_transform (\<pi> \<bullet> t) (\<pi> \<bullet> ae)"
  unfolding map_transform_def by simp

lemma domA_map_transform[simp]: "domA (map_transform t ae \<Gamma>) = domA \<Gamma>"
  unfolding map_transform_def by simp

lemma length_map_transform[simp]: "length (map_transform t ae xs) = length xs"
  unfolding map_transform_def map_ran_def by simp
 
lemma map_transform_delete:
  "map_transform t ae (delete x \<Gamma>) = delete x (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by (simp add: map_ran_delete)

lemma map_transform_restrA:
  "map_transform t ae (restrictA S \<Gamma>) = restrictA S (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by (auto simp add: map_ran_restrictA)

lemma delete_map_transform_env_delete:
  "delete x (map_transform t (env_delete x ae) \<Gamma>) = delete x (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by (induction \<Gamma>) auto

lemma map_transform_Nil[simp]:
  "map_transform t ae [] = []"
  unfolding map_transform_def by simp

lemma map_transform_Cons:
  "map_transform t ae ((x,e)# \<Gamma>) = (x, lift_transform t (ae x) e) #  (map_transform t ae \<Gamma>)"
  unfolding map_transform_def by simp

lemma map_transform_append:
  "map_transform t ae (\<Delta>@\<Gamma>) = map_transform t ae \<Delta> @ map_transform t ae \<Gamma>"
  unfolding map_transform_def by (simp add: map_ran_append)

lemma map_transform_fundef_cong[fundef_cong]:
  "(\<And>x e a. (x,e) \<in> set m1 \<Longrightarrow> t1 a e = t2 a e) \<Longrightarrow> ae1 = ae2 \<Longrightarrow> m1 = m2 \<Longrightarrow> map_transform t1 ae1 m1 = map_transform t2 ae2 m2"
  by (induction m2 arbitrary: m1)
     (fastforce simp add: map_transform_Nil map_transform_Cons intro!: lift_transform_fun_cong)+

lemma map_transform_cong:
  "(\<And>x. x \<in> domA m1 \<Longrightarrow> ae x = ae' x) \<Longrightarrow> m1 = m2 \<Longrightarrow> map_transform t ae m1 = map_transform t ae' m2"
  unfolding map_transform_def by (auto intro!: map_ran_cong dest: domA_from_set)

lemma map_of_map_transform: "map_of (map_transform t ae \<Gamma>) x = map_option (lift_transform t (ae x)) (map_of \<Gamma> x)"
  unfolding map_transform_def by (simp add: map_ran_conv)

lemma supp_map_transform_step:
  assumes "\<And> x e a. (x, e) \<in> set \<Gamma> \<Longrightarrow> supp (t a e) \<subseteq> supp e"
  shows "supp (map_transform t ae \<Gamma>) \<subseteq> supp \<Gamma>"
  using assms
    apply (induction \<Gamma>)
    apply (auto simp add: supp_Nil supp_Cons map_transform_Nil map_transform_Cons supp_Pair pure_supp)
    apply (case_tac "ae a")
    apply (fastforce)+
    done

lemma subst_map_transform: 
  assumes "\<And> x' e a. (x',e) : set \<Gamma> \<Longrightarrow> (t a e)[x ::= y] = t a (e[x ::= y])"
  shows "(map_transform t ae \<Gamma>)[x ::h=y] = map_transform t ae (\<Gamma>[x ::h= y])"
  using assms
  apply (induction \<Gamma>)
  apply (auto simp add: map_transform_Nil map_transform_Cons)
  apply (subst subst_lift_transform)
  apply auto
  done

locale supp_bounded_transform = 
  fixes trans :: "'a::cont_pt \<Rightarrow> exp \<Rightarrow> exp"
  assumes supp_trans: "supp (trans a e) \<subseteq> supp e"
begin
  lemma supp_lift_transform: "supp (lift_transform trans a e) \<subseteq> supp e"
    by (cases "(trans, a, e)" rule:lift_transform.cases) (auto dest!: subsetD[OF supp_trans])

  lemma supp_map_transform: "supp (map_transform trans ae \<Gamma>) \<subseteq> supp \<Gamma>"
  unfolding map_transform_def
     by (induction \<Gamma>) (auto simp add: supp_Pair supp_Cons dest!: subsetD[OF supp_lift_transform])

  lemma fresh_transform[intro]: "a \<sharp> e \<Longrightarrow> a \<sharp> trans n e"
    by (auto simp add: fresh_def) (auto dest!: subsetD[OF supp_trans])

  lemma fresh_star_transform[intro]: "a \<sharp>* e \<Longrightarrow> a \<sharp>* trans n e"
    by (auto simp add: fresh_star_def)

  lemma fresh_map_transform[intro]: "a \<sharp> \<Gamma> \<Longrightarrow> a \<sharp> map_transform trans ae \<Gamma>"
    unfolding fresh_def using supp_map_transform by auto

  lemma fresh_star_map_transform[intro]: "a \<sharp>* \<Gamma> \<Longrightarrow> a \<sharp>* map_transform trans ae \<Gamma>"
    by (auto simp add: fresh_star_def)
end


end
