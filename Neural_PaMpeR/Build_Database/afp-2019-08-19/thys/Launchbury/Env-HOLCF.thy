theory "Env-HOLCF"
  imports Env "HOLCF-Utils"
begin

subsubsection \<open>Continuity and pcpo-valued functions\<close>

lemma  override_on_belowI:
  assumes "\<And> a. a \<in> S \<Longrightarrow> y a \<sqsubseteq> z a"
  and "\<And> a. a \<notin> S \<Longrightarrow> x a \<sqsubseteq> z a"
  shows  "x ++\<^bsub>S\<^esub> y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fun_belowI)
  apply (case_tac "xa \<in> S")
  apply auto
  done

lemma override_on_cont1: "cont (\<lambda> x. x ++\<^bsub>S\<^esub> m)"
  by (rule cont2cont_lambda) (auto simp add: override_on_def)

lemma override_on_cont2: "cont (\<lambda> x. m ++\<^bsub>S\<^esub> x)"
  by (rule cont2cont_lambda) (auto simp add: override_on_def)

lemma override_on_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. f x ++\<^bsub>S\<^esub> g x)"
by (rule cont_apply[OF assms(1) override_on_cont1 cont_compose[OF override_on_cont2 assms(2)]])

lemma override_on_mono:
  assumes "x1 \<sqsubseteq> (x2 :: 'a::type \<Rightarrow> 'b::cpo)"
  assumes "y1 \<sqsubseteq> y2"
  shows "x1 ++\<^bsub>S\<^esub> y1 \<sqsubseteq> x2 ++\<^bsub>S\<^esub> y2"
by (rule below_trans[OF cont2monofunE[OF override_on_cont1 assms(1)] cont2monofunE[OF override_on_cont2 assms(2)]])

lemma fun_upd_below_env_deleteI:
  assumes "env_delete x \<rho> \<sqsubseteq> env_delete x \<rho>'" 
  assumes "y \<sqsubseteq> \<rho>' x"
  shows  "\<rho>(x := y) \<sqsubseteq> \<rho>'"
  using assms
  apply (auto intro!: fun_upd_belowI   simp add: env_delete_def)
  by (metis fun_belowD fun_upd_other)

lemma fun_upd_belowI2:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> z \<sqsubseteq> \<rho>' z" 
  assumes "\<rho> x \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x := y)"
  apply (rule fun_belowI)
  using assms by auto

lemma env_restr_belowI:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> (m1 f|` S) x \<sqsubseteq> (m2 f|` S) x"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
  apply (rule fun_belowI)
  by (metis assms below_bottom_iff lookup_env_restr_not_there)

lemma env_restr_belowI2:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> m1 x \<sqsubseteq> m2 x"
  shows "m1 f|` S \<sqsubseteq> m2"
  by (rule fun_belowI)
     (simp add: assms env_restr_def)


lemma env_restr_below_itself:
  shows "m f|` S \<sqsubseteq> m"
  apply (rule fun_belowI)
  apply (case_tac "x \<in> S")
  apply auto
  done  

lemma env_restr_cont:  "cont (env_restr S)"
  apply (rule cont2cont_lambda)
  apply (case_tac "y \<in> S")
  apply auto
  done

lemma env_restr_belowD:
  assumes "m1 f|` S \<sqsubseteq> m2 f|` S"
  assumes "x \<in> S"
  shows "m1 x \<sqsubseteq> m2 x"
  using fun_belowD[OF assms(1), where x = x] assms(2) by simp

lemma env_restr_eqD:
  assumes "m1 f|` S = m2 f|` S"
  assumes "x \<in> S"
  shows "m1 x = m2  x"
  by (metis assms(1) assms(2) lookup_env_restr)

lemma env_restr_below_subset:
  assumes "S \<subseteq> S'"
  and "m1 f|` S' \<sqsubseteq> m2 f|` S'"
  shows "m1 f|` S \<sqsubseteq> m2 f|` S"
using assms
by (auto intro!: env_restr_belowI dest: env_restr_belowD)



lemma  override_on_below_restrI:
  assumes " x f|` (-S) \<sqsubseteq> z f|` (-S)"
  and "y f|` S \<sqsubseteq> z f|` S"
  shows  "x ++\<^bsub>S\<^esub> y \<sqsubseteq> z"
using assms
by (auto intro: override_on_belowI dest:env_restr_belowD)

lemma  fmap_below_add_restrI:
  assumes "x f|` (-S) \<sqsubseteq> y f|` (-S)"
  and     "x f|` S \<sqsubseteq> z f|` S"
  shows  "x \<sqsubseteq> y ++\<^bsub>S\<^esub> z"
using assms
by (auto intro!: fun_belowI dest:env_restr_belowD simp add: lookup_override_on_eq)

lemmas env_restr_cont2cont[simp,cont2cont] = cont_compose[OF env_restr_cont]

lemma env_delete_cont:  "cont (env_delete x)"
  apply (rule cont2cont_lambda)
  apply (case_tac "y = x")
  apply auto
  done
lemmas env_delete_cont2cont[simp,cont2cont] = cont_compose[OF env_delete_cont]


end
