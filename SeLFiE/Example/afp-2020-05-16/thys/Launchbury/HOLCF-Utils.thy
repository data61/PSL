theory "HOLCF-Utils"
  imports  HOLCF Pointwise
begin

default_sort type

lemmas cont_fun[simp]
lemmas cont2cont_fun[simp]

lemma cont_compose2:
  assumes "\<And> y. cont (\<lambda> x. c x y)"
  assumes "\<And> x. cont (\<lambda> y. c x y)"
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda>x. c (f x) (g x))"
  by (intro cont_apply[OF assms(4) assms(2)]
            cont2cont_fun[OF cont_compose[OF _ assms(3)]]
            cont2cont_lambda[OF assms(1)])

lemma pointwise_adm:
  fixes P :: "'a::pcpo \<Rightarrow> 'b::pcpo \<Rightarrow> bool"
  assumes "adm (\<lambda> x. P (fst x) (snd x))"
  shows "adm (\<lambda> m. pointwise P (fst m) (snd m))"
proof (rule admI, goal_cases)
  case prems: (1 Y)
  show ?case
    apply (rule pointwiseI)
    apply (rule admD[OF adm_subst[where t = "\<lambda>p . (fst p x, snd p x)" for x, OF _ assms, simplified] \<open>chain Y\<close>])
    using prems(2) unfolding pointwise_def apply auto
    done
qed

lemma cfun_beta_Pair:
  assumes "cont (\<lambda> p. f (fst p) (snd p))"
  shows "csplit\<cdot>(\<Lambda> a b . f a b)\<cdot>(x, y) = f x y"
  apply simp
  apply (subst beta_cfun)
  apply (rule cont2cont_LAM')
  apply (rule assms)
  apply (rule beta_cfun)
  apply (rule cont2cont_fun)
  using assms
  unfolding prod_cont_iff
  apply auto
  done


lemma fun_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x := v1) \<sqsubseteq> \<rho>2(x := v2)"
  apply (rule fun_belowI)
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fun_belowD)
  done

lemma fun_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. (f x)(v := h x) :: 'a \<Rightarrow> 'b::pcpo)"
  by (rule cont2cont_lambda)(auto simp add: assms)

lemma fun_upd_belowI:
  assumes "\<And> z . z \<noteq> x \<Longrightarrow> \<rho> z \<sqsubseteq> \<rho>' z" 
  assumes "y \<sqsubseteq> \<rho>' x"
  shows  "\<rho>(x := y) \<sqsubseteq> \<rho>'"
  apply (rule fun_belowI)
  using assms
  apply (case_tac "xa = x")
  apply auto
  done


lemma cont_if_else_above: 
  assumes "cont f"
  assumes "cont g"
  assumes "\<And> x. f x \<sqsubseteq> g x"
  assumes "\<And> x y. x \<sqsubseteq> y \<Longrightarrow> P y \<Longrightarrow> P x"
  assumes "adm P"
  shows "cont (\<lambda>x. if P x then f x else g x)" (is "cont ?I")
proof(intro contI2 monofunI)
  fix x y :: 'a
  assume "x \<sqsubseteq> y"
  with assms(4)[OF this]
  show "?I x \<sqsubseteq> ?I y"
    apply (auto)
    apply (rule cont2monofunE[OF assms(1)], assumption)
    apply (rule below_trans[OF cont2monofunE[OF assms(1)] assms(3)], assumption)
    apply (rule cont2monofunE[OF assms(2)], assumption)
    done
next
  fix Y :: "nat \<Rightarrow> 'a"
  assume "chain Y"
  assume "chain (\<lambda>i . ?I (Y i))"

  have ch_f: "f (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. f (Y i))" by (metis \<open>chain Y\<close> assms(1) below_refl cont2contlubE)

  show "?I (\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. ?I (Y i))" 
  proof(cases "\<forall> i. P (Y i)")
    case True hence "P (\<Squnion> i. Y i)" by (metis \<open>chain Y\<close> adm_def assms(5))
    with True ch_f show ?thesis by auto
  next
    case False
    then obtain j where "\<not> P (Y j)" by auto
    hence *:  "\<forall> i \<ge> j. \<not> P (Y i)" "\<not> P (\<Squnion> i. Y i)"
      apply (auto)
      apply (metis assms(4) chain_mono[OF \<open>chain Y\<close>])
      apply (metis assms(4) is_ub_thelub[OF \<open>chain Y\<close>])
      done

    have "?I (\<Squnion> i. Y i) = g (\<Squnion> i. Y i)" using * by simp
    also have "\<dots> = g (\<Squnion> i. Y (i + j))" by (metis lub_range_shift[OF \<open>chain Y\<close>])
    also have "\<dots> = (\<Squnion> i. (g (Y (i + j))))" by (rule cont2contlubE[OF assms(2) chain_shift[OF \<open>chain Y\<close>]] )
    also have "\<dots> = (\<Squnion> i. (?I (Y (i + j))))" using * by auto
    also have "\<dots> = (\<Squnion> i. (?I (Y i)))" by (metis lub_range_shift[OF \<open>chain (\<lambda>i . ?I (Y i))\<close>])
    finally show ?thesis by simp
  qed
qed

fun up2option :: "'a::cpo\<^sub>\<bottom> \<Rightarrow> 'a option"
  where "up2option Ibottom = None"
  |     "up2option (Iup a) = Some a"

lemma up2option_simps[simp]:
  "up2option \<bottom> = None"
  "up2option (up\<cdot>x) = Some x"
  unfolding up_def by (simp_all add: cont_Iup inst_up_pcpo)

fun option2up :: "'a option \<Rightarrow> 'a::cpo\<^sub>\<bottom>"
  where "option2up None = \<bottom>"
  |     "option2up (Some a) = up\<cdot>a"

lemma option2up_up2option[simp]:
  "option2up (up2option x) = x"
  by (cases x) auto
lemma up2option_option2up[simp]:
  "up2option (option2up x) = x"
  by (cases x) auto

lemma adm_subst2: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f (fst x) = g (snd x))"
  apply (rule admI)
  apply (simp add:
      cont2contlubE[where f = f]  cont2contlubE[where f = g]
      cont2contlubE[where f = snd]  cont2contlubE[where f = fst]
      )
  done


subsubsection \<open>Composition of fun and cfun\<close>

lemma cont2cont_comp [simp, cont2cont]:
  assumes "cont f"
  assumes "\<And> x. cont (f x)"
  assumes "cont g"
  shows "cont (\<lambda> x. (f x) \<circ> (g x))"
  unfolding comp_def
  by (rule cont2cont_lambda)
     (intro cont2cont  \<open>cont g\<close> \<open>cont f\<close> cont_compose2[OF cont2cont_fun[OF assms(1)] assms(2)] cont2cont_fun)

definition cfun_comp :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> ('c::type \<Rightarrow> 'a) \<rightarrow> ('c::type \<Rightarrow> 'b)"
  where  "cfun_comp = (\<Lambda> f \<rho>. (\<lambda> x. f\<cdot>x) \<circ> \<rho>)"

lemma [simp]: "cfun_comp\<cdot>f\<cdot>(\<rho>(x := v)) = (cfun_comp\<cdot>f\<cdot>\<rho>)(x := f\<cdot>v)"
  unfolding cfun_comp_def by auto

lemma cfun_comp_app[simp]: "(cfun_comp\<cdot>f\<cdot>\<rho>) x = f\<cdot>(\<rho> x)"
  unfolding cfun_comp_def by auto

lemma fix_eq_fix:
  "f\<cdot>(fix\<cdot>g) \<sqsubseteq> fix\<cdot>g \<Longrightarrow> g\<cdot>(fix\<cdot>f) \<sqsubseteq> fix\<cdot>f \<Longrightarrow> fix\<cdot>f = fix\<cdot>g"
  by (metis fix_least_below below_antisym)

subsubsection \<open>Additional transitivity rules\<close>

text \<open>
These collect side-conditions of the form @{term "cont f"}, so the usual way to discharge them
is to write @{text[source] "by this (intro cont2cont)+"} at the end.
\<close>

lemma below_trans_cong[trans]:
  "a \<sqsubseteq> f x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> cont f \<Longrightarrow> a \<sqsubseteq> f y "
by (metis below_trans cont2monofunE)

lemma not_bot_below_trans[trans]:
  "a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b \<Longrightarrow> b \<noteq> \<bottom>"
  by (metis below_bottom_iff)

lemma not_bot_below_trans_cong[trans]:
  "f a \<noteq> \<bottom> \<Longrightarrow> a \<sqsubseteq> b \<Longrightarrow> cont f \<Longrightarrow> f b \<noteq> \<bottom>"
  by (metis below_bottom_iff cont2monofunE)

end
