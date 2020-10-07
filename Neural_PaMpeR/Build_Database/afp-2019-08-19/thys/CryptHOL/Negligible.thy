(* Title: Negligible.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Negligibility\<close>

theory Negligible imports
  Complex_Main
  Landau_Symbols.Landau_More
begin

named_theorems negligible_intros

definition negligible :: "(nat \<Rightarrow> real) \<Rightarrow> bool" (* TODO: generalise types? *)
where "negligible f \<longleftrightarrow> (\<forall>c>0. f \<in> o(\<lambda>x. inverse (x powr c)))"

lemma negligibleI [intro?]:
  "(\<And>c. c > 0 \<Longrightarrow> f \<in> o(\<lambda>x. inverse (x powr c))) \<Longrightarrow> negligible f"
unfolding negligible_def by(simp)

lemma negligibleD:
  "\<lbrakk> negligible f; c > 0 \<rbrakk> \<Longrightarrow> f \<in> o(\<lambda>x. inverse (x powr c))"
unfolding negligible_def by(simp)

lemma negligibleD_real:
  assumes "negligible f"
  shows "f \<in> o(\<lambda>x. inverse (x powr c))"
proof -
  let ?c = "max 1 c"
  have "f \<in> o(\<lambda>x. inverse (x powr ?c))" using assms by(rule negligibleD) simp
  also have "(\<lambda>x. x powr c) \<in> O(\<lambda>x. real x powr max 1 c)"
    by(rule bigoI[where c=1])(auto simp add: eventually_at_top_linorder intro!: exI[where x=1] powr_mono)
  then have "(\<lambda>x. inverse (real x powr max 1 c)) \<in> O(\<lambda>x. inverse (x powr c))"
    by(auto simp add: eventually_at_top_linorder exI[where x=1] intro: landau_o.big.inverse)
  finally show ?thesis .
qed

lemma negligible_mono: "\<lbrakk> negligible g; f \<in> O(g) \<rbrakk> \<Longrightarrow> negligible f"
by(rule negligibleI)(drule (1) negligibleD; erule (1) landau_o.big_small_trans)

lemma negligible_le: "\<lbrakk> negligible g; \<And>\<eta>. \<bar>f \<eta>\<bar> \<le> g \<eta> \<rbrakk> \<Longrightarrow> negligible f"
by(erule negligible_mono)(force intro: order_trans intro!: eventually_sequentiallyI landau_o.big_mono)

lemma negligible_K0 [negligible_intros, simp, intro!]: "negligible (\<lambda>_. 0)"
by(rule negligibleI) simp

lemma negligible_0 [negligible_intros, simp, intro!]: "negligible 0"
by(simp add: zero_fun_def)

lemma negligible_const_iff [simp]: "negligible (\<lambda>_. c :: real) \<longleftrightarrow> c = 0"
by(auto simp add: negligible_def const_smallo_inverse_powr filterlim_real_sequentially dest!: spec[where x=1])

lemma not_negligible_1: "\<not> negligible (\<lambda>_. 1 :: real)"
by simp

lemma negligible_plus [negligible_intros]:
  "\<lbrakk> negligible f; negligible g \<rbrakk> \<Longrightarrow> negligible (\<lambda>\<eta>. f \<eta> + g \<eta>)"
by(auto intro!: negligibleI dest!: negligibleD intro: sum_in_smallo)

lemma negligible_uminus [simp]: "negligible (\<lambda>\<eta>. - f \<eta>) \<longleftrightarrow> negligible f"
by(simp add: negligible_def)

lemma negligible_uminusI [negligible_intros]: "negligible f \<Longrightarrow> negligible (\<lambda>\<eta>. - f \<eta>)"
by simp

lemma negligible_minus [negligible_intros]:
  "\<lbrakk> negligible f; negligible g \<rbrakk> \<Longrightarrow> negligible (\<lambda>\<eta>. f \<eta> - g \<eta>)"
by(auto simp add: uminus_add_conv_diff[symmetric] negligible_plus simp del: uminus_add_conv_diff)

lemma negligible_cmult: "negligible (\<lambda>\<eta>. c * f \<eta>) \<longleftrightarrow> negligible f \<or> c = 0"
by(auto intro!: negligibleI dest!: negligibleD)

lemma negligible_cmultI [negligible_intros]:
  "(c \<noteq> 0 \<Longrightarrow> negligible f) \<Longrightarrow> negligible (\<lambda>\<eta>. c * f \<eta>)"
by(auto simp add: negligible_cmult)

lemma negligible_multc: "negligible (\<lambda>\<eta>. f \<eta> * c) \<longleftrightarrow> negligible f \<or> c = 0"
by(subst mult.commute)(simp add: negligible_cmult)

lemma negligible_multcI [negligible_intros]:
  "(c \<noteq> 0 \<Longrightarrow> negligible f) \<Longrightarrow> negligible (\<lambda>\<eta>. f \<eta> * c)"
by(auto simp add: negligible_multc)

lemma negligible_times [negligible_intros]:
  assumes f: "negligible f"
  and g: "negligible g"
  shows "negligible (\<lambda>\<eta>. f \<eta> * g \<eta> :: real)"
proof
  fix c :: real
  assume "0 < c"
  hence "0 < c / 2" by simp
  from negligibleD[OF f this] negligibleD[OF g this]
  have "(\<lambda>\<eta>. f \<eta> * g \<eta>) \<in> o(\<lambda>x. inverse (x powr (c / 2)) * inverse (x powr (c / 2)))"
    by(rule landau_o.small_mult)
  also have "\<dots> = o(\<lambda>x. inverse (x powr c))"
    by(rule landau_o.small.cong)(auto simp add: inverse_mult_distrib[symmetric] powr_add[symmetric] eventually_at_top_linorder intro!: exI[where x=1] simp del: inverse_mult_distrib)
  finally show "(\<lambda>\<eta>. f \<eta> * g \<eta>) \<in> \<dots>" .
qed

lemma negligible_power [negligible_intros]:
  assumes "negligible f"
  and "n > 0"
  shows "negligible (\<lambda>\<eta>. f \<eta> ^ n :: real)"
using \<open>n > 0\<close>
proof(induct n)
  case (Suc n)
  thus ?case using \<open>negligible f\<close> by(cases n)(simp_all add: negligible_times)
qed simp

lemma negligible_powr [negligible_intros]:
  assumes f: "negligible f"
  and p: "p > 0"         
  shows "negligible (\<lambda>x. \<bar>f x\<bar> powr p :: real)"
proof
  fix c :: real
  let ?c = "c / p"
  assume c: "0 < c"
  with p have "0 < ?c" by simp
  with f have "f \<in> o(\<lambda>x. inverse (x powr ?c))" by(rule negligibleD)
  hence "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o(\<lambda>x. \<bar>inverse (x powr ?c)\<bar> powr p)" using p by(rule smallo_powr)
  also have "\<dots> = o(\<lambda>x. inverse (x powr c))"
    apply(rule landau_o.small.cong) using p by(auto simp add: powr_powr)
  finally show "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> \<dots>" .
qed

lemma negligible_abs [simp]: "negligible (\<lambda>x. \<bar>f x\<bar>) \<longleftrightarrow> negligible f"
by(simp add: negligible_def)

lemma negligible_absI [negligible_intros]: "negligible f \<Longrightarrow> negligible (\<lambda>x. \<bar>f x\<bar>)"
by(simp)

lemma negligible_powrI [negligible_intros]:
  assumes "0 \<le> k" "k < 1"
  shows "negligible (\<lambda>x. k powr x)"
proof(cases "k = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof
    fix c :: real
    assume "0 < c"
    then have "(\<lambda>x. real x powr c) \<in> o(\<lambda>x. inverse k powr real x)" using assms False
      by(intro powr_fast_growth_tendsto)(simp_all add: one_less_inverse_iff filterlim_real_sequentially)
    then have "(\<lambda>x. inverse (k powr - real x)) \<in> o(\<lambda>x. inverse (real x powr c))" using assms
      by(intro landau_o.small.inverse)(auto simp add: False eventually_sequentially powr_minus intro: exI[where x=1])
    also have "(\<lambda>x. inverse (k powr - real x)) = (\<lambda>x. k powr real x)" by(simp add: powr_minus)
    finally show "\<dots> \<in> o(\<lambda>x. inverse (x powr c))" .
  qed
qed

lemma negligible_powerI [negligible_intros]:
  fixes k :: real
  assumes "\<bar>k\<bar> < 1"
  shows "negligible (\<lambda>n. k ^ n)"
proof(cases "k = 0")
  case True
  show ?thesis using negligible_K0
    by(rule negligible_mono)(auto intro: exI[where x=1] simp add: True eventually_at_top_linorder)
next
  case False
  hence "0 < \<bar>k\<bar>" by auto
  from assms have "negligible (\<lambda>x. \<bar>k\<bar> powr real x)" using negligible_powrI[of "\<bar>k\<bar>"] by simp
  hence "negligible (\<lambda>x. \<bar>k\<bar> ^ x)" using False
    by(elim negligible_mono)(simp add: powr_realpow)
  then show ?thesis by(simp add: power_abs[symmetric])
qed

lemma negligible_inverse_powerI [negligible_intros]: "\<bar>k\<bar> > 1 \<Longrightarrow> negligible (\<lambda>\<eta>. 1 / k ^ \<eta>)"
using negligible_powerI[of "1 / k"] by(simp add: power_one_over)

inductive polynomial :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  for f
where "f \<in> O(\<lambda>x. x powr n) \<Longrightarrow> polynomial f"

lemma negligible_times_poly:
  assumes f: "negligible f"
  and g: "g \<in> O(\<lambda>x. x powr n)"
  shows "negligible (\<lambda>x. f x * g x)"
proof
  fix c :: real
  assume c: "0 < c"
  from negligibleD_real[OF f] g
  have "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. inverse (x powr (c + n)) * x powr n)"
    by(rule landau_o.small_big_mult)
  also have "\<dots> = o(\<lambda>x. inverse (x powr c))"
    by(rule landau_o.small.cong)(auto simp add: powr_minus[symmetric] powr_add[symmetric] intro!: exI[where x=0])
  finally show "(\<lambda>x. f x * g x) \<in> o(\<lambda>x. inverse (x powr c))" .
qed

lemma negligible_poly_times:
  "\<lbrakk> f \<in> O(\<lambda>x. x powr n); negligible g \<rbrakk> \<Longrightarrow> negligible (\<lambda>x. f x * g x)"
by(subst mult.commute)(rule negligible_times_poly)

lemma negligible_times_polynomial [negligible_intros]:
  "\<lbrakk> negligible f; polynomial g \<rbrakk> \<Longrightarrow> negligible (\<lambda>x. f x * g x)"
by(clarsimp simp add: polynomial.simps negligible_times_poly)

lemma negligible_polynomial_times [negligible_intros]:
  "\<lbrakk> polynomial f; negligible g \<rbrakk> \<Longrightarrow> negligible (\<lambda>x. f x * g x)"
by(clarsimp simp add: polynomial.simps negligible_poly_times)

lemma negligible_divide_poly1:
  "\<lbrakk> f \<in> O(\<lambda>x. x powr n); negligible (\<lambda>\<eta>. 1 / g \<eta>) \<rbrakk> \<Longrightarrow> negligible (\<lambda>\<eta>. real (f \<eta>) / g \<eta>)"
by(drule (1) negligible_times_poly) simp

lemma negligible_divide_polynomial1 [negligible_intros]:
  "\<lbrakk> polynomial f; negligible (\<lambda>\<eta>. 1 / g \<eta>) \<rbrakk> \<Longrightarrow> negligible (\<lambda>\<eta>. real (f \<eta>) / g \<eta>)"
by(clarsimp simp add: polynomial.simps negligible_divide_poly1)

end
