(* File:   Akra_Bazzi_Asymptotics.thy
   Author: Manuel Eberl <eberlm@in.tum.de>

   Proofs for the four(ish) asymptotic inequalities required for proving the
   Akra Bazzi theorem with variation functions in the recursive calls.
*)

section \<open>Asymptotic bounds\<close>
theory Akra_Bazzi_Asymptotics
imports
  Complex_Main
  Akra_Bazzi_Library
  "HOL-Library.Landau_Symbols"
begin

locale akra_bazzi_asymptotics_bep =
  fixes b e p hb :: real
  assumes bep: "b > 0" "b < 1" "e > 0" "hb > 0"
begin

context
begin

text \<open>
  Functions that are negligible w.r.t. @{term "ln (b*x) powr (e/2 + 1)"}.
\<close>
private abbreviation (input) negl :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "negl f \<equiv> f \<in> o(\<lambda>x. ln (b*x) powr (-(e/2 + 1)))"

private lemma neglD: "negl f \<Longrightarrow> c > 0 \<Longrightarrow> eventually (\<lambda>x. \<bar>f x\<bar> \<le> c / ln (b*x) powr (e/2+1)) at_top"
  by (drule (1) landau_o.smallD, subst (asm) powr_minus) (simp add: field_simps)

private lemma negl_mult: "negl f \<Longrightarrow> negl g \<Longrightarrow> negl (\<lambda>x. f x * g x)"
  by (erule landau_o.small_1_mult, rule landau_o.small_imp_big, erule landau_o.small_trans)
     (insert bep, simp)

private lemma ev4:
  assumes g: "negl g"
  shows   "eventually (\<lambda>x. ln (b*x) powr (-e/2) - ln x powr (-e/2) \<ge> g x) at_top"
proof (rule smallo_imp_le_real)
  define h1 where [abs_def]:
    "h1 x = (1 + ln b/ln x) powr (-e/2) - 1 + e/2 * (ln b/ln x)" for x
  define h2 where [abs_def]:
    "h2 x = ln x powr (- e / 2) * ((1 + ln b / ln x) powr (- e / 2) - 1)" for x
  from bep have "((\<lambda>x. ln b / ln x) \<longlongrightarrow> 0) at_top"
    by (simp add: tendsto_0_smallo_1)
  note one_plus_x_powr_Taylor2_bigo[OF this, of "-e/2"]
  also have "(\<lambda>x. (1 + ln b / ln x) powr (- e / 2) - 1 - - e / 2 * (ln b / ln x)) = h1"
    by (simp add: h1_def)
  finally have "h1 \<in> o(\<lambda>x. 1 / ln x)"
    by (rule landau_o.big_small_trans) (insert bep, simp add: power2_eq_square)
  with bep have "(\<lambda>x. h1 x - e/2 * (ln b / ln x)) \<in> \<Theta>(\<lambda>x. 1 / ln x)" by simp
  also have "(\<lambda>x. h1 x - e/2 * (ln b/ln x)) = (\<lambda>x. (1 + ln b/ ln x) powr (-e/2) - 1)"
    by (rule ext) (simp add: h1_def)
  finally have "h2 \<in> \<Theta>(\<lambda>x. ln x powr (-e/2) * (1 / ln x))" unfolding h2_def
    by (intro landau_theta.mult) simp_all
  also have "(\<lambda>x. ln x powr (-e/2) * (1 / ln x)) \<in> \<Theta>(\<lambda>x. ln x powr (-(e/2+1)))" by simp
  also from g bep have "(\<lambda>x. ln x powr (-(e/2+1))) \<in> \<omega>(g)" by (simp add: smallomega_iff_smallo)
  finally have "g \<in> o(h2)" by (simp add: smallomega_iff_smallo)
  also have "eventually (\<lambda>x. h2 x = ln (b*x) powr (-e/2) - ln x powr (-e/2)) at_top"
    using eventually_gt_at_top[of "1::real"] eventually_gt_at_top[of "1/b"]
    by eventually_elim (insert bep, simp add: field_simps powr_diff [symmetric]  h2_def
                                      ln_mult [symmetric] powr_divide del: ln_mult)
  hence "h2 \<in> \<Theta>(\<lambda>x. ln (b*x) powr (-e/2) - ln x powr (-e/2))" by (rule bigthetaI_cong)
  finally show "g \<in> o(\<lambda>x. ln (b * x) powr (- e / 2) - ln x powr (- e / 2))" .
next
  show "eventually (\<lambda>x. ln (b*x) powr (-e/2) - ln x powr (-e/2) \<ge> 0) at_top"
    using eventually_gt_at_top[of "1/b"] eventually_gt_at_top[of "1::real"]
    by eventually_elim (insert bep, auto intro!: powr_mono2' simp: field_simps simp del: ln_mult)
qed

private lemma ev1:
  "negl (\<lambda>x. (1 + c * inverse b * ln x powr (-(1+e))) powr p - 1)"
proof-
  from bep have "((\<lambda>x. c * inverse b * ln x powr (-(1+e))) \<longlongrightarrow> 0) at_top"
    by (simp add: tendsto_0_smallo_1)
  have "(\<lambda>x. (1 + c * inverse b * ln x powr (-(1+e))) powr p - 1)
           \<in> O(\<lambda>x. c * inverse b * ln x powr - (1 + e))"
    using bep by (intro one_plus_x_powr_Taylor1_bigo) (simp add: tendsto_0_smallo_1)
  also from bep have "negl (\<lambda>x. c * inverse b * ln x powr - (1 + e))" by simp
  finally show ?thesis .
qed

private lemma ev2_aux:
  defines "f \<equiv> \<lambda>x. (1 + 1/ln (b*x) * ln (1 + hb / b * ln x powr (-1-e))) powr (-e/2)"
  obtains h where "eventually (\<lambda>x. f x \<ge> 1 + h x) at_top" "h \<in> o(\<lambda>x. 1 / ln x)"
proof (rule that[of "\<lambda>x. f x - 1"])
  define g where [abs_def]: "g x = 1/ln (b*x) * ln (1 + hb / b * ln x powr (-1-e))" for x
  have lim: "((\<lambda>x. ln (1 + hb / b * ln x powr (- 1 - e))) \<longlongrightarrow> 0) at_top"
    by (rule tendsto_eq_rhs[OF tendsto_ln[OF tendsto_add[OF tendsto_const, of _ 0]]])
       (insert bep, simp_all add: tendsto_0_smallo_1)
  hence lim': "(g \<longlongrightarrow> 0) at_top" unfolding g_def
    by (intro tendsto_mult_zero) (insert bep, simp add: tendsto_0_smallo_1)
  from one_plus_x_powr_Taylor2_bigo[OF this, of "-e/2"]
    have "(\<lambda>x. (1 + g x) powr (-e/2) - 1 - - e/2 * g x) \<in> O(\<lambda>x. (g x)\<^sup>2)" .
  also from lim' have "(\<lambda>x. g x ^ 2) \<in> o(\<lambda>x. g x * 1)" unfolding power2_eq_square
    by (intro landau_o.big_small_mult smalloI_tendsto) simp_all
  also have "o(\<lambda>x. g x * 1) = o(g)" by simp
  also have "(\<lambda>x. (1 + g x) powr (-e/2) - 1 - - e/2 * g x) = (\<lambda>x. f x - 1 + e/2 * g x)"
    by (simp add: f_def g_def)
  finally have A: "(\<lambda>x. f x - 1 + e / 2 * g x) \<in> O(g)" by (rule landau_o.small_imp_big)
  hence "(\<lambda>x. f x - 1 + e/2 * g x - e/2 * g x) \<in> O(g)"
    by (rule sum_in_bigo) (insert bep, simp)
  also have "(\<lambda>x. f x - 1 + e/2 * g x - e/2 * g x) = (\<lambda>x. f x - 1)" by simp
  finally have "(\<lambda>x. f x - 1) \<in> O(g)" .
  also from bep lim have "g \<in> o(\<lambda>x. 1 / ln x)" unfolding g_def
    by (auto intro!: smallo_1_tendsto_0)
  finally show "(\<lambda>x. f x - 1) \<in> o(\<lambda>x. 1 / ln x)" .
qed simp_all

private lemma ev2:
  defines "f \<equiv> \<lambda>x. ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2)"
  obtains h where
    "negl h"
    "eventually (\<lambda>x. f x \<ge> ln (b * x) powr (-e/2) + h x) at_top"
    "eventually (\<lambda>x. \<bar>ln (b * x) powr (-e/2) + h x\<bar> < 1) at_top"
proof -
  define f'
    where "f' x = (1 + 1 / ln (b*x) * ln (1 + hb / b * ln x powr (-1-e))) powr (-e/2)" for x
  from ev2_aux obtain g where g: "eventually (\<lambda>x. 1 + g x \<le> f' x) at_top" "g \<in> o(\<lambda>x. 1 / ln x)"
    unfolding f'_def .
  define h where [abs_def]: "h x = ln (b*x) powr (-e/2) * g x" for x
  show ?thesis
  proof (rule that[of h])
    from bep g show "negl h" unfolding h_def
      by (auto simp: powr_diff elim: landau_o.small_big_trans)
  next
    from g(2) have "g \<in> o(\<lambda>x. 1)" by (rule landau_o.small_big_trans) simp
    with bep have "eventually (\<lambda>x. \<bar>ln (b*x) powr (-e/2) * (1 + g x)\<bar> < 1) at_top"
      by (intro smallo_imp_abs_less_real) simp_all
    thus "eventually (\<lambda>x. \<bar>ln (b*x) powr (-e/2) + h x\<bar> < 1) at_top"
      by (simp add: algebra_simps h_def)
  next
    from eventually_gt_at_top[of "1/b"] and g(1)
      show "eventually (\<lambda>x. f x \<ge> ln (b*x) powr (-e/2) + h x) at_top"
    proof eventually_elim
      case (elim x)
      from bep have "b * x + hb * x / ln x powr (1 + e) = b*x * (1 + hb / b * ln x powr (-1 - e))"
        by (simp add: field_simps powr_diff powr_add powr_minus)
      also from elim(1) bep
        have "ln \<dots> = ln (b*x) * (1 + 1/ln (b*x) * ln (1 + hb / b * ln x powr (-1-e)))"
        by (subst ln_mult) (simp_all add: add_pos_nonneg field_simps)
      also from elim(1) bep have "\<dots> powr (-e/2) = ln (b*x) powr (-e/2) * f' x"
        by (subst powr_mult) (simp_all add: field_simps f'_def)
      also from elim have "\<dots> \<ge> ln (b*x) powr (-e/2) * (1 + g x)"
        by (intro mult_left_mono) simp_all
      finally show "f x \<ge> ln (b*x) powr (-e/2) + h x"
        by (simp add: f_def h_def algebra_simps)
    qed
  qed
qed

private lemma ev21:
  obtains g where
    "negl g"
    "eventually (\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<ge>
         1 + ln (b * x) powr (-e/2) + g x) at_top"
    "eventually (\<lambda>x. 1 + ln (b * x) powr (-e/2) + g x > 0) at_top"
proof-
  from ev2 guess g . note g = this
  from g(3) have "eventually (\<lambda>x. 1 + ln (b * x) powr (-e/2) + g x > 0) at_top"
    by eventually_elim simp
  with g(1,2) show ?thesis by (intro that[of g]) simp_all
qed

private lemma ev22:
  obtains g where
    "negl g"
    "eventually (\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<le>
         1 - ln (b * x) powr (-e/2) - g x) at_top"
    "eventually (\<lambda>x. 1 - ln (b * x) powr (-e/2) - g x > 0) at_top"
proof-
  from ev2 guess g . note g = this
  from g(2) have "eventually (\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (-e/2) \<le>
                                      1 - ln (b * x) powr (-e/2) - g x) at_top"
    by eventually_elim simp
  moreover from g(3) have "eventually (\<lambda>x. 1 - ln (b * x) powr (-e/2) - g x > 0) at_top"
    by eventually_elim simp
  ultimately show ?thesis using g(1) by (intro that[of g]) simp_all
qed


lemma asymptotics1:
  shows "eventually (\<lambda>x.
             (1 + c * inverse b * ln x powr -(1+e)) powr p *
             (1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<ge>
             1 + (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 + c * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 + ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"
  define f where [abs_def]: "f x = 1 - ?f x" for x
  from ev1[of c] have "negl f" unfolding f_def
    by (subst landau_o.small.uminus_in_iff [symmetric]) simp
  from landau_o.smallD[OF this zero_less_one]
    have f: "eventually (\<lambda>x. f x \<le> ln (b*x) powr -(e/2+1)) at_top"
    by eventually_elim (simp add: f_def)

  from ev21 guess g . note g = this
  define h where [abs_def]: "h x = -g x + f x + f x * ln (b*x) powr (-e/2) + f x * g x" for x

  have A: "eventually (\<lambda>x. ?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x) at_top"
    using g(2,3) f
  proof eventually_elim
    case (elim x)
    let ?t = "ln (b*x) powr (-e/2)"
    have "1 + ?t - h x = (1 - f x) * (1 + ln (b*x) powr (-e/2) + g x)"
      by (simp add: algebra_simps h_def)
    also from elim have "?f x * ?g x \<ge> (1 - f x) * (1 + ln (b*x) powr (-e/2) + g x)"
      by (intro mult_mono[OF _ elim(1)]) (simp_all add: algebra_simps f_def)
    finally show "?f x * ?g x \<ge> 1 + ln (b*x) powr (-e/2) - h x" .
  qed
  from bep \<open>negl f\<close> g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_diff
                  intro: landau_o.small_trans)+
  from ev4[OF this] A show ?thesis by eventually_elim simp
qed

lemma asymptotics2:
  shows "eventually (\<lambda>x.
             (1 + c * inverse b * ln x powr -(1+e)) powr p *
             (1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)) \<le>
             1 - (ln x powr (-e/2))) at_top"
proof-
  let ?f = "\<lambda>x. (1 + c * inverse b * ln x powr -(1+e)) powr p"
  let ?g = "\<lambda>x. 1 - ln (b * x + hb * x / ln x powr (1 + e)) powr (- e / 2)"

  define f where [abs_def]: "f x = 1 - ?f x" for x
  from ev1[of c] have "negl f" unfolding f_def
    by (subst landau_o.small.uminus_in_iff [symmetric]) simp
  from landau_o.smallD[OF this zero_less_one]
    have f: "eventually (\<lambda>x. f x \<le> ln (b*x) powr -(e/2+1)) at_top"
    by eventually_elim (simp add: f_def)

  from ev22 guess g . note g = this
  define h where [abs_def]: "h x = -g x - f x + f x * ln (b*x) powr (-e/2) + f x * g x" for x
  have "((\<lambda>x. ln (b * x + hb * x / ln x powr (1 + e)) powr - (e / 2)) \<longlongrightarrow> 0) at_top"
    apply (insert bep, intro tendsto_neg_powr, simp)
    apply (rule filterlim_compose[OF ln_at_top])
    apply (rule filterlim_at_top_smallomega_1, simp)
    using eventually_gt_at_top[of "max 1 (1/b)"]
    apply (auto elim!: eventually_mono intro!: add_pos_nonneg simp: field_simps)
    done
  hence ev_g: "eventually (\<lambda>x. \<bar>1 - ?g x\<bar> < 1) at_top"
    by (intro smallo_imp_abs_less_real smalloI_tendsto) simp_all

  have A: "eventually (\<lambda>x. ?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x) at_top"
    using g(2,3) ev_g f
  proof eventually_elim
    case (elim x)
    let ?t = "ln (b*x) powr (-e/2)"
    from elim have "?f x * ?g x \<le> (1 - f x) * (1 - ln (b*x) powr (-e/2) - g x)"
      by (intro mult_mono) (simp_all add: f_def)
    also have "... = 1 - ?t + h x" by (simp add: algebra_simps h_def)
    finally show "?f x * ?g x \<le> 1 - ln (b*x) powr (-e/2) + h x" .
  qed
  from bep \<open>negl f\<close> g(1) have "negl h" unfolding h_def
    by (fastforce intro!: sum_in_smallo landau_o.small.mult simp: powr_diff
                  intro: landau_o.small_trans)+
  from ev4[OF this] A show ?thesis by eventually_elim simp
qed

lemma asymptotics3: "eventually (\<lambda>x. (1 + (ln x powr (-e/2))) / 2 \<le> 1) at_top"
  (is "eventually (\<lambda>x. ?f x \<le> 1) _")
proof (rule eventually_mp[OF always_eventually], clarify)
  from bep have "(?f \<longlongrightarrow> 1/2) at_top"
    by (force intro: tendsto_eq_intros tendsto_neg_powr ln_at_top)
  hence "\<And>e. e>0 \<Longrightarrow> eventually (\<lambda>x. \<bar>?f x - 0.5\<bar> < e) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  from this[of "0.5"] show "eventually (\<lambda>x. \<bar>?f x - 0.5\<bar> < 0.5) at_top" by simp
  fix x assume "\<bar>?f x - 0.5\<bar> < 0.5"
  thus "?f x \<le> 1" by simp
qed

lemma asymptotics4: "eventually (\<lambda>x. (1 - (ln x powr (-e/2))) * 2 \<ge> 1) at_top"
  (is "eventually (\<lambda>x. ?f x \<ge> 1) _")
proof (rule eventually_mp[OF always_eventually], clarify)
  from bep have "(?f \<longlongrightarrow> 2) at_top"
    by (force intro: tendsto_eq_intros tendsto_neg_powr ln_at_top)
  hence "\<And>e. e>0 \<Longrightarrow> eventually (\<lambda>x. \<bar>?f x - 2\<bar> < e) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  from this[of 1] show "eventually (\<lambda>x. \<bar>?f x - 2\<bar> < 1) at_top" by simp
  fix x assume "\<bar>?f x - 2\<bar> < 1"
  thus "?f x \<ge> 1" by simp
qed

lemma asymptotics5: "eventually (\<lambda>x. ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2) < 1) at_top"
proof-
  from bep have "((\<lambda>x. b - hb * ln x powr -(1+e)) \<longlongrightarrow> b - 0) at_top"
    by (intro tendsto_intros tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp_all
  hence "LIM x at_top. (b - hb * ln x powr -(1+e)) * x :> at_top"
    by (rule filterlim_tendsto_pos_mult_at_top[OF _ _ filterlim_ident], insert bep) simp_all
  also have "(\<lambda>x. (b - hb * ln x powr -(1+e)) * x) = (\<lambda>x. b*x - hb*x*ln x powr -(1+e))"
    by (intro ext) (simp add: algebra_simps)
  finally have "filterlim ... at_top at_top" .
  with bep have "((\<lambda>x. ln (b*x - hb*x*ln x powr -(1+e)) powr -(e/2)) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_neg_powr filterlim_compose[OF ln_at_top]) simp_all
  hence "eventually (\<lambda>x. \<bar>ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2)\<bar> < 1) at_top"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  thus ?thesis by simp
qed

lemma asymptotics6: "eventually (\<lambda>x. hb / ln x powr (1 + e) < b/2) at_top"
  and asymptotics7: "eventually (\<lambda>x. hb / ln x powr (1 + e) < (1 - b) / 2) at_top"
  and asymptotics8: "eventually (\<lambda>x. x*(1 - b - hb / ln x powr (1 + e)) > 1) at_top"
proof-
  from bep have A: "(\<lambda>x. hb / ln x powr (1 + e)) \<in> o(\<lambda>_. 1)" by simp
  from bep have B: "b/3 > 0" and C: "(1 - b)/3 > 0" by simp_all
  from landau_o.smallD[OF A B] show "eventually (\<lambda>x. hb / ln x powr (1+e) < b/2) at_top"
    by eventually_elim (insert bep, simp)
  from landau_o.smallD[OF A C] show "eventually (\<lambda>x. hb / ln x powr (1 + e) < (1 - b)/2) at_top"
    by eventually_elim (insert bep, simp)

  from bep have "(\<lambda>x. hb / ln x powr (1 + e)) \<in> o(\<lambda>_. 1)" "(1 - b) / 2 > 0" by simp_all
  from landau_o.smallD[OF this] eventually_gt_at_top[of "1::real"]
    have A: "eventually (\<lambda>x. 1 - b - hb / ln x powr (1 + e) > 0) at_top"
    by eventually_elim (insert bep, simp add: field_simps)
  from bep have "(\<lambda>x. x * (1 - b - hb / ln x powr (1+e))) \<in> \<omega>(\<lambda>_. 1)" "(0::real) < 2" by simp_all
  from landau_omega.smallD[OF this] A eventually_gt_at_top[of "0::real"]
    show "eventually (\<lambda>x. x*(1 - b - hb / ln x powr (1 + e)) > 1) at_top"
    by eventually_elim (simp_all add: abs_mult)
qed

end
end


definition "akra_bazzi_asymptotic1 b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic1' b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 + ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
  \<ge> 1 + (ln x powr (-e/2) :: real)"
definition "akra_bazzi_asymptotic2 b hb e p x \<longleftrightarrow>
  (1 + hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic2' b hb e p x \<longleftrightarrow>
  (1 - hb * inverse b * ln x powr -(1+e)) powr p * (1 - ln (b*x + hb*x/ln x powr (1+e)) powr (-e/2))
      \<le> 1 - ln x powr (-e/2 :: real)"
definition "akra_bazzi_asymptotic3 e x \<longleftrightarrow> (1 + (ln x powr (-e/2))) / 2 \<le> (1::real)"
definition "akra_bazzi_asymptotic4 e x \<longleftrightarrow> (1 - (ln x powr (-e/2))) * 2 \<ge> (1::real)"
definition "akra_bazzi_asymptotic5 b hb e x \<longleftrightarrow>
  ln (b*x - hb*x*ln x powr -(1+e)) powr (-e/2::real) < 1"

definition "akra_bazzi_asymptotic6 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < b/2"
definition "akra_bazzi_asymptotic7 b hb e x \<longleftrightarrow> hb / ln x powr (1 + e :: real) < (1 - b) / 2"
definition "akra_bazzi_asymptotic8 b hb e x \<longleftrightarrow> x*(1 - b - hb / ln x powr (1 + e :: real)) > 1"

definition "akra_bazzi_asymptotics b hb e p x \<longleftrightarrow>
  akra_bazzi_asymptotic1 b hb e p x \<and> akra_bazzi_asymptotic1' b hb e p x \<and>
  akra_bazzi_asymptotic2 b hb e p x \<and> akra_bazzi_asymptotic2' b hb e p x \<and>
  akra_bazzi_asymptotic3 e x \<and> akra_bazzi_asymptotic4 e x \<and> akra_bazzi_asymptotic5 b hb e x \<and>
  akra_bazzi_asymptotic6 b hb e x \<and> akra_bazzi_asymptotic7 b hb e x \<and>
  akra_bazzi_asymptotic8 b hb e x"

lemmas akra_bazzi_asymptotic_defs =
  akra_bazzi_asymptotic1_def akra_bazzi_asymptotic1'_def
  akra_bazzi_asymptotic2_def akra_bazzi_asymptotic2'_def akra_bazzi_asymptotic3_def
  akra_bazzi_asymptotic4_def akra_bazzi_asymptotic5_def akra_bazzi_asymptotic6_def
  akra_bazzi_asymptotic7_def akra_bazzi_asymptotic8_def akra_bazzi_asymptotics_def

lemma akra_bazzi_asymptotics:
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"
  assumes "hb > 0" "e > 0"
  shows "eventually (\<lambda>x. \<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) at_top"
proof (intro eventually_ball_finite ballI)
  fix b assume "b \<in> set bs"
  with assms interpret akra_bazzi_asymptotics_bep b e p hb by unfold_locales auto
  show "eventually (\<lambda>x. akra_bazzi_asymptotics b hb e p x) at_top"
    unfolding akra_bazzi_asymptotic_defs
    using asymptotics1[of "-c" for c] asymptotics2[of "-c" for c]
    by (intro eventually_conj asymptotics1 asymptotics2 asymptotics3
              asymptotics4 asymptotics5 asymptotics6 asymptotics7 asymptotics8) simp_all
qed simp

end
