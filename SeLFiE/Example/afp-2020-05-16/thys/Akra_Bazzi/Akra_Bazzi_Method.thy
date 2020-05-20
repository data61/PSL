(*
  File:   Akra_Bazzi_Method.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Provides the "master_theorem" and "akra_bazzi_termination" proof methods.
*)
section \<open>The proof methods\<close>
subsection \<open>Master theorem and termination\<close>
theory Akra_Bazzi_Method
imports 
  Complex_Main
  Akra_Bazzi
  Master_Theorem
  Eval_Numeral
begin

lemma landau_symbol_ge_3_cong:
  assumes "landau_symbol L L' Lr"
  assumes "\<And>x::'a::linordered_semidom. x \<ge> 3 \<Longrightarrow> f x = g x"
  shows   "L at_top (f) = L at_top (g)"
apply (rule landau_symbol.cong[OF assms(1)])
apply (subst eventually_at_top_linorder, rule exI[of _ 3], simp add: assms(2))
done

lemma exp_1_lt_3: "exp (1::real) < 3"
proof-
  from Taylor_up[of 3 "\<lambda>_. exp" exp 0 1 0] 
    obtain t :: real where "t > 0" "t < 1" "exp 1 = 5/2 + exp t / 6" by (auto simp: eval_nat_numeral)
  note this(3)
  also from \<open>t < 1\<close> have "exp t < exp 1" by simp
  finally show "exp (1::real) < 3" by (simp add: field_simps)
qed

lemma ln_ln_pos:
  assumes "(x::real) \<ge> 3"
  shows   "ln (ln x) > 0"
proof (subst ln_gt_zero_iff)
  from assms exp_1_lt_3 have "ln x > ln (exp 1)" by (intro ln_mono_strict) simp_all
  thus "ln x > 0" "ln x > 1" by simp_all
qed

definition akra_bazzi_terms where
  "akra_bazzi_terms x\<^sub>0 x\<^sub>1 bs ts = (\<forall>i<length bs. akra_bazzi_term x\<^sub>0 x\<^sub>1 (bs!i) (ts!i))"

lemma akra_bazzi_termsI:
  "(\<And>i. i < length bs \<Longrightarrow> akra_bazzi_term x\<^sub>0 x\<^sub>1 (bs!i) (ts!i)) \<Longrightarrow> akra_bazzi_terms x\<^sub>0 x\<^sub>1 bs ts"
  unfolding akra_bazzi_terms_def by blast

lemma master_theorem_functionI:
  assumes "\<forall>x\<in>{x\<^sub>0..<x\<^sub>1}. f x \<ge> 0"
  assumes "\<forall>x\<ge>x\<^sub>1. f x = g x + (\<Sum>i<k. as ! i * f ((ts ! i) x))"
  assumes "\<forall>x\<ge>x\<^sub>1. g x \<ge> 0"
  assumes "\<forall>a\<in>set as. a \<ge> 0"
  assumes "list_ex (\<lambda>a. a > 0) as"
  assumes "\<forall>b\<in>set bs. b \<in> {0<..<1}"
  assumes "k \<noteq> 0"
  assumes "length as = k"
  assumes "length bs = k"
  assumes "length ts = k"
  assumes "akra_bazzi_terms x\<^sub>0 x\<^sub>1 bs ts"
  shows "master_theorem_function x\<^sub>0 x\<^sub>1 k as bs ts f g"
using assms unfolding akra_bazzi_terms_def by unfold_locales (auto simp: list_ex_iff)

lemma akra_bazzi_term_measure:
  " x \<ge> x\<^sub>1 \<Longrightarrow> akra_bazzi_term 0 x\<^sub>1 b t \<Longrightarrow> (t x, x) \<in> Wellfounded.measure (\<lambda>n::nat. n)"
  " x > x\<^sub>1 \<Longrightarrow> akra_bazzi_term 0 (Suc x\<^sub>1) b t \<Longrightarrow> (t x, x) \<in> Wellfounded.measure (\<lambda>n::nat. n)"
  unfolding akra_bazzi_term_def by auto

lemma measure_prod_conv: 
  "((a, b), (c, d)) \<in> Wellfounded.measure (\<lambda>x. t (fst x)) \<longleftrightarrow> (a, c) \<in> Wellfounded.measure t"
  "((e, f), (g, h)) \<in> Wellfounded.measure (\<lambda>x. t (snd x)) \<longleftrightarrow> (f, h) \<in> Wellfounded.measure t"
by simp_all

lemmas measure_prod_conv' = measure_prod_conv[where t = "\<lambda>x. x"]

lemma akra_bazzi_termination_simps:
  fixes x :: nat
  shows "a * real x / b = a/b * real x" "real x / b = 1/b * real x"
  by simp_all

lemma akra_bazzi_params_nonzeroI:
  "length as = length bs \<Longrightarrow>  
   (\<forall>a\<in>set as. a \<ge> 0) \<Longrightarrow> (\<forall>b\<in>set bs. b \<in> {0<..<1}) \<Longrightarrow> (\<exists>a\<in>set as. a > 0) \<Longrightarrow>
   akra_bazzi_params_nonzero (length as) as bs" by (unfold_locales, simp_all) []

lemmas akra_bazzi_p_rel_intros = 
  akra_bazzi_params_nonzero.p_lessI[rotated, OF _ akra_bazzi_params_nonzeroI]
  akra_bazzi_params_nonzero.p_greaterI[rotated, OF _ akra_bazzi_params_nonzeroI]
  akra_bazzi_params_nonzero.p_leI[rotated, OF _ akra_bazzi_params_nonzeroI]
  akra_bazzi_params_nonzero.p_geI[rotated, OF _ akra_bazzi_params_nonzeroI]
  akra_bazzi_params_nonzero.p_boundsI[rotated, OF _ akra_bazzi_params_nonzeroI]
  akra_bazzi_params_nonzero.p_boundsI'[rotated, OF _ akra_bazzi_params_nonzeroI]

lemma eval_length: "length [] = 0" "length (x # xs) = Suc (length xs)" by simp_all

lemma eval_akra_bazzi_sum:
  "(\<Sum>i<0. as!i * bs!i powr x) = 0"
  "(\<Sum>i<Suc 0. (a#as)!i * (b#bs)!i powr x) = a * b powr x"
  "(\<Sum>i<Suc k. (a#as)!i * (b#bs)!i powr x) = a * b powr x + (\<Sum>i<k. as!i * bs!i powr x)"
  apply simp
  apply simp
  apply (induction k arbitrary: a as b bs)
  apply simp_all
  done

lemma eval_akra_bazzi_sum':
  "(\<Sum>i<0. as!i * f ((ts!i) x)) = 0"
  "(\<Sum>i<Suc 0. (a#as)!i * f (((t#ts)!i) x)) = a * f (t x)"
  "(\<Sum>i<Suc k. (a#as)!i * f (((t#ts)!i) x)) = a * f (t x) + (\<Sum>i<k. as!i * f ((ts!i) x))"
  apply simp
  apply simp
  apply (induction k arbitrary: a as t ts)
  apply (simp_all add: algebra_simps)
  done

lemma akra_bazzi_termsI':
  "akra_bazzi_terms x\<^sub>0 x\<^sub>1 [] []"
  "akra_bazzi_term x\<^sub>0 x\<^sub>1 b t \<Longrightarrow> akra_bazzi_terms x\<^sub>0 x\<^sub>1 bs ts \<Longrightarrow> akra_bazzi_terms x\<^sub>0 x\<^sub>1 (b#bs) (t#ts)"
unfolding akra_bazzi_terms_def using less_Suc_eq_0_disj by auto

lemma ball_set_intros: "(\<forall>x\<in>set []. P x)" "P x \<Longrightarrow> (\<forall>x\<in>set xs. P x) \<Longrightarrow> (\<forall>x\<in>set (x#xs). P x)"
  by auto

lemma ball_set_simps: "(\<forall>x\<in>set []. P x) = True" "(\<forall>x\<in>set (x#xs). P x) = (P x \<and> (\<forall>x\<in>set xs. P x))"
  by auto

lemma bex_set_simps: "(\<exists>x\<in>set []. P x) = False" "(\<exists>x\<in>set (x#xs). P x) = (P x \<or> (\<exists>x\<in>set xs. P x))"
  by auto

lemma eval_akra_bazzi_le_list_ex:
  "list_ex P (x#y#xs) \<longleftrightarrow> P x \<or> list_ex P (y#xs)"
  "list_ex P [x] \<longleftrightarrow> P x"
  "list_ex P [] \<longleftrightarrow> False"
  by (auto simp: list_ex_iff)

lemma eval_akra_bazzi_le_sum_list:
  "x \<le> sum_list [] \<longleftrightarrow> x \<le> 0" "x \<le> sum_list (y#ys) \<longleftrightarrow> x \<le> y + sum_list ys"
  "x \<le> z + sum_list [] \<longleftrightarrow> x \<le> z" "x \<le> z + sum_list (y#ys) \<longleftrightarrow> x \<le> z + y + sum_list ys"
  by (simp_all add: algebra_simps)

lemma atLeastLessThanE: "x \<in> {a..<b} \<Longrightarrow> (x \<ge> a \<Longrightarrow> x < b \<Longrightarrow> P) \<Longrightarrow> P" by simp

lemma master_theorem_preprocess:
  "\<Theta>(\<lambda>n::nat. 1) = \<Theta>(\<lambda>n::nat. real n powr 0)"
  "\<Theta>(\<lambda>n::nat. real n) = \<Theta>(\<lambda>n::nat. real n powr 1)"
  "O(\<lambda>n::nat. 1) = O(\<lambda>n::nat. real n powr 0)"
  "O(\<lambda>n::nat. real n) = O(\<lambda>n::nat. real n powr 1)"

  "\<Theta>(\<lambda>n::nat. ln (ln (real n))) = \<Theta>(\<lambda>n::nat. real n powr 0 * ln (ln (real n)))"
  "\<Theta>(\<lambda>n::nat. real n * ln (ln (real n))) = \<Theta>(\<lambda>n::nat. real n powr 1 * ln (ln (real n)))"

  "\<Theta>(\<lambda>n::nat. ln (real n)) = \<Theta>(\<lambda>n::nat. real n powr 0 * ln (real n) powr 1)"
  "\<Theta>(\<lambda>n::nat. real n * ln (real n)) = \<Theta>(\<lambda>n::nat. real n powr 1 * ln (real n) powr 1)"
  "\<Theta>(\<lambda>n::nat. real n powr p * ln (real n)) = \<Theta>(\<lambda>n::nat. real n powr p * ln (real n) powr 1)"
  "\<Theta>(\<lambda>n::nat. ln (real n) powr p') = \<Theta>(\<lambda>n::nat. real n powr 0 * ln (real n) powr p')"
  "\<Theta>(\<lambda>n::nat. real n * ln (real n) powr p') = \<Theta>(\<lambda>n::nat. real n powr 1 * ln (real n) powr p')"
apply (simp_all)
apply (simp_all cong: landau_symbols[THEN landau_symbol_ge_3_cong])?
done

lemma akra_bazzi_term_imp_size_less:
  "x\<^sub>1 \<le> x \<Longrightarrow> akra_bazzi_term 0 x\<^sub>1 b t \<Longrightarrow> size (t x) < size x" 
  "x\<^sub>1 < x \<Longrightarrow> akra_bazzi_term 0 (Suc x\<^sub>1) b t \<Longrightarrow> size (t x) < size x" 
  by (simp_all add: akra_bazzi_term_imp_less)

definition "CLAMP (f :: nat \<Rightarrow> real) x = (if x < 3 then 0 else f x)"
definition "CLAMP' (f :: nat \<Rightarrow> real) x = (if x < 3 then 0 else f x)"
definition "MASTER_BOUND a b c x = real x powr a * ln (real x) powr b * ln (ln (real x)) powr c"
definition "MASTER_BOUND' a b x = real x powr a * ln (real x) powr b"
definition "MASTER_BOUND'' a x = real x powr a"

lemma ln_1_imp_less_3:
  "ln x = (1::real) \<Longrightarrow> x < 3"
proof-
  assume "ln x = 1"
  also have "(1::real) \<le> ln (exp 1)" by simp
  finally have "ln x \<le> ln (exp 1)" by simp
  hence "x \<le> exp 1"
    by (cases "x > 0") (force simp del: ln_exp simp add: not_less intro: order.trans)+
  also have "... < 3" by (rule exp_1_lt_3)
  finally show ?thesis .
qed

lemma ln_1_imp_less_3': "ln (real (x::nat)) = 1 \<Longrightarrow> x < 3" by (drule ln_1_imp_less_3) simp

lemma ln_ln_nonneg: "x \<ge> (3::real) \<Longrightarrow> ln (ln x) \<ge> 0" using ln_ln_pos[of "x"] by simp
lemma ln_ln_nonneg': "x \<ge> (3::nat) \<Longrightarrow> ln (ln (real x)) \<ge> 0" using ln_ln_pos[of "real x"] by simp

lemma MASTER_BOUND_postproc:
  "CLAMP (MASTER_BOUND' a 0) = CLAMP (MASTER_BOUND'' a)"
  "CLAMP (MASTER_BOUND' a 1) = CLAMP (\<lambda>x. CLAMP (MASTER_BOUND'' a) x * CLAMP (\<lambda>x. ln (real x)) x)"
  "CLAMP (MASTER_BOUND' a (numeral n)) = 
       CLAMP (\<lambda>x. CLAMP (MASTER_BOUND'' a) x * CLAMP (\<lambda>x. ln (real x) ^ numeral n) x)"
  "CLAMP (MASTER_BOUND' a (-1)) =
       CLAMP (\<lambda>x. CLAMP (MASTER_BOUND'' a) x / CLAMP (\<lambda>x. ln (real x)) x)"
  "CLAMP (MASTER_BOUND' a (-numeral n)) = 
       CLAMP (\<lambda>x. CLAMP (MASTER_BOUND'' a) x / CLAMP (\<lambda>x. ln (real x) ^ numeral n) x)"
  "CLAMP (MASTER_BOUND' a b) = 
       CLAMP (\<lambda>x. CLAMP (MASTER_BOUND'' a) x * CLAMP (\<lambda>x. ln (real x) powr b) x)"

  "CLAMP (MASTER_BOUND'' 0) = CLAMP (\<lambda>x. 1)"
  "CLAMP (MASTER_BOUND'' 1) = CLAMP (\<lambda>x. (real x))"
  "CLAMP (MASTER_BOUND'' (numeral n)) = CLAMP (\<lambda>x. (real x) ^ numeral n)"
  "CLAMP (MASTER_BOUND'' (-1)) = CLAMP (\<lambda>x. 1 / (real x))"
  "CLAMP (MASTER_BOUND'' (-numeral n)) = CLAMP (\<lambda>x. 1 / (real x) ^ numeral n)"
  "CLAMP (MASTER_BOUND'' a) = CLAMP (\<lambda>x. (real x) powr a)"

  and MASTER_BOUND_UNCLAMP:
  "CLAMP (\<lambda>x. CLAMP f x * CLAMP g x) = CLAMP (\<lambda>x. f x * g x)"
  "CLAMP (\<lambda>x. CLAMP f x / CLAMP g x) = CLAMP (\<lambda>x. f x / g x)"
  "CLAMP (CLAMP f) = CLAMP f"
  unfolding CLAMP_def[abs_def] MASTER_BOUND'_def[abs_def] MASTER_BOUND''_def[abs_def]
  by (simp_all add: powr_minus divide_inverse fun_eq_iff)

  
context
begin

private lemma CLAMP_: 
  "landau_symbol L L' Lr \<Longrightarrow> L at_top (f::nat \<Rightarrow> real) \<equiv> L at_top (\<lambda>x. CLAMP f x)"
  unfolding CLAMP_def[abs_def]
  by (intro landau_symbol.cong eq_reflection) 
     (auto intro: eventually_mono[OF eventually_ge_at_top[of "3::nat"]])

private lemma UNCLAMP'_: 
  "landau_symbol L L' Lr \<Longrightarrow> L at_top (CLAMP' (MASTER_BOUND a b c)) \<equiv> L at_top (MASTER_BOUND a b c)"
  unfolding CLAMP'_def[abs_def] CLAMP_def[abs_def]
  by (intro landau_symbol.cong eq_reflection) 
     (auto intro: eventually_mono[OF eventually_ge_at_top[of "3::nat"]])

private lemma UNCLAMP_: 
  "landau_symbol L L' Lr \<Longrightarrow> L at_top (CLAMP f) \<equiv> L at_top (f)"
  using eventually_ge_at_top[of "3::nat"] unfolding CLAMP'_def[abs_def] CLAMP_def[abs_def]
  by (intro landau_symbol.cong eq_reflection) 
     (auto intro: eventually_mono[OF eventually_ge_at_top[of "3::nat"]])

lemmas CLAMP = landau_symbols[THEN CLAMP_]
lemmas UNCLAMP' = landau_symbols[THEN UNCLAMP'_]
lemmas UNCLAMP = landau_symbols[THEN UNCLAMP_]
end

lemma propagate_CLAMP:
  "CLAMP (\<lambda>x. f x * g x) = CLAMP' (\<lambda>x. CLAMP f x * CLAMP g x)"
  "CLAMP (\<lambda>x. f x / g x) = CLAMP' (\<lambda>x. CLAMP f x / CLAMP g x)"
  "CLAMP (\<lambda>x. inverse (f x)) = CLAMP' (\<lambda>x. inverse (CLAMP f x))"
  "CLAMP (\<lambda>x. real x) = CLAMP' (MASTER_BOUND 1 0 0)"
  "CLAMP (\<lambda>x. real x powr a) = CLAMP' (MASTER_BOUND a 0 0)"
  "CLAMP (\<lambda>x. real x ^ a') = CLAMP' (MASTER_BOUND (real a') 0 0)"
  "CLAMP (\<lambda>x. ln (real x)) = CLAMP' (MASTER_BOUND 0 1 0)"
  "CLAMP (\<lambda>x. ln (real x) powr b) = CLAMP' (MASTER_BOUND 0 b 0)"
  "CLAMP (\<lambda>x. ln (real x) ^ b') = CLAMP' (MASTER_BOUND 0 (real b') 0)"
  "CLAMP (\<lambda>x. ln (ln (real x))) = CLAMP' (MASTER_BOUND 0 0 1)"
  "CLAMP (\<lambda>x. ln (ln (real x)) powr c) = CLAMP' (MASTER_BOUND 0 0 c)"
  "CLAMP (\<lambda>x. ln (ln (real x)) ^ c') = CLAMP' (MASTER_BOUND 0 0 (real c'))"
  "CLAMP' (CLAMP f) = CLAMP' f"
  "CLAMP' (\<lambda>x. CLAMP' (MASTER_BOUND a1 b1 c1) x * CLAMP' (MASTER_BOUND a2 b2 c2) x) = 
       CLAMP' (MASTER_BOUND (a1+a2) (b1+b2) (c1+c2))"
  "CLAMP' (\<lambda>x. CLAMP' (MASTER_BOUND a1 b1 c1) x / CLAMP' (MASTER_BOUND a2 b2 c2) x) = 
       CLAMP' (MASTER_BOUND (a1-a2) (b1-b2) (c1-c2))"
  "CLAMP' (\<lambda>x. inverse (MASTER_BOUND a1 b1 c1 x)) = CLAMP' (MASTER_BOUND (-a1) (-b1) (-c1))"
by (insert ln_1_imp_less_3')
   (rule ext, simp add: CLAMP_def CLAMP'_def MASTER_BOUND_def 
      powr_realpow powr_one[OF ln_ln_nonneg'] powr_realpow[OF ln_ln_pos] powr_add
      powr_diff powr_minus)+

lemma numeral_assoc_simps:
  "((a::real) + numeral b) + numeral c = a + numeral (b + c)"
  "(a + numeral b) - numeral c = a + neg_numeral_class.sub b c"
  "(a - numeral b) + numeral c = a + neg_numeral_class.sub c b"
  "(a - numeral b) - numeral c = a - numeral (b + c)" by simp_all

lemmas CLAMP_aux =
  arith_simps numeral_assoc_simps of_nat_power of_nat_mult of_nat_numeral
  one_add_one numeral_One [symmetric]

lemmas CLAMP_postproc = numeral_One

context master_theorem_function
begin

lemma master1_bigo_automation:
  assumes "g \<in> O(\<lambda>x. real x powr p')" "1 < (\<Sum>i<k. as ! i * bs ! i powr p')" 
  shows   "f \<in> O(MASTER_BOUND p 0 0)"
proof-
  have "MASTER_BOUND p 0 0 \<in> \<Theta>(\<lambda>x::nat. x powr p)" unfolding MASTER_BOUND_def[abs_def]
    by (intro landau_real_nat_transfer bigthetaI_cong 
          eventually_mono[OF eventually_ge_at_top[of "3::real"]]) (auto dest!: ln_1_imp_less_3)
  from landau_o.big.cong_bigtheta[OF this] master1_bigo[OF assms] show ?thesis by simp
qed

lemma master1_automation:
  assumes "g \<in> O(MASTER_BOUND'' p')" "1 < (\<Sum>i<k. as ! i * bs ! i powr p')" 
          "eventually (\<lambda>x. f x > 0) at_top"
  shows   "f \<in> \<Theta>(MASTER_BOUND p 0 0)"
proof-
  have A: "MASTER_BOUND p 0 0 \<in> \<Theta>(\<lambda>x::nat. x powr p)" unfolding MASTER_BOUND_def[abs_def]
    by (intro landau_real_nat_transfer bigthetaI_cong 
      eventually_mono[OF eventually_ge_at_top[of "3::real"]]) (auto dest!: ln_1_imp_less_3)
  have B: "O(MASTER_BOUND'' p') = O(\<lambda>x::nat. real x powr p')"
    using eventually_ge_at_top[of "2::nat"]
    by (intro landau_o.big.cong) (auto elim!: eventually_mono simp: MASTER_BOUND''_def)
  from landau_theta.cong_bigtheta[OF A] B assms(1) master1[OF _ assms(2-)] show ?thesis by simp
qed

lemma master2_1_automation:
  assumes "g \<in> \<Theta>(MASTER_BOUND' p p')" "p' < -1"
  shows   "f \<in> \<Theta>(MASTER_BOUND p 0 0)"
proof-
  have A: "MASTER_BOUND p 0 0 \<in> \<Theta>(\<lambda>x::nat. x powr p)" unfolding MASTER_BOUND_def[abs_def]
    by (intro landau_real_nat_transfer bigthetaI_cong 
          eventually_mono[OF eventually_ge_at_top[of "3::real"]]) (auto dest!: ln_1_imp_less_3)
  have B: "\<Theta>(MASTER_BOUND' p p') = \<Theta>(\<lambda>x::nat. real x powr p * ln (real x) powr p')"
    by (subst CLAMP, (subst MASTER_BOUND_postproc MASTER_BOUND_UNCLAMP)+, simp only: UNCLAMP)
  from landau_theta.cong_bigtheta[OF A] B assms(1) master2_1[OF _ assms(2-)] show ?thesis by simp
qed

lemma master2_2_automation:
  assumes "g \<in> \<Theta>(MASTER_BOUND' p (-1))"
  shows   "f \<in> \<Theta>(MASTER_BOUND p 0 1)"
proof-
  have A: "MASTER_BOUND p 0 1 \<in> \<Theta>(\<lambda>x::nat. x powr p * ln (ln x))" unfolding MASTER_BOUND_def[abs_def]
    using eventually_ge_at_top[of "3::real"]
    apply (intro landau_real_nat_transfer, intro bigthetaI_cong)
    apply (elim eventually_mono, subst powr_one[OF ln_ln_nonneg])
    apply simp_all
    done
  have B: "\<Theta>(MASTER_BOUND' p (-1)) = \<Theta>(\<lambda>x::nat. real x powr p / ln (real x))"
    by (subst CLAMP, (subst MASTER_BOUND_postproc MASTER_BOUND_UNCLAMP)+, simp only: UNCLAMP)
  from landau_theta.cong_bigtheta[OF A] B assms(1) master2_2 show ?thesis by simp
qed

lemma master2_3_automation:
  assumes "g \<in> \<Theta>(MASTER_BOUND' p (p' - 1))" "p' > 0"
  shows   "f \<in> \<Theta>(MASTER_BOUND p p' 0)"
proof-
  have A: "MASTER_BOUND p p' 0 \<in> \<Theta>(\<lambda>x::nat. x powr p * ln x powr p')" unfolding MASTER_BOUND_def[abs_def]
    using eventually_ge_at_top[of "3::real"]
    apply (intro landau_real_nat_transfer, intro bigthetaI_cong)
    apply (elim eventually_mono, auto dest: ln_1_imp_less_3)
    done
  have B: "\<Theta>(MASTER_BOUND' p (p' - 1)) = \<Theta>(\<lambda>x::nat. real x powr p * ln x powr (p' - 1))"
    by (subst CLAMP, (subst MASTER_BOUND_postproc MASTER_BOUND_UNCLAMP)+, simp only: UNCLAMP)
  from landau_theta.cong_bigtheta[OF A] B assms(1) master2_3[OF _ assms(2-)] show ?thesis by simp
qed

lemma master3_automation:
  assumes "g \<in> \<Theta>(MASTER_BOUND'' p')" "1 > (\<Sum>i<k. as ! i * bs ! i powr p')"
  shows   "f \<in> \<Theta>(MASTER_BOUND p' 0 0)"
proof-
  have A: "MASTER_BOUND p' 0 0 \<in> \<Theta>(\<lambda>x::nat. x powr p')" unfolding MASTER_BOUND_def[abs_def]
    using eventually_ge_at_top[of "3::real"]
    apply (intro landau_real_nat_transfer, intro bigthetaI_cong)
    apply (elim eventually_mono, auto dest: ln_1_imp_less_3)
    done
  have B: "\<Theta>(MASTER_BOUND'' p') = \<Theta>(\<lambda>x::nat. real x powr p')"
    by (subst CLAMP, (subst MASTER_BOUND_postproc)+, simp only: UNCLAMP)
  from landau_theta.cong_bigtheta[OF A] B assms(1) master3[OF _ assms(2-)] show ?thesis by simp
qed

lemmas master_automation = 
  master1_automation master2_1_automation master2_2_automation 
  master2_2_automation master3_automation


ML \<open>

fun generalize_master_thm ctxt thm =
  let
    val ([p'], ctxt') = Variable.variant_fixes ["p''"] ctxt
    val p' = Free (p', HOLogic.realT)
    val a = @{term "nth as"} $ Bound 0
    val b = @{term "Transcendental.powr :: real => real => real"} $ 
              (@{term "nth bs"} $ Bound 0) $ p'
    val f = Abs ("i", HOLogic.natT, @{term "(*) :: real => real => real"} $ a $ b)
    val sum = @{term "sum :: (nat => real) => nat set => real"} $ f $ @{term "{..<k}"}
    val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (sum, @{term "1::real"}))
    val cprop = Thm.cterm_of ctxt' prop
  in
    thm
    |> Local_Defs.unfold ctxt' [Thm.assume cprop RS @{thm p_unique}]
    |> Thm.implies_intr cprop
    |> rotate_prems 1
    |> singleton (Variable.export ctxt' ctxt)
  end

fun generalize_master_thm' (binding, thm) ctxt =
  Local_Theory.note ((binding, []), [generalize_master_thm ctxt thm]) ctxt |> snd

\<close>

local_setup \<open>
  fold generalize_master_thm' 
    [(@{binding master1_automation'}, @{thm master1_automation}), 
     (@{binding master1_bigo_automation'}, @{thm master1_bigo_automation}), 
     (@{binding master2_1_automation'}, @{thm master2_1_automation}),
     (@{binding master2_2_automation'}, @{thm master2_2_automation}),
     (@{binding master2_3_automation'}, @{thm master2_3_automation}), 
     (@{binding master3_automation'}, @{thm master3_automation})]
\<close>

end


definition "arith_consts (x :: real) (y :: nat) = 
  (if \<not> (-x) + 3 / x * 5 - 1 \<le> x \<and> True \<or> True \<longrightarrow> True then 
  x < inverse 3 powr 21 else x = real (Suc 0 ^ 2 + 
  (if 42 - x \<le> 1 \<and> 1 div y = y mod 2 \<or> y < Numeral1 then 0 else 0)) + Numeral1)"

ML_file \<open>akra_bazzi.ML\<close>

hide_const arith_consts

method_setup master_theorem = \<open>
  Akra_Bazzi.setup_master_theorem
\<close> "automatically apply the Master theorem for recursive functions"

method_setup akra_bazzi_termination = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Akra_Bazzi.akra_bazzi_termination_tac ctxt))
\<close> "prove termination of Akra-Bazzi functions"

hide_const CLAMP CLAMP' MASTER_BOUND MASTER_BOUND' MASTER_BOUND''

end
