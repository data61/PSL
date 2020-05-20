(*
  File:   Akra_Bazzi.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  The Akra-Bazzi theorem for functions on the naturals.
*)

section \<open>The discrete Akra-Bazzi theorem\<close>
theory Akra_Bazzi
imports
  Complex_Main
  "HOL-Library.Landau_Symbols"
  Akra_Bazzi_Real
begin

lemma ex_mono: "(\<exists>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> (\<exists>x. Q x)" by blast

lemma x_over_ln_mono:
  assumes "(e::real) > 0"
  assumes "x > exp e"
  assumes "x \<le> y"
  shows   "x / ln x powr e \<le> y / ln y powr e"
proof (rule DERIV_nonneg_imp_mono[of _ _ "\<lambda>x. x / ln x powr e"])
  fix t assume t: "t \<in> {x..y}"
  from assms(1) have "1 < exp e" by simp
  from this and assms(2) have "x > 1" by (rule less_trans)
  with t have t': "t > 1" by simp
  from \<open>x > exp e\<close> and t have "t > exp e" by simp
  with t' have "ln t > ln (exp e)" by (subst ln_less_cancel_iff) simp_all
  hence t'': "ln t > e" by simp
  show "((\<lambda>x. x / ln x powr e) has_real_derivative 
            (ln t - e) / ln t powr (e+1)) (at t)" using assms t t' t''
    by (force intro!: derivative_eq_intros simp: powr_diff field_simps powr_add)
  from t'' show "(ln t - e) / ln t powr (e + 1) \<ge> 0" by (intro divide_nonneg_nonneg) simp_all
qed (simp_all add: assms)


definition akra_bazzi_term :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "akra_bazzi_term x\<^sub>0 x\<^sub>1 b t = 
    (\<exists>e h. e > 0 \<and> (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e)) \<and>
               (\<forall>x\<ge>x\<^sub>1. t x \<ge> x\<^sub>0 \<and> t x < x \<and> b*x + h x = real (t x)))"

lemma akra_bazzi_termI [intro?]:
  assumes "e > 0" "(\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))"
          "\<And>x. x \<ge> x\<^sub>1 \<Longrightarrow> t x \<ge> x\<^sub>0" "\<And>x. x \<ge> x\<^sub>1 \<Longrightarrow> t x < x"
          "\<And>x. x \<ge> x\<^sub>1 \<Longrightarrow> b*x + h x = real (t x)"
  shows "akra_bazzi_term x\<^sub>0 x\<^sub>1 b t"
  using assms unfolding akra_bazzi_term_def by blast

lemma akra_bazzi_term_imp_less:
  assumes "akra_bazzi_term x\<^sub>0 x\<^sub>1 b t" "x \<ge> x\<^sub>1"
  shows   "t x < x"
  using assms unfolding akra_bazzi_term_def by blast

lemma akra_bazzi_term_imp_less':
  assumes "akra_bazzi_term x\<^sub>0 (Suc x\<^sub>1) b t" "x > x\<^sub>1"
  shows   "t x < x"
  using assms unfolding akra_bazzi_term_def by force


locale akra_bazzi_recursion =
  fixes x\<^sub>0 x\<^sub>1 k :: nat and as bs :: "real list" and ts :: "(nat \<Rightarrow> nat) list" and  f :: "nat \<Rightarrow> real"  
  assumes k_not_0:   "k \<noteq> 0"
  and     length_as: "length as = k"
  and     length_bs: "length bs = k"
  and     length_ts: "length ts = k"
  and     a_ge_0:    "a \<in> set as \<Longrightarrow> a \<ge> 0"
  and     b_bounds:  "b \<in> set bs \<Longrightarrow> b \<in> {0<..<1}"
  and     ts:        "i < length bs \<Longrightarrow> akra_bazzi_term x\<^sub>0 x\<^sub>1 (bs!i) (ts!i)"
begin

sublocale akra_bazzi_params k as bs
  using length_as length_bs k_not_0 a_ge_0 b_bounds by unfold_locales

lemma ts_nonempty: "ts \<noteq> []" using length_ts k_not_0 by (cases ts) simp_all

definition e_hs :: "real \<times> (nat \<Rightarrow> real) list" where
  "e_hs = (SOME (e,hs). 
     e > 0 \<and> length hs = k \<and> (\<forall>h\<in>set hs. (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))) \<and>
     (\<forall>t\<in>set ts. \<forall>x\<ge>x\<^sub>1. t x \<ge> x\<^sub>0 \<and> t x < x) \<and> 
     (\<forall>i<k. \<forall>x\<ge>x\<^sub>1. (bs!i)*x + (hs!i) x = real ((ts!i) x))
   )"

definition "e = (case e_hs of (e,_) \<Rightarrow> e)"
definition "hs = (case e_hs of (_,hs) \<Rightarrow> hs)"

lemma filterlim_powr_zero_cong: 
  "filterlim (\<lambda>x. P (x::real) (x powr (0::real))) F at_top = filterlim (\<lambda>x. P x 1) F at_top"
  apply (rule filterlim_cong[OF refl refl])
  using eventually_gt_at_top[of "0::real"] by eventually_elim simp_all
  

lemma e_hs_aux:
  "0 < e \<and> length hs = k \<and>
  (\<forall>h\<in>set hs. (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1 + e))) \<and>
  (\<forall>t\<in>set ts. \<forall>x\<ge>x\<^sub>1. x\<^sub>0 \<le> t x \<and> t x < x) \<and> 
  (\<forall>i<k. \<forall>x\<ge>x\<^sub>1. (bs!i)*x + (hs!i) x = real ((ts!i) x))"
proof-
  have "Ex (\<lambda>(e,hs). e > 0 \<and> length hs = k \<and> 
    (\<forall>h\<in>set hs. (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))) \<and>
    (\<forall>t\<in>set ts. \<forall>x\<ge>x\<^sub>1. t x \<ge> x\<^sub>0 \<and> t x < x) \<and> 
    (\<forall>i<k. \<forall>x\<ge>x\<^sub>1. (bs!i)*x + (hs!i) x = real ((ts!i) x)))"
  proof-
    from ts have A: "\<forall>i\<in>{..<k}. akra_bazzi_term x\<^sub>0 x\<^sub>1 (bs!i) (ts!i)" by (auto simp: length_bs)
    hence "\<exists>e h. (\<forall>i<k. e i > 0 \<and> 
             (\<lambda>x. h i x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e i)) \<and>
             (\<forall>x\<ge>x\<^sub>1. (ts!i) x \<ge> x\<^sub>0 \<and> (ts!i) x < x) \<and> 
             (\<forall>i<k. \<forall>x\<ge>x\<^sub>1. (bs!i)*real x + h i x = real ((ts!i) x)))"
             unfolding akra_bazzi_term_def
      by (subst (asm) bchoice_iff, subst (asm) bchoice_iff) blast
    then guess ee :: "_ \<Rightarrow> real" and hh :: "_ \<Rightarrow> nat \<Rightarrow> real" 
      by (elim exE conjE) note eh = this
    define e where "e = Min {ee i |i. i < k}"
    define hs where "hs = map hh (upt 0 k)"
    have e_pos: "e > 0" unfolding e_def using eh k_not_0 by (subst Min_gr_iff) auto
    moreover have "length hs = k" unfolding hs_def by (simp_all add: length_ts)
    moreover have hs_growth: "\<forall>h\<in>set hs. (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))"
    proof
      fix h assume "h \<in> set hs"
      then obtain i where t: "i < k" "h = hh i" unfolding hs_def by force
      hence "(\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+ee i))" using eh by blast
      also from t k_not_0 have "e \<le> ee i" unfolding e_def by (subst Min_le_iff) auto
      hence "(\<lambda>x::nat. real x / ln (real x) powr (1+ee i)) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))"
        by (intro bigo_real_nat_transfer) auto
      finally show "(\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1+e))" .
    qed
    moreover have "\<forall>t\<in>set ts. (\<forall>x\<ge>x\<^sub>1. t x \<ge> x\<^sub>0 \<and> t x < x)"
    proof (rule ballI)
      fix t assume "t \<in> set ts"
      then obtain i where "i < k" "t = ts!i" using length_ts by (subst (asm) in_set_conv_nth) auto
      with eh show "\<forall>x\<ge>x\<^sub>1. t x \<ge> x\<^sub>0 \<and> t x < x" unfolding hs_def by force
    qed
    moreover have "\<forall>i<k. \<forall>x\<ge>x\<^sub>1. (bs!i)*x + (hs!i) x = real ((ts!i) x)"
    proof (rule allI, rule impI)
      fix i assume i: "i < k"
      with eh show "\<forall>x\<ge>x\<^sub>1. (bs!i)*x + (hs!i) x = real ((ts!i) x)"
        using length_ts unfolding hs_def by fastforce
    qed
    ultimately show ?thesis by blast
  qed
  from someI_ex[OF this, folded e_hs_def] show ?thesis
    unfolding e_def hs_def by (intro conjI) fastforce+
qed

lemma
  e_pos: "e > 0" and length_hs: "length hs = k" and 
  hs_growth:  "\<And>h. h \<in> set hs \<Longrightarrow> (\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1 + e))" and
  step_ge_x0: "\<And>t x. t \<in> set ts \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> x\<^sub>0 \<le> t x" and
  step_less:  "\<And>t x. t \<in> set ts \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> t x < x" and
  decomp:     "\<And>i x. i < k \<Longrightarrow> x \<ge> x\<^sub>1 \<Longrightarrow> (bs!i)*x + (hs!i) x = real ((ts!i) x)"
by (insert e_hs_aux) simp_all

lemma h_in_hs [intro, simp]: "i < k \<Longrightarrow> hs ! i \<in> set hs"
  by (rule nth_mem) (simp add: length_hs)

lemma t_in_ts [intro, simp]: "i < k \<Longrightarrow> ts ! i \<in> set ts"
  by (rule nth_mem) (simp add: length_ts)

lemma x0_less_x1: "x\<^sub>0 < x\<^sub>1" and x0_le_x1: "x\<^sub>0 \<le> x\<^sub>1"
proof-
  from ts_nonempty have "x\<^sub>0 \<le> hd ts x\<^sub>1" using step_ge_x0[of "hd ts" x\<^sub>1] by simp
  also from ts_nonempty have "... < x\<^sub>1" by (intro step_less) simp_all
  finally show "x\<^sub>0 < x\<^sub>1" by simp
  thus "x\<^sub>0 \<le> x\<^sub>1" by simp
qed

lemma akra_bazzi_induct [consumes 1, case_names base rec]:
  assumes "x \<ge> x\<^sub>0"
  assumes base: "\<And>x. x \<ge> x\<^sub>0 \<Longrightarrow> x < x\<^sub>1 \<Longrightarrow> P x"
  assumes rec:  "\<And>x. x \<ge> x\<^sub>1 \<Longrightarrow> (\<And>t. t \<in> set ts \<Longrightarrow> P (t x)) \<Longrightarrow> P x"
  shows   "P x"
proof (insert assms(1), induction x rule: less_induct)
  case (less x)
  with assms step_less step_ge_x0 show "P x" by (cases "x < x\<^sub>1") auto
qed

end

locale akra_bazzi_function = akra_bazzi_recursion +
  fixes integrable integral 
  assumes integral: "akra_bazzi_integral integrable integral"
  fixes g :: "nat \<Rightarrow> real"
  assumes f_nonneg_base: "x \<ge> x\<^sub>0 \<Longrightarrow> x < x\<^sub>1 \<Longrightarrow> f x \<ge> 0"
  and     f_rec:         "x \<ge> x\<^sub>1 \<Longrightarrow> f x = g x + (\<Sum>i<k. as!i * f ((ts!i) x))"
  and     g_nonneg:      "x \<ge> x\<^sub>1 \<Longrightarrow> g x \<ge> 0"
  and     ex_pos_a:      "\<exists>a\<in>set as. a > 0"
begin

lemma ex_pos_a': "\<exists>i<k. as!i > 0"
  using ex_pos_a by (auto simp: in_set_conv_nth length_as)

sublocale akra_bazzi_params_nonzero
  using length_as length_bs ex_pos_a a_ge_0 b_bounds by unfold_locales


definition g_real :: "real \<Rightarrow> real" where "g_real x = g (nat \<lfloor>x\<rfloor>)"

lemma g_real_real[simp]: "g_real (real x) = g x" unfolding g_real_def by simp

lemma f_nonneg: "x \<ge> x\<^sub>0 \<Longrightarrow> f x \<ge> 0"
proof (induction x rule: akra_bazzi_induct)
  case (base x)
  with f_nonneg_base show "f x \<ge> 0" by simp
next
  case (rec x)
  from rec.hyps have "g x \<ge> 0" by (intro g_nonneg) simp
  moreover have "(\<Sum>i<k. as!i*f ((ts!i) x)) \<ge> 0" using rec.hyps length_ts length_as
    by (intro sum_nonneg ballI mult_nonneg_nonneg[OF a_ge_0 rec.IH]) simp_all
  ultimately show "f x \<ge> 0" using rec.hyps by (simp add: f_rec)
qed  

definition "hs' = map (\<lambda>h x. h (nat \<lfloor>x::real\<rfloor>)) hs"

lemma length_hs': "length hs' = k" unfolding hs'_def by (simp add: length_hs)

lemma hs'_real: "i < k \<Longrightarrow> (hs'!i) (real x) = (hs!i) x"
  unfolding hs'_def by (simp add: length_hs)

lemma h_bound:
  obtains hb where "hb > 0" and
      "eventually (\<lambda>x. \<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb * x / ln x powr (1 + e)) at_top"
proof-
  have "\<forall>h\<in>set hs. \<exists>c>0. eventually (\<lambda>x. \<bar>h x\<bar> \<le> c * real x / ln (real x) powr (1 + e)) at_top"
  proof
    fix h assume h: "h \<in> set hs"
    hence "(\<lambda>x. h x) \<in> O(\<lambda>x. real x / ln (real x) powr (1 + e))" by (rule hs_growth)
    thus "\<exists>c>0. eventually (\<lambda>x. \<bar>h x\<bar> \<le> c * x / ln x powr (1 + e)) at_top"
     unfolding bigo_def by auto
  qed
  from bchoice[OF this] obtain hb where hb:
      "\<forall>h\<in>set hs. hb h > 0 \<and> eventually (\<lambda>x. \<bar>h x\<bar> \<le> hb h * real x / ln (real x) powr (1 + e)) at_top" by blast
  define hb' where "hb' = max 1 (Max {hb h |h. h \<in> set hs})"
  have "hb' > 0" unfolding hb'_def by simp
  moreover have "\<forall>h\<in>set hs. eventually (\<lambda>x. \<bar>h (nat \<lfloor>x\<rfloor>)\<bar> \<le> hb' * x / ln x powr (1 + e)) at_top"
  proof (intro ballI, rule eventually_mp[OF always_eventually eventually_conj], clarify)
    fix h assume h: "h \<in> set hs"
    with hb have hb_pos: "hb h > 0" by auto
    
    show "eventually (\<lambda>x. x > exp (1 + e) + 1) at_top" by (rule eventually_gt_at_top)
    from h hb have e: "eventually (\<lambda>x. \<bar>h (nat \<lfloor>x :: real\<rfloor>)\<bar> \<le> 
        hb h * real (nat \<lfloor>x\<rfloor>) / ln (real (nat \<lfloor>x\<rfloor>)) powr (1 + e)) at_top" 
      by (intro eventually_natfloor) blast
    show "eventually (\<lambda>x. \<bar>h (nat \<lfloor>x :: real\<rfloor>)\<bar> \<le> hb' * x / ln x powr (1 + e)) at_top"
      using e eventually_gt_at_top
    proof eventually_elim      
      fix x :: real assume x: "x > exp (1 + e) + 1"
 
      have x': "x > 0" by (rule le_less_trans[OF _ x]) simp_all
      assume "\<bar>h (nat \<lfloor>x\<rfloor>)\<bar> \<le> hb h*real (nat \<lfloor>x\<rfloor>)/ln (real (nat \<lfloor>x\<rfloor>)) powr (1 + e)"
      also {
        from x have "exp (1 + e) < real (nat \<lfloor>x\<rfloor>)" by linarith
        moreover have "x > 0" by (rule le_less_trans[OF _ x]) simp_all
        hence "real (nat \<lfloor>x\<rfloor>) \<le> x" by simp
        ultimately have "real (nat \<lfloor>x\<rfloor>)/ln (real (nat \<lfloor>x\<rfloor>)) powr (1+e) \<le> x/ln x powr (1+e)"
          using e_pos by (intro x_over_ln_mono) simp_all
        from hb_pos mult_left_mono[OF this, of "hb h"]
          have "hb h * real (nat \<lfloor>x\<rfloor>)/ln (real (nat \<lfloor>x\<rfloor>)) powr (1+e) \<le> hb h * x / ln x powr (1+e)"
          by (simp add: algebra_simps)
      }
      also from h have "hb h \<le> hb'"
        unfolding hb'_def f_rec by (intro order.trans[OF Max.coboundedI max.cobounded2]) auto
      with x' have "hb h*x/ln x powr (1+e) \<le> hb'*x/ln x powr (1+e)"
        by (intro mult_right_mono divide_right_mono) simp_all
      finally show "\<bar>h (nat \<lfloor>x\<rfloor>)\<bar> \<le> hb' * x / ln x powr (1 + e)" .
    qed
  qed
  hence "\<forall>h\<in>set hs'. eventually (\<lambda>x. \<bar>h x\<bar> \<le> hb' * x / ln x powr (1 + e)) at_top"
    by (auto simp: hs'_def)
  hence "eventually (\<lambda>x. \<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb' * x / ln x powr (1 + e)) at_top"
    by (intro eventually_ball_finite) simp_all
  ultimately show ?thesis by (rule that)
qed

lemma C_bound:
  assumes "\<And>b. b \<in> set bs \<Longrightarrow> C < b" "hb > 0"
  shows   "eventually (\<lambda>x::real. \<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e)) at_top"
proof-
  from e_pos have "((\<lambda>x. hb * ln x powr -(1+e)) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp_all
  with assms have "\<forall>b\<in>set bs. eventually (\<lambda>x. \<bar>hb * ln x powr -(1+e)\<bar> < b - C) at_top"
    by (force simp: tendsto_iff dist_real_def)
  hence "eventually (\<lambda>x. \<forall>b\<in>set bs. \<bar>hb * ln x powr -(1+e)\<bar> < b - C) at_top"
    by (intro eventually_ball_finite) simp_all
  note A = eventually_conj[OF this eventually_gt_at_top]
  show ?thesis using A apply eventually_elim
  proof clarify
    fix x b :: real assume x: "x > 0" and b: "b \<in> set bs"
    assume A: "\<forall>b\<in>set bs. \<bar>hb * ln x powr -(1+e)\<bar> < b - C"
    from b A assms have "hb * ln x powr -(1+e) < b - C" by simp
    with x have "x * (hb * ln x powr -(1+e)) < x * (b - C)" by (intro mult_strict_left_mono)
    thus "C*x \<le> b*x - hb*x / ln x powr (1+e)"
      by (subst (asm) powr_minus) (simp_all add: field_simps)
  qed
qed

end



locale akra_bazzi_lower = akra_bazzi_function +
  fixes   g' :: "real \<Rightarrow> real"
  assumes f_pos:      "eventually (\<lambda>x. f x > 0) at_top"
  and     g_growth2:  "\<exists>C c2. c2 > 0 \<and> C < Min (set bs) \<and> 
                           eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. g' u \<le> c2 * g' x) at_top"
  and     g'_integrable:  "\<exists>a. \<forall>b\<ge>a. integrable (\<lambda>u. g' u / u powr (p + 1)) a b"
  and     g'_bounded:  "eventually (\<lambda>a::real. (\<forall>b>a. \<exists>c. \<forall>x\<in>{a..b}. g' x \<le> c)) at_top"
  and     g_bigomega: "g \<in> \<Omega>(\<lambda>x. g' (real x))"
  and     g'_nonneg:  "eventually (\<lambda>x. g' x \<ge> 0) at_top"
begin

definition "gc2 \<equiv> SOME gc2. gc2 > 0 \<and> eventually (\<lambda>x. g x \<ge> gc2 * g' (real x)) at_top"

lemma gc2: "gc2 > 0" "eventually (\<lambda>x. g x \<ge> gc2 * g' (real x)) at_top"
proof-
  from g_bigomega guess c by (elim landau_omega.bigE) note c = this
  from g'_nonneg have "eventually (\<lambda>x::nat. g' (real x) \<ge> 0) at_top" by (rule eventually_nat_real)
  with c(2) have "eventually (\<lambda>x. g x \<ge> c * g' (real x)) at_top" 
    using eventually_ge_at_top[of x\<^sub>1] by eventually_elim (insert g_nonneg, simp_all)
  with c(1) have "\<exists>gc2. gc2 > 0 \<and> eventually (\<lambda>x. g x \<ge> gc2 * g' (real x)) at_top" by blast
  from someI_ex[OF this] show "gc2 > 0" "eventually (\<lambda>x. g x \<ge> gc2 * g' (real x)) at_top"
    unfolding gc2_def by blast+
qed

definition "gx0 \<equiv> max x\<^sub>1 (SOME gx0. \<forall>x\<ge>gx0. g x \<ge> gc2 * g' (real x) \<and> f x > 0 \<and> g' (real x) \<ge> 0)"
definition "gx1 \<equiv> max gx0 (SOME gx1. \<forall>x\<ge>gx1. \<forall>i<k. (ts!i) x \<ge> gx0)"

lemma gx0:
  assumes "x \<ge> gx0"
  shows   "g x \<ge> gc2 * g' (real x)" "f x > 0" "g' (real x) \<ge> 0"
proof-
  from eventually_conj[OF gc2(2) eventually_conj[OF f_pos eventually_nat_real[OF g'_nonneg]]]
    have "\<exists>gx0. \<forall>x\<ge>gx0. g x \<ge> gc2 * g' (real x) \<and> f x > 0 \<and> g' (real x) \<ge> 0" 
    by (simp add: eventually_at_top_linorder)
  note someI_ex[OF this]
  moreover have "x \<ge> (SOME gx0. \<forall>x\<ge>gx0. g x \<ge> gc2 * g' (real x) \<and>f x > 0 \<and> g' (real x) \<ge> 0)"
    using assms unfolding gx0_def by simp
  ultimately show "g x \<ge> gc2 * g' (real x)" "f x > 0" "g' (real x) \<ge> 0" unfolding gx0_def by blast+
qed

lemma gx1:
  assumes "x \<ge> gx1" "i < k"
  shows  "(ts!i) x \<ge> gx0"
proof-
  define mb where "mb = Min (set bs)/2"
  from b_bounds bs_nonempty have mb_pos: "mb > 0" unfolding mb_def by simp
  from h_bound guess hb . note hb = this
  from e_pos have "((\<lambda>x. hb * ln x powr -(1 + e)) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr ln_at_top) simp_all
  moreover note mb_pos
  ultimately have "eventually (\<lambda>x. hb * ln x powr -(1 + e) < mb) at_top" using hb(1)
    by (subst (asm) tendsto_iff) (simp_all add: dist_real_def)

  from eventually_nat_real[OF hb(2)] eventually_nat_real[OF this]
       eventually_ge_at_top eventually_ge_at_top
  have "eventually (\<lambda>x. \<forall>i<k. (ts!i) x \<ge> gx0) at_top" apply eventually_elim
  proof clarify
    fix i x :: nat assume A: "hb * ln (real x) powr -(1+e) < mb" and i: "i < k"
    assume B: "\<forall>h\<in>set hs'. \<bar>h (real x)\<bar> \<le> hb * real x / ln (real x) powr (1+e)"
    with i have B': "\<bar>(hs'!i) (real x)\<bar> \<le> hb * real x / ln (real x) powr (1+e)"
      using length_hs'[symmetric] by auto
    assume C: "x \<ge> nat \<lceil>gx0/mb\<rceil>"
    hence C': "real gx0/mb \<le> real x" by linarith
    assume D: "x \<ge> x\<^sub>1"
      
    from mb_pos have "real gx0 = mb * (real gx0/mb)" by simp
    also from i bs_nonempty have "mb \<le> bs!i/2" unfolding mb_def by simp
    hence "mb * (real gx0/mb) \<le> bs!i/2 * x" 
      using C' i b_bounds[of "bs!i"] mb_pos by (intro mult_mono) simp_all
    also have "... = bs!i*x + -bs!i/2 * x" by simp
    also {
      have "-(hs!i) x \<le> \<bar>(hs!i) x\<bar>" by simp
      also from i B' length_hs have "\<bar>(hs!i) x\<bar> \<le> hb * real x / ln (real x) powr (1+e)" 
        by (simp add: hs'_def)
      also from A have "hb / ln x powr (1+e) \<le> mb" 
        by (subst (asm) powr_minus) (simp add: field_simps)
      hence "hb / ln x powr (1+e) * x \<le> mb * x" by (intro mult_right_mono) simp_all
      hence "hb * x / ln x powr (1+e) \<le> mb * x" by simp
      also from i have "... \<le> (bs!i/2) * x" unfolding mb_def by (intro mult_right_mono) simp_all
      finally have "-bs!i/2 * x \<le> (hs!i) x" by simp
    }
    also have "bs!i*real x + (hs!i) x = real ((ts!i) x)" using i D decomp by simp
    finally show "(ts!i) x \<ge> gx0" by simp
  qed
  hence "\<exists>gx1. \<forall>x\<ge>gx1. \<forall>i<k. gx0 \<le> (ts!i) x" (is "Ex ?P")
    by (simp add: eventually_at_top_linorder)
  from someI_ex[OF this] have "?P (SOME x. ?P x)" .
  moreover have "\<And>x. x \<ge> gx1 \<Longrightarrow> x \<ge> (SOME x. ?P x)" unfolding gx1_def by simp
  ultimately have "?P gx1" by blast
  with assms show ?thesis by blast
qed

lemma gx0_ge_x1: "gx0 \<ge> x\<^sub>1" unfolding gx0_def by simp
lemma gx0_le_gx1: "gx0 \<le> gx1" unfolding gx1_def by simp

function f2' :: "nat \<Rightarrow> real" where
  "x < gx1 \<Longrightarrow> f2' x = max 0 (f x / gc2)"
| "x \<ge> gx1 \<Longrightarrow> f2' x = g' (real x) + (\<Sum>i<k. as!i*f2' ((ts!i) x))"
using le_less_linear by (blast, simp_all)
termination by (relation "Wellfounded.measure (\<lambda>x. x)") 
               (insert gx0_le_gx1 gx0_ge_x1, simp_all add: step_less)

lemma f2'_nonneg: "x \<ge> gx0 \<Longrightarrow> f2' x \<ge> 0"
by (induction x rule: f2'.induct)
   (auto intro!: add_nonneg_nonneg sum_nonneg gx0 gx1  mult_nonneg_nonneg[OF a_ge_0])
               
lemma f2'_le_f: "x \<ge> x\<^sub>0 \<Longrightarrow> gc2 * f2' x \<le> f x"
proof (induction rule: f2'.induct)
  case (1 x)
  with gc2 f_nonneg show ?case by (simp add: max_def field_simps)
next
  case prems: (2 x)
  with gx0 gx0_le_gx1 have "gc2 * g' (real x) \<le> g x" by force
  moreover from step_ge_x0 prems(1) gx0_ge_x1 gx0_le_gx1
    have "\<And>i. i < k \<Longrightarrow> x\<^sub>0 \<le> (ts!i) x" by simp
  hence "\<And>i. i < k \<Longrightarrow> as!i * (gc2 * f2' ((ts!i) x)) \<le> as!i * f ((ts!i) x)"
    using prems(1) by (intro mult_left_mono a_ge_0 prems(2)) auto
  hence "gc2 * (\<Sum>i<k. as!i*f2' ((ts!i) x)) \<le> (\<Sum>i<k. as!i*f ((ts!i) x))"
    by (subst sum_distrib_left, intro sum_mono) (simp_all add: algebra_simps)
  ultimately show ?case using prems(1) gx0_ge_x1 gx0_le_gx1
    by (simp_all add: algebra_simps f_rec)
qed

lemma f2'_pos: "eventually (\<lambda>x. f2' x > 0) at_top"
proof (subst eventually_at_top_linorder, intro exI allI impI)
  fix x :: nat assume "x \<ge> gx0"
  thus "f2' x > 0"
  proof (induction x rule: f2'.induct)
    case (1 x)
    with gc2 gx0(2)[of x] show ?case by (simp add: max_def field_simps)
  next
    case prems: (2 x)
    have "(\<Sum>i<k. as!i*f2' ((ts!i) x)) > 0"
    proof (rule sum_pos')
      from ex_pos_a' guess i by (elim exE conjE) note i = this
      with prems(1) gx0 gx1 have "as!i * f2' ((ts!i) x) > 0"
        by (intro mult_pos_pos prems(2)) simp_all
      with i show "\<exists>i\<in>{..<k}. as!i * f2' ((ts!i) x) > 0" by blast
    next
      fix i assume i: "i \<in> {..<k}"
      with prems(1) have "f2' ((ts!i) x) > 0" by (intro prems(2) gx1) simp_all
      with i show "as!i * f2' ((ts!i) x) \<ge> 0" by (intro mult_nonneg_nonneg[OF a_ge_0]) simp_all
    qed simp_all
    with prems(1) gx0_le_gx1 show ?case by (auto intro!: add_nonneg_pos gx0)
  qed
qed


lemma bigomega_f_aux: 
  obtains a where "a \<ge> A" "\<forall>a'\<ge>a. a' \<in> \<nat> \<longrightarrow> 
    f \<in> \<Omega>(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p + 1)) a' x))"
proof-
  from g'_integrable guess a0 by (elim exE) note a0 = this
  from h_bound guess hb . note hb = this
  moreover from g_growth2 guess C c2 by (elim conjE exE) note C = this
  hence "eventually (\<lambda>x. \<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1 + e)) at_top"
    using hb(1) bs_nonempty by (intro C_bound) simp_all
  moreover from b_bounds hb(1) e_pos 
    have "eventually (\<lambda>x. \<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) at_top"
    by (rule akra_bazzi_asymptotics)
  moreover note g'_bounded C(3) g'_nonneg eventually_natfloor[OF f2'_pos] eventually_natfloor[OF gc2(2)]
  ultimately have "eventually (\<lambda>x. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e)) \<and>
                     (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e)) \<and>
                     (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) \<and>
                     (\<forall>b>x. \<exists>c. \<forall>x\<in>{x..b}. g' x \<le> c) \<and> f2' (nat \<lfloor>x\<rfloor>) > 0 \<and> 
                     (\<forall>u\<in>{C * x..x}. g' u \<le> c2 * g' x) \<and>
                     g' x \<ge> 0) at_top"
    by (intro eventually_conj) (force elim!: eventually_conjE)+
  then have "\<exists>X. (\<forall>x\<ge>X. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e)) \<and>
                        (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e)) \<and>
                        (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) \<and>
                        (\<forall>b>x. \<exists>c. \<forall>x\<in>{x..b}. g' x \<le> c) \<and> 
                        (\<forall>u\<in>{C * x..x}. g' u \<le> c2 * g' x) \<and>
                        f2' (nat \<lfloor>x\<rfloor>) > 0 \<and> g' x \<ge> 0)"
    by (subst (asm) eventually_at_top_linorder) (erule ex_mono, blast)
  then guess X by (elim exE conjE) note X = this

  define x\<^sub>0'_min where "x\<^sub>0'_min = max A (max X (max a0 (max gx1 (max 1 (real x\<^sub>1 + 1)))))"
  {
  fix x\<^sub>0' :: real assume x0'_props: "x\<^sub>0' \<ge> x\<^sub>0'_min" "x\<^sub>0' \<in> \<nat>"
  hence x0'_ge_x1: "x\<^sub>0' \<ge> real (x\<^sub>1+1)" and x0'_ge_1: "x\<^sub>0' \<ge> 1" and x0'_ge_X: "x\<^sub>0' \<ge> X" 
    unfolding x\<^sub>0'_min_def by linarith+
  hence x0'_pos: "x\<^sub>0' > 0" and  x0'_nonneg: "x\<^sub>0' \<ge> 0" by simp_all
  have x0': "\<forall>x\<ge>x\<^sub>0'. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e))"
            "\<forall>x\<ge>x\<^sub>0'. (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e))"
            "\<forall>x\<ge>x\<^sub>0'. (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x)"
            "\<forall>a\<ge>x\<^sub>0'. \<forall>b>a. \<exists>c. \<forall>x\<in>{a..b}. g' x \<le> c"
            "\<forall>x\<ge>x\<^sub>0'. \<forall>u\<in>{C * x..x}. g' u \<le> c2 * g' x"
            "\<forall>x\<ge>x\<^sub>0'. f2' (nat \<lfloor>x\<rfloor>) > 0" "\<forall>x\<ge>x\<^sub>0'. g' x \<ge> 0"
    using X x0'_ge_X by auto
  from x0'_props(2) have x0'_int: "real (nat \<lfloor>x\<^sub>0'\<rfloor>) = x\<^sub>0'" by (rule real_natfloor_nat)
  from x0'_props have x0'_ge_gx1: "x\<^sub>0' \<ge> gx1" and x0'_ge_a0: "x\<^sub>0' \<ge> a0" 
    unfolding x\<^sub>0'_min_def by simp_all
  with gx0_le_gx1 have f2'_nonneg: "\<And>x. x \<ge> x\<^sub>0' \<Longrightarrow> f2' x \<ge> 0" by (force intro!: f2'_nonneg)
           
  define bm where "bm = Min (set bs)"
  define x\<^sub>1' where "x\<^sub>1' = 2 * x\<^sub>0' * inverse bm"
  define fb2 where "fb2 = Min {f2' x |x. x \<in> {x\<^sub>0'..x\<^sub>1'}}"
  define gb2 where "gb2 = (SOME c. \<forall>x\<in>{x\<^sub>0'..x\<^sub>1'}. g' x \<le> c)"
  
  from b_bounds bs_nonempty have "bm > 0" "bm < 1" unfolding bm_def by auto
  hence "1 < 2 * inverse bm" by (simp add: field_simps)
  from mult_strict_left_mono[OF this x0'_pos] 
    have x0'_lt_x1': "x\<^sub>0' < x\<^sub>1'" and x0'_le_x1': "x\<^sub>0' \<le> x\<^sub>1'" unfolding x\<^sub>1'_def by simp_all 
    
  from x0_le_x1 x0'_ge_x1 have ge_x0'D: "\<And>x. x\<^sub>0' \<le> real x \<Longrightarrow> x\<^sub>0 \<le> x" by simp
  from x0'_ge_x1 x0'_le_x1' have gt_x1'D: "\<And>x. x\<^sub>1' < real x \<Longrightarrow> x\<^sub>1 \<le> x" by simp
  
  have x0'_x1': "\<forall>b\<in>set bs. 2 * x\<^sub>0' * inverse b \<le> x\<^sub>1'"
  proof
    fix b assume b: "b \<in> set bs"
    hence "bm \<le> b" by (simp add: bm_def)
    moreover from b bs_nonempty b_bounds have "bm > 0" "b > 0" unfolding bm_def by auto
    ultimately have "inverse b \<le> inverse bm" by simp
    with x0'_nonneg show "2 * x\<^sub>0' * inverse b \<le> x\<^sub>1'" 
      unfolding x\<^sub>1'_def by (intro mult_left_mono) simp_all
  qed
  
  note f_nonneg' = f_nonneg
  have "\<And>x. real x \<ge> x\<^sub>0' \<Longrightarrow> x \<ge> nat \<lfloor>x\<^sub>0'\<rfloor>" "\<And>x. real x \<le> x\<^sub>1' \<Longrightarrow> x \<le> nat \<lceil>x\<^sub>1'\<rceil>" by linarith+  
  hence "{x |x. real x \<in> {x\<^sub>0'..x\<^sub>1'}} \<subseteq> {x |x. x \<in> {nat \<lfloor>x\<^sub>0'\<rfloor>..nat \<lceil>x\<^sub>1'\<rceil>}}" by auto
  hence "finite {x |x::nat. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by (rule finite_subset) auto
  hence fin: "finite {f2' x |x::nat. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by force

  note facts = hs'_real e_pos length_hs' length_as length_bs k_not_0 a_ge_0 p_props x0'_ge_1
               f2'_nonneg f_rec[OF gt_x1'D] x0' x0'_int x0'_x1' gc2(1) decomp
  from b_bounds x0'_le_x1' x0'_ge_gx1 gx0_le_gx1 x0'_ge_x1
    interpret abr: akra_bazzi_nat_to_real as bs hs' k x\<^sub>0' x\<^sub>1' hb e p f2' g'
    by (unfold_locales) (auto simp: facts simp del: f2'.simps intro!: f2'.simps(2))
  
  have f'_nat: "\<And>x::nat. abr.f' (real x) = f2' x"
  proof-
    fix x :: nat show "abr.f' (real (x::nat)) = f2' x"
    proof (induction "real x" arbitrary: x rule: abr.f'.induct)
      case (2 x)
      note x = this(1) and IH = this(2)
      from x have "abr.f' (real x) = g' (real x) + (\<Sum>i<k. as!i*abr.f' (bs!i*real x + (hs!i) x))"
        by (auto simp: gt_x1'D hs'_real g_real_def intro!: sum.cong)
      also have "(\<Sum>i<k. as!i*abr.f' (bs!i*real x + (hs!i) x)) = 
                 (\<Sum>i<k. as!i*f2' ((ts!i) x))"
      proof (rule sum.cong, simp, clarify)
        fix i assume i: "i < k"
        from i x x0'_le_x1' x0'_ge_x1 have *: "bs!i * real x + (hs!i) x = real ((ts!i) x)"
          by (intro decomp) simp_all
        also from i * have "abr.f' ... = f2' ((ts!i) x)"
          by (subst IH[of i]) (simp_all add: hs'_real)
        finally show "as!i*abr.f' (bs!i*real x+(hs!i) x) = as!i*f2' ((ts!i) x)" by simp
      qed
      also have "g' x + ... = f2' x" using x x0'_ge_gx1 x0'_le_x1' 
        by (intro f2'.simps(2)[symmetric] gt_x1'D) simp_all
      finally show ?case .
    qed simp
  qed
  interpret akra_bazzi_integral integrable integral by (rule integral) 
  interpret akra_bazzi_real_lower as bs hs' k x\<^sub>0' x\<^sub>1' hb e p 
      integrable integral abr.f' g' C fb2 gb2 c2
  proof unfold_locales
    fix x assume "x \<ge> x\<^sub>0'" "x \<le> x\<^sub>1'"
    thus "abr.f' x \<ge> 0" by (intro abr.f'_base) simp_all
  next
    fix x assume x:"x \<ge> x\<^sub>0'"
    show "integrable (\<lambda>x. g' x / x powr (p + 1)) x\<^sub>0' x"
      by (rule integrable_subinterval[of _ a0 x]) (insert a0 x0'_ge_a0 x, auto)
  next
    fix x assume x: "x \<ge> x\<^sub>0'" "x \<le> x\<^sub>1'"
    have "x\<^sub>0' = real (nat \<lfloor>x\<^sub>0'\<rfloor>)" by (simp add: x0'_int)
    also from x have "... \<le> real (nat \<lfloor>x\<rfloor>)" by (auto intro!: nat_mono floor_mono)
    finally have "x\<^sub>0' \<le> real (nat \<lfloor>x\<rfloor>)" .
    moreover have "real (nat \<lfloor>x\<rfloor>) \<le> x\<^sub>1'" using x x0'_ge_1 by linarith
    ultimately have "f2' (nat \<lfloor>x\<rfloor>) \<in> {f2' x |x. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by force
    from fin and this have "f2' (nat \<lfloor>x\<rfloor>) \<ge> fb2" unfolding fb2_def by (rule Min_le)
    with x show "abr.f' x \<ge> fb2" by simp
  next
    from x0'_int x0'_le_x1' have "\<exists>x::nat. real x \<ge> x\<^sub>0' \<and> real x \<le> x\<^sub>1'" 
        by (intro exI[of _ "nat \<lfloor>x\<^sub>0'\<rfloor>"]) simp_all
    moreover {
      fix x :: nat assume "real x \<ge> x\<^sub>0' \<and> real x \<le> x\<^sub>1'"
      with x0'(6) have "f2' (nat \<lfloor>real x\<rfloor>) > 0" by blast
      hence "f2' x > 0" by simp
    }
    ultimately show "fb2 > 0" unfolding fb2_def using fin by (subst Min_gr_iff) auto 
  next
    fix x assume x: "x\<^sub>0' \<le> x" "x \<le> x\<^sub>1'"
    with x0'(4) x0'_lt_x1' have "\<exists>c. \<forall>x\<in>{x\<^sub>0'..x\<^sub>1'}. g' x \<le> c" by force
    from someI_ex[OF this] x show "g' x \<le> gb2" unfolding gb2_def by simp
  qed (insert g_nonneg integral x0'(2) C x0'_le_x1' x0'_ge_x1, simp_all add: facts)
  
  from akra_bazzi_lower guess c5 . note c5 = this
  have "eventually (\<lambda>x. \<bar>f x\<bar> \<ge> gc2 * c5 * \<bar>f_approx (real x)\<bar>) at_top"
  proof (unfold eventually_at_top_linorder, intro exI allI impI)
    fix x :: nat assume "x \<ge> nat \<lceil>x\<^sub>0'\<rceil>"
    hence x: "real x \<ge> x\<^sub>0'" by linarith
    note c5(1)[OF x]
    also have "abr.f' (real x) = f2' x" by (rule f'_nat)
    also have "gc2 * ... \<le> f x" using x x0'_ge_x1 x0_le_x1 by (intro f2'_le_f) simp_all
    also have "f x = \<bar>f x\<bar>" using x f_nonneg' x0'_ge_x1 x0_le_x1 by simp
    finally show "gc2 * c5 * \<bar>f_approx (real x)\<bar> \<le> \<bar>f x\<bar>" 
      using gc2 f_approx_nonneg[OF x] by (simp add: algebra_simps)
  qed
  hence "f \<in> \<Omega>(\<lambda>x. f_approx (real x))" using gc2(1) f_nonneg' f_approx_nonneg
    by (intro landau_omega.bigI[of "gc2 * c5"] eventually_conj 
        mult_pos_pos c5 eventually_nat_real) (auto simp: eventually_at_top_linorder)
  note this[unfolded f_approx_def]
  }
  moreover have "x\<^sub>0'_min \<ge> A" unfolding x\<^sub>0'_min_def gx0_ge_x1 by simp
  ultimately show ?thesis by (intro that) auto
qed

lemma bigomega_f: 
  obtains a where "a \<ge> A" "f \<in> \<Omega>(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p+1)) a x))"
proof-
  from bigomega_f_aux[of A] guess a . note a = this
  define a' where "a' = real (max (nat \<lceil>a\<rceil>) 0) + 1"
  note a
  moreover have "a' \<in> \<nat>" by (auto simp: max_def a'_def)
  moreover have *: "a' \<ge> a + 1" unfolding a'_def by linarith
  moreover from * and a have "a' \<ge> A" by simp
  ultimately show ?thesis by (intro that[of a']) auto
qed

end



locale akra_bazzi_upper = akra_bazzi_function +
  fixes   g' :: "real \<Rightarrow> real"
  assumes g'_integrable:  "\<exists>a. \<forall>b\<ge>a. integrable (\<lambda>u. g' u / u powr (p + 1)) a b"
  and     g_growth1: "\<exists>C c1. c1 > 0 \<and> C < Min (set bs) \<and> 
                          eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. g' u \<ge> c1 * g' x) at_top"
  and     g_bigo:    "g \<in> O(g')"
  and     g'_nonneg: "eventually (\<lambda>x. g' x \<ge> 0) at_top"
begin


definition "gc1 \<equiv> SOME gc1. gc1 > 0 \<and> eventually (\<lambda>x. g x \<le> gc1 * g' (real x)) at_top"

lemma gc1: "gc1 > 0" "eventually (\<lambda>x. g x \<le> gc1 * g' (real x)) at_top"
proof-
  from g_bigo guess c by (elim landau_o.bigE) note c = this
  from g'_nonneg have "eventually (\<lambda>x::nat. g' (real x) \<ge> 0) at_top" by (rule eventually_nat_real)
  with c(2) have "eventually (\<lambda>x. g x \<le> c * g' (real x)) at_top" 
    using eventually_ge_at_top[of x\<^sub>1] by eventually_elim (insert g_nonneg, simp_all)
  with c(1) have "\<exists>gc1. gc1 > 0 \<and> eventually (\<lambda>x. g x \<le> gc1 * g' (real x)) at_top" by blast
  from someI_ex[OF this] show "gc1 > 0" "eventually (\<lambda>x. g x \<le> gc1 * g' (real x)) at_top"
    unfolding gc1_def by blast+
qed

definition "gx3 \<equiv> max x\<^sub>1 (SOME gx0. \<forall>x\<ge>gx0. g x \<le> gc1 * g' (real x))"

lemma gx3:
  assumes "x \<ge> gx3"
  shows   "g x \<le> gc1 * g' (real x)"
proof-
  from gc1(2) have "\<exists>gx3. \<forall>x\<ge>gx3. g x \<le> gc1 * g' (real x)" by (simp add: eventually_at_top_linorder)
  note someI_ex[OF this]
  moreover have "x \<ge> (SOME gx0. \<forall>x\<ge>gx0. g x \<le> gc1 * g' (real x))"
    using assms unfolding gx3_def by simp
  ultimately show "g x \<le> gc1 * g' (real x)" unfolding gx3_def by blast
qed

lemma gx3_ge_x1: "gx3 \<ge> x\<^sub>1" unfolding gx3_def by simp

function f' :: "nat \<Rightarrow> real" where
  "x < gx3 \<Longrightarrow> f' x = max 0 (f x / gc1)"
| "x \<ge> gx3 \<Longrightarrow> f' x = g' (real x) + (\<Sum>i<k. as!i*f' ((ts!i) x))"
using le_less_linear by (blast, simp_all)
termination by (relation "Wellfounded.measure (\<lambda>x. x)") 
               (insert gx3_ge_x1, simp_all add: step_less)

lemma f'_ge_f: "x \<ge> x\<^sub>0 \<Longrightarrow> gc1 * f' x \<ge> f x"
proof (induction rule: f'.induct)
  case (1 x)
  with gc1 f_nonneg show ?case by (simp add: max_def field_simps)
next
  case prems: (2 x)
  with gx3 have "gc1 * g' (real x) \<ge> g x" by force
  moreover from step_ge_x0 prems(1) gx3_ge_x1
    have "\<And>i. i < k \<Longrightarrow> x\<^sub>0 \<le> nat \<lfloor>(ts!i) x\<rfloor>" by (intro le_nat_floor) simp
  hence "\<And>i. i < k \<Longrightarrow> as!i * (gc1 * f' ((ts!i) x)) \<ge> as!i * f ((ts!i) x)"
    using prems(1) by (intro mult_left_mono a_ge_0 prems(2)) auto
  hence "gc1 * (\<Sum>i<k. as!i*f' ((ts!i) x)) \<ge> (\<Sum>i<k. as!i*f ((ts!i) x))"
    by (subst sum_distrib_left, intro sum_mono) (simp_all add: algebra_simps)
  ultimately show ?case using prems(1) gx3_ge_x1
    by (simp_all add: algebra_simps f_rec)
qed

lemma bigo_f_aux:
  obtains a where "a \<ge> A" "\<forall>a'\<ge>a. a' \<in> \<nat> \<longrightarrow> 
    f \<in> O(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p + 1)) a' x))"
proof-
  from g'_integrable guess a0 by (elim exE) note a0 = this
  from h_bound guess hb . note hb = this
  moreover from g_growth1 guess C c1 by (elim conjE exE) note C = this
  hence "eventually (\<lambda>x. \<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1 + e)) at_top"
    using hb(1) bs_nonempty by (intro C_bound) simp_all
  moreover from b_bounds hb(1) e_pos 
    have "eventually (\<lambda>x. \<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) at_top"
    by (rule akra_bazzi_asymptotics)
  moreover note gc1(2) C(3) g'_nonneg
  ultimately have "eventually (\<lambda>x. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e)) \<and>
                     (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e)) \<and>
                     (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) \<and> 
                     (\<forall>u\<in>{C*x..x}. g' u \<ge> c1 * g' x) \<and> g' x \<ge> 0) at_top"
    by (intro eventually_conj) (force elim!: eventually_conjE)+
  then have "\<exists>X. (\<forall>x\<ge>X. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e)) \<and>
                        (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e)) \<and>
                        (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x) \<and> 
                        (\<forall>u\<in>{C*x..x}. g' u \<ge> c1 * g' x) \<and> g' x \<ge> 0)"
    by (subst (asm) eventually_at_top_linorder) fast
  then guess X by (elim exE conjE) note X = this
  
  define x\<^sub>0'_min where "x\<^sub>0'_min = max A (max X (max 1 (max a0 (max gx3 (real x\<^sub>1 + 1)))))"
  {
  fix x\<^sub>0' :: real assume x0'_props: "x\<^sub>0' \<ge> x\<^sub>0'_min" "x\<^sub>0' \<in> \<nat>"
  hence x0'_ge_x1: "x\<^sub>0' \<ge> real (x\<^sub>1+1)" and x0'_ge_1: "x\<^sub>0' \<ge> 1" and x0'_ge_X: "x\<^sub>0' \<ge> X" 
    unfolding x\<^sub>0'_min_def by linarith+
  hence x0'_pos: "x\<^sub>0' > 0" and  x0'_nonneg: "x\<^sub>0' \<ge> 0" by simp_all
  have x0': "\<forall>x\<ge>x\<^sub>0'. (\<forall>h\<in>set hs'. \<bar>h x\<bar> \<le> hb*x/ln x powr (1+e))"
            "\<forall>x\<ge>x\<^sub>0'. (\<forall>b\<in>set bs. C*x \<le> b*x - hb*x/ln x powr (1+e))"
            "\<forall>x\<ge>x\<^sub>0'. (\<forall>b\<in>set bs. akra_bazzi_asymptotics b hb e p x)" 
            "\<forall>x\<ge>x\<^sub>0'. \<forall>u\<in>{C*x..x}. g' u \<ge> c1 * g' x" "\<forall>x\<ge>x\<^sub>0'. g' x \<ge> 0"
            using X x0'_ge_X by auto
  from x0'_props(2) have x0'_int: "real (nat \<lfloor>x\<^sub>0'\<rfloor>) = x\<^sub>0'" by (rule real_natfloor_nat)
  from x0'_props have x0'_ge_gx0: "x\<^sub>0' \<ge> gx3" and x0'_ge_a0: "x\<^sub>0' \<ge> a0" 
    unfolding x\<^sub>0'_min_def by simp_all
  hence f'_nonneg: "\<And>x. x \<ge> x\<^sub>0' \<Longrightarrow> f' x \<ge> 0"
    using order.trans[OF f_nonneg f'_ge_f] gc1(1) x0'_ge_x1 x0_le_x1
    by (simp add: zero_le_mult_iff del: f'.simps)
  
  define bm where "bm = Min (set bs)"
  define x\<^sub>1' where "x\<^sub>1' = 2 * x\<^sub>0' * inverse bm"
  define fb1 where "fb1 = Max {f' x |x. x \<in> {x\<^sub>0'..x\<^sub>1'}}"
  
from b_bounds bs_nonempty have "bm > 0" "bm < 1" unfolding bm_def by auto
  hence "1 < 2 * inverse bm" by (simp add: field_simps)
  from mult_strict_left_mono[OF this x0'_pos] 
    have x0'_lt_x1': "x\<^sub>0' < x\<^sub>1'" and x0'_le_x1': "x\<^sub>0' \<le> x\<^sub>1'" unfolding x\<^sub>1'_def by simp_all 
    
  from x0_le_x1 x0'_ge_x1 have ge_x0'D: "\<And>x. x\<^sub>0' \<le> real x \<Longrightarrow> x\<^sub>0 \<le> x" by simp
  from x0'_ge_x1 x0'_le_x1' have gt_x1'D: "\<And>x. x\<^sub>1' < real x \<Longrightarrow> x\<^sub>1 \<le> x" by simp
  
  have x0'_x1': "\<forall>b\<in>set bs. 2 * x\<^sub>0' * inverse b \<le> x\<^sub>1'"
  proof
    fix b assume b: "b \<in> set bs"
    hence "bm \<le> b" by (simp add: bm_def)
    moreover from b b_bounds bs_nonempty have "bm > 0" "b > 0" unfolding bm_def by auto
    ultimately have "inverse b \<le> inverse bm" by simp
    with x0'_nonneg show "2 * x\<^sub>0' * inverse b \<le> x\<^sub>1'" 
      unfolding x\<^sub>1'_def by (intro mult_left_mono) simp_all
  qed
  
  note f_nonneg' = f_nonneg
  have "\<And>x. real x \<ge> x\<^sub>0' \<Longrightarrow> x \<ge> nat \<lfloor>x\<^sub>0'\<rfloor>" "\<And>x. real x \<le> x\<^sub>1' \<Longrightarrow> x \<le> nat \<lceil>x\<^sub>1'\<rceil>" by linarith+  
  hence "{x |x. real x \<in> {x\<^sub>0'..x\<^sub>1'}} \<subseteq> {x |x. x \<in> {nat \<lfloor>x\<^sub>0'\<rfloor>..nat \<lceil>x\<^sub>1'\<rceil>}}" by auto
  hence "finite {x |x::nat. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by (rule finite_subset) auto
  hence fin: "finite {f' x |x::nat. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by force

  note facts = hs'_real e_pos length_hs' length_as length_bs k_not_0 a_ge_0 p_props x0'_ge_1
               f'_nonneg f_rec[OF gt_x1'D] x0' x0'_int x0'_x1' gc1(1) decomp
  from b_bounds x0'_le_x1' x0'_ge_gx0 x0'_ge_x1 
  interpret abr: akra_bazzi_nat_to_real as bs hs' k x\<^sub>0' x\<^sub>1' hb e p f' g'
    by (unfold_locales) (auto simp add: facts simp del: f'.simps intro!: f'.simps(2))
  
  have f'_nat: "\<And>x::nat. abr.f' (real x) = f' x"
  proof-
    fix x :: nat show "abr.f' (real (x::nat)) = f' x"
    proof (induction "real x" arbitrary: x rule: abr.f'.induct)
      case (2 x)
      note x = this(1) and IH = this(2)
      from x have "abr.f' (real x) = g' (real x) + (\<Sum>i<k. as!i*abr.f' (bs!i*real x + (hs!i) x))"
        by (auto simp: gt_x1'D hs'_real intro!: sum.cong)
      also have "(\<Sum>i<k. as!i*abr.f' (bs!i*real x + (hs!i) x)) = (\<Sum>i<k. as!i*f' ((ts!i) x))"
      proof (rule sum.cong, simp, clarify)
        fix i assume i: "i < k"
        from i x x0'_le_x1' x0'_ge_x1 have *: "bs!i * real x + (hs!i) x = real ((ts!i) x)"
          by (intro decomp) simp_all
        also from i * have "abr.f' ... = f' ((ts!i) x)"
          by (subst IH[of i]) (simp_all add: hs'_real)
        finally show "as!i*abr.f' (bs!i*real x+(hs!i) x) = as!i*f' ((ts!i) x)" by simp
      qed
      also from x have "g' x + ... = f' x" using x0'_le_x1' x0'_ge_gx0 by simp
      finally show ?case .
    qed simp
  qed
  
  interpret akra_bazzi_integral integrable integral by (rule integral)
  interpret akra_bazzi_real_upper as bs hs' k x\<^sub>0' x\<^sub>1' hb e p integrable integral abr.f' g' C fb1 c1
  proof (unfold_locales)
    fix x assume "x \<ge> x\<^sub>0'" "x \<le> x\<^sub>1'"
    thus "abr.f' x \<ge> 0" by (intro abr.f'_base) simp_all
  next
    fix x assume x:"x \<ge> x\<^sub>0'"
    show "integrable (\<lambda>x. g' x / x powr (p + 1)) x\<^sub>0' x"
      by (rule integrable_subinterval[of _ a0 x]) (insert a0 x0'_ge_a0 x, auto)
  next
    fix x assume x: "x \<ge> x\<^sub>0'" "x \<le> x\<^sub>1'"
    have "x\<^sub>0' = real (nat \<lfloor>x\<^sub>0'\<rfloor>)" by (simp add: x0'_int)
    also from x have "... \<le> real (nat \<lfloor>x\<rfloor>)" by (auto intro!: nat_mono floor_mono)
    finally have "x\<^sub>0' \<le> real (nat \<lfloor>x\<rfloor>)" .
    moreover have "real (nat \<lfloor>x\<rfloor>) \<le> x\<^sub>1'" using x x0'_ge_1 by linarith
    ultimately have "f' (nat \<lfloor>x\<rfloor>) \<in> {f' x |x. real x \<in> {x\<^sub>0'..x\<^sub>1'}}" by force
    from fin and this have "f' (nat \<lfloor>x\<rfloor>) \<le> fb1" unfolding fb1_def by (rule Max_ge)
    with x show "abr.f' x \<le> fb1" by simp
  qed (insert x0'(2) x0'_le_x1' x0'_ge_x1 C, simp_all add: facts)

  from akra_bazzi_upper guess c6 . note c6 = this
  { 
    fix x :: nat assume "x \<ge> nat \<lceil>x\<^sub>0'\<rceil>"
    hence x: "real x \<ge> x\<^sub>0'" by linarith
    have "f x \<le> gc1 * f' x" using x x0'_ge_x1 x0_le_x1 by (intro f'_ge_f) simp_all
    also have "f' x = abr.f' (real x)" by (simp add: f'_nat)
    also note c6(1)[OF x]
    also from f_nonneg' x x0'_ge_x1 x0_le_x1 have "f x = \<bar>f x\<bar>" by simp
    also from f_approx_nonneg x have "f_approx (real x) = \<bar>f_approx (real x)\<bar>" by simp
    finally have "gc1 * c6 * \<bar>f_approx (real x)\<bar> \<ge> \<bar>f x\<bar>" using gc1 by (simp add: algebra_simps)
  }
  hence "eventually (\<lambda>x. \<bar>f x\<bar> \<le> gc1 * c6 * \<bar>f_approx (real x)\<bar>) at_top"
    using eventually_ge_at_top[of "nat \<lceil>x\<^sub>0'\<rceil>"] by (auto elim!: eventually_mono)
  hence "f \<in> O(\<lambda>x. f_approx (real x))" using gc1(1) f_nonneg' f_approx_nonneg
    by (intro landau_o.bigI[of "gc1 * c6"] eventually_conj 
        mult_pos_pos c6 eventually_nat_real) (auto simp: eventually_at_top_linorder)
  note this[unfolded f_approx_def]
  }
  moreover have "x\<^sub>0'_min \<ge> A" unfolding x\<^sub>0'_min_def gx3_ge_x1 by simp
  ultimately show ?thesis by (intro that) auto
qed

lemma bigo_f: 
  obtains a where "a > A" "f \<in> O(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p + 1)) a x))"
proof-
  from bigo_f_aux[of A] guess a . note a = this
  define a' where "a' = real (max (nat \<lceil>a\<rceil>) 0) + 1"
  note a
  moreover have "a' \<in> \<nat>" by (auto simp: max_def a'_def)
  moreover have *: "a' \<ge> a + 1" unfolding a'_def by linarith
  moreover from * and a have "a' > A" by simp
  ultimately show ?thesis by (intro that[of a']) auto
qed

end

locale akra_bazzi = akra_bazzi_function +
  fixes   g' :: "real \<Rightarrow> real"
  assumes f_pos:         "eventually (\<lambda>x. f x > 0) at_top"
  and     g'_nonneg:     "eventually (\<lambda>x. g' x \<ge> 0) at_top"
  assumes g'_integrable:  "\<exists>a. \<forall>b\<ge>a. integrable (\<lambda>u. g' u / u powr (p + 1)) a b"
  and     g_growth1:  "\<exists>C c1. c1 > 0 \<and> C < Min (set bs) \<and> 
                           eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. g' u \<ge> c1 * g' x) at_top"
  and     g_growth2:  "\<exists>C c2. c2 > 0 \<and> C < Min (set bs) \<and> 
                           eventually (\<lambda>x. \<forall>u\<in>{C*x..x}. g' u \<le> c2 * g' x) at_top"
  and     g_bounded:  "eventually (\<lambda>a::real. (\<forall>b>a. \<exists>c. \<forall>x\<in>{a..b}. g' x \<le> c)) at_top"
  and     g_bigtheta: "g \<in> \<Theta>(g')"
begin

sublocale akra_bazzi_lower using f_pos g_growth2 g_bounded 
  bigthetaD2[OF g_bigtheta] g'_nonneg g'_integrable by unfold_locales 
sublocale akra_bazzi_upper using g_growth1 bigthetaD1[OF g_bigtheta] 
  g'_nonneg g'_integrable by unfold_locales

lemma bigtheta_f: 
  obtains a where "a > A" "f \<in> \<Theta>(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p + 1)) a x))"
proof-
  from bigo_f_aux[of A] guess a . note a = this
  moreover from bigomega_f_aux[of A] guess b . note b = this
  let ?a = "real (max (max (nat \<lceil>a\<rceil>) (nat \<lceil>b\<rceil>)) 0) + 1"
  have "?a \<in> \<nat>" by (auto simp: max_def)
  moreover have "?a \<ge> a" "?a \<ge> b" by linarith+
  ultimately have "f \<in> \<Theta>(\<lambda>x. x powr p *(1 + integral (\<lambda>u. g' u / u powr (p + 1)) ?a x))" 
    using a b by (intro bigthetaI) blast+
  moreover from a b have "?a > A" by linarith
  ultimately show ?thesis by (intro that[of ?a]) simp_all
qed

end


named_theorems akra_bazzi_term_intros "introduction rules for Akra-Bazzi terms"

lemma akra_bazzi_term_floor_add [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 + c" "c < (1 - b) * real x\<^sub>1" "x\<^sub>1 > 0"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x + c\<rfloor>)"
proof (rule akra_bazzi_termI[OF zero_less_one])
  fix x assume x: "x \<ge> x\<^sub>1"
  from assms x have "real x\<^sub>0 \<le> b * real x\<^sub>1 + c" by simp
  also from x assms have "... \<le> b * real x + c" by auto
  finally have step_ge_x0: "b * real x + c \<ge> real x\<^sub>0" by simp
  thus "nat \<lfloor>b * real x + c\<rfloor> \<ge> x\<^sub>0" by (subst le_nat_iff) (simp_all add: le_floor_iff)

  from assms x have "c < (1 - b) * real x\<^sub>1" by simp
  also from assms x have "... \<le> (1 - b) * real x" by (intro mult_left_mono) simp_all
  finally show "nat \<lfloor>b * real x + c\<rfloor> < x" using assms step_ge_x0 
    by (subst nat_less_iff) (simp_all add: floor_less_iff algebra_simps)
  
  from step_ge_x0 have "real_of_int \<lfloor>c + b * real x\<rfloor> = real_of_int (nat \<lfloor>c + b * real x\<rfloor>)" by linarith
  thus "(b * real x) + (\<lfloor>b * real x + c\<rfloor> - (b * real x)) = 
          real (nat \<lfloor>b * real x + c\<rfloor>)" by linarith
next
  have "(\<lambda>x::nat. real_of_int \<lfloor>b * real x + c\<rfloor> - b * real x) \<in> O(\<lambda>_. \<bar>c\<bar> + 1)"
    by (intro landau_o.big_mono always_eventually allI, unfold real_norm_def) linarith
  also have "(\<lambda>_::nat. \<bar>c\<bar> + 1) \<in> O(\<lambda>x. real x / ln (real x) powr (1 + 1))" by force
  finally show "(\<lambda>x::nat. real_of_int \<lfloor>b * real x + c\<rfloor> - b * real x) \<in> 
                    O(\<lambda>x. real x / ln (real x) powr (1+1))" .
qed

lemma akra_bazzi_term_floor_add' [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 + real c" "real c < (1 - b) * real x\<^sub>1" "x\<^sub>1 > 0"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x\<rfloor> + c)"
proof-
  from assms have "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x + real c\<rfloor>)" 
    by (rule akra_bazzi_term_floor_add)
  also have "(\<lambda>x. nat \<lfloor>b*real x + real c\<rfloor>) = (\<lambda>x::nat. nat \<lfloor>b*real x\<rfloor> + c)"
  proof
    fix x :: nat 
    have "\<lfloor>b * real x + real c\<rfloor> = \<lfloor>b * real x\<rfloor> + int c" by linarith
    also from assms have "nat ... = nat \<lfloor>b * real x\<rfloor> + c" by (simp add: nat_add_distrib)
    finally show "nat \<lfloor>b * real x + real c\<rfloor> = nat \<lfloor>b * real x\<rfloor> + c" .
  qed
  finally show ?thesis .
qed

lemma akra_bazzi_term_floor_subtract [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 - c" "0 < c + (1 - b) * real x\<^sub>1" "x\<^sub>1 > 0"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x - c\<rfloor>)"
  by (subst diff_conv_add_uminus, rule akra_bazzi_term_floor_add, insert assms) simp_all

lemma akra_bazzi_term_floor_subtract' [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 - real c" "0 < real c + (1 - b) * real x\<^sub>1" "x\<^sub>1 > 0"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x\<rfloor> - c)"
proof-
  from assms have "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x - real c\<rfloor>)" 
    by (intro akra_bazzi_term_floor_subtract) simp_all
  also have "(\<lambda>x. nat \<lfloor>b*real x - real c\<rfloor>) = (\<lambda>x::nat. nat \<lfloor>b*real x\<rfloor> - c)"
  proof
    fix x :: nat 
    have "\<lfloor>b * real x - real c\<rfloor> = \<lfloor>b * real x\<rfloor> - int c" by linarith
    also from assms have "nat ... = nat \<lfloor>b * real x\<rfloor> - c" by (simp add: nat_diff_distrib)
    finally show "nat \<lfloor>b * real x - real c\<rfloor> = nat \<lfloor>b * real x\<rfloor> - c" .
  qed
  finally show ?thesis .
qed


lemma akra_bazzi_term_floor [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1" "0 < (1 - b) * real x\<^sub>1" "x\<^sub>1 > 0"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lfloor>b*real x\<rfloor>)"
  using assms akra_bazzi_term_floor_add[where c = 0] by simp



lemma akra_bazzi_term_ceiling_add [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 + c" "c + 1 \<le> (1 - b) * x\<^sub>1"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x + c\<rceil>)"
proof (rule akra_bazzi_termI[OF zero_less_one])
  fix x assume x: "x \<ge> x\<^sub>1"
  have "0 \<le> real x\<^sub>0" by simp
  also from assms have "real x\<^sub>0 \<le> b * real x\<^sub>1 + c" by simp
  also from assms x have "b * real x\<^sub>1 \<le> b * real x" by (intro mult_left_mono) simp_all
  hence "b * real x\<^sub>1 + c \<le> b * real x + c" by simp
  also have "b * real x + c \<le> real_of_int \<lceil>b * real x + c\<rceil>" by linarith
  finally have bx_nonneg: "real_of_int \<lceil>b * real x + c\<rceil> \<ge> 0" .
  
  have "c + 1 \<le> (1 - b) * x\<^sub>1" by fact
  also have "(1 - b) * x\<^sub>1 \<le> (1 - b) * x" using assms x by (intro mult_left_mono) simp_all
  finally have "b * real x + c + 1 \<le> real x" using assms by (simp add: algebra_simps)
  with bx_nonneg show "nat \<lceil>b * real x + c\<rceil> < x" by (subst nat_less_iff) (simp_all add: ceiling_less_iff)
  
  have "real x\<^sub>0 \<le> b * real x\<^sub>1 + c" by fact
  also have "... \<le> real_of_int \<lceil>...\<rceil>" by linarith
  also have "x\<^sub>1 \<le> x" by fact
  finally show "x\<^sub>0 \<le> nat \<lceil>b * real x + c\<rceil>" using assms by (force simp: ceiling_mono)
  
  show "b * real x + (\<lceil>b * real x + c\<rceil> - b * real x) = real (nat \<lceil>b * real x + c\<rceil>)"
    using assms bx_nonneg by simp
next
  have "(\<lambda>x::nat. real_of_int \<lceil>b * real x + c\<rceil> - b * real x) \<in> O(\<lambda>_. \<bar>c\<bar> + 1)"
    by (intro landau_o.big_mono always_eventually allI, unfold real_norm_def) linarith
  also have "(\<lambda>_::nat. \<bar>c\<bar> + 1) \<in> O(\<lambda>x. real x / ln (real x) powr (1 + 1))" by force
  finally show "(\<lambda>x::nat. real_of_int \<lceil>b * real x + c\<rceil> - b * real x) \<in> 
                    O(\<lambda>x. real x / ln (real x) powr (1+1))" .
qed

lemma akra_bazzi_term_ceiling_add' [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 + real c" "real c + 1 \<le> (1 - b) * x\<^sub>1"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x\<rceil> + c)"
proof-
  from assms have "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x + real c\<rceil>)" 
    by (rule akra_bazzi_term_ceiling_add)
  also have "(\<lambda>x. nat \<lceil>b*real x + real c\<rceil>) = (\<lambda>x::nat. nat \<lceil>b*real x\<rceil> + c)"
  proof
    fix x :: nat 
    from assms have "0 \<le> b * real x" by simp
    also have "b * real x \<le> real_of_int \<lceil>b * real x\<rceil>" by linarith
    finally have bx_nonneg: "\<lceil>b * real x\<rceil> \<ge> 0" by simp

    have "\<lceil>b * real x + real c\<rceil> = \<lceil>b * real x\<rceil> + int c" by linarith
    also from assms bx_nonneg have "nat ... = nat \<lceil>b * real x\<rceil> + c" 
      by (subst nat_add_distrib) simp_all
    finally show "nat \<lceil>b * real x + real c\<rceil> = nat \<lceil>b * real x\<rceil> + c" .
  qed
  finally show ?thesis .
qed

lemma akra_bazzi_term_ceiling_subtract [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 - c" "1 \<le> c + (1 - b) * x\<^sub>1"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x - c\<rceil>)"
  by (subst diff_conv_add_uminus, rule akra_bazzi_term_ceiling_add, insert assms) simp_all

lemma akra_bazzi_term_ceiling_subtract' [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1 - real c" "1 \<le> real c + (1 - b) * x\<^sub>1"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x\<rceil> - c)"
proof-
  from assms have "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x - real c\<rceil>)" 
    by (intro akra_bazzi_term_ceiling_subtract) simp_all
  also have "(\<lambda>x. nat \<lceil>b*real x - real c\<rceil>) = (\<lambda>x::nat. nat \<lceil>b*real x\<rceil> - c)"
  proof
    fix x :: nat 
    from assms have "0 \<le> b * real x" by simp
    also have "b * real x \<le> real_of_int \<lceil>b * real x\<rceil>" by linarith
    finally have bx_nonneg: "\<lceil>b * real x\<rceil> \<ge> 0" by simp

    have "\<lceil>b * real x - real c\<rceil> = \<lceil>b * real x\<rceil> - int c" by linarith
    also from assms bx_nonneg have "nat ... = nat \<lceil>b * real x\<rceil> - c" by simp
    finally show "nat \<lceil>b * real x - real c\<rceil> = nat \<lceil>b * real x\<rceil> - c" .
  qed
  finally show ?thesis .
qed

lemma akra_bazzi_term_ceiling [akra_bazzi_term_intros]:
  assumes "(b::real) > 0" "b < 1" "real x\<^sub>0 \<le> b * real x\<^sub>1" "1 \<le> (1 - b) * x\<^sub>1"
  shows   "akra_bazzi_term x\<^sub>0 x\<^sub>1 b (\<lambda>x. nat \<lceil>b*real x\<rceil>)"
  using assms akra_bazzi_term_ceiling_add[where c = 0] by simp


end
