theory Asymptotic_Equivalence
imports Complex_Main Landau_Simprocs
begin

named_theorems asymp_equiv_intros
named_theorems asymp_equiv_simps

definition asymp_equiv :: "('a::order \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" (infix "\<sim>" 50) 
  where "f \<sim> g \<longleftrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) at_top"

lemma asymp_equivI: "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) at_top \<Longrightarrow> f \<sim> g"
  by (simp add: asymp_equiv_def)

lemma asymp_equivD: "f \<sim> g \<Longrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) at_top"
  by (simp add: asymp_equiv_def)

lemma asymp_equiv_refl [simp, asymp_equiv_intros]: "f \<sim> f"
proof (intro asymp_equivI)
  have "eventually (\<lambda>x. 1 = (if f x = 0 \<and> f x = 0 then 1 else f x / f x)) at_top"
    by (intro always_eventually) simp
  moreover have "((\<lambda>_. 1) \<longlongrightarrow> 1) at_top" by simp
  ultimately show "((\<lambda>x. if f x = 0 \<and> f x = 0 then 1 else f x / f x) \<longlongrightarrow> 1) at_top"
    by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_symI: 
  assumes "f \<sim> g"
  shows   "g \<sim> f"
  using tendsto_inverse[OF asymp_equivD[OF assms]]
  by (auto intro!: asymp_equivI simp: if_distrib conj_commute cong: if_cong)

lemma asymp_equiv_sym: "f \<sim> g \<longleftrightarrow> g \<sim> f"
  by (blast intro: asymp_equiv_symI)

lemma asymp_equivI': 
  assumes "((\<lambda>x::'a::order. f x / g x) \<longlongrightarrow> 1) at_top"
  shows   "f \<sim> g"
proof (cases "(at_top :: 'a filter) = bot")
  case False
  have "eventually (\<lambda>x. f x \<noteq> 0) at_top"
  proof (rule ccontr)
    assume "\<not>eventually (\<lambda>x. f x \<noteq> 0) at_top"
    hence "frequently (\<lambda>x. f x = 0) at_top" by (simp add: frequently_def)
    hence "frequently (\<lambda>x. f x / g x = 0) at_top" by (auto elim!: frequently_elim1)
    from limit_frequently_eq[OF False this assms] show False by simp_all
  qed
  hence "eventually (\<lambda>x. f x / g x = (if f x = 0 \<and> g x = 0 then 1 else f x / g x)) at_top"
    by eventually_elim simp
  from this and assms show "f \<sim> g" unfolding asymp_equiv_def 
    by (rule Lim_transform_eventually)
qed (simp_all add: asymp_equiv_def)


lemma asymp_equiv_cong:
  assumes "eventually (\<lambda>x. f1 x = f2 x) at_top" "eventually (\<lambda>x. g1 x = g2 x) at_top"
  shows   "f1 \<sim> g1 \<longleftrightarrow> f2 \<sim> g2"
  unfolding asymp_equiv_def
proof (rule tendsto_cong, goal_cases)
  case 1
  from assms show ?case by eventually_elim simp
qed

lemma asymp_equiv_eventually_zeros:
  assumes "f \<sim> g"
  shows   "eventually (\<lambda>x. f x = 0 \<longleftrightarrow> g x = 0) at_top"
proof -
  from order_tendstoD[OF asymp_equivD[OF assms], of "1/2"]
    have "\<forall>\<^sub>F x in at_top. 1 / 2 < (if f x = 0 \<and> g x = 0 then 1 else f x / g x)" by simp
  thus ?thesis by eventually_elim (auto split: if_splits)
qed

lemma asymp_equiv_transfer:
  assumes "f1 \<sim> g1" "eventually (\<lambda>x. f1 x = f2 x) at_top" "eventually (\<lambda>x. g1 x = g2 x) at_top"
  shows   "f2 \<sim> g2"
  using assms(1) asymp_equiv_cong[OF assms(2,3)] by simp

lemma asymp_equiv_transfer_trans [trans]:
  assumes "(\<lambda>x. f x (h1 x)) \<sim> (\<lambda>x. g x (h1 x))"
  assumes "eventually (\<lambda>x. h1 x = h2 x) at_top"
  shows   "(\<lambda>x. f x (h2 x)) \<sim> (\<lambda>x. g x (h2 x))"
  by (rule asymp_equiv_transfer[OF assms(1)]) (insert assms(2), auto elim!: eventually_mono)

lemma asymp_equiv_trans [trans]:
  fixes f g h
  assumes "f \<sim> g" "g \<sim> h"
  shows   "f \<sim> h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from assms[THEN asymp_equiv_eventually_zeros]
    have "eventually (\<lambda>x. ?T f g x * ?T g h x = ?T f h x) at_top" by eventually_elim simp
  moreover from tendsto_mult[OF assms[THEN asymp_equivD]] 
    have "((\<lambda>x. ?T f g x * ?T g h x) \<longlongrightarrow> 1) at_top" by simp
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_trans_lift1 [trans]:
  assumes "a \<sim> f b" "b \<sim> c" "\<And>c d. c \<sim> d \<Longrightarrow> f c \<sim> f d"
  shows   "a \<sim> f c"
  using assms by (blast intro: asymp_equiv_trans)

lemma asymp_equiv_trans_lift2 [trans]:
  assumes "f a \<sim> b" "a \<sim> c" "\<And>c d. c \<sim> d \<Longrightarrow> f c \<sim> f d"
  shows   "f c \<sim> b"
  using asymp_equiv_symI[OF assms(3)[OF assms(2)]] assms(1)
  by (blast intro: asymp_equiv_trans)

(* TODO Move *)
lemma Lim_eventually: "eventually (\<lambda>x. f x = c) F \<Longrightarrow> filterlim f (nhds c) F"
  by (simp add: eventually_mono eventually_nhds_x_imp_x filterlim_iff)

lemma asymp_equivD_const:
  assumes "f \<sim> (\<lambda>_. c)"
  shows   "(f \<longlongrightarrow> c) at_top"
proof (cases "c = 0")
  case False
  with tendsto_mult_right[OF asymp_equivD[OF assms], of c] show ?thesis by simp
next
  case True
  with asymp_equiv_eventually_zeros[OF assms] show ?thesis
    by (simp add: Lim_eventually)
qed

lemma asymp_equiv_refl_ev:
  assumes "eventually (\<lambda>x. f x = g x) at_top"
  shows   "f \<sim> g"
  by (intro asymp_equivI Lim_eventually)
     (insert assms, auto elim!: eventually_mono)

lemma asymp_equiv_sandwich:
  assumes "eventually (\<lambda>x. f x \<ge> 0) at_top"
  assumes "eventually (\<lambda>x. f x \<le> g x) at_top"
  assumes "eventually (\<lambda>x. g x \<le> h x) at_top"
  assumes "f \<sim> h"
  shows   "g \<sim> f" "g \<sim> h"
proof -
  show "g \<sim> f"
  proof (rule asymp_equivI, rule tendsto_sandwich)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. (if h n = 0 \<and> f n = 0 then 1 else h n / f n) \<ge>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) at_top"
        by eventually_elim (auto intro!: divide_right_mono)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. 1 \<le>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) at_top"
        by eventually_elim (auto intro!: divide_right_mono)
  qed (insert asymp_equiv_symI[OF assms(4)], simp_all add: asymp_equiv_def)
  also note \<open>f \<sim> h\<close>
  finally show "g \<sim> h" .
qed


context
begin

private lemma asymp_equiv_add_rightI:
  assumes "f \<sim> g" "h \<in> o(g)"
  shows   "(\<lambda>x. f x + h x) \<sim> g"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from landau_o.smallD[OF assms(2) zero_less_one]
    have ev: "eventually (\<lambda>x. g x = 0 \<longrightarrow> h x = 0) at_top" by eventually_elim auto
  have "(\<lambda>x. f x + h x) \<sim> g \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1) at_top"
    unfolding asymp_equiv_def using ev
    by (intro tendsto_cong) (auto elim!: eventually_mono simp: divide_simps)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1 + 0) at_top" by simp
  also have \<dots> by (intro tendsto_intros asymp_equivD assms smalloD_tendsto)
  finally show "(\<lambda>x. f x + h x) \<sim> g" .
qed

lemma asymp_equiv_add_right [asymp_equiv_simps]:
  assumes "h \<in> o(g)"
  shows   "(\<lambda>x. f x + h x) \<sim> g \<longleftrightarrow> f \<sim> g"
proof
  assume "(\<lambda>x. f x + h x) \<sim> g"
  from asymp_equiv_add_rightI[OF this, of "\<lambda>x. -h x"] assms show "f \<sim> g"
    by simp
qed (simp_all add: asymp_equiv_add_rightI assms)

end

lemma asymp_equiv_add_left [asymp_equiv_simps]: 
  assumes "h \<in> o(g)"
  shows   "(\<lambda>x. h x + f x) \<sim> g \<longleftrightarrow> f \<sim> g"
  using asymp_equiv_add_right[OF assms] by (simp add: add.commute)

lemma asymp_equiv_add_right' [asymp_equiv_simps]:
  assumes "h \<in> o(g)"
  shows   "g \<sim> (\<lambda>x. f x + h x) \<longleftrightarrow> g \<sim> f"
  using asymp_equiv_add_right[OF assms] by (simp add: asymp_equiv_sym)
  
lemma asymp_equiv_add_left' [asymp_equiv_simps]:
  assumes "h \<in> o(g)"
  shows   "g \<sim> (\<lambda>x. h x + f x) \<longleftrightarrow> g \<sim> f"
  using asymp_equiv_add_left[OF assms] by (simp add: asymp_equiv_sym)

lemma asymp_equiv_uminus [asymp_equiv_intros]:
  "f \<sim> g \<Longrightarrow> (\<lambda>x. -f x) \<sim> (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_uminus_iff [asymp_equiv_simps]:
  "(\<lambda>x. -f x) \<sim> g \<longleftrightarrow> f \<sim> (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_mult [asymp_equiv_intros]:
  fixes f1 f2 g1 g2 :: "'a :: order \<Rightarrow> real"
  assumes "f1 \<sim> g1" "f2 \<sim> g2"
  shows   "(\<lambda>x. f1 x * f2 x) \<sim> (\<lambda>x. g1 x * g2 x)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  let ?S = "\<lambda>x. (if f1 x = 0 \<and> g1 x = 0 then 1 - ?T f2 g2 x
                   else if f2 x = 0 \<and> g2 x = 0 then 1 - ?T f1 g1 x else 0)"
  let ?S' = "\<lambda>x. ?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) x - ?T f1 g1 x * ?T f2 g2 x"
  {
    fix f g :: "'a \<Rightarrow> real" assume "f \<sim> g"
    have "((\<lambda>x. 1 - ?T f g x) \<longlongrightarrow> 0) at_top"
      by (rule tendsto_eq_intros refl asymp_equivD[OF \<open>f \<sim> g\<close>])+ simp_all
  } note A = this    

  from assms have "((\<lambda>x. ?T f1 g1 x * ?T f2 g2 x) \<longlongrightarrow> 1 * 1) at_top"
    by (intro tendsto_mult asymp_equivD)
  moreover {
    have "eventually (\<lambda>x. ?S x = ?S' x) at_top"
      using assms[THEN asymp_equiv_eventually_zeros] by eventually_elim auto
    moreover have "(?S \<longlongrightarrow> 0) at_top"
      by (intro filterlim_If assms[THEN A, THEN tendsto_mono[rotated]])
         (auto intro: le_infI1 le_infI2)
    ultimately have "(?S' \<longlongrightarrow> 0) at_top" by (rule Lim_transform_eventually)
  }
  ultimately have "(?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) \<longlongrightarrow> 1 * 1) at_top"
    by (rule Lim_transform)
  thus ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_power [asymp_equiv_intros]:
  "f \<sim> g \<Longrightarrow> (\<lambda>x. f x ^ n) \<sim> (\<lambda>x. g x ^ n)"
  by (induction n) (simp_all add: asymp_equiv_mult)

lemma asymp_equiv_inverse [asymp_equiv_intros]:
  assumes "f \<sim> g"
  shows   "(\<lambda>x. inverse (f x)) \<sim> (\<lambda>x. inverse (g x))"
proof -
  from tendsto_inverse[OF asymp_equivD[OF assms]]
    have "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) \<longlongrightarrow> 1) at_top"
    by (simp add: if_distrib cong: if_cong)
  also have "(\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) =
               (\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else inverse (f x) / inverse (g x))"
    by (intro ext) (simp add: field_simps)
  finally show ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_inverse_iff [asymp_equiv_simps]:
  "(\<lambda>x. inverse (f x)) \<sim> (\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<sim> g"
proof
  assume "(\<lambda>x. inverse (f x)) \<sim> (\<lambda>x. inverse (g x))"
  hence "(\<lambda>x. inverse (inverse (f x))) \<sim> (\<lambda>x. inverse (inverse (g x)))" (is ?P)
    by (rule asymp_equiv_inverse)
  also have "?P \<longleftrightarrow> f \<sim> g" by (intro asymp_equiv_cong) simp_all
  finally show "f \<sim> g" .
qed (simp_all add: asymp_equiv_inverse)

lemma asymp_equiv_divide [asymp_equiv_intros]:
  assumes "f1 \<sim> g1" "f2 \<sim> g2"
  shows   "(\<lambda>x. f1 x / f2 x) \<sim> (\<lambda>x. g1 x / g2 x)"
  using asymp_equiv_mult[OF assms(1) asymp_equiv_inverse[OF assms(2)]] by (simp add: field_simps)

lemma asymp_equiv_compose [asymp_equiv_intros]:
  assumes "f \<sim> g" "filterlim h at_top at_top"
  shows   "f \<circ> h \<sim> g \<circ> h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "f \<circ> h \<sim> g \<circ> h \<longleftrightarrow> ((?T f g \<circ> h) \<longlongrightarrow> 1) at_top"
    by (simp add: asymp_equiv_def o_def)
  also have "\<dots> \<longleftrightarrow> (?T f g \<longlongrightarrow> 1) (filtermap h at_top)"
    by (rule tendsto_compose_filtermap)
  also have "\<dots>"
    by (rule tendsto_mono[of _ at_top]) (insert assms, simp_all add: asymp_equiv_def filterlim_def)
  finally show ?thesis .
qed

lemma asymp_equiv_compose':
  assumes "f \<sim> g" "filterlim h at_top at_top"
  shows   "(\<lambda>x. f (h x)) \<sim> (\<lambda>x. g (h x))"
  using asymp_equiv_compose[OF assms] by (simp add: o_def)
  
lemma asymp_equiv_powr_real [asymp_equiv_intros]:
  assumes "f \<sim> g" "eventually (\<lambda>x. f x \<ge> 0) at_top" "eventually (\<lambda>x. g x \<ge> 0) at_top"
  shows   "(\<lambda>x. f x powr y) \<sim> (\<lambda>x. g x powr y)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "eventually (\<lambda>x. ?T f g x powr y = ?T (\<lambda>x. f x powr y) (\<lambda>x. g x powr y) x) at_top"
    using asymp_equiv_eventually_zeros[OF assms(1)] assms(2,3)
    by eventually_elim (auto simp: powr_divide)
  moreover have "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1 powr y) at_top"
    by (intro tendsto_intros asymp_equivD[OF assms(1)]) simp_all
  hence "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1) at_top" by simp
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_abs [asymp_equiv_intros]:
  assumes "f \<sim> g"
  shows   "(\<lambda>x. \<bar>f x\<bar>) \<sim> (\<lambda>x. \<bar>g x\<bar>)"
  using tendsto_rabs[OF asymp_equivD[OF assms]] 
  by (simp add: if_distrib asymp_equiv_def cong: if_cong)

lemma asymp_equiv_imp_eventually_le:
  assumes "f \<sim> g" "c > 1"
  shows   "eventually (\<lambda>x. \<bar>f x\<bar> \<le> c * \<bar>g x\<bar>) at_top"
proof -
  from order_tendstoD(2)[OF asymp_equivD[OF asymp_equiv_abs[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_eventually_ge:
  assumes "f \<sim> g" "c < 1"
  shows   "eventually (\<lambda>x. \<bar>f x\<bar> \<ge> c * \<bar>g x\<bar>) at_top"
proof -
  from order_tendstoD(1)[OF asymp_equivD[OF asymp_equiv_abs[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_bigo:
  assumes "f \<sim> g"
  shows   "f \<in> O(g)"
proof (rule bigoI)
  have "(3/2::real) > 1" by simp
  from asymp_equiv_imp_eventually_le[OF assms this]
    show "eventually (\<lambda>x. norm (f x) \<le> 3/2 * norm (g x)) at_top"
    by eventually_elim simp
qed

lemma asymp_equiv_imp_bigomega:
  "f \<sim> g \<Longrightarrow> f \<in> \<Omega>(g)"
  using asymp_equiv_imp_bigo[of g f] by (simp add: asymp_equiv_sym bigomega_iff_bigo)

lemma asymp_equiv_imp_bigtheta:
  "f \<sim> g \<Longrightarrow> f \<in> \<Theta>(g)"
  by (intro bigthetaI asymp_equiv_imp_bigo asymp_equiv_imp_bigomega)
  

lemma asymp_equivI'_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) at_top" "c \<noteq> 0"
  shows   "f \<sim> (\<lambda>x. c * g x)"
  using tendsto_mult[OF assms(1) tendsto_const[of "inverse c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)

lemma asymp_equivI'_inverse_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> inverse c) at_top" "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) \<sim> g"
  using tendsto_mult[OF assms(1) tendsto_const[of "c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)

lemma asymp_equiv_plus_const_left: "(\<lambda>n. c + real n) \<sim> (\<lambda>n. real n)"
  by (subst asymp_equiv_add_left) (auto intro!: asymp_equiv_intros eventually_gt_at_top)

lemma asymp_equiv_plus_const_right: "(\<lambda>n. real n + c) \<sim> (\<lambda>n. real n)"
  using asymp_equiv_plus_const_left[of c] by (simp add: add.commute)
  
end
