theory MVT_Ex
imports
  "HOL-Analysis.Analysis"
  "HOL-Decision_Procs.Approximation"
  "../ODE_Auxiliarities"
begin

subsection \<open>(Counter)Example of Mean Value Theorem in Euclidean Space \label{sec:countermvt}\<close>

text \<open>There is no exact analogon of the mean value theorem in the multivariate case!\<close>

lemma MVT_wrong: assumes
  "\<And>J a u (f::real*real\<Rightarrow>real*real).
      (\<And>x. FDERIV f x :> J x) \<Longrightarrow>
      (\<exists>t\<in>{0<..<1}. f (a + u) - f a = J (a + t *\<^sub>R u) u)"
  shows "False"
proof -
  have "\<And>t::real*real. FDERIV (\<lambda>t. (cos (fst t), sin (fst t))) t :> (\<lambda>h. (- ((fst h) * sin (fst t)), (fst h) * cos (fst t)))"
    by (auto intro!: derivative_eq_intros)
  from assms[OF this, of "(pi, pi)" "(pi, pi)"] obtain t::real where t: "0 < t" "t < 1" and
    "pi * sin (t * pi) = 2" "cos (t * pi) = 0"
    by auto
  then obtain n where tpi: "t * pi = real_of_int n * (pi / 2)" and "odd n"
    by (auto simp: cos_zero_iff_int)
  then have teq: "t = real_of_int n / 2" by auto
  then have "n = 1" using t \<open>odd n\<close> by arith
  then have "t = 1/2" using teq by simp
  have "sin (t * pi) = 1"
    by (simp add: \<open>t = 1/2\<close> sin_eq_1)
  with \<open>pi * sin (t * pi) = 2\<close>
  have "pi = 2" by simp
  moreover have "pi > 2" using pi_approx by simp
  ultimately show False by simp
qed

lemma MVT_corrected:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::euclidean_space"
  assumes fderiv: "\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D)"
  assumes line_in: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> a + x *\<^sub>R u \<in> D"
  shows "(\<exists>t\<in>Basis\<rightarrow>{0<..<1}. (f (a + u) - f a) = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i))"
proof -
  {
    fix i::'b
    assume "i \<in> Basis"
    have subset: "((\<lambda>x. a + x *\<^sub>R u) ` {0..1}) \<subseteq> D"
      using line_in by force
    have "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> ((\<lambda>b. f (a + b *\<^sub>R u) \<bullet> i) has_derivative (\<lambda>b. b *\<^sub>R J (a + x *\<^sub>R u) u \<bullet> i)) (at x within {0..1})"
      using line_in
      by (auto intro!: derivative_eq_intros
        has_derivative_subset[OF _ subset]
        has_derivative_in_compose[where f="\<lambda>x. a + x *\<^sub>R u"]
        fderiv line_in
        simp add: linear.scaleR[OF has_derivative_linear[OF fderiv]])
    with zero_less_one
    have "\<exists>x\<in>{0<..<1}. f (a + 1 *\<^sub>R u) \<bullet> i - f (a + 0 *\<^sub>R u) \<bullet> i = (1 - 0) *\<^sub>R J (a + x *\<^sub>R u) u \<bullet> i"
      by (rule mvt_simple)
  }
  then obtain t where "\<forall>i\<in>Basis. t i \<in> {0<..<1} \<and> f (a + u) \<bullet> i - f a \<bullet> i = J (a + t i *\<^sub>R u) u \<bullet> i"
    by atomize_elim (force intro!: bchoice)
  hence "t \<in> Basis \<rightarrow> {0<..<1}" "\<And>i. i \<in> Basis \<Longrightarrow> (f (a + u) - f a) \<bullet> i = J (a + t i *\<^sub>R u) u \<bullet> i"
    by (auto simp: inner_diff_left)
  moreover hence "(f (a + u) - f a) = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i)"
    by (intro euclidean_eqI[where 'a='b]) simp
  ultimately show ?thesis by blast
qed

lemma MVT_ivl:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D)"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x u \<in> {J0 .. J1}"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> a + x *\<^sub>R u \<in> D"
  shows "f (a + u) - f a \<in> {J0..J1}"
proof -
  from MVT_corrected[OF fderiv line_in] obtain t where
    t: "t\<in>Basis \<rightarrow> {0<..<1}" and
    mvt: "f (a + u) - f a = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i)"
    by auto
  note mvt
  also have "\<dots> \<in> {J0 .. J1}"
  proof -
    have J: "\<And>i. i \<in> Basis \<Longrightarrow> J0 \<le> J (a + t i *\<^sub>R u) u"
            "\<And>i. i \<in> Basis \<Longrightarrow> J (a + t i *\<^sub>R u) u \<le> J1"
      using J_ivl t line_in by (auto simp: Pi_iff)
    show ?thesis
      using J
      unfolding atLeastAtMost_iff eucl_le[where 'a='b]
      by auto
  qed
  finally show ?thesis .
qed

lemma MVT:
  shows
  "\<And>J J0 J1 a u (f::real*real\<Rightarrow>real*real).
    (\<And>x. FDERIV f x :> J x) \<Longrightarrow>
    (\<And>x. J x u \<in> {J0 .. J1}) \<Longrightarrow>
    f (a + u) - f a \<in> {J0 .. J1}"
  by (rule_tac J = J in MVT_ivl[where D=UNIV]) auto

lemma MVT_ivl':
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "(\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D))"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x (a - b) \<in> {J0..J1}"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> b + x *\<^sub>R (a - b) \<in> D"
  shows "f a \<in> {f b + J0..f b + J1}"
proof -
  have "f (b + (a - b)) - f b \<in> {J0 .. J1}"
    using J_ivl MVT_ivl fderiv line_in by blast
  thus ?thesis
    by (auto simp: diff_le_eq le_diff_eq ac_simps)
qed

end
