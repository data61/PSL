section \<open>Smooth Functions between Normed Vector Spaces\<close>
theory Smooth
  imports
    Analysis_More
begin

subsection \<open>From/To \<open>Multivariate_Taylor.thy\<close>\<close>

lemma multivariate_Taylor_integral:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::banach"
    and Df::"'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "n > 0"
  assumes Df_Nil: "\<And>a x. Df a 0 H = f a"
  assumes Df_Cons: "\<And>a i d. a \<in> closed_segment X (X + H) \<Longrightarrow> i < n \<Longrightarrow>
      ((\<lambda>a. Df a i H) has_derivative (Df a (Suc i))) (at a within G)"
  assumes cs: "closed_segment X (X + H) \<subseteq> G"
  defines "i \<equiv> \<lambda>x.
      ((1 - x) ^ (n - 1) / fact (n - 1)) *\<^sub>R Df (X + x *\<^sub>R H) n H"
  shows multivariate_Taylor_has_integral:
    "(i has_integral f (X + H) - (\<Sum>i<n. (1 / fact i) *\<^sub>R Df X i H)) {0..1}"
  and multivariate_Taylor:
    "f (X + H) = (\<Sum>i<n. (1 / fact i) *\<^sub>R Df X i H) + integral {0..1} i"
  and multivariate_Taylor_integrable:
    "i integrable_on {0..1}"
proof goal_cases
  case 1
  let ?G = "closed_segment X (X + H)"
  define line where "line t = X + t *\<^sub>R H" for t
  have segment_eq: "closed_segment X (X + H) = line ` {0 .. 1}"
    by (auto simp: line_def closed_segment_def algebra_simps)
  have line_deriv: "\<And>x. (line has_derivative (\<lambda>t. t *\<^sub>R H)) (at x)"
    by (auto intro!: derivative_eq_intros simp: line_def [abs_def])
  define g where "g = f o line"
  define Dg where "Dg n t = Df (line t) n H" for n :: nat and t :: real
  note \<open>n > 0\<close>
  moreover
  have Dg0: "Dg 0 = g" by (auto simp add: Dg_def Df_Nil g_def)
  moreover
  have DgSuc: "(Dg m has_vector_derivative Dg (Suc m) t) (at t within {0..1})"
    if "m < n" "0 \<le> t" "t \<le> 1" for m::nat and t::real
  proof -
    from that have [intro]: "line t \<in> ?G" using assms
      by (auto simp: segment_eq)
    note [derivative_intros] = has_derivative_in_compose[OF _ has_derivative_within_subset[OF Df_Cons]]
    interpret Df: linear "(\<lambda>d. Df (line t) (Suc m) d)"
      by (auto intro!: has_derivative_linear derivative_intros \<open>m < n\<close>)
    note [derivative_intros] =
      has_derivative_compose[OF _ line_deriv]
    show ?thesis
      using Df.scaleR \<open>m < n\<close>
      by (auto simp: Dg_def [abs_def] has_vector_derivative_def g_def segment_eq
         intro!: derivative_eq_intros subsetD[OF cs])
  qed
  ultimately
  have g_Taylor: "(i has_integral g 1 - (\<Sum>i<n. ((1 - 0) ^ i / fact i) *\<^sub>R Dg i 0)) {0 .. 1}"
    unfolding i_def Dg_def [abs_def] line_def
    by (rule Taylor_has_integral) auto
  then show c: ?case using \<open>n > 0\<close> by (auto simp: g_def line_def Dg_def)
  case 2 show ?case using c
    by (simp add: integral_unique add.commute)
  case 3 show ?case using c by force
qed


subsection \<open>Higher-order differentiable\<close>

fun higher_differentiable_on ::
  "'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> nat \<Rightarrow> bool" where
  "higher_differentiable_on S f 0 \<longleftrightarrow> continuous_on S f"
| "higher_differentiable_on S f (Suc n) \<longleftrightarrow>
   (\<forall>x\<in>S. f differentiable (at x)) \<and>
   (\<forall>v. higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) n)"

lemma ball_differentiable_atD: "\<forall>x\<in>S. f differentiable at x \<Longrightarrow> f differentiable_on S"
  by (auto simp: differentiable_on_def differentiable_at_withinI)

lemma higher_differentiable_on_imp_continuous_on:
  "continuous_on S f" if "higher_differentiable_on S f n"
  using that
  by (cases n) (auto simp: differentiable_imp_continuous_on ball_differentiable_atD)

lemma higher_differentiable_on_imp_differentiable_on:
  "f differentiable_on S" if "higher_differentiable_on S f k" "k > 0"
  using that
  by (cases k) (auto simp: ball_differentiable_atD)

lemma higher_differentiable_on_congI:
  assumes "open S" "higher_differentiable_on S g n"
    and "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "higher_differentiable_on S f n"
  using assms(2,3)
proof (induction n arbitrary: f g)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have 1: "\<forall>x\<in>S. g differentiable (at x)" and
       2: "higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) v) n" for v
    using Suc by auto
  have 3: "\<forall>x\<in>S. f differentiable (at x)" using 1 Suc(3) assms(1)
    by (metis differentiable_eqI) 
  have 4: "frechet_derivative f (at x) v = frechet_derivative g (at x) v" if "x \<in> S" for x v
    using "3" Suc.prems(2) assms(1) frechet_derivative_transform_within_open_ext that by blast
  from 2 3 4 show ?case
    using Suc.IH[OF 2 4] by auto
qed

lemma higher_differentiable_on_cong:
  assumes "open S" "S = T"
    and "\<And>x. x \<in> T \<Longrightarrow> f x = g x"
  shows "higher_differentiable_on S f n \<longleftrightarrow> higher_differentiable_on T g n"
  using higher_differentiable_on_congI assms by auto


lemma higher_differentiable_on_SucD:
  "higher_differentiable_on S f n" if "higher_differentiable_on S f (Suc n)"
  using that
  by (induction n arbitrary: f) (auto simp: differentiable_imp_continuous_on ball_differentiable_atD)

lemma higher_differentiable_on_addD:
  "higher_differentiable_on S f n" if "higher_differentiable_on S f (n + m)"
  using that
  by (induction m arbitrary: f n)
    (auto simp del: higher_differentiable_on.simps dest!: higher_differentiable_on_SucD)

lemma higher_differentiable_on_le:
  "higher_differentiable_on S f n" if "higher_differentiable_on S f m" "n \<le> m"
  using higher_differentiable_on_addD[of S f n "m - n"] that
  by auto

lemma higher_differentiable_on_open_subsetsI:
  "higher_differentiable_on S f n"
  if "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. x \<in> T \<and> open T \<and> higher_differentiable_on T f n"
  using that
proof (induction n arbitrary: f)
  case 0
  show ?case
    by (force simp: continuous_on_def
        dest!: 0
        dest: at_within_open
        intro!: Lim_at_imp_Lim_at_within[where S=S])
next
  case (Suc n)
  have "f differentiable at x" if "x \<in> S" for x
    using Suc.prems[OF \<open>x \<in> S\<close>]
    by (auto simp: differentiable_on_def dest: at_within_open dest!: bspec)
  then have "f differentiable_on S"
    by (auto simp: differentiable_on_def intro!: differentiable_at_withinI[where s=S])
  with Suc show ?case
    by fastforce
qed

lemma higher_differentiable_on_const: "higher_differentiable_on S (\<lambda>x. c) n"
  by (induction n arbitrary: c) (auto simp: continuous_intros frechet_derivative_const)

lemma higher_differentiable_on_id: "higher_differentiable_on S (\<lambda>x. x) n"
  by (cases n) (auto simp: frechet_derivative_works higher_differentiable_on_const)

lemma higher_differentiable_on_add:
  "higher_differentiable_on S (\<lambda>x. f x + g x) n"
  if "higher_differentiable_on S f n"
    "higher_differentiable_on S g n"
    "open S"
  using that
proof (induction n arbitrary: f g)
  case 0
  then show ?case by (auto intro!: continuous_intros)
next
  case (Suc n)
  from Suc.prems have
    f: "\<And>x. x\<in>S \<Longrightarrow> f differentiable (at x)"
    and hf: "higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) n"
    and g: "\<And>x. x\<in>S \<Longrightarrow> g differentiable (at x)"
    and hg: "higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) v) n"
    for v
    by auto
  show ?case
    using f g \<open>open S\<close>
    by (auto simp: frechet_derivative_plus
        intro!: derivative_intros f g Suc.IH hf hg
        cong: higher_differentiable_on_cong)
qed

lemma (in bounded_bilinear) differentiable:
 "(\<lambda>x. prod (f x) (g x)) differentiable at x within S" 
 if "f differentiable at x within S"
    "g differentiable at x within S"
  by (blast intro: differentiableI frechet_derivative_worksI that FDERIV)


context begin
private lemmas d = bounded_bilinear.differentiable
lemmas differentiable_inner = bounded_bilinear_inner[THEN d]
   and differentiable_scaleR = bounded_bilinear_scaleR[THEN d]
   and differentiable_mult = bounded_bilinear_mult[THEN d]
end

lemma (in bounded_bilinear) differentiable_on:
  "(\<lambda>x. prod (f x) (g x)) differentiable_on S"
  if "f differentiable_on S" "g differentiable_on S"
  using that by (auto simp: differentiable_on_def differentiable)

context begin
private lemmas do = bounded_bilinear.differentiable_on
lemmas differentiable_on_inner = bounded_bilinear_inner[THEN do]
   and differentiable_on_scaleR = bounded_bilinear_scaleR[THEN do]
   and differentiable_on_mult = bounded_bilinear_mult[THEN do]
end

lemma (in bounded_bilinear) higher_differentiable_on:
  "higher_differentiable_on S (\<lambda>x. prod (f x) (g x)) n"
  if
    "higher_differentiable_on S f n"
    "higher_differentiable_on S g n"
    "open S"
  using that
proof (induction n arbitrary: f g)
  case 0
  then show ?case by (auto intro!: continuous_intros continuous_on)
next
  case (Suc n)
  from Suc.prems have
    f: "\<And>x. x\<in>S \<Longrightarrow> f differentiable (at x)"
    and hf: "higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) n"
    and g: "\<And>x. x\<in>S \<Longrightarrow> g differentiable (at x)"
    and hg: "higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) v) n"
    for v
    by auto
  show ?case
    using f g \<open>open S\<close> Suc
    by (auto simp: frechet_derivative
        intro!: derivative_intros f g differentiable higher_differentiable_on_add Suc.IH
        intro: higher_differentiable_on_SucD
        cong: higher_differentiable_on_cong)
qed

context begin
private lemmas hdo = bounded_bilinear.higher_differentiable_on
lemmas higher_differentiable_on_inner = bounded_bilinear_inner[THEN hdo]
   and higher_differentiable_on_scaleR = bounded_bilinear_scaleR[THEN hdo]
   and higher_differentiable_on_mult = bounded_bilinear_mult[THEN hdo]
end

lemma higher_differentiable_on_sum:
  "higher_differentiable_on S (\<lambda>x. \<Sum>i\<in>F. f i x) n"
  if "\<And>i. i \<in> F \<Longrightarrow> finite F \<Longrightarrow> higher_differentiable_on S (f i) n" "open S"
  using that
  by (induction F rule: infinite_finite_induct)
    (auto intro!: higher_differentiable_on_const higher_differentiable_on_add)

lemma higher_differentiable_on_subset:
  "higher_differentiable_on S f n"
  if "higher_differentiable_on T f n" "S \<subseteq> T"
  using that
  by (induction n arbitrary: f) (auto intro: continuous_on_subset differentiable_on_subset)

lemma higher_differentiable_on_compose:
  "higher_differentiable_on S (f o g) n"
  if "higher_differentiable_on T f n" "higher_differentiable_on S g n"  "g ` S \<subseteq> T" "open S" "open T"
  for g::"_\<Rightarrow>_::euclidean_space"\<comment>\<open>TODO: can we get around this restriction?\<close>
  using that(1-3)
proof (induction n arbitrary: f g)
  case 0
  then show ?case using that(4-)
    by (auto simp: continuous_on_compose2)
next
  case (Suc n)
  from Suc.prems
  have
    f: "\<And>x. x \<in> T \<Longrightarrow> f differentiable (at x)"
    and g: "\<And>x. x \<in> S \<Longrightarrow> g differentiable (at x)"
    and hf: "higher_differentiable_on T (\<lambda>x. frechet_derivative f (at x) v) n"
    and hg: "higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) w) n"
    for v w
    by auto
  show ?case
    using \<open>g ` _ \<subseteq> _\<close> \<open>open S\<close> f g \<open>open T\<close> Suc
      Suc.IH[where f="\<lambda>x. frechet_derivative f (at x) v"
        and g = "\<lambda>x. g x" for v, unfolded o_def]
      higher_differentiable_on_SucD[OF Suc.prems(2)]
    by (auto
        simp: frechet_derivative_compose_eucl subset_iff
        simp del: o_apply
        intro!: differentiable_chain_within higher_differentiable_on_sum
          higher_differentiable_on_scaleR higher_differentiable_on_inner
          higher_differentiable_on_const
        intro: differentiable_at_withinI
        cong: higher_differentiable_on_cong)
qed


lemma higher_differentiable_on_uminus:
  "higher_differentiable_on S (\<lambda>x. - f x) n"
  if "higher_differentiable_on S f n" "open S"
  using higher_differentiable_on_scaleR[of S "\<lambda>x. -1" n f] that
  by (auto simp: higher_differentiable_on_const)

lemma higher_differentiable_on_minus:
  "higher_differentiable_on S (\<lambda>x. f x - g x) n"
  if "higher_differentiable_on S f n"
    "higher_differentiable_on S g n"
    "open S"
  using higher_differentiable_on_add[OF _ higher_differentiable_on_uminus, OF that(1,2,3,3)]
  by simp

lemma higher_differentiable_on_inverse:
  "higher_differentiable_on S (\<lambda>x. inverse (f x)) n"
  if "higher_differentiable_on S f n" "0 \<notin> f ` S" "open S"
  for f::"_\<Rightarrow>_::real_normed_field"
  using that
proof (induction n arbitrary: f)
  case 0
  then show ?case by (auto simp: continuous_on_inverse)
next
  case (Suc n)
  from Suc.prems(1) have fn: "higher_differentiable_on S f n" by (rule higher_differentiable_on_SucD)
  from Suc show ?case
    by (auto simp: continuous_on_inverse image_iff power2_eq_square
        frechet_derivative_inverse divide_inverse
        intro!: differentiable_inverse higher_differentiable_on_uminus higher_differentiable_on_mult
          Suc.IH fn
        cong: higher_differentiable_on_cong)
qed

lemma higher_differentiable_on_divide:
  "higher_differentiable_on S (\<lambda>x. f x / g x) n"
  if
    "higher_differentiable_on S f n"
    "higher_differentiable_on S g n"
    "\<And>x. x \<in> S \<Longrightarrow> g x \<noteq> 0"
    "open S"
  for f::"_\<Rightarrow>_::real_normed_field"
  using higher_differentiable_on_mult[OF _ higher_differentiable_on_inverse, OF that(1,2) _ that(4,4)]
    that(3)
  by (auto simp: divide_inverse image_iff)

lemma differentiable_on_open_Union:
  "f differentiable_on \<Union>S"
  if "\<And>s. s \<in> S \<Longrightarrow> f differentiable_on s"
    "\<And>s. s \<in> S \<Longrightarrow> open s"
  using that
  unfolding differentiable_on_def
  by (metis Union_iff at_within_open open_Union)

lemma higher_differentiable_on_open_Union: "higher_differentiable_on (\<Union>S) f n"
  if "\<And>s. s \<in> S \<Longrightarrow> higher_differentiable_on s f n"
    "\<And>s. s \<in> S \<Longrightarrow> open s"
  using that
proof (induction n arbitrary: f)
  case 0
  then show ?case by (auto simp: continuous_on_open_Union)
next
  case (Suc n)
  then show ?case
    by (auto simp: differentiable_on_open_Union)
qed

lemma differentiable_on_open_Un:
  "f differentiable_on S \<union> T"
  if "f differentiable_on S"
    "f differentiable_on T"
    "open S" "open T"
  using that differentiable_on_open_Union[of "{S, T}" f]
  by auto

lemma higher_differentiable_on_open_Un: "higher_differentiable_on (S \<union> T) f n"
  if "higher_differentiable_on S f n"
    "higher_differentiable_on T f n"
    "open S" "open T"
  using higher_differentiable_on_open_Union[of "{S, T}" f n] that
  by auto

lemma higher_differentiable_on_sqrt: "higher_differentiable_on S (\<lambda>x. sqrt (f x)) n"
  if "higher_differentiable_on S f n" "0 \<notin> f ` S" "open S"
  using that
proof (induction n arbitrary: f)
  case 0
  then show ?case by (auto simp: continuous_intros)
next
  case (Suc n)
  from Suc.prems(1) have fn: "higher_differentiable_on S f n" by (rule higher_differentiable_on_SucD)
  then have "continuous_on S f"
    by (rule higher_differentiable_on_imp_continuous_on)
  with \<open>open S\<close> have op: "open (S \<inter> f -` {0<..})" (is "open ?op")
    by (rule open_continuous_vimage') simp
  from \<open>open S\<close> \<open>continuous_on S f\<close> have on: "open (S \<inter> f -` {..<0})" (is "open ?on")
    by (rule open_continuous_vimage') simp
  have op': "higher_differentiable_on ?op (\<lambda>x. 1) n" and on': "higher_differentiable_on ?on (\<lambda>x. -1) n"
     by (rule higher_differentiable_on_const)+
  then have i: "higher_differentiable_on (?op \<union> ?on) (\<lambda>x. if 0 < f x then 1::real else - 1) n"
    by (auto intro!: higher_differentiable_on_open_Un op on
          higher_differentiable_on_congI[OF _ op'] higher_differentiable_on_congI[OF _ on'])
  also have "?op \<union> ?on = S" using Suc by auto
  finally have i: "higher_differentiable_on S (\<lambda>x. if 0 < f x then 1::real else - 1) n" .
  from fn i Suc show ?case
    by (auto simp: sqrt_differentiable_on image_iff frechet_derivative_sqrt
        intro!: sqrt_differentiable higher_differentiable_on_mult higher_differentiable_on_inverse
          higher_differentiable_on_divide higher_differentiable_on_const
        cong: higher_differentiable_on_cong)
qed


lemma higher_differentiable_on_frechet_derivativeI:
  "higher_differentiable_on X (\<lambda>x. frechet_derivative f (at x) h) i"
  if "higher_differentiable_on X f (Suc i)" "open X" "x \<in> X"
  using that(1)
  by (induction i arbitrary: f h) auto

lemma higher_differentiable_on_norm:
  "higher_differentiable_on S (\<lambda>x. norm (f x)) n"
  if "higher_differentiable_on S f n" "0 \<notin> f ` S" "open S"
  for f::"_\<Rightarrow>_::real_inner"
  using that
proof (induction n arbitrary: f)
  case 0
  then show ?case by (auto simp: continuous_on_norm)
next
  case (Suc n)
  from Suc.prems(1) have fn: "higher_differentiable_on S f n" by (rule higher_differentiable_on_SucD)
  from Suc show ?case
    by (auto simp: continuous_on_norm frechet_derivative_norm image_iff sgn_div_norm
        cong: higher_differentiable_on_cong
        intro!: differentiable_norm_compose_at higher_differentiable_on_inner
          higher_differentiable_on_inverse
          higher_differentiable_on_mult Suc.IH fn)
qed

declare higher_differentiable_on.simps [simp del]

lemma higher_differentiable_on_Pair:
  "higher_differentiable_on S f k \<Longrightarrow> higher_differentiable_on S g k \<Longrightarrow>
   higher_differentiable_on S (\<lambda>x. (f x, g x)) k"
  if "open S"
proof (induction k arbitrary: f g)
  case 0
  then show ?case
    unfolding higher_differentiable_on.simps
    by (auto intro!: continuous_intros)
next
  case (Suc k)
  then show ?case using that
    unfolding higher_differentiable_on.simps
    by (auto simp: frechet_derivative_pair[of f _ g] cong: higher_differentiable_on_cong)
qed

lemma higher_differentiable_on_compose':
  "higher_differentiable_on S (\<lambda>x. f (g x)) n"
  if "higher_differentiable_on T f n" "higher_differentiable_on S g n"  "g ` S \<subseteq> T" "open S" "open T"
  for g::"_\<Rightarrow>_::euclidean_space"
  using higher_differentiable_on_compose[of T f n S g] comp_def that
  by (metis (no_types, lifting) higher_differentiable_on_cong)

lemma higher_differentiable_on_fst:
  "higher_differentiable_on (S \<times> T) fst k"
proof (induction k)
  case (Suc k)
  then show ?case
    unfolding higher_differentiable_on.simps
    by (auto simp: differentiable_at_fst frechet_derivative_fst frechet_derivative_id higher_differentiable_on_const)
qed (auto simp: higher_differentiable_on.simps continuous_on_fst)

lemma higher_differentiable_on_snd:
  "higher_differentiable_on (S \<times> T) snd k"
proof (induction k)
  case (Suc k)
  then show ?case
    unfolding higher_differentiable_on.simps
    by (auto intro!: continuous_intros
        simp: differentiable_at_snd frechet_derivative_snd frechet_derivative_id higher_differentiable_on_const)
qed (auto simp: higher_differentiable_on.simps continuous_on_snd)

lemma higher_differentiable_on_fst_comp:
  "higher_differentiable_on S (\<lambda>x. fst (f x)) k"
  if "higher_differentiable_on S f k" "open S"
  using that
  by (induction k arbitrary: f)
    (auto intro!: continuous_intros differentiable_at_fst
      cong: higher_differentiable_on_cong
      simp: higher_differentiable_on.simps frechet_derivative_fst)

lemma higher_differentiable_on_snd_comp:
  "higher_differentiable_on S (\<lambda>x. snd (f x)) k"
  if "higher_differentiable_on S f k" "open S"
  using that
  by (induction k arbitrary: f)
    (auto intro!: continuous_intros differentiable_at_snd
      cong: higher_differentiable_on_cong
      simp: higher_differentiable_on.simps frechet_derivative_snd)

lemma higher_differentiable_on_Pair':
  "higher_differentiable_on S f k \<Longrightarrow> higher_differentiable_on T g k \<Longrightarrow>
   higher_differentiable_on (S \<times> T) (\<lambda>x. (f (fst x), g (snd x))) k"
  if S: "open S" and T: "open T"
  for f::"_::euclidean_space\<Rightarrow>_" and g::"_::euclidean_space\<Rightarrow>_"
  by (auto intro!: higher_differentiable_on_Pair open_Times S T
      higher_differentiable_on_fst
      higher_differentiable_on_snd
      higher_differentiable_on_compose'[where f=f and T=S]
      higher_differentiable_on_compose'[where f=g and T=T])


lemma higher_differentiable_on_sin: "higher_differentiable_on S (\<lambda>x. sin (f x::real)) n"
  and higher_differentiable_on_cos: "higher_differentiable_on S (\<lambda>x. cos (f x::real)) n"
  if f: "higher_differentiable_on S f n" and S: "open S"
  unfolding atomize_conj
  using f
proof (induction n)
  case (Suc n)
  then have "higher_differentiable_on S f n"
    "higher_differentiable_on S (\<lambda>x. sin (f x)) n"
    "higher_differentiable_on S (\<lambda>x. cos (f x)) n"
    "\<And>x. x \<in> S \<Longrightarrow> f differentiable at x"
    using higher_differentiable_on_SucD
    by (auto simp: higher_differentiable_on.simps)
  with Suc show ?case
    by (auto simp: higher_differentiable_on.simps sin_differentiable_at cos_differentiable_at
        frechet_derivative_sin frechet_derivative_cos S
        intro!: higher_differentiable_on_mult higher_differentiable_on_uminus
        cong: higher_differentiable_on_cong[OF S])
qed (auto simp: higher_differentiable_on.simps intro!: continuous_intros)


subsection \<open>Higher directional derivatives\<close>

primrec nth_derivative :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  "nth_derivative 0 f x h = f x"
| "nth_derivative (Suc i) f x h = nth_derivative i (\<lambda>x. frechet_derivative f (at x) h) x h"

lemma frechet_derivative_nth_derivative_commute:
  "frechet_derivative (\<lambda>x. nth_derivative i f x h) (at x) h =
    nth_derivative i (\<lambda>x. frechet_derivative f (at x) h) x h"
  by (induction i arbitrary: f) auto

lemma nth_derivative_funpow:
  "nth_derivative i f x h = ((\<lambda>f x. frechet_derivative f (at x) h) ^^ i) f x"
  by (induction i arbitrary: f) (auto simp del: funpow.simps simp: funpow_Suc_right)

lemma nth_derivative_exists:
  "\<exists>f'. ((\<lambda>x. nth_derivative i f x h) has_derivative f') (at x) \<and>
    f' h = nth_derivative (Suc i) f x h"
  if "higher_differentiable_on X f (Suc i)" "open X" "x \<in> X"
  using that(1)
proof (induction i arbitrary: f)
  case 0
  with that show ?case
    by (auto simp: higher_differentiable_on.simps that dest!: frechet_derivative_worksI)
next
  case (Suc i)
  from Suc.prems
  have "\<And>x. x \<in> X \<Longrightarrow> f differentiable at x" "higher_differentiable_on X (\<lambda>x. frechet_derivative f (at x) h) (Suc i)"
    unfolding higher_differentiable_on.simps(2)[where n = "Suc i"]
    by auto
  from Suc.IH[OF this(2)] show ?case
    by auto
qed

lemma higher_derivatives_exists:
  assumes "higher_differentiable_on X f n" "open X"
  obtains Df where
    "\<And>a h. Df a 0 h = f a"
    "\<And>a h i. i < n \<Longrightarrow> a \<in> X \<Longrightarrow> ((\<lambda>a. Df a i H) has_derivative Df a (Suc i)) (at a)"
    "\<And>a i. i \<le> n \<Longrightarrow> a \<in> X \<Longrightarrow> Df a i H = nth_derivative i f a H"
proof -
  have "higher_differentiable_on X f (Suc i)" if "i < n" for i
    apply (rule higher_differentiable_on_le[OF assms(1)])
    using that by simp
  from nth_derivative_exists[OF this assms(2)]
  have "\<forall>i\<in>{..<n}. \<forall>x \<in> X. \<exists>f'. ((\<lambda>x. nth_derivative i f x H) has_derivative f') (at x) \<and> f' H = nth_derivative (Suc i) f x H"
    by blast
  from this[unfolded bchoice_iff]
  obtain f' where f': "i < n \<Longrightarrow> x \<in> X \<Longrightarrow> ((\<lambda>x. nth_derivative i f x H) has_derivative f' x i) (at x)"
    "i < n \<Longrightarrow> x \<in> X \<Longrightarrow> f' x i H = nth_derivative (Suc i) f x H" for x i
    by force
  define Df where "Df a i h = (if i = 0 then f a else f' a (i - 1) h)" for a i h
  have "Df a 0 h = f a" for a h
    by (auto simp: Df_def)
  moreover have "i < n \<Longrightarrow> a \<in> X \<Longrightarrow> ((\<lambda>a. Df a i H) has_derivative Df a (Suc i)) (at a)"
    for i a
    apply (auto simp: Df_def[abs_def])
    using _ \<open>open X\<close>
    apply (rule has_derivative_transform_within_open)
      apply (rule f')
       apply (auto simp: f')
    done
  moreover have "i \<le> n \<Longrightarrow> a \<in> X \<Longrightarrow> Df a i H = nth_derivative i f a H" for i a
    by (auto simp: Df_def f')
  ultimately show ?thesis ..
qed

lemma nth_derivative_differentiable:
  assumes "higher_differentiable_on S f (Suc n)" "x \<in> S"
  shows "(\<lambda>x. nth_derivative n f x v) differentiable at x"
  using assms
  by (induction n arbitrary: f) (auto simp: higher_differentiable_on.simps)

lemma higher_differentiable_on_imp_continuous_nth_derivative:
  assumes "higher_differentiable_on S f n"
  shows "continuous_on S (\<lambda>x. nth_derivative n f x v)"
  using assms
  by (induction n arbitrary: f) (auto simp: higher_differentiable_on.simps)

lemma frechet_derivative_at_real_eq_scaleR:
  "frechet_derivative f (at x) v = v *\<^sub>R frechet_derivative f (at x) 1"
  if "f differentiable (at x)" "NO_MATCH 1 v"
  by (simp add: frechet_derivative_eq_vector_derivative that)

lemma higher_differentiable_on_real_Suc:
  "higher_differentiable_on S f (Suc n) \<longleftrightarrow>
     (\<forall>x\<in>S. f differentiable (at x)) \<and>
      (higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) 1) n)"
  if "open S"
  for S::"real set"
  using \<open>open S\<close>
  by (auto simp: higher_differentiable_on.simps frechet_derivative_at_real_eq_scaleR
      intro!: higher_differentiable_on_scaleR higher_differentiable_on_const
      cong: higher_differentiable_on_cong)

lemma higher_differentiable_on_real_SucI:
  fixes S::"real set"
  assumes
    "\<And>x. x \<in> S \<Longrightarrow> (\<lambda>x. nth_derivative n f x 1) differentiable at x"
    "continuous_on S (\<lambda>x. nth_derivative (Suc n) f x 1)"
    "higher_differentiable_on S f n"
    and o: "open S"
  shows "higher_differentiable_on S f (Suc n)"
  using assms
proof (induction n arbitrary: f)
  case 0
  then show ?case
      by (auto simp: higher_differentiable_on_real_Suc higher_differentiable_on.simps(1) o)
qed (fastforce simp: higher_differentiable_on_real_Suc)

lemma higher_differentiable_on_real_Suc':
  "open S \<Longrightarrow> higher_differentiable_on S f (Suc n) \<longleftrightarrow>
    (\<forall>v. continuous_on S (\<lambda>x. nth_derivative (Suc n) f x 1)) \<and>
    (\<forall>x\<in>S. \<forall>v. (\<lambda>x. nth_derivative n f x 1) differentiable (at x)) \<and> higher_differentiable_on S f n"
  for S::"real set"
  apply (auto simp: nth_derivative_differentiable
      dest: higher_differentiable_on_SucD
      intro: higher_differentiable_on_real_SucI)
  by (auto simp: higher_differentiable_on_real_Suc higher_differentiable_on.simps(1)
      higher_differentiable_on_imp_continuous_nth_derivative)

lemma closed_segment_subsetD:
  "0 \<le> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> (X + x *\<^sub>R H) \<in> S"
  if "closed_segment X (X + H) \<subseteq> S"
  using that
  by (rule subsetD) (auto simp: closed_segment_def algebra_simps intro!: exI[where x=x])


lemma higher_differentiable_Taylor:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::banach"
    and H::"'a"
    and Df::"'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "n > 0"
  assumes hd: "higher_differentiable_on S f n" "open S"
  assumes cs: "closed_segment X (X + H) \<subseteq> S"
  defines "i \<equiv> \<lambda>x. ((1 - x) ^ (n - 1) / fact (n - 1)) *\<^sub>R nth_derivative n f (X + x *\<^sub>R H) H"
  shows "(i has_integral f (X + H) - (\<Sum>i<n. (1 / fact i) *\<^sub>R nth_derivative i f X H)) {0..1}" (is ?th1)
  and "f (X + H) = (\<Sum>i<n. (1 / fact i) *\<^sub>R nth_derivative i f X H) + integral {0..1} i" (is ?th2)
  and "i integrable_on {0..1}" (is ?th3)
proof -
  from higher_derivatives_exists[OF hd]
  obtain Df where Df: "(\<And>a h. Df a 0 h = f a)"
    "(\<And>a h i. i < n \<Longrightarrow> a \<in> S \<Longrightarrow> ((\<lambda>a. Df a i H) has_derivative Df a (Suc i)) (at a))"
    "\<And>a i. i \<le> n \<Longrightarrow> a \<in> S \<Longrightarrow> Df a i H = nth_derivative i f a H"
    by blast
  from multivariate_Taylor_integral[OF \<open>n > 0\<close>, of Df H f X, OF Df(1,2)] cs
  have mt: "((\<lambda>x. ((1 - x) ^ (n - 1) / fact (n - 1)) *\<^sub>R Df (X + x *\<^sub>R H) n H) has_integral
     f (X + H) - (\<Sum>i<n. (1 / fact i) *\<^sub>R Df X i H))
     {0..1}"
    by force
  from cs have "X \<in> S" by auto
  show ?th1
    apply (rule has_integral_eq_rhs)
    unfolding i_def
    using negligible_empty _ mt
     apply (rule has_integral_spike)
    using closed_segment_subsetD[OF cs]
    by (auto simp: Df \<open>X \<in> S\<close>)
  then show ?th2 ?th3
    unfolding has_integral_iff
    by auto
qed

lemma frechet_derivative_componentwise:
  "frechet_derivative f (at a) v = (\<Sum>i\<in>Basis. (v \<bullet> i) * (frechet_derivative f (at a) i))"
  if "f differentiable at a"
  for f::"'a::euclidean_space \<Rightarrow> real"
proof -
  have "linear (frechet_derivative f (at a))"
    using that
    by (rule linear_frechet_derivative)
  from Linear_Algebra.linear_componentwise[OF this, of v 1]
  show ?thesis
    by simp
qed

lemma second_derivative_componentwise:
  "nth_derivative 2 f a v =
    (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. frechet_derivative (\<lambda>a. frechet_derivative f (at a) j) (at a) i * (v \<bullet> j)) * (v \<bullet> i))"
  if "higher_differentiable_on S f 2" and S: "open S" "a \<in> S"
  for f::"'a::euclidean_space \<Rightarrow> real"
proof -
  have diff: "(\<lambda>x. frechet_derivative f (at x) v) differentiable at a" for v
    using that
    by (auto simp: numeral_2_eq_2 higher_differentiable_on.simps differentiable_on_openD
        dest!: spec[where x=v])
  have d1: "x \<in> S \<Longrightarrow> f differentiable at x" for x
    using that
    by (auto simp: numeral_2_eq_2 higher_differentiable_on.simps dest!: differentiable_on_openD)
  have eq: "\<And>x. x \<in> Basis \<Longrightarrow>
         frechet_derivative
          (\<lambda>x. \<Sum>i\<in>Basis. v \<bullet> i * frechet_derivative f (at x) i) (at a) x =
         (\<Sum>j\<in>Basis. frechet_derivative (\<lambda>a. frechet_derivative f (at a) j) (at a) x * (v \<bullet> j))"
    apply (subst frechet_derivative_sum)
    subgoal by (auto intro!: differentiable_mult diff)
    apply (rule sum.cong)
     apply simp
    apply (subst frechet_derivative_times)
    subgoal by simp
    subgoal by (rule diff)
    by (simp add: frechet_derivative_const)
  show ?thesis
    apply (simp add: numeral_2_eq_2)
    apply (subst frechet_derivative_componentwise[OF diff])
    apply (rule sum.cong)
     apply simp
    apply simp
    apply (rule disjI2)
    apply (rule trans)
     apply (rule frechet_derivative_transform_within_open_ext [OF _ S frechet_derivative_componentwise])
    apply (simp add: diff)
       apply (rule d1, assumption)
    apply (simp add: eq)
    done
qed

lemma higher_differentiable_Taylor1:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::banach"
  assumes hd: "higher_differentiable_on S f 2" "open S"
  assumes cs: "closed_segment X (X + H) \<subseteq> S"
  defines "i \<equiv> \<lambda>x. ((1 - x)) *\<^sub>R nth_derivative 2 f (X + x *\<^sub>R H) H"
  shows "(i has_integral f (X + H) - (f X + nth_derivative 1 f X H)) {0..1}"
    and "f (X + H) = f X + nth_derivative 1 f X H + integral {0..1} i"
    and "i integrable_on {0..1}"
  using higher_differentiable_Taylor[OF _ hd cs]
  by (auto simp: numeral_2_eq_2 i_def)

lemma differentiable_on_open_blinfunE:
  assumes "f differentiable_on S" "open S"
  obtains f' where "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
proof -
  {
    fix x assume "x \<in> S"
    with assms obtain f' where f': "(f has_derivative f') (at x)"
      by (auto dest!: differentiable_on_openD simp: differentiable_def)
    then have "bounded_linear f'"
      by (rule has_derivative_bounded_linear)
    then obtain bf' where "f' = blinfun_apply bf'"
      by (metis bounded_linear_Blinfun_apply)
    then have "\<exists>bf'. (f has_derivative blinfun_apply bf') (at x)" using f'
      by blast
  } then obtain f' where "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
    by metis
  then show ?thesis ..
qed

lemma continuous_on_blinfunI1:
  "continuous_on X f"
  if "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on X (\<lambda>x. blinfun_apply (f x) i)"
  using that
  by (auto simp: continuous_on_def intro: tendsto_componentwise1)

lemma c1_euclidean_blinfunE:
  fixes f::"'a::euclidean_space\<Rightarrow>'b::real_normed_vector"
  assumes "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f' x) (at x within S)"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on S (\<lambda>x. f' x i)"
  obtains bf' where
    "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (bf' x)) (at x within S)"
    "continuous_on S bf'"
    "\<And>x. x \<in> S \<Longrightarrow> blinfun_apply (bf' x) = f' x"
proof -
  from assms have "bounded_linear (f' x)" if "x \<in> S" for x
    by (auto intro!: has_derivative_bounded_linear that)
  then obtain bf' where bf': "\<forall>x \<in> S. f' x = blinfun_apply (bf' x)"
    apply atomize_elim
    apply (rule bchoice)
    apply auto
    by (metis bounded_linear_Blinfun_apply)
  with assms have "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (bf' x)) (at x within S)"
    by simp
  moreover
  have f_tendsto: "((\<lambda>n. f' n j) \<longlongrightarrow> f' x j) (at x within S)"
    if "x \<in> S" "j \<in> Basis"
    for x j
    using assms by (auto simp: continuous_on_def that)
  have "continuous_on S bf'"
    by (rule continuous_on_blinfunI1) (simp add: bf'[rule_format, symmetric] assms)
  moreover have "\<And>x. x \<in> S \<Longrightarrow> blinfun_apply (bf' x) = f' x" using bf' by auto
  ultimately show ?thesis ..
qed

lemma continuous_Sigma:
  assumes defined: "y \<in> Pi T X"
  assumes f_cont: "continuous_on (Sigma T X) (\<lambda>(t, x). f t x)"
  assumes y_cont: "continuous_on T y"
  shows "continuous_on T (\<lambda>x. f x (y x))"
  using
    defined
    continuous_on_compose2[OF
      continuous_on_subset[where t="(\<lambda>x. (x, y x)) ` T", OF f_cont]
      continuous_on_Pair[OF continuous_on_id y_cont]]
  by auto

lemma continuous_on_Times_swap:
  "continuous_on (X \<times> Y) (\<lambda>(x, y). f x y)"
  if "continuous_on (Y \<times> X) (\<lambda>(y, x). f x y)"
  using continuous_on_compose2[OF that continuous_on_swap, where s="X \<times> Y"]
  by (auto simp: split_beta' product_swap)

lemma leibniz_rule':
  "\<And>x. x \<in> S \<Longrightarrow>
      ((\<lambda>x. integral (cbox a b) (f x)) has_derivative (\<lambda>v. integral (cbox a b) (\<lambda>t. fx x t v)))
          (at x within S)"
  "(\<lambda>x. integral (cbox a b) (f x)) differentiable_on S"
  if "convex S"
    and c1: "\<And>t x. t \<in> cbox a b \<Longrightarrow> x \<in> S \<Longrightarrow> ((\<lambda>x. f x t) has_derivative fx x t) (at x within S)"
    "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on (S \<times> cbox a b) (\<lambda>(x, t). fx x t i)"
    and i: "\<And>x. x \<in> S \<Longrightarrow> f x integrable_on cbox a b"
  for S::"'a::euclidean_space set"
    and f::"'a \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
proof -
  have fx1: "continuous_on S (\<lambda>x. fx x t i)" if "t \<in> cbox a b" "i \<in> Basis" for i t
    by (rule continuous_Sigma[OF _ c1(2), where y="\<lambda>_. t"]) (auto simp: continuous_intros that)
  {
    fix x assume "x \<in> S"
    have fx2: "continuous_on (cbox a b) (\<lambda>t. fx x t i)" if "i \<in> Basis" for i
      by (rule continuous_Sigma[OF _ continuous_on_Times_swap[OF c1(2)]])
        (auto simp: continuous_intros that \<open>x \<in> S\<close>)
    {
      fix t
      assume "t \<in> cbox a b"
      have "\<exists>f'. (\<forall>x \<in> S. ((\<lambda>x. f x t) has_derivative blinfun_apply (f' x)) (at x within S) \<and>
      blinfun_apply (f' x) = fx x t) \<and>
      continuous_on S f'"
        by (rule c1_euclidean_blinfunE[OF c1(1)[OF \<open>t \<in> _\<close>] fx1[OF \<open>t \<in> _\<close>]]) (auto, metis)
    } then obtain fx' where
      fx':
      "\<And>t x. t \<in> cbox a b \<Longrightarrow> x \<in> S \<Longrightarrow> ((\<lambda>x. f x t) has_derivative blinfun_apply (fx' t x)) (at x within S)"
      "\<And>t x. t \<in> cbox a b \<Longrightarrow> x \<in> S \<Longrightarrow> blinfun_apply (fx' t x) = fx x t"
      "\<And>t. t \<in> cbox a b \<Longrightarrow> continuous_on S (fx' t)"
      by metis
    have c: "continuous_on (S \<times> cbox a b) (\<lambda>(x, t). fx' t x)"
      apply (rule continuous_on_blinfunI1)
      using c1(2)
      apply (rule continuous_on_eq) apply assumption
      by (auto simp: fx' split_beta')
    from leibniz_rule[of S a b f "\<lambda>x t. fx' t x" x, OF fx'(1) i c \<open>x \<in> S\<close> \<open>convex S\<close>]
    have "((\<lambda>x. integral (cbox a b) (f x)) has_derivative blinfun_apply (integral (cbox a b) (\<lambda>t. fx' t x))) (at x within S)"
      by auto
    then have "((\<lambda>x. integral (cbox a b) (f x)) has_derivative blinfun_apply (integral (cbox a b) (\<lambda>t. fx' t x))) (at x within S)"
      by auto
    also
    have fx'xi: "(\<lambda>t. fx' t x) integrable_on cbox a b"
      apply (rule integrable_continuous)
      apply (rule continuous_on_blinfunI1)
      by (simp add: fx' \<open>x \<in> S\<close> fx2)
    have "blinfun_apply (integral (cbox a b) (\<lambda>t. fx' t x)) = (\<lambda>v. integral (cbox a b) (\<lambda>xb. fx x xb v))"
      apply (rule ext)
      apply (subst blinfun_apply_integral)
       apply (rule fx'xi)
      by (simp add: \<open>x \<in> S\<close> fx' cong: integral_cong)
    finally show "((\<lambda>x. integral (cbox a b) (f x)) has_derivative (\<lambda>c. integral (cbox a b) (\<lambda>xb. fx x xb c))) (at x within S)"
      by simp
  } then show "(\<lambda>x. integral (cbox a b) (f x)) differentiable_on S"
    by (auto simp: differentiable_on_def differentiable_def)
qed

lemmas leibniz_rule'_interval = leibniz_rule'[where 'b="_::ordered_euclidean_space",
    unfolded cbox_interval]

lemma leibniz_rule'_higher:
  "higher_differentiable_on S (\<lambda>x. integral (cbox a b) (f x)) k"
  if "convex S" "open S"
    and c1: "higher_differentiable_on (S\<times>cbox a b) (\<lambda>(x, t). f x t) k"
    \<comment>\<open>this condition is actually too strong:
      it would suffice if higher partial derivatives (w.r.t. x) are continuous w.r.t. t.
      but it makes the statement short and no need to introduce new constants\<close>
  for S::"'a::euclidean_space set"
    and f::"'a \<Rightarrow> 'b::euclidean_space \<Rightarrow> 'c::euclidean_space"
  using c1
proof (induction k arbitrary: f)
  case 0
  then show ?case
    by (auto simp: higher_differentiable_on.simps intro!: integral_continuous_on_param)
next
  case (Suc k)
  define D where "D x = frechet_derivative (\<lambda>(x, y). f x y) (at x)" for x
  note [continuous_intros] =
    Suc.prems[THEN higher_differentiable_on_imp_continuous_on, THEN continuous_on_compose2,
      of _ "\<lambda>x. (f x, g x)" for f g, unfolded split_beta' fst_conv snd_conv]
  from Suc.prems have prems:
    "\<And>xt. xt \<in> S \<times> cbox a b \<Longrightarrow> (\<lambda>(x, y). f x y) differentiable at xt"
    "higher_differentiable_on (S \<times> cbox a b) (\<lambda>x. D x (dx, dt)) k"
    for dx dt
    by (auto simp: higher_differentiable_on.simps D_def)
  from frechet_derivative_worksI[OF this(1), folded D_def]
  have D: "x \<in> S \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>(x, y). f x y) has_derivative D (x, t)) (at (x, t))" for x t
    by auto
  have p1: "((\<lambda>x. (x, t::'b)) has_derivative (\<lambda>h. (h, 0))) (at x within S)" for x t
    by (auto intro!: derivative_eq_intros)
  have Dx: "x \<in> S \<Longrightarrow> t \<in> cbox a b \<Longrightarrow> ((\<lambda>x. f x t) has_derivative (\<lambda>dx. D (x, t) (dx, 0))) (at x within S)" for x t
    by (drule has_derivative_compose[OF p1 D], assumption) auto
  have cD: "continuous_on (S \<times> cbox a b) (\<lambda>(x, t). D (x, t) v)" for v
    apply (rule higher_differentiable_on_imp_continuous_on[where n=k])
    using prems(2)[of "fst v" "snd v"]
    by (auto simp: split_beta')
  have fi: "x \<in> S \<Longrightarrow> f x integrable_on cbox a b" for x
    by (rule integrable_continuous) (auto intro!: continuous_intros)
  from leibniz_rule'[OF \<open>convex S\<close> Dx cD fi]
  have ihd: "x \<in> S \<Longrightarrow> ((\<lambda>x. integral (cbox a b) (f x)) has_derivative (\<lambda>v. integral (cbox a b) (\<lambda>t. D (x, t) (v, 0))))
     (at x within S)"
    and "(\<lambda>x. integral (cbox a b) (f x)) differentiable_on S"
    for x
    by auto
  then have "x \<in> S \<Longrightarrow> (\<lambda>x. integral (cbox a b) (f x)) differentiable at x" for x
    using \<open>open S\<close>
    by (auto simp: differentiable_on_openD)
  moreover
  have "higher_differentiable_on S (\<lambda>x. frechet_derivative (\<lambda>x. integral (cbox a b) (f x)) (at x) v) k" for v
  proof -
    have *: "frechet_derivative (\<lambda>x. integral (cbox a b) (f x)) (at x) =
      (\<lambda>v. integral (cbox a b) (\<lambda>t. D (x, t) (v, 0)))"
      if "x \<in> S"
      for x
      apply (rule frechet_derivative_at')
      using ihd(1)[OF that] at_within_open[OF that \<open>open S\<close>]
      by auto
    have **: "higher_differentiable_on S (\<lambda>x. integral (cbox a b) (\<lambda>t. D (x, t) (v, 0))) k"
      apply (rule Suc.IH)
      using prems by auto
    show ?thesis
      using \<open>open S\<close>
      by (auto simp: * ** cong: higher_differentiable_on_cong)
  qed
  ultimately
  show ?case
    by (auto simp: higher_differentiable_on.simps)
qed

lemmas leibniz_rule'_higher_interval = leibniz_rule'_higher[where 'b="_::ordered_euclidean_space",
    unfolded cbox_interval]


subsection \<open>Smoothness\<close>

definition k_smooth_on :: "enat \<Rightarrow>'a::real_normed_vector set \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  ("_-smooth'_on" [1000]) where
 smooth_on_def: "k-smooth_on S f = (\<forall>n\<le>k. higher_differentiable_on S f n)"

abbreviation "smooth_on S f \<equiv> \<infinity>-smooth_on S f"

lemma derivative_is_smooth':
  assumes "(k+1)-smooth_on S f"
  shows "k-smooth_on S (\<lambda>x. frechet_derivative f (at x) v)"
  unfolding smooth_on_def
proof (intro allI impI)
  fix n assume "enat n \<le> k" then have "Suc n \<le> k + 1"
    unfolding plus_1_eSuc
    by (auto simp: eSuc_def split: enat.splits)
  then have "higher_differentiable_on S f (Suc n)"
    using assms(1) by (auto simp: smooth_on_def)
  then show "higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) n"
    by (auto simp: higher_differentiable_on.simps(2))
qed

lemma derivative_is_smooth: "smooth_on S f \<Longrightarrow> smooth_on S (\<lambda>x. frechet_derivative f (at x) v)"
  using derivative_is_smooth'[of \<infinity> S f] by simp

lemma smooth_on_imp_continuous_on: "continuous_on S f" if "k-smooth_on S f"
  apply (rule higher_differentiable_on_imp_continuous_on[where n=0])
  using that
  by (simp add: smooth_on_def enat_0)

lemma smooth_on_imp_differentiable_on[simp]: "f differentiable_on S" if "k-smooth_on S f" "k \<noteq> 0"
  using that
  by (auto simp: smooth_on_def Suc_ile_eq enat_0
      dest!: spec[where x=1]
      intro!: higher_differentiable_on_imp_differentiable_on[where k=1])

lemma smooth_on_cong:
  assumes "k-smooth_on S g" "open S"
    and "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "k-smooth_on S f"
  using assms unfolding smooth_on_def
  by (auto cong: higher_differentiable_on_cong)

lemma smooth_on_open_Un:
  "k-smooth_on S f \<Longrightarrow> k-smooth_on T f \<Longrightarrow> open S \<Longrightarrow> open T \<Longrightarrow> k-smooth_on (S \<union> T) f"
  by (auto simp: smooth_on_def higher_differentiable_on_open_Un)

lemma smooth_on_open_subsetsI:
  "k-smooth_on S f"
  if "\<And>x. x \<in> S \<Longrightarrow> \<exists>T. x \<in> T \<and> open T \<and> k-smooth_on T f"
  using that
  unfolding smooth_on_def
  by (force intro: higher_differentiable_on_open_subsetsI)

lemma smooth_on_const[intro]: "k-smooth_on S (\<lambda>x. c)"
  by (auto simp: smooth_on_def higher_differentiable_on_const)

lemma smooth_on_id[intro]: "k-smooth_on S (\<lambda>x. x)"
  by (auto simp: smooth_on_def higher_differentiable_on_id)

lemma smooth_on_add_fun: "k-smooth_on S f \<Longrightarrow> k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow> k-smooth_on S (f + g)"
  by (auto simp: smooth_on_def higher_differentiable_on_add plus_fun_def)

lemmas smooth_on_add = smooth_on_add_fun[unfolded plus_fun_def]

lemma smooth_on_sum:
  "n-smooth_on S (\<lambda>x. \<Sum>i\<in>F. f i x)"
  if "\<And>i. i \<in> F \<Longrightarrow> finite F \<Longrightarrow> n-smooth_on S (f i)" "open S"
  using that
  by (auto simp: smooth_on_def higher_differentiable_on_sum)

lemma (in bounded_bilinear) smooth_on:
  includes no_matrix_mult
  assumes "k-smooth_on S f" "k-smooth_on S g" "open S"
  shows "k-smooth_on S (\<lambda>x. (f x) ** (g x))"
  using assms
  by (auto simp: smooth_on_def higher_differentiable_on)

lemma smooth_on_compose2:
  fixes g::"_\<Rightarrow>_::euclidean_space"
  assumes "k-smooth_on T f" "k-smooth_on S g" "open U" "open T" "g ` U \<subseteq> T" "U \<subseteq> S" 
  shows "k-smooth_on U (f o g)"
  using assms
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_compose intro: higher_differentiable_on_subset)

lemma smooth_on_compose:
  fixes g::"_\<Rightarrow>_::euclidean_space"
  assumes "k-smooth_on T f" "k-smooth_on S g" "open S" "open T" "g ` S \<subseteq> T"
  shows "k-smooth_on S (f o g)"
  using assms by (rule smooth_on_compose2) auto

lemma smooth_on_subset:
  "k-smooth_on S f"
  if "k-smooth_on T f" "S \<subseteq> T"
  using higher_differentiable_on_subset[of T f _ S] that
  by (auto simp: smooth_on_def)

context begin
private lemmas s = bounded_bilinear.smooth_on
lemmas smooth_on_inner = bounded_bilinear_inner[THEN s]
   and smooth_on_scaleR = bounded_bilinear_scaleR[THEN s]
   and smooth_on_mult = bounded_bilinear_mult[THEN s]
end

lemma smooth_on_divide:"k-smooth_on S f \<Longrightarrow> k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow>(\<And>x. x \<in> S \<Longrightarrow> g x \<noteq> 0) \<Longrightarrow>
  k-smooth_on S (\<lambda>x. f x / g x)"
  for f::"_\<Rightarrow>_::real_normed_field"
  by (auto simp: smooth_on_def higher_differentiable_on_divide)

lemma smooth_on_scaleR_fun: "k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow> k-smooth_on S (c *\<^sub>R g)"
  by (auto simp: scaleR_fun_def intro!: smooth_on_scaleR )

lemma smooth_on_uminus_fun: "k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow> k-smooth_on S (- g)"
  using smooth_on_scaleR_fun[where c="-1", of k S g]
  by auto

lemmas smooth_on_uminus = smooth_on_uminus_fun[unfolded fun_Compl_def]

lemma smooth_on_minus_fun: "k-smooth_on S f \<Longrightarrow> k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow> k-smooth_on S (f - g)"
  unfolding diff_conv_add_uminus
  apply (rule smooth_on_add_fun)
    apply assumption
   apply (rule smooth_on_uminus_fun)
  by auto

lemmas smooth_on_minus = smooth_on_minus_fun[unfolded fun_diff_def]

lemma smooth_on_times_fun: "k-smooth_on S f \<Longrightarrow> k-smooth_on S g \<Longrightarrow> open S \<Longrightarrow> k-smooth_on S (f * g)"
  for f g::"_ \<Rightarrow>_::real_normed_algebra"
  by (auto simp: times_fun_def intro!: smooth_on_mult)

lemma smooth_on_le:
  "l-smooth_on S f"
  if "k-smooth_on S f" "l \<le> k"
  using that
  by (auto simp: smooth_on_def)

lemma smooth_on_inverse: "k-smooth_on S (\<lambda>x. inverse (f x))"
  if "k-smooth_on S f" "0 \<notin> f ` S" "open S"
  for f::"_ \<Rightarrow>_::real_normed_field"
  using that
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_inverse)

lemma smooth_on_norm: "k-smooth_on S (\<lambda>x. norm (f x))"
  if "k-smooth_on S f" "0 \<notin> f ` S" "open S"
  for f::"_ \<Rightarrow>_::real_inner"
  using that
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_norm)

lemma smooth_on_sqrt: "k-smooth_on S (\<lambda>x. sqrt (f x))"
  if "k-smooth_on S f" "0 \<notin> f ` S" "open S"
  using that
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_sqrt)

lemma smooth_on_frechet_derivative:
  "\<infinity>-smooth_on UNIV (\<lambda>x. frechet_derivative f (at x) v)"
  if "\<infinity>-smooth_on UNIV f"
    \<comment>\<open>TODO: generalize\<close>
  using that
  apply (auto simp: smooth_on_def)
  apply (rule higher_differentiable_on_frechet_derivativeI)
  by auto

lemmas smooth_on_frechet_derivivative_comp = smooth_on_compose2[OF smooth_on_frechet_derivative, unfolded o_def]

lemma smooth_onD: "higher_differentiable_on S f n" if "m-smooth_on S f" "enat n \<le> m"
  using that
  by (auto simp: smooth_on_def)

lemma (in bounded_linear) higher_differentiable_on: "higher_differentiable_on S f n"
proof (induction n)
  case 0
  then show ?case
    by (auto simp: higher_differentiable_on.simps linear_continuous_on bounded_linear_axioms)
next
  case (Suc n)
  then show ?case
    apply (auto simp: higher_differentiable_on.simps frechet_derivative higher_differentiable_on_const)
    using bounded_linear_axioms apply (rule bounded_linear_imp_differentiable)
    done
qed

lemma (in bounded_linear) smooth_on: "k-smooth_on S f"
  by (auto simp: smooth_on_def higher_differentiable_on)

lemma smooth_on_snd:
  "k-smooth_on S (\<lambda>x. snd (f x))"
  if "k-smooth_on S f" "open S"
  using higher_differentiable_on_snd_comp that
  by (auto simp: smooth_on_def)

lemma smooth_on_fst:
  "k-smooth_on S (\<lambda>x. fst (f x))"
  if "k-smooth_on S f" "open S"
  using higher_differentiable_on_fst_comp that
  by (auto simp: smooth_on_def)

lemma smooth_on_sin: "n-smooth_on S (\<lambda>x. sin (f x::real))" if "n-smooth_on S f" "open S"
  using that
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_sin)

lemma smooth_on_cos: "n-smooth_on S (\<lambda>x. cos (f x::real))" if "n-smooth_on S f" "open S"
  using that
  by (auto simp: smooth_on_def intro!: higher_differentiable_on_cos)

lemma smooth_on_Taylor2E:
  fixes f::"'a::euclidean_space \<Rightarrow> real"
  assumes hd: "\<infinity>-smooth_on UNIV f"
  obtains g where "\<And>Y.
    f Y = f X + frechet_derivative f (at X) (Y - X) + (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. ((Y - X) \<bullet> j) * ((Y - X) \<bullet> i) * g i j Y))"
    "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> \<infinity>-smooth_on UNIV (g i j)"
    \<comment>\<open>TODO: generalize\<close>
proof -
  define S::"'a set" where "S = UNIV"
  have "open S" and "convex S" "X \<in> S" by (auto simp: S_def)
  have hd: "\<infinity>-smooth_on S f"
    using hd by (auto simp: S_def)
  define i where "i H x = ((1 - x)) *\<^sub>R nth_derivative 2 f (X + x *\<^sub>R H) H" for x H
  define d2 where "d2 v v' = (\<lambda>x. frechet_derivative (\<lambda>x. frechet_derivative f (at x) v') (at x) v)" for v v'
  define g where "g H x i j = d2 i j (X + x *\<^sub>R H)" for i j x H
  define g' where  "g' i j H = integral {0 .. 1} (\<lambda>x. (1 - x) * g H x i j)" for i j H
  have "higher_differentiable_on S f 2"
    using hd(1) by (auto simp: smooth_on_def dest!: spec[where x=2])
  note hd2 = this \<open>open S\<close>

  have d2_cont: "continuous_on S (d2 i j)" for i j
    using hd2(1)
    by (auto simp: g_def numeral_2_eq_2 higher_differentiable_on.simps d2_def)
  note [continuous_intros] = continuous_on_compose2[OF d2_cont]

  have hdiff2: "\<infinity>-smooth_on S (d2 v v')" for v v'
    apply (auto simp: d2_def)
    apply (rule smooth_on_frechet_derivivative_comp)
    apply (rule smooth_on_frechet_derivivative_comp)
    by (auto simp: S_def assms)
  {
    fix Y
    assume "Y \<in> S"
    define H where "H = Y - X"
    from \<open>Y \<in> S\<close> have "X + H \<in> S" by (simp add: H_def)
    with \<open>X \<in> S\<close> have cs: "closed_segment X (X + H) \<subseteq> S"
      using \<open>convex S\<close>
      by (rule closed_segment_subset)

    have i: "(i H has_integral f (X + H) - (f X + nth_derivative 1 f X H)) {0..1}"
      "f (X + H) = f X + nth_derivative 1 f X H + integral {0..1} (i H)"
      "i H integrable_on {0..1}"
      unfolding i_def
      using higher_differentiable_Taylor1[OF hd2 cs]
      by auto
    note i(2)
    also

    have integrable: "(\<lambda>x. \<Sum>n\<in>Basis. (1 - x) * (g H x a n * (H \<bullet> n) * (H \<bullet> a))) integrable_on {0..1}"
      "(\<lambda>x. (1 - x) * (g H x n a * (H \<bullet> a) * (H \<bullet> n))) integrable_on {0..1}" 
      for a n
       by (auto intro!: integrable_continuous_interval continuous_intros closed_segment_subsetD
          cs simp: g_def)

    have i_eq: "i H x = (1 - x) *\<^sub>R (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. g H x i j * (H \<bullet> j)) * (H \<bullet> i))"
      if "0 \<le> x" "x \<le> 1"
      for x
      unfolding i_def
      apply (subst second_derivative_componentwise[OF hd2])
       apply (rule closed_segment_subsetD, rule cs, rule that, rule that)
      by (simp add: g_def d2_def)

    have "integral {0 .. 1} (i H) = integral {0..1} (\<lambda>x. (1 - x) * (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. g H x i j * (H \<bullet> j)) * (H \<bullet> i)))"
      apply (subst integral_spike[OF negligible_empty])
       apply (rule sym)
       apply (rule i_eq)
      by (auto simp: that)
    also
    have "\<dots> = (\<Sum>i\<in>Basis. (\<Sum>j\<in>Basis. (H \<bullet> j) * (H \<bullet> i) * g' i j H))"
      apply (simp add: sum_distrib_left sum_distrib_right integral_sum integrable g'_def)
      apply (simp add: integral_mult_right[symmetric] del: integral_mult_right)
      by (simp only: ac_simps)
    finally have "f (X + H) = f X + nth_derivative 1 f X H + (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. H \<bullet> j * (H \<bullet> i) * g' i j H)" .
  } note * = this
  have "f Y = f X + frechet_derivative f (at X) (Y - X) + (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. (Y - X) \<bullet> j * ((Y - X) \<bullet> i) * g' i j (Y - X))"
    for Y
    using *[of Y]
    by (auto simp: S_def)
  moreover
  define T::"real set" where "T = {- 1<..<2}"
  have "open T"
    by (auto simp: T_def)
  have "{0 .. 1} \<subseteq> T"
    by (auto simp: T_def)
  have T_small: "a \<in> S \<Longrightarrow> b \<in> T \<Longrightarrow> X + b *\<^sub>R (a - X) \<in> S" for a b
    by (auto simp: S_def)
  have "open (S \<times> T)"
    by (auto intro: open_Times \<open>open S\<close> \<open>open T\<close>)
  have "smooth_on S (\<lambda>Y. g' i j (Y - X))" if i: "i \<in> Basis" and j: "j \<in> Basis" for i j
    unfolding smooth_on_def
    apply safe
    apply (simp add: g'_def)
    apply (rule leibniz_rule'_higher_interval)
      apply fact
     apply fact
    apply (rule higher_differentiable_on_subset[where T="S \<times> T"])
     apply (auto intro!: higher_differentiable_on_mult simp: split_beta')
       apply (subst diff_conv_add_uminus)
       apply (rule higher_differentiable_on_add)
         apply (rule higher_differentiable_on_const)
        apply (subst scaleR_minus1_left[symmetric])
        apply (rule higher_differentiable_on_scaleR)
          apply (rule higher_differentiable_on_const)
         apply (rule higher_differentiable_on_snd_comp)
          apply (rule higher_differentiable_on_id)
         apply fact apply fact apply fact
      apply (auto simp: g_def)
      apply (rule smooth_onD)
       apply (rule smooth_on_compose2[OF hdiff2, unfolded o_def])
    using \<open>open S\<close> \<open>open T\<close>
    using T_small \<open>_ \<subseteq> T\<close>
    by (auto intro!: open_Times smooth_on_add smooth_on_scaleR smooth_on_snd
        smooth_on_minus smooth_on_fst)
  ultimately show ?thesis unfolding S_def ..
qed


lemma smooth_on_Pair:
  "k-smooth_on S (\<lambda>x. (f x, g x))"
  if "open S" "k-smooth_on S f" "k-smooth_on S g"
proof (auto simp: smooth_on_def)
  fix n assume n: "enat n \<le> k"
  have 1: "higher_differentiable_on S f n"
    using that(2) n unfolding smooth_on_def by auto
  have 2: "higher_differentiable_on S g n"
    using that(3) n unfolding smooth_on_def by auto
  show "higher_differentiable_on S (\<lambda>x. (f x, g x)) n"
    by (rule higher_differentiable_on_Pair [OF that(1) 1 2])
qed


lemma smooth_on_Pair':
  "k-smooth_on (S \<times> T) (\<lambda>x. (f (fst x), g (snd x)))"
  if "open S" "open T" "k-smooth_on S f" "k-smooth_on T g"
  for f::"_::euclidean_space\<Rightarrow>_" and g::"_::euclidean_space\<Rightarrow>_"
proof (auto simp: smooth_on_def)
  fix n assume n: "enat n \<le> k"
  have 1: "higher_differentiable_on S f n"
    using that(3) n unfolding smooth_on_def by auto
  have 2: "higher_differentiable_on T g n"
    using that(4) n unfolding smooth_on_def by auto
  show "higher_differentiable_on (S \<times> T) (\<lambda>x. (f (fst x), g (snd x))) n"
    by (rule higher_differentiable_on_Pair'[OF that(1,2) 1 2])
qed


subsection \<open>Diffeomorphism\<close>

definition "diffeomorphism k S T p p' \<longleftrightarrow>
  k-smooth_on S p \<and> k-smooth_on T p' \<and> homeomorphism S T p p'"

lemma diffeomorphism_imp_homeomorphism:
  assumes "diffeomorphism k s t p p'"
  shows  "homeomorphism s t p p'"
  using assms
  by (auto simp: diffeomorphism_def)

lemma diffeomorphismD:
  assumes "diffeomorphism k S T f g"
  shows diffeomorphism_smoothD: "k-smooth_on S f" "k-smooth_on T g"
    and diffeomorphism_inverseD: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x" "\<And>y. y \<in> T \<Longrightarrow> f (g y) = y"
    and diffeomorphism_image_eq: "(f ` S = T)" "(g ` T = S)"
  using assms by (auto simp: diffeomorphism_def homeomorphism_def)

lemma diffeomorphism_compose:
  "diffeomorphism n S T f g \<Longrightarrow> diffeomorphism n T U h k \<Longrightarrow> open S \<Longrightarrow> open T \<Longrightarrow> open U \<Longrightarrow>
    diffeomorphism n S U (h \<circ> f) (g \<circ> k)"
  for f::"_\<Rightarrow>_::euclidean_space"
  by (auto simp: diffeomorphism_def intro!: smooth_on_compose homeomorphism_compose)
    (auto simp: homeomorphism_def)

lemma diffeomorphism_add: "diffeomorphism k UNIV UNIV (\<lambda>x. x + c) (\<lambda>x. x - c)"
  by (auto simp: diffeomorphism_def homeomorphism_add intro!: smooth_on_minus smooth_on_add)

lemma diffeomorphism_scaleR: "diffeomorphism k UNIV UNIV (\<lambda>x. c *\<^sub>R x) (\<lambda>x. x /\<^sub>R c)"
  if "c \<noteq> 0"
  by (auto simp: that diffeomorphism_def homeomorphism_scaleR
      intro!: smooth_on_minus smooth_on_scaleR)

end
