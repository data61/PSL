theory Cartan
imports "HOL-Analysis.Analysis"

begin

section\<open>First Cartan Theorem\<close>

text\<open>Ported from HOL Light. See
      Gianni Ciolli, Graziano Gentili, Marco Maggesi.
      A Certified Proof of the Cartan Fixed Point Theorems.
      J Automated Reasoning (2011) 47:319--336    DOI 10.1007/s10817-010-9198-6\<close>

lemma deriv_left_inverse:
  assumes "f holomorphic_on S" and "g holomorphic_on T"
      and "open S" and "open T"
      and "f ` S \<subseteq> T"
      and [simp]: "\<And>z. z \<in> S \<Longrightarrow> g (f z) = z"
      and "w \<in> S"
    shows "deriv f w * deriv g (f w) = 1"
proof -
  have "deriv f w * deriv g (f w) = deriv g (f w) * deriv f w"
    by (simp add: algebra_simps)
  also have "... = deriv (g o f) w"
    using assms
    by (metis analytic_on_imp_differentiable_at analytic_on_open complex_derivative_chain image_subset_iff)
  also have "... = deriv id w"
    apply (rule complex_derivative_transform_within_open [where s=S])
    apply (rule assms holomorphic_on_compose_gen holomorphic_intros)+
    apply simp
    done
  also have "... = 1"
    using higher_deriv_id [of 1] by simp
  finally show ?thesis .
qed

lemma Cauchy_higher_deriv_bound:
    assumes holf: "f holomorphic_on (ball z r)"
        and contf: "continuous_on (cball z r) f"
        and "0 < r" and "0 < n"
        and fin : "\<And>w. w \<in> ball z r \<Longrightarrow> f w \<in> ball y B0"
      shows "norm ((deriv ^^ n) f z) \<le> (fact n) * B0 / r^n"
proof -
  have "0 < B0" using \<open>0 < r\<close> fin [of z]
    by (metis ball_eq_empty ex_in_conv fin not_less)
  have le_B0: "\<And>w. cmod (w - z) \<le> r \<Longrightarrow> cmod (f w - y) \<le> B0"
    apply (rule continuous_on_closure_norm_le [of "ball z r" "\<lambda>w. f w - y"])
    apply (auto simp: \<open>0 < r\<close>  dist_norm norm_minus_commute)
    apply (rule continuous_intros contf)+
    using fin apply (simp add: dist_commute dist_norm less_eq_real_def)
    done
  have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w) z - (deriv ^^ n) (\<lambda>w. y) z"
    using \<open>0 < n\<close> by simp
  also have "... = (deriv ^^ n) (\<lambda>w. f w - y) z"
    by (rule higher_deriv_diff [OF holf, symmetric]) (auto simp: \<open>0 < r\<close> holomorphic_on_const)
  finally have "(deriv ^^ n) f z = (deriv ^^ n) (\<lambda>w. f w - y) z" .
  have contf': "continuous_on (cball z r) (\<lambda>u. f u - y)"
    by (rule contf continuous_intros)+
  have holf': "(\<lambda>u. (f u - y)) holomorphic_on (ball z r)"
    by (simp add: holf holomorphic_on_diff holomorphic_on_const)
  define a where "a = (2 * pi)/(fact n)"
  have "0 < a"  by (simp add: a_def)
  have "B0/r^(Suc n)*2 * pi * r = a*((fact n)*B0/r^n)"
    using \<open>0 < r\<close> by (simp add: a_def divide_simps)
  have der_dif: "(deriv ^^ n) (\<lambda>w. f w - y) z = (deriv ^^ n) f z"
    using \<open>0 < r\<close> \<open>0 < n\<close>
    by (auto simp: higher_deriv_diff [OF holf holomorphic_on_const])
  have "norm ((2 * of_real pi * \<i>)/(fact n) * (deriv ^^ n) (\<lambda>w. f w - y) z)
        \<le> (B0/r^(Suc n)) * (2 * pi * r)"
    apply (rule has_contour_integral_bound_circlepath [of "(\<lambda>u. (f u - y)/(u - z)^(Suc n))" _ z])
    using Cauchy_has_contour_integral_higher_derivative_circlepath [OF contf' holf']
    using \<open>0 < B0\<close> \<open>0 < r\<close>
    apply (auto simp: norm_divide norm_mult norm_power divide_simps le_B0)
    done
  then show ?thesis
    using \<open>0 < r\<close>
    by (auto simp: norm_divide norm_mult norm_power field_simps der_dif le_B0)
qed

lemma higher_deriv_comp_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and "z \<in> s"
        and t: "open t" and holg: "g holomorphic_on t"
        and fst: "f ` s \<subseteq> t"
        and n: "i \<le> n"
        and dfz: "deriv f z = 1" and zero: "\<And>i. \<lbrakk>1 < i; i \<le> n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ i) (g o f) z = (deriv ^^ i) g (f z)"
using n holg
proof (induction i arbitrary: g)
  case 0 then show ?case by simp
next
  case (Suc i)
  have "g \<circ> f holomorphic_on s" using "Suc.prems" holf
    using fst  by (simp add: holomorphic_on_compose_gen image_subset_iff)
  then have 1: "deriv (g \<circ> f) holomorphic_on s"
    by (simp add: holomorphic_deriv s)
  have dg: "deriv g holomorphic_on t"
    using Suc.prems by (simp add: Suc.prems(2) holomorphic_deriv t)
  then have "deriv g holomorphic_on f ` s"
    using fst  by (simp add: holomorphic_on_subset image_subset_iff)
  then have dgf: "(deriv g o f) holomorphic_on s"
    by (simp add: holf holomorphic_on_compose)
  then have 2: "(\<lambda>w. (deriv g o f) w * deriv f w) holomorphic_on s"
    by (blast intro: holomorphic_intros holomorphic_on_compose holf s)
  have "(deriv ^^ i) (deriv (g o f)) z = (deriv ^^ i) (\<lambda>w. deriv g (f w) * deriv f w) z"
    apply (rule higher_deriv_transform_within_open [OF 1 2 [unfolded o_def] s \<open>z \<in> s\<close>])
    apply (rule complex_derivative_chain)
    using holf Suc.prems fst apply (auto simp: holomorphic_on_imp_differentiable_at s t)
    done
  also have "... = (\<Sum>j=0..i. of_nat(i choose j) * (deriv ^^ j) (\<lambda>w. deriv g (f w)) z * (deriv ^^ (i - j)) (deriv f) z)"
    apply (rule higher_deriv_mult [OF dgf [unfolded o_def] _ s \<open>z \<in> s\<close>])
    by (simp add: holf holomorphic_deriv s)
  also have "... = (\<Sum>j=i..i. of_nat(i choose j) * (deriv ^^ j) (\<lambda>w. deriv g (f w)) z * (deriv ^^ Suc (i - j)) f z)"
  proof -
    have *: "(deriv ^^ j) (\<lambda>w. deriv g (f w)) z = 0"  if "j < i" and nz: "(deriv ^^ (i - j)) (deriv f) z \<noteq> 0" for j
    proof -
      have "1 < Suc (i - j)" "Suc (i - j) \<le> n"
        using \<open>j < i\<close> \<open>Suc i \<le> n\<close> by auto
      then show ?thesis  by (metis comp_def funpow.simps(2) funpow_swap1 zero nz)
    qed
    then show ?thesis
      apply (simp only: funpow_Suc_right o_def)
      apply (rule comm_monoid_add_class.sum.mono_neutral_right, auto)
      done
  qed
  also have "... = (deriv ^^ i) (deriv g) (f z)"
    using Suc.IH [OF _ dg] Suc.prems by (simp add: dfz)
  finally show ?case
    by (simp only: funpow_Suc_right o_def)
qed


lemma higher_deriv_comp_iter_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and n: "i \<le> n"
        and dfz: "deriv f z = 1" and zero: "\<And>i. \<lbrakk>1 < i; i \<le> n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ i) (f^^m) z = (deriv ^^ i) f z"
proof -
  have holfm: "(f^^m) holomorphic_on s" for m
    apply (induction m, simp add: holomorphic_on_ident)
    apply (simp only: funpow_Suc_right holomorphic_on_compose_gen [OF holf _ fss])
    done
  show ?thesis using n
  proof (induction m)
    case 0 with dfz show ?case
      by (auto simp: zero)
  next
    case (Suc m)
    have "(deriv ^^ i) (f ^^ m \<circ> f) z = (deriv ^^ i) (f ^^ m) (f z)"
      using Suc.prems holfm \<open>z \<in> s\<close> dfz fss higher_deriv_comp_lemma holf s zero by blast
    also have "... = (deriv ^^ i) f z"
      by (simp add: Suc)
    finally show ?case
      by (simp only: funpow_Suc_right)
  qed
qed

lemma higher_deriv_iter_top_lemma:
    assumes s: "open s" and holf: "f holomorphic_on s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and dfz [simp]: "deriv f z = 1"
        and n: "1 < n" "\<And>i. \<lbrakk>1 < i; i < n\<rbrakk> \<Longrightarrow> (deriv ^^ i) f z = 0"
      shows "(deriv ^^ n) (f ^^ m) z = m * (deriv ^^ n) f z"
using n
proof (induction n arbitrary: m)
  case 0 then show ?case by simp
next
  case (Suc n)
  have [simp]: "(f^^m) z = z" for m
    by (induction m) auto
  have fms_sb: "(f^^m) ` s \<subseteq> s" for m
    apply (induction m)
    using fss
    apply force+
    done
  have holfm: "(f^^m) holomorphic_on s" for m
    apply (induction m, simp add: holomorphic_on_ident)
    apply (simp only: funpow_Suc_right holomorphic_on_compose_gen [OF holf _ fss])
    done
  then have holdfm: "deriv (f ^^ m) holomorphic_on s" for m
    by (simp add: holomorphic_deriv s)
  have holdffm: "(\<lambda>z. deriv f ((f ^^ m) z)) holomorphic_on s" for m
    apply (rule holomorphic_on_compose_gen [where g="deriv f" and t=s, unfolded o_def])
    using s \<open>z \<in> s\<close> holfm holf fms_sb by (auto intro: holomorphic_intros)
  have f_cd_w: "\<And>w. w \<in> s \<Longrightarrow> f field_differentiable at w"
    using holf holomorphic_on_imp_differentiable_at s by blast
  have f_cd_mw: "\<And>m w. w \<in> s \<Longrightarrow> (f^^m) field_differentiable at w"
    using holfm holomorphic_on_imp_differentiable_at s by auto
  have der_fm [simp]: "deriv (f ^^ m) z = 1" for m
    apply (induction m, simp add: deriv_ident)
    apply (subst funpow_Suc_right)
    apply (subst complex_derivative_chain)
    using \<open>z \<in> s\<close> holfm holomorphic_on_imp_differentiable_at s f_cd_w apply auto
    done
  note Suc(3) [simp]
  note n_Suc = Suc
  show ?case
  proof (induction m)
    case 0 with n_Suc show ?case
      by (metis Zero_not_Suc funpow_simps_right(1) higher_deriv_id lambda_zero nat_neq_iff of_nat_0)
  next
    case (Suc m)
    have deriv_nffm: "(deriv ^^ n) (deriv f o (f ^^ m)) z = (deriv ^^ n) (deriv f) ((f ^^ m) z)"
      apply (rule higher_deriv_comp_lemma [OF s holfm \<open>z \<in> s\<close> s _ fms_sb order_refl])
      using \<open>z \<in> s\<close> fss higher_deriv_comp_iter_lemma holf holf holomorphic_deriv s
        apply auto
      done
    have "deriv (f ^^ m \<circ> f) holomorphic_on s"
      by (metis funpow_Suc_right holdfm)
    moreover have "(\<lambda>w. deriv f ((f ^^ m) w) * deriv (f ^^ m) w) holomorphic_on s"
      by (rule holomorphic_on_mult [OF holdffm holdfm])
    ultimately have "(deriv ^^ n) (deriv (f ^^ m \<circ> f)) z = (deriv ^^ n) (\<lambda>w. deriv f ((f ^^ m) w) * deriv (f ^^ m) w) z"
      apply (rule higher_deriv_transform_within_open [OF _ _ s \<open>z \<in> s\<close>])
      by (metis comp_funpow complex_derivative_chain f_cd_mw f_cd_w fms_sb funpow_swap1 image_subset_iff o_id)
    also have "... =
          (\<Sum>i=0..n. of_nat(n choose i) * (deriv ^^ i) (\<lambda>w. deriv f ((f ^^ m) w)) z *
                     (deriv ^^ (n - i)) (deriv (f ^^ m)) z)"
      by (rule higher_deriv_mult [OF holdffm holdfm s \<open>z \<in> s\<close>])
    also have "... = (\<Sum>i \<in> {0,n}. of_nat(n choose i) * (deriv ^^ i) (\<lambda>w. deriv f ((f ^^ m) w)) z *
                     (deriv ^^ (n - i)) (deriv (f ^^ m)) z)"
    proof -
      have *: "(deriv ^^ i) (\<lambda>w. deriv f ((f ^^ m) w)) z = 0"  if "i \<le> n" "0 < i" "i \<noteq> n" and nz: "(deriv ^^ (n - i)) (deriv (f ^^ m)) z \<noteq> 0" for i
      proof -
        have less: "1 < Suc (n-i)" and le: "Suc (n-i) \<le> n"
          using that by auto
        have "(deriv ^^ (Suc (n - i))) (f ^^ m) z = (deriv ^^(Suc (n - i))) f z"
          apply (rule higher_deriv_comp_iter_lemma [OF s holf fss \<open>z \<in> s\<close> \<open>f z = z\<close> le dfz])
          by simp
        also have "... = 0"
          using n_Suc(3) less le le_imp_less_Suc by blast
        finally have "(deriv ^^ (Suc (n - i))) (f ^^ m) z = 0" .
        then show ?thesis by (simp add: funpow_swap1 nz)
      qed
      show ?thesis
        by (rule comm_monoid_add_class.sum.mono_neutral_right) (auto simp: *)
    qed
    also have "... = of_nat (Suc m) * (deriv ^^ n) (deriv f) z"
      apply (subst Groups_Big.comm_monoid_add_class.sum.insert)
      apply (simp_all add: deriv_nffm [unfolded o_def] of_nat_Suc [of 0] del: of_nat_Suc)
      using n_Suc(2) Suc
      apply (auto simp del: funpow.simps simp: algebra_simps funpow_simps_right)
      done
    finally have "(deriv ^^ n) (deriv (f ^^ m \<circ> f)) z = of_nat (Suc m) * (deriv ^^ n) (deriv f) z" .
    then show ?case
      apply (simp only: funpow_Suc_right)
      apply (simp add: o_def del: of_nat_Suc)
      done
  qed
qed


text\<open>Should be proved for n-dimensional vectors of complex numbers\<close>
theorem first_Cartan_dim_1:
    assumes holf: "f holomorphic_on s"
        and "open s" "connected s" "bounded s"
        and fss: "f ` s \<subseteq> s"
        and "z \<in> s" and [simp]: "f z = z"
        and dfz [simp]: "deriv f z = 1"
        and "w \<in> s"
      shows "f w = w"
proof -
  obtain c where "0 < c" and c: "s \<subseteq> ball z c"
    using \<open>bounded s\<close> bounded_subset_ballD by blast
  obtain r where "0 < r" and r: "cball z r \<subseteq> s"
    using \<open>z \<in> s\<close> open_contains_cball \<open>open s\<close> by blast
  then have bzr: "ball z r \<subseteq> s" using ball_subset_cball by blast
  have fms_sb: "(f^^m) ` s \<subseteq> s" for m
    apply (induction m)
    using fss apply force+
    done
  have holfm: "(f^^m) holomorphic_on s" for m
    apply (induction m, simp add: holomorphic_on_ident)
    apply (simp only: funpow_Suc_right holomorphic_on_compose_gen [OF holf _ fss])
    done
  have *: "(deriv ^^ n) f z = (deriv ^^ n) id z" for n
  proof -
    consider "n = 0" | "n = 1" | "1 < n" by arith
    then show ?thesis
    proof cases
      assume "n = 0" then show ?thesis by force
    next
      assume "n = 1" then show ?thesis by force
    next
      assume n1: "n > 1"
      then have "(deriv ^^ n) f z = 0"
      proof (induction n rule: less_induct)
        case (less n)
        have le: "real m * cmod ((deriv ^^ n) f z) \<le> fact n * c / r ^ n" if "m\<noteq>0" for m
        proof -
          have holfm': "(f ^^ m) holomorphic_on ball z r"
            using holfm bzr holomorphic_on_subset by blast
          then have contfm': "continuous_on (cball z r) (f ^^ m)"
            using \<open>cball z r \<subseteq> s\<close> holfm holomorphic_on_imp_continuous_on holomorphic_on_subset by blast
          have "real m * cmod ((deriv ^^ n) f z) = cmod (real m * (deriv ^^ n) f z)"
            by (simp add: norm_mult)
          also have "... = cmod ((deriv ^^ n) (f ^^ m) z)"
            apply (subst higher_deriv_iter_top_lemma [OF \<open>open s\<close> holf fss \<open>z \<in> s\<close> \<open>f z = z\<close> dfz])
            using less apply auto
            done
          also have "... \<le> fact n * c / r ^ n"
            apply (rule Cauchy_higher_deriv_bound [OF holfm' contfm' \<open>0 < r\<close>, where y=z])
            using less.prems apply linarith
            using fms_sb c r ball_subset_cball
            apply blast
            done
          finally show ?thesis .
        qed
        have "cmod ((deriv ^^ n) f z) = 0"
          apply (rule real_archimedian_rdiv_eq_0 [where c = "(fact n) * c / r ^ n"])
          apply simp
          using \<open>0 < r\<close> \<open>0 < c\<close>
          apply (simp add: divide_simps)
          apply (blast intro: le)
          done
        then show ?case by simp
      qed
      with n1 show ?thesis by simp
    qed
  qed
  have "f w = id w"
    by (rule holomorphic_fun_eq_on_connected
                 [OF holf holomorphic_on_id \<open>open s\<close> \<open>connected s\<close> * \<open>z \<in> s\<close> \<open>w \<in> s\<close>])
  also have "... = w" by simp
  finally show ?thesis .
qed


text\<open>Second Cartan Theorem.\<close>

lemma Cartan_is_linear:
  assumes holf: "f holomorphic_on s"
      and "open s" and "connected s"
      and "0 \<in> s"
      and ins: "\<And>u z. \<lbrakk>norm u = 1; z \<in> s\<rbrakk> \<Longrightarrow> u * z \<in> s"
      and feq: "\<And>u z. \<lbrakk>norm u = 1; z \<in> s\<rbrakk> \<Longrightarrow> f (u * z) = u * f z"
    shows "\<exists>c. \<forall>z \<in> s. f z = c * z"
proof -
  have [simp]: "f 0 = 0"
    using feq [of "-1" 0] assms by simp
  have uneq: "u^n * (deriv ^^ n) f (u * z) = u * (deriv ^^ n) f z"
       if "norm u = 1" "z \<in> s" for n u z
  proof -
    have holfuw: "(\<lambda>w. f (u * w)) holomorphic_on s"
      apply (rule holomorphic_on_compose_gen [OF _ holf, unfolded o_def])
      using that ins by (auto simp: holomorphic_on_linear)
    have hol_d_fuw: "(deriv ^^ n) (\<lambda>w. u * f w) holomorphic_on s" for n
      by (rule holomorphic_higher_deriv holomorphic_intros holf assms)+
    have *: "(deriv ^^ n) (\<lambda>w. u * f w) z = u * (deriv ^^ n) f z" if "z \<in> s" for z
    using that
    proof (induction n arbitrary: z)
      case 0 then show ?case by simp
    next
      case (Suc n)
      have "deriv ((deriv ^^ n) (\<lambda>w. u * f w)) z = deriv (\<lambda>w. u * (deriv ^^ n) f w) z"
        apply (rule complex_derivative_transform_within_open [OF hol_d_fuw])
        apply (auto intro!: holomorphic_higher_deriv holomorphic_intros assms Suc)
        done
      also have "... = u * deriv ((deriv ^^ n) f) z"
        apply (rule deriv_cmult)
        using Suc \<open>open s\<close> holf holomorphic_higher_deriv holomorphic_on_imp_differentiable_at by blast
      finally show ?case by simp
    qed
    have "(deriv ^^ n) (\<lambda>w. f (u * w)) z = u ^ n * (deriv ^^ n) f (u * z)"
      apply (rule higher_deriv_compose_linear [OF holf \<open>open s\<close> \<open>open s\<close>])
      apply (simp add: that)
      apply (simp add: ins that)
      done
    moreover have "(deriv ^^ n) (\<lambda>w. f (u * w)) z = u * (deriv ^^ n) f z"
      apply (subst higher_deriv_transform_within_open [OF holfuw, of "\<lambda>w. u * f w"])
      apply (rule holomorphic_intros holf assms that)+
      apply blast
      using * \<open>z \<in> s\<close> apply blast
      done
    ultimately show ?thesis by metis
  qed
  have dnf0: "(deriv ^^ n) f 0 = 0" if len: "2 \<le> n" for n
  proof -
    have **: "z = 0" if "\<And>u::complex. norm u = 1 \<Longrightarrow> u ^ n * z = u * z" for z
    proof -
      have "\<exists>u::complex. norm u = 1 \<and> u ^ n \<noteq> u"
        using complex_not_root_unity [of "n-1"] len
        apply (simp add: algebra_simps le_diff_conv2, clarify)
        apply (rule_tac x=u in exI)
        apply (subst (asm) power_diff)
        apply auto
        done
      with that show ?thesis
        by auto
    qed
    show ?thesis
      apply (rule **)
      using uneq [OF _ \<open>0 \<in> s\<close>]
      by force
  qed
  show ?thesis
    apply (rule_tac x = "deriv f 0" in exI, clarify)
    apply (rule holomorphic_fun_eq_on_connected [OF holf _ \<open>open s\<close> \<open>connected s\<close> _ \<open>0 \<in> s\<close>])
    using dnf0 apply (auto simp: holomorphic_on_linear)
    done
qed

text\<open>Should be proved for n-dimensional vectors of complex numbers\<close>
theorem second_Cartan_dim_1:
  assumes holf: "f holomorphic_on ball 0 r"
      and holg: "g holomorphic_on ball 0 r"
      and [simp]: "f 0 = 0" and [simp]: "g 0 = 0"
      and ballf: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f z \<in> ball 0 r"
      and ballg: "\<And>z. z \<in> ball 0 r \<Longrightarrow> g z \<in> ball 0 r"
      and fg: "\<And>z. z \<in> ball 0 r \<Longrightarrow> f (g z) = z"
      and gf: "\<And>z. z \<in> ball 0 r \<Longrightarrow> g (f z) = z"
      and "0 < r"
    shows "\<exists>t. \<forall>z \<in> ball 0 r. g z = exp(\<i> * of_real t) * z"
proof -
  have c_le_1: "c \<le> 1"
    if "0 \<le> c" "\<And>x. 0 \<le> x \<Longrightarrow> x < r \<Longrightarrow> c * x < r" for c
  proof -
    have rst: "\<And>r s t::real. 0 = r \<or> s/r < t \<or> r < 0 \<or> \<not> s < r * t"
      by (metis (no_types) mult_less_cancel_left_disj nonzero_mult_div_cancel_left times_divide_eq_right)
    { assume "\<not> r < c \<and> c * (c * (c * (c * r))) < 1"
     then have "1 \<le> c \<Longrightarrow> (\<exists>r. \<not> 1 < r \<and> \<not> r < c)"
          using \<open>0 \<le> c\<close> by (metis (full_types) less_eq_real_def mult.right_neutral mult_left_mono not_less)
      then have "\<not> 1 < c \<or> \<not> 1 \<le> c"
        by linarith }
    moreover
    { have "\<not> 0 \<le> r / c \<Longrightarrow> \<not> 1 \<le> c"
          using \<open>0 < r\<close> by force
      then have "1 < c \<Longrightarrow> \<not> 1 \<le> c"
        using rst \<open>0 < r\<close> that
        by (metis div_by_1 frac_less2 less_le_trans mult.commute not_le order_refl pos_divide_le_eq zero_less_one) }
    ultimately show ?thesis
      by (metis (no_types) linear not_less)
  qed
  have ugeq: "u * g z = g (u * z)" if nou: "norm u = 1" and z: "z \<in> ball 0 r" for u z
  proof -
    have [simp]: "u \<noteq> 0" using that by auto
    have hol1: "(\<lambda>a. f (u * g a) / u) holomorphic_on ball 0 r"
      apply (rule holomorphic_intros)
      apply (rule holomorphic_on_compose_gen [OF _ holf, unfolded o_def])
      apply (rule holomorphic_intros holg)+
      using nou ballg
      apply (auto simp: dist_norm norm_mult holomorphic_on_const)
      done
    have cdf: "f field_differentiable at 0"
      using \<open>0 < r\<close> holf holomorphic_on_imp_differentiable_at by auto
    have cdg: "g field_differentiable at 0"
      using \<open>0 < r\<close> holg holomorphic_on_imp_differentiable_at by auto
    have cd_fug: "(\<lambda>a. f (u * g a)) field_differentiable at 0"
      apply (rule field_differentiable_compose [where g=f and f = "\<lambda>a. (u * g a)", unfolded o_def])
      apply (rule derivative_intros)+
      using cdf cdg
      apply auto
      done
    have "deriv g 0 = deriv g (f 0)"
      by simp
    then have "deriv f 0 * deriv g 0 = 1"
      by (metis open_ball \<open>0 < r\<close> ballf centre_in_ball deriv_left_inverse gf holf holg image_subsetI)
    then have equ: "deriv f 0 * deriv (\<lambda>a. u * g a) 0 = u"
      by (simp add: cdg deriv_cmult)
    have der1: "deriv (\<lambda>a. f (u * g a) / u) 0 = 1"
      apply (simp add: field_class.field_divide_inverse deriv_cmult_right [OF cd_fug])
      apply (subst complex_derivative_chain [where g=f and f = "\<lambda>a. (u * g a)", unfolded o_def])
      apply (rule derivative_intros cdf cdg | simp add: equ)+
      done
    have fugeq: "\<And>w. w \<in> ball 0 r \<Longrightarrow> f (u * g w) / u = w"
      apply (rule first_Cartan_dim_1 [OF hol1, where z=0])
      apply (simp_all add: \<open>0 < r\<close>)
      apply (auto simp: der1)
      using nou ballf ballg
      apply (simp add: dist_norm norm_mult norm_divide)
      done
    have "f(u * g z) = u * z"
      by (metis \<open>u \<noteq> 0\<close> fugeq nonzero_mult_div_cancel_left z times_divide_eq_right)
    also have "... = f (g (u * z))"
      by (metis (no_types, lifting) fg mem_ball_0 mult_cancel_right2 norm_mult nou z)
    finally have "f(u * g z) = f (g (u * z))" .
    then have "g (f (u * g z)) = g (f (g (u * z)))"
      by simp
    then show ?thesis
      apply (subst (asm) gf)
      apply (simp add: dist_norm norm_mult nou)
      using ballg mem_ball_0 z apply blast
      apply (subst (asm) gf)
      apply (simp add: dist_norm norm_mult nou)
      apply (metis ballg mem_ball_0 mult.left_neutral norm_mult nou z, simp)
      done
  qed
  obtain c where c: "\<And>z. z \<in> ball 0 r \<Longrightarrow> g z = c * z"
    apply (rule exE [OF Cartan_is_linear [OF holg]])
    apply (simp_all add: \<open>0 < r\<close> ugeq)
    apply (auto simp: dist_norm norm_mult)
    done
  have gr2: "g (f (r/2)) = c * f(r/2)"
    apply (rule c) using \<open>0 < r\<close> ballf mem_ball_0 by force
  then have "norm c > 0"
    using \<open>0 < r\<close>
    by simp (metis \<open>f 0 = 0\<close> c dist_commute fg mem_ball mult_zero_left perfect_choose_dist)
  then have [simp]: "c \<noteq> 0" by auto
  have xless: "x < r * cmod c" if "0 \<le> x" "x < r" for x
  proof -
    have "x = norm (g (f (of_real x)))"
    proof -
      have "r > cmod (of_real x)"
        by (simp add: that)
      then have "complex_of_real x \<in> ball 0 r"
        using mem_ball_0 by blast
      then show ?thesis
        using gf \<open>0 \<le> x\<close> by force
    qed
    then show ?thesis
      apply (rule ssubst)
      apply (subst c)
      apply (rule ballf)
      using ballf [of x] that
      apply (auto simp: norm_mult dist_0_norm)
      done
  qed
  have 11: "1 / norm c \<le> 1"
    apply (rule c_le_1)
    using xless apply (auto simp: divide_simps)
    done
  have "\<lbrakk>0 \<le> x; x < r\<rbrakk> \<Longrightarrow> cmod c * x < r" for x
    using c [of x] ballg [of x] by (auto simp: norm_mult dist_0_norm)
    then have "norm c \<le> 1"
    by (force intro: c_le_1)
  moreover have "1 \<le> norm c"
    using 11 by simp
  ultimately have "norm c = 1"  by (rule antisym)
  with complex_norm_eq_1_exp c show ?thesis
    by metis
qed

end
