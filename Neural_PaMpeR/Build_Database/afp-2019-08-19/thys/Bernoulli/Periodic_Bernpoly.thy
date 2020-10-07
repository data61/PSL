(*  
  File:        Periodic_Bernpoly.thy
  Author:      Manuel Eberl <eberlm@in.tum.de> 

  Definition of the periodic Bernoulli polynomials as required for the Euler-Maclaurin 
  summation formula and Stirling's formula for the lnGamma function.
*)
section \<open>Periodic Bernoulli polynomials\<close>

theory Periodic_Bernpoly
imports 
  Bernoulli
  "HOL-Library.Periodic_Fun"
begin
  
text \<open>
  Given the $n$-th Bernoulli polynomial $B_n(x)$, one can define the periodic function 
  $P_n(x) = B_n(x - \lfloor x\rfloor)$, which shares many of the interesting properties of 
  the Bernoulli polynomials. In particular, all $P_n(x)$ with $n\neq 1$ are continuous and 
  if $n \geq 3$, they are continuously differentiable with $P_n'(x) = n P_{n-1}(x)$ just 
  like the Bernoully polynomials themselves.

  These functions occur e.\,g.\ in the Euler--MacLaurin summation formula and Stirling's
  approximation for the logarithmic Gamma function.
\<close>

(* TODO Move to distribution *)
lemma frac_0 [simp]: "frac 0 = 0" by (simp add: frac_def)  

lemma frac_eq_id: "x \<in> {0..<1} \<Longrightarrow> frac x = x"
  by (simp add: frac_eq)
    
lemma periodic_continuous_onI:
  fixes f :: "real \<Rightarrow> real"
  assumes periodic: "\<And>x. f (x + p) = f x" "p > 0"
  assumes cont: "continuous_on {a..a+p} f"
  shows   "continuous_on UNIV f"
unfolding continuous_on_def
proof safe
  fix x :: real
  interpret f: periodic_fun_simple f p by unfold_locales (rule periodic)

  have "continuous_on {a-p..a} (f \<circ> (\<lambda>x. x + p))"
    by (intro continuous_on_compose) (auto intro!: continuous_intros cont)
  also have "f \<circ> (\<lambda>x. x + p) = f" by (rule ext) (simp add: f.periodic_simps)
  finally have "continuous_on ({a-p..a} \<union> {a..a+p}) f" using cont
    by (intro continuous_on_closed_Un) simp_all
  also have "{a-p..a} \<union> {a..a+p} = {a-p..a+p}" by auto
  finally have "continuous_on {a-p..a+p} f" .
  hence cont: "continuous_on {a-p<..<a+p} f" by (rule continuous_on_subset) auto

  define n :: int where "n = \<lceil>(a - x) / p\<rceil>"
  have "(a - x) / p \<le> n" "n < (a - x) / p + 1" unfolding n_def by linarith+
  with \<open>p > 0\<close> have "x + n * p \<in> {a-p<..<a + p}" by (simp add: field_simps)
  with cont have "isCont f (x + n * p)"
    by (subst (asm) continuous_on_eq_continuous_at) auto
  hence *: "f \<midarrow>x+n*p\<rightarrow> f (x+n*p)" by (simp add: isCont_def f.periodic_simps)
  have "(\<lambda>x. f (x + n*p)) \<midarrow>x\<rightarrow> f (x+n*p)"
    by (intro tendsto_compose[OF *] tendsto_intros)
  thus "f \<midarrow>x\<rightarrow> f x" by (simp add: f.periodic_simps)
qed
  
lemma has_field_derivative_at_within_union:
  assumes "(f has_field_derivative D) (at x within A)" 
          "(f has_field_derivative D) (at x within B)"
  shows   "(f has_field_derivative D) (at x within (A \<union> B))"
proof -
  from assms have "((\<lambda>y. (f y - f x) / (y - x)) \<longlongrightarrow> D) (sup (at x within A) (at x within B))"
    unfolding has_field_derivative_iff by (rule filterlim_sup)
  also have "sup (at x within A) (at x within B) = at x within (A \<union> B)" 
    using at_within_union ..
  finally show ?thesis unfolding has_field_derivative_iff .
qed 
  
lemma has_field_derivative_cong_ev':
  assumes "x = y"
    and *: "eventually (\<lambda>x. x \<in> s \<longrightarrow> f x = g x) (nhds x)"
    and "u = v" "s = t" "f x = g y"
  shows "(f has_field_derivative u) (at x within s) = (g has_field_derivative v) (at y within t)"
proof -
  have "(f has_field_derivative u) (at x within (s \<union> {x})) =
            (g has_field_derivative v) (at y within (s \<union> {x}))" using assms
    by (intro has_field_derivative_cong_ev) (auto elim!: eventually_mono)
  also from assms have "at x within (s \<union> {x}) = at x within s" by (simp add: at_within_def)
  also from assms have "at y within (s \<union> {x}) = at y within t" by (simp add: at_within_def)
  finally show ?thesis .
qed


interpretation frac: periodic_fun_simple' frac
  by unfold_locales (simp add: frac_def)

lemma tendsto_frac_at_right_0: 
  "(frac \<longlongrightarrow> 0) (at_right (0 :: 'a :: {floor_ceiling,order_topology}))"
proof -
  have *: "eventually (\<lambda>x. x = frac x) (at_right (0::'a))"
    by (intro eventually_at_rightI[of 0 1]) (simp_all add: frac_eq eq_commute[of _ "frac x" for x])
  moreover have **: "((\<lambda>x::'a. x) \<longlongrightarrow> 0) (at_right 0)"
    by (rule tendsto_ident_at)
  ultimately show ?thesis by (rule Lim_transform_eventually)
qed

lemma tendsto_frac_at_left_1: 
  "(frac \<longlongrightarrow> 1) (at_left (1 :: 'a :: {floor_ceiling,order_topology}))"
proof -
  have *: "eventually (\<lambda>x. x = frac x) (at_left (1::'a))"
    by (intro eventually_at_leftI[of 0]) (simp_all add: frac_eq eq_commute[of _ "frac x" for x])
  moreover have **: "((\<lambda>x::'a. x) \<longlongrightarrow> 1) (at_left 1)"
    by (rule tendsto_ident_at)
  ultimately show ?thesis by (rule Lim_transform_eventually)
qed

lemma continuous_on_frac [THEN continuous_on_subset, continuous_intros]: 
  "continuous_on {0::'a::{floor_ceiling,order_topology}..<1} frac"
proof (subst continuous_on_cong[OF refl])
  fix x :: 'a assume "x \<in> {0..<1}"
  thus "frac x = x" by (simp add: frac_eq)
qed (auto intro: continuous_intros)

lemma isCont_frac [continuous_intros]: 
  assumes "(x :: 'a :: {floor_ceiling,order_topology,t2_space}) \<in> {0<..<1}"
  shows   "isCont frac x"
proof -
  have "continuous_on {0<..<(1::'a)} frac" by (rule continuous_on_frac) auto
  with assms show ?thesis
    by (subst (asm) continuous_on_eq_continuous_at) auto
qed  
  
lemma has_field_derivative_frac:
  assumes "(x::real) \<notin> \<int>"
  shows   "(frac has_field_derivative 1) (at x)"
proof -
  have "((\<lambda>t. t - of_int \<lfloor>x\<rfloor>) has_field_derivative 1) (at x)" 
    by (auto intro!: derivative_eq_intros)
  also have "?this \<longleftrightarrow> ?thesis"
    using eventually_floor_eq[OF filterlim_ident assms]
    by (intro DERIV_cong_ev refl) (auto elim!: eventually_mono simp: frac_def)
  finally show ?thesis .
qed
  
lemmas has_field_derivative_frac' [derivative_intros] = 
  DERIV_chain'[OF _ has_field_derivative_frac]
    
lemma continuous_on_compose_fracI:
  fixes f :: "real \<Rightarrow> real"
  assumes cont1: "continuous_on {0..1} f"
  assumes cont2: "f 0 = f 1"
  shows   "continuous_on UNIV (\<lambda>x. f (frac x))"
proof (rule periodic_continuous_onI)
  have cont: "continuous_on {0..1} (\<lambda>x. f (frac x))"
    unfolding continuous_on_def
  proof safe
    fix x :: real assume x: "x \<in> {0..1}"
    show "((\<lambda>x. f (frac x)) \<longlongrightarrow> f (frac x)) (at x within {0..1})"
    proof (cases "x = 1")
      case False
      with x have [simp]: "frac x = x" by (simp add: frac_eq)
      from x False have "eventually (\<lambda>x. x \<in> {..<1}) (nhds x)"
        by (intro eventually_nhds_in_open) auto
      hence "eventually (\<lambda>x. frac x = x) (at x within {0..1})"
        by (auto simp: eventually_at_filter frac_eq elim!: eventually_mono)
      hence "eventually (\<lambda>x. f x = f (frac x)) (at x within {0..1})"
        by eventually_elim simp
      moreover from cont1 x have "(f \<longlongrightarrow> f (frac x)) (at x within {0..1})"
        by (simp add: continuous_on_def)
      ultimately show "((\<lambda>x. f (frac x)) \<longlongrightarrow> f (frac x)) (at x within {0..1})"
        by (rule Lim_transform_eventually)
    next
      case True
      from cont1 have **: "(f \<longlongrightarrow> f 1) (at 1 within {0..1})" by (simp add: continuous_on_def)
      moreover have *: "filterlim frac (at 1 within {0..1}) (at 1 within {0..1})"
      proof (subst filterlim_cong[OF refl refl])
        show "eventually (\<lambda>x. frac x = x) (at 1 within {0..1})"
          by (auto simp: eventually_at_filter frac_eq)
      qed (simp add: filterlim_ident)
      ultimately have "((\<lambda>x. f (frac x)) \<longlongrightarrow> f 1) (at 1 within {0..1})"
        by (rule filterlim_compose)
      thus ?thesis by (simp add: True cont2 frac_def)
    qed
  qed
  thus "continuous_on {0..0+1} (\<lambda>x. f (frac x))" by simp
qed (simp_all add: frac.periodic_simps)
(* END TODO *)


definition pbernpoly :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "pbernpoly n x = bernpoly n (frac x)"

lemma pbernpoly_0 [simp]: "pbernpoly n 0 = bernoulli n"
  by (simp add: pbernpoly_def)  

lemma pbernpoly_eq_bernpoly: "x \<in> {0..<1} \<Longrightarrow> pbernpoly n x = bernpoly n x"
  by (simp add: pbernpoly_def frac_eq_id)

interpretation pbernpoly: periodic_fun_simple' "pbernpoly n"
  by unfold_locales (simp add: pbernpoly_def frac.periodic_simps)

lemma continuous_on_pbernpoly [continuous_intros]:
  assumes "n \<noteq> 1"
  shows   "continuous_on A (pbernpoly n)"
proof (cases "n = 0")
  case True
  thus ?thesis by (auto intro: continuous_intros simp: pbernpoly_def bernpoly_def)
next
  case False
  with assms have n: "n \<ge> 2" by auto
  have "continuous_on UNIV (pbernpoly n)" unfolding pbernpoly_def [abs_def]
    by (rule continuous_on_compose_fracI)
       (insert n, auto intro!: continuous_intros simp: bernpoly_0 bernpoly_1)
  thus ?thesis by (rule continuous_on_subset) simp_all
qed

lemma continuous_on_pbernpoly' [continuous_intros]:
  assumes "n \<noteq> 1" "continuous_on A f"
  shows   "continuous_on A (\<lambda>x. pbernpoly n (f x))"
  using continuous_on_compose[OF assms(2) continuous_on_pbernpoly[OF assms(1)]]
  by (simp add: o_def)

lemma isCont_pbernpoly [continuous_intros]: "n \<noteq> 1 \<Longrightarrow> isCont (pbernpoly n) x"
  using continuous_on_pbernpoly[of n UNIV] by (simp add: continuous_on_eq_continuous_at)   

lemma has_field_derivative_pbernpoly_Suc:
  assumes "n \<ge> 2 \<or> x \<notin> \<int>"
  shows   "(pbernpoly (Suc n) has_field_derivative real (Suc n) * pbernpoly n x) (at x)"
using assms
proof (cases "x \<in> \<int>")
  assume "x \<notin> \<int>"
  with assms show ?thesis unfolding pbernpoly_def 
    by (auto intro!: derivative_eq_intros simp del: of_nat_Suc)
next
  case True
  from True obtain k where k: "x = of_int k" by (auto elim: Ints_cases)
  have "(pbernpoly (Suc n) has_field_derivative real (Suc n) * pbernpoly n x) 
          (at x within ({..<x} \<union> {x<..}))"
  proof (rule has_field_derivative_at_within_union)
    have "((\<lambda>x. bernpoly (Suc n) (x - of_int (k-1))) has_field_derivative
                  real (Suc n) * bernpoly n (x - of_int (k-1))) (at_left x)"
      by (auto intro!: derivative_eq_intros)
    also have "?this \<longleftrightarrow> (pbernpoly (Suc n) has_field_derivative 
                            real (Suc n) * pbernpoly n x) (at_left x)" using assms
    proof (intro has_field_derivative_cong_ev' refl)
      have "\<forall>\<^sub>F y in nhds x. y \<in> {x - 1<..<x + 1}" by (intro eventually_nhds_in_open) simp_all
      thus "\<forall>\<^sub>F t in nhds x. t \<in> {..<x} \<longrightarrow> bernpoly (Suc n) (t - real_of_int (k - 1)) =
                pbernpoly (Suc n) t"
      proof (elim eventually_mono, safe)
        fix t assume "t < x" "t \<in> {x-1<..<x+1}"
        hence "frac t = t - real_of_int (k - 1)" using k
          by (subst frac_unique_iff) auto
        thus "bernpoly (Suc n) (t - real_of_int (k - 1)) = pbernpoly (Suc n) t" 
          by (simp add: pbernpoly_def)
      qed
    qed (insert k, auto simp: pbernpoly_def bernpoly_1)
    finally show "(pbernpoly (Suc n) has_real_derivative 
                      real (Suc n) * pbernpoly n x) (at_left x)" .
  next
    have "((\<lambda>x. bernpoly (Suc n) (x - of_int k)) has_field_derivative
                  real (Suc n) * bernpoly n (x - of_int k)) (at_right x)"
      by (auto intro!: derivative_eq_intros)
    also have "?this \<longleftrightarrow> (pbernpoly (Suc n) has_field_derivative 
                            real (Suc n) * pbernpoly n x) (at_right x)" using assms
    proof (intro has_field_derivative_cong_ev' refl)
      have "\<forall>\<^sub>F y in nhds x. y \<in> {x - 1<..<x + 1}" by (intro eventually_nhds_in_open) simp_all
      thus "\<forall>\<^sub>F t in nhds x. t \<in> {x<..} \<longrightarrow> bernpoly (Suc n) (t - real_of_int k) =
                pbernpoly (Suc n) t"
      proof (elim eventually_mono, safe)
        fix t assume "t > x" "t \<in> {x-1<..<x+1}"
        hence "frac t = t - real_of_int k" using k
          by (subst frac_unique_iff) auto
        thus "bernpoly (Suc n) (t - real_of_int k) = pbernpoly (Suc n) t" 
          by (simp add: pbernpoly_def)
      qed
    qed (insert k, auto simp: pbernpoly_def bernpoly_1)
    finally show "(pbernpoly (Suc n) has_real_derivative 
                      real (Suc n) * pbernpoly n x) (at_right x)" .    
  qed
  also have "{..<x} \<union> {x<..} = UNIV - {x}" by auto
  also have "at x within \<dots> = at x" by (simp add: at_within_def)
  finally show ?thesis .
qed

lemmas has_field_derivative_pbernpoly_Suc' =
  DERIV_chain'[OF _ has_field_derivative_pbernpoly_Suc]    

lemma bounded_pbernpoly: obtains c where "\<And>x. norm (pbernpoly n x) \<le> c"
proof -
  have "\<exists>x\<in>{0..1}. \<forall>y\<in>{0..1}. norm (bernpoly n y :: real) \<le> norm (bernpoly n x :: real)"
    by (intro continuous_attains_sup) (auto intro!: continuous_intros)
  then obtain x where x: 
    "\<And>y. y \<in> {0..1} \<Longrightarrow> norm (bernpoly n y :: real) \<le> norm (bernpoly n x :: real)" 
    by blast
  have "norm (pbernpoly n y) \<le> norm (bernpoly n x :: real)" for y
    unfolding pbernpoly_def using frac_lt_1[of y] by (intro x) simp_all
  thus ?thesis by (rule that)
qed
 
end
