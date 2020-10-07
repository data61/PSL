(* Author: Alexander Maletzky *)

section \<open>Polynomial Mappings and Univariate Polynomials\<close>

theory Univariate_PM
  imports "HOL-Computational_Algebra.Polynomial" Polynomials.MPoly_PM
begin

subsection \<open>Morphisms \<open>pm_of_poly\<close> and \<open>poly_of_pm\<close>\<close>

text \<open>Many things in this section are copied from theory \<open>Polynomials.MPoly_Type_Univariate\<close>.\<close>

lemma pm_of_poly_aux:
  "{t. (poly.coeff p (lookup t x) when t \<in> .[{x}]) \<noteq> 0} =
          Poly_Mapping.single x ` {d. poly.coeff p d \<noteq> 0}" (is "?M = _")
proof (intro subset_antisym subsetI)
  fix t
  assume "t \<in> ?M"
  hence "\<And>y. y \<noteq> x \<Longrightarrow> Poly_Mapping.lookup t y = 0" by (fastforce simp: PPs_def in_keys_iff)
  hence "t = Poly_Mapping.single x (lookup t x)"
    using poly_mapping_eqI by (metis (full_types) lookup_single_eq lookup_single_not_eq)
  then show "t \<in> (Poly_Mapping.single x) ` {d. poly.coeff p d \<noteq> 0}" using \<open>t \<in> ?M\<close> by auto
qed (auto split: if_splits simp: PPs_def)

lift_definition pm_of_poly :: "'x \<Rightarrow> 'a poly \<Rightarrow> ('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_monoid_add"
  is "\<lambda>x p t. (poly.coeff p (lookup t x)) when t \<in> .[{x}]"
proof -
  fix x::'x and p::"'a poly"
  show "finite {t. (poly.coeff p (lookup t x) when t \<in> .[{x}]) \<noteq> 0}" unfolding pm_of_poly_aux
    using finite_surj[OF MOST_coeff_eq_0[unfolded eventually_cofinite]] by blast
qed

definition poly_of_pm :: "'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> 'a::comm_monoid_add poly"
  where "poly_of_pm x p = Abs_poly (\<lambda>d. lookup p (Poly_Mapping.single x d))"

lemma lookup_pm_of_poly_single [simp]:
  "lookup (pm_of_poly x p) (Poly_Mapping.single x d) = poly.coeff p d"
  by (simp add: pm_of_poly.rep_eq PPs_closed_single)

lemma keys_pm_of_poly: "keys (pm_of_poly x p) = Poly_Mapping.single x ` {d. poly.coeff p d \<noteq> 0}"
proof -
  have "keys (pm_of_poly x p) = {t. (poly.coeff p (lookup t x) when t \<in> .[{x}]) \<noteq> 0}"
    by (rule set_eqI) (simp add: pm_of_poly.rep_eq flip: lookup_not_eq_zero_eq_in_keys)
  also have "\<dots> = Poly_Mapping.single x ` {d. poly.coeff p d \<noteq> 0}" by (fact pm_of_poly_aux)
  finally show ?thesis .
qed

lemma coeff_poly_of_pm [simp]: "poly.coeff (poly_of_pm x p) k = lookup p (Poly_Mapping.single x k)"
proof -
  have 0:"Poly_Mapping.single x ` {d. lookup p (Poly_Mapping.single x d) \<noteq> 0} \<subseteq> {d. lookup p d \<noteq> 0}"
    by auto
  have "\<forall>\<^sub>\<infinity> k. lookup p (Poly_Mapping.single x k) = 0" unfolding coeff_def eventually_cofinite
    using finite_imageD[OF finite_subset[OF 0 Poly_Mapping.finite_lookup]] inj_single
    by (metis inj_eq inj_onI)
  then show ?thesis by (simp add: poly_of_pm_def Abs_poly_inverse)
qed

lemma pm_of_poly_of_pm:
  assumes "p \<in> P[{x}]"
  shows "pm_of_poly x (poly_of_pm x p) = p"
proof (rule poly_mapping_eqI)
  fix t
  from assms have "keys p \<subseteq> .[{x}]" by (rule PolysD)
  show "lookup (pm_of_poly x (poly_of_pm x p)) t = lookup p t"
  proof (simp add: pm_of_poly.rep_eq when_def, intro conjI impI)
    assume "t \<in> .[{x}]"
    hence "Poly_Mapping.single x (lookup t x) = t"
      by (simp add: PPsD keys_subset_singleton_imp_monomial)
    thus "lookup p (Poly_Mapping.single x (lookup t x)) = lookup p t" by simp
  next
    assume "t \<notin> .[{x}]"
    with assms PolysD have "t \<notin> keys p" by blast
    thus "lookup p t = 0" by (simp add: in_keys_iff)
  qed
qed

lemma poly_of_pm_of_poly [simp]: "poly_of_pm x (pm_of_poly x p) = p"
  by (simp add: poly_of_pm_def coeff_inverse)

lemma pm_of_poly_in_Polys: "pm_of_poly x p \<in> P[{x}]"
  by (auto simp: keys_pm_of_poly PPs_closed_single intro!: PolysI)

lemma pm_of_poly_zero [simp]: "pm_of_poly x 0 = 0"
  by (rule poly_mapping_eqI) (simp add: pm_of_poly.rep_eq)

lemma pm_of_poly_eq_zero_iff [iff]: "pm_of_poly x p = 0 \<longleftrightarrow> p = 0"
  by (metis poly_of_pm_of_poly pm_of_poly_zero)

lemma pm_of_poly_monom: "pm_of_poly x (Polynomial.monom c d) = monomial c (Poly_Mapping.single x d)"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup (pm_of_poly x (Polynomial.monom c d)) t = lookup (monomial c (monomial d x)) t"
  proof (cases "t \<in> .[{x}]")
    case True
    thus ?thesis
      by (auto simp: pm_of_poly.rep_eq lookup_single PPs_singleton when_def dest: monomial_inj)
  next
    case False
    thus ?thesis by (auto simp add: pm_of_poly.rep_eq lookup_single PPs_singleton)
  qed
qed

lemma pm_of_poly_plus: "pm_of_poly x (p + q) = pm_of_poly x p + pm_of_poly x q"
  by (rule poly_mapping_eqI) (simp add: pm_of_poly.rep_eq lookup_add when_add_distrib)

lemma pm_of_poly_uminus [simp]: "pm_of_poly x (- p) = - pm_of_poly x p"
  by (rule poly_mapping_eqI) (simp add: pm_of_poly.rep_eq when_distrib)

lemma pm_of_poly_minus: "pm_of_poly x (p - q) = pm_of_poly x p - pm_of_poly x q"
  by (rule poly_mapping_eqI) (simp add: pm_of_poly.rep_eq lookup_minus when_diff_distrib)

lemma pm_of_poly_one [simp]: "pm_of_poly x 1 = 1"
  by (simp add: pm_of_poly_monom flip: single_one monom_eq_1)

lemma pm_of_poly_pCons:
  "pm_of_poly x (pCons c p) =
      monomial c 0 + punit.monom_mult (1::_::monoid_mult) (Poly_Mapping.single x 1) (pm_of_poly x p)"
    (is "?l = ?r")
proof (rule poly_mapping_eqI)
  fix t
  let ?x = "Poly_Mapping.single x (Suc 0)"
  show "lookup ?l t = lookup ?r t"
  proof (cases "?x adds t")
    case True
    have 1: "t - ?x \<in> .[{x}] \<longleftrightarrow> t \<in> .[{x}]"
    proof
      assume "t - ?x \<in> .[{x}]"
      moreover have "?x \<in> .[{x}]" by (rule PPs_closed_single) simp
      ultimately have "(t - ?x) + ?x \<in> .[{x}]" by (rule PPs_closed_plus)
      with True show "t \<in> .[{x}]" by (simp add: adds_minus)
    qed (rule PPs_closed_minus)
    from True have "0 < lookup t x"
      by (metis adds_minus lookup_add lookup_single_eq n_not_Suc_n neq0_conv plus_eq_zero_2)
    moreover from this have "t \<noteq> 0" by auto
    ultimately show ?thesis using True
      by (simp add: pm_of_poly.rep_eq lookup_add lookup_single punit.lookup_monom_mult 1 coeff_pCons
                    lookup_minus split: nat.split)
  next
    case False
    moreover have "t \<in> .[{x}] \<longleftrightarrow> t = 0"
    proof
      assume "t \<in> .[{x}]"
      hence "keys t \<subseteq> {x}" by (rule PPsD)
      show "t = 0"
      proof (rule ccontr)
        assume "t \<noteq> 0"
        hence "keys t \<noteq> {}" by simp
        then obtain y where "y \<in> keys t" by blast
        with \<open>keys t \<subseteq> {x}\<close> have "y \<in> {x}" ..
        hence "y = x" by simp
        with \<open>y \<in> keys t\<close> have "Suc 0 \<le> lookup t x" by (simp add: in_keys_iff)
        hence "?x adds t"
          by (metis adds_poly_mappingI le0 le_funI lookup_single_eq lookup_single_not_eq)
        with False show False ..
      qed
    qed (simp only: zero_in_PPs)
    ultimately show ?thesis
      by (simp add: pm_of_poly.rep_eq lookup_add lookup_single punit.lookup_monom_mult when_def)
  qed
qed

lemma pm_of_poly_smult [simp]: "pm_of_poly x (Polynomial.smult c p) = c \<cdot> pm_of_poly x p"
  by (rule poly_mapping_eqI) (simp add: pm_of_poly.rep_eq when_distrib)

lemma pm_of_poly_times: "pm_of_poly x (p * q) = pm_of_poly x p * pm_of_poly x (q::_::ring_1 poly)"
proof (induct p)
  case 0
  show ?case by simp
next
  case (pCons a p)
  show ?case
    by (simp add: pm_of_poly_plus pm_of_poly_pCons map_scale_eq_times pCons(2) algebra_simps
             flip: times_monomial_left)
qed

lemma pm_of_poly_sum: "pm_of_poly x (sum f I) = (\<Sum>i\<in>I. pm_of_poly x (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: pm_of_poly_plus)

lemma pm_of_poly_prod: "pm_of_poly x (prod f I) = (\<Prod>i\<in>I. pm_of_poly x (f i :: _::ring_1 poly))"
  by (induct I rule: infinite_finite_induct) (simp_all add: pm_of_poly_times)

lemma pm_of_poly_power [simp]: "pm_of_poly x (p ^ m) = pm_of_poly x (p::_::ring_1 poly) ^ m"
  by (induct m) (simp_all add: pm_of_poly_times)

lemma poly_of_pm_zero [simp]: "poly_of_pm x 0 = 0"
  by (metis poly_of_pm_of_poly pm_of_poly_zero)

lemma poly_of_pm_eq_zero_iff: "poly_of_pm x p = 0 \<longleftrightarrow> keys p \<inter> .[{x}] = {}"
proof
  assume eq: "poly_of_pm x p = 0"
  {
    fix t
    assume "t \<in> .[{x}]"
    then obtain d where "t = Poly_Mapping.single x d" unfolding PPs_singleton ..
    moreover assume "t \<in> keys p"
    ultimately have "0 \<noteq> lookup p (Poly_Mapping.single x d)" by (simp add: in_keys_iff)
    also have "lookup p (Poly_Mapping.single x d) = Polynomial.coeff (poly_of_pm x p) d"
      by simp
    also have "\<dots> = 0" by (simp add: eq)
    finally have False by blast
  }
  thus "keys p \<inter> .[{x}] = {}" by blast
next
  assume *: "keys p \<inter> .[{x}] = {}"
  {
    fix d
    have "Poly_Mapping.single x d \<in> .[{x}]" (is "?x \<in> _") by (rule PPs_closed_single) simp
    with * have "?x \<notin> keys p" by blast
    hence "Polynomial.coeff (poly_of_pm x p) d = 0" by (simp add: in_keys_iff)
  }
  thus "poly_of_pm x p = 0" using leading_coeff_0_iff by blast
qed

lemma poly_of_pm_monomial:
  "poly_of_pm x (monomial c t) = (Polynomial.monom c (lookup t x) when t \<in> .[{x}])"
proof (cases "t \<in> .[{x}]")
  case True
  moreover from this obtain d where "t = Poly_Mapping.single x d"
    by (metis PPsD keys_subset_singleton_imp_monomial)
  ultimately show ?thesis unfolding Polynomial.monom.abs_eq coeff_poly_of_pm
    by (auto simp: poly_of_pm_def lookup_single when_def
        dest!: monomial_inj intro!: arg_cong[where f=Abs_poly])
next
  case False
  moreover from this have "t \<noteq> monomial d x" for d by (auto simp: PPs_closed_single)
  ultimately show ?thesis unfolding Polynomial.monom.abs_eq coeff_poly_of_pm
    by (auto simp: poly_of_pm_def lookup_single when_def zero_poly.abs_eq)
qed

lemma poly_of_pm_plus: "poly_of_pm x (p + q) = poly_of_pm x p + poly_of_pm x q"
  unfolding Polynomial.plus_poly.abs_eq coeff_poly_of_pm by (simp add: poly_of_pm_def lookup_add)

lemma poly_of_pm_uminus [simp]: "poly_of_pm x (- p) = - poly_of_pm x p"
  unfolding Polynomial.uminus_poly.abs_eq coeff_poly_of_pm by (simp add: poly_of_pm_def)

lemma poly_of_pm_minus: "poly_of_pm x (p - q) = poly_of_pm x p - poly_of_pm x q"
  unfolding Polynomial.minus_poly.abs_eq coeff_poly_of_pm by (simp add: poly_of_pm_def lookup_minus)

lemma poly_of_pm_one [simp]: "poly_of_pm x 1 = 1"
  by (simp add: poly_of_pm_monomial zero_in_PPs flip: single_one monom_eq_1)

lemma poly_of_pm_times:
  "poly_of_pm x (p * q) = poly_of_pm x p * poly_of_pm x (q::_ \<Rightarrow>\<^sub>0 'a::comm_semiring_1)"
proof -
  have eq: "poly_of_pm x (monomial c t * q) = poly_of_pm x (monomial c t) * poly_of_pm x q"
    if "c \<noteq> 0" for c t
  proof (cases "t \<in> .[{x}]")
    case True
    then obtain d where t: "t = Poly_Mapping.single x d" unfolding PPs_singleton ..
    have "poly_of_pm x (monomial c t) * poly_of_pm x q = Polynomial.monom c (lookup t x) * poly_of_pm x q"
      by (simp add: True poly_of_pm_monomial)
    also have "\<dots> = poly_of_pm x (monomial c t * q)" unfolding t
    proof (induct d)
      case 0
      have "Polynomial.smult c (poly_of_pm x q) = poly_of_pm x (c \<cdot> q)"
        unfolding Polynomial.smult.abs_eq coeff_poly_of_pm by (simp add: poly_of_pm_def)
      with that show ?case by (simp add: Polynomial.times_poly_def flip: map_scale_eq_times)
    next
      case (Suc d)
      have 1: "Poly_Mapping.single x a adds Poly_Mapping.single x b \<longleftrightarrow> a \<le> b" for a b :: nat
        by (metis adds_def deg_pm_mono deg_pm_single le_Suc_ex single_add)
      have 2: "poly_of_pm x (punit.monom_mult 1 (Poly_Mapping.single x 1) r) = pCons 0 (poly_of_pm x r)"
        for r :: "_ \<Rightarrow>\<^sub>0 'a" unfolding poly.coeff_inject[symmetric]
        by (rule ext) (simp add: coeff_pCons punit.lookup_monom_mult adds_zero monomial_0_iff 1
                            flip: single_diff split: nat.split)
      from Suc that have "Polynomial.monom c (lookup (monomial (Suc d) x) x) * poly_of_pm x q =
                          poly_of_pm x (punit.monom_mult 1 (Poly_Mapping.single x 1)
                                            ((monomial c (monomial d x)) * q))"
        by (simp add: Polynomial.times_poly_def 2 del: One_nat_def)
      also have "\<dots> = poly_of_pm x (monomial c (Poly_Mapping.single x (Suc d)) * q)"
        by (simp add: ac_simps times_monomial_monomial flip: single_add times_monomial_left)
      finally show ?case .
    qed
    finally show ?thesis by (rule sym)
  next
    case False
    {
      fix s
      assume "s \<in> keys (monomial c t * q)"
      also have "\<dots> \<subseteq> (+) t ` keys q" unfolding times_monomial_left
        by (fact punit.keys_monom_mult_subset[simplified])
      finally obtain u where s: "s = t + u" ..
      assume "s \<in> .[{x}]"
      hence "s - u \<in> .[{x}]" by (rule PPs_closed_minus)
      hence "t \<in> .[{x}]" by (simp add: s)
      with False have False ..
    }
    hence "poly_of_pm x (monomial c t * q) = 0" by (auto simp: poly_of_pm_eq_zero_iff)
    with False show ?thesis by (simp add: poly_of_pm_monomial)
  qed
  show ?thesis
    by (induct p rule: poly_mapping_plus_induct) (simp_all add: poly_of_pm_plus eq distrib_right)
qed

lemma poly_of_pm_sum: "poly_of_pm x (sum f I) = (\<Sum>i\<in>I. poly_of_pm x (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: poly_of_pm_plus)

lemma poly_of_pm_prod: "poly_of_pm x (prod f I) = (\<Prod>i\<in>I. poly_of_pm x (f i))"
  by (induct I rule: infinite_finite_induct) (simp_all add: poly_of_pm_times)

lemma poly_of_pm_power [simp]: "poly_of_pm x (p ^ m) = poly_of_pm x p ^ m"
  by (induct m) (simp_all add: poly_of_pm_times)

subsection \<open>Evaluating Polynomials\<close>

lemma poly_eq_poly_eval: "poly (poly_of_pm x p) a = poly_eval (\<lambda>y. a when y = x) p"
proof (induction p rule: poly_mapping_plus_induct)
  case 1
  show ?case by simp
next
  case (2 p c t)
  show ?case
  proof (cases "t \<in> .[{x}]")
    case True
    have "poly_eval (\<lambda>y. a when y = x) (monomial c t) = c * (\<Prod>y\<in>keys t. (a when y = x) ^ lookup t y)"
      by (simp only: poly_eval_monomial)
    also from True have "(\<Prod>y\<in>keys t. (a when y = x) ^ lookup t y) = (\<Prod>y\<in>{x}. (a when y = x) ^ lookup t y)"
      by (intro prod.mono_neutral_left ballI) (auto simp: in_keys_iff dest: PPsD)
    also have "\<dots> = a ^ lookup t x" by simp
    finally show ?thesis
      by (simp add: poly_of_pm_plus poly_of_pm_monomial poly_monom poly_eval_plus True 2(3))
  next
    case False
    have "poly_eval (\<lambda>y. a when y = x) (monomial c t) = c * (\<Prod>y\<in>keys t. (a when y = x) ^ lookup t y)"
      by (simp only: poly_eval_monomial)
    also from finite_keys have "(\<Prod>y\<in>keys t. (a when y = x) ^ lookup t y) = 0"
    proof (rule prod_zero)
      from False obtain y where "y \<in> keys t" and "y \<noteq> x" by (auto simp: PPs_def)
      from this(1) show "\<exists>y\<in>keys t. (a when y = x) ^ lookup t y = 0"
      proof
        from \<open>y \<in> keys t\<close> have "0 < lookup t y" by (simp add: in_keys_iff)
        with \<open>y \<noteq> x\<close> show "(a when y = x) ^ lookup t y = 0" by (simp add: zero_power)
      qed
    qed
    finally show ?thesis
      by (simp add: poly_of_pm_plus poly_of_pm_monomial poly_monom poly_eval_plus False 2(3))
  qed
qed

corollary poly_eq_poly_eval':
  assumes "p \<in> P[{x}]"
  shows "poly (poly_of_pm x p) a = poly_eval (\<lambda>_. a) p"
  unfolding poly_eq_poly_eval using refl
proof (rule poly_eval_cong)
  fix y
  assume "y \<in> indets p"
  also from assms have "\<dots> \<subseteq> {x}" by (rule PolysD)
  finally show "(a when y = x) = a" by simp
qed

lemma poly_eval_eq_poly: "poly_eval a (pm_of_poly x p) = poly p (a x)"
  by (induct p)
    (simp_all add: pm_of_poly_pCons poly_eval_plus poly_eval_times poly_eval_monomial
              flip: times_monomial_left)

subsection \<open>Morphisms \<open>flat_pm_of_poly\<close> and \<open>poly_of_focus\<close>\<close>

definition flat_pm_of_poly :: "'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) poly \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::semiring_1)"
  where "flat_pm_of_poly x = flatten \<circ> pm_of_poly x"

definition poly_of_focus :: "'x \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_monoid_add) poly"
  where "poly_of_focus x = poly_of_pm x \<circ> focus {x}"

lemma flat_pm_of_poly_in_Polys:
  assumes "range (poly.coeff p) \<subseteq> P[Y]"
  shows "flat_pm_of_poly x p \<in> P[insert x Y]"
proof -
  let ?p = "pm_of_poly x p"
  from assms have "lookup ?p ` keys ?p \<subseteq> P[Y]" by (simp add: keys_pm_of_poly image_image) blast
  with pm_of_poly_in_Polys have "flatten ?p \<in> P[{x} \<union> Y]" by (rule flatten_in_Polys)
  thus ?thesis by (simp add: flat_pm_of_poly_def)
qed

corollary indets_flat_pm_of_poly_subset:
  "indets (flat_pm_of_poly x p) \<subseteq> insert x (\<Union> (indets ` range (poly.coeff p)))"
proof -
  let ?p = "pm_of_poly x p"
  let ?Y = "\<Union> (indets ` range (poly.coeff p))"
  have "range (poly.coeff p) \<subseteq> P[?Y]" by (auto intro: PolysI_alt)
  hence "flat_pm_of_poly x p \<in> P[insert x ?Y]" by (rule flat_pm_of_poly_in_Polys)
  thus ?thesis by (rule PolysD)
qed

lemma
  shows flat_pm_of_poly_zero [simp]: "flat_pm_of_poly x 0 = 0"
    and flat_pm_of_poly_monom: "flat_pm_of_poly x (Polynomial.monom c d) =
                                    punit.monom_mult 1 (Poly_Mapping.single x d) c"
    and flat_pm_of_poly_plus: "flat_pm_of_poly x (p + q) =
                                  flat_pm_of_poly x p + flat_pm_of_poly x q"
    and flat_pm_of_poly_one [simp]: "flat_pm_of_poly x 1 = 1"
    and flat_pm_of_poly_sum: "flat_pm_of_poly x (sum f I) = (\<Sum>i\<in>I. flat_pm_of_poly x (f i))"
  by (simp_all add: flat_pm_of_poly_def pm_of_poly_monom flatten_monomial pm_of_poly_plus
                    flatten_plus pm_of_poly_sum flatten_sum)

lemma
  shows flat_pm_of_poly_uminus [simp]: "flat_pm_of_poly x (- p) = - flat_pm_of_poly x p"
    and flat_pm_of_poly_minus: "flat_pm_of_poly x (p - q) =
                                  flat_pm_of_poly x p - flat_pm_of_poly x (q::_::ring poly)"
  by (simp_all add: flat_pm_of_poly_def pm_of_poly_minus flatten_minus)

lemma flat_pm_of_poly_pCons:
  "flat_pm_of_poly x (pCons c p) =
    c + punit.monom_mult 1 (Poly_Mapping.single x 1) (flat_pm_of_poly x (p::_::comm_semiring_1 poly))"
  by (simp add: flat_pm_of_poly_def pm_of_poly_pCons flatten_plus flatten_monomial flatten_times
          flip: times_monomial_left)

lemma flat_pm_of_poly_smult [simp]:
  "flat_pm_of_poly x (Polynomial.smult c p) = c * flat_pm_of_poly x (p::_::comm_semiring_1 poly)"
  by (simp add: flat_pm_of_poly_def map_scale_eq_times flatten_times flatten_monomial pm_of_poly_times)

lemma
  shows flat_pm_of_poly_times: "flat_pm_of_poly x (p * q) = flat_pm_of_poly x p * flat_pm_of_poly x q"
    and flat_pm_of_poly_prod: "flat_pm_of_poly x (prod f I) =
                                  (\<Prod>i\<in>I. flat_pm_of_poly x (f i :: _::comm_ring_1 poly))"
    and flat_pm_of_poly_power: "flat_pm_of_poly x (p ^ m) = flat_pm_of_poly x (p::_::comm_ring_1 poly) ^ m"
  by (simp_all add: flat_pm_of_poly_def flatten_times pm_of_poly_times flatten_prod pm_of_poly_prod)

lemma coeff_poly_of_focus_subset_Polys:
  assumes "p \<in> P[X]"
  shows "range (poly.coeff (poly_of_focus x p)) \<subseteq> P[X - {x}]"
proof -
  have "range (poly.coeff (poly_of_focus x p)) \<subseteq> range (lookup (focus {x} p))"
    by (auto simp: poly_of_focus_def)
  also from assms have "\<dots> \<subseteq> P[X - {x}]" by (rule focus_coeffs_subset_Polys')
  finally show ?thesis .
qed

lemma
  shows poly_of_focus_zero [simp]: "poly_of_focus x 0 = 0"
    and poly_of_focus_uminus [simp]: "poly_of_focus x (- p) = - poly_of_focus x p"
    and poly_of_focus_plus: "poly_of_focus x (p + q) = poly_of_focus x p + poly_of_focus x q"
    and poly_of_focus_minus: "poly_of_focus x (p - q) = poly_of_focus x p - poly_of_focus x q"
    and poly_of_focus_one [simp]: "poly_of_focus x 1 = 1"
    and poly_of_focus_sum: "poly_of_focus x (sum f I) = (\<Sum>i\<in>I. poly_of_focus x (f i))"
  by (simp_all add: poly_of_focus_def keys_focus poly_of_pm_plus focus_plus poly_of_pm_minus focus_minus
                    poly_of_pm_sum focus_sum)

lemma poly_of_focus_eq_zero_iff [iff]: "poly_of_focus x p = 0 \<longleftrightarrow> p = 0"
  using focus_in_Polys[of "{x}" p]
  by (auto simp: poly_of_focus_def poly_of_pm_eq_zero_iff Int_absorb2 dest: PolysD)

lemma poly_of_focus_monomial:
  "poly_of_focus x (monomial c t) = Polynomial.monom (monomial c (except t {x})) (lookup t x)"
  by (simp add: poly_of_focus_def focus_monomial poly_of_pm_monomial PPs_def keys_except lookup_except)

lemma
  shows poly_of_focus_times: "poly_of_focus x (p * q) = poly_of_focus x p * poly_of_focus x q"
    and poly_of_focus_prod: "poly_of_focus x (prod f I) =
                                  (\<Prod>i\<in>I. poly_of_focus x (f i :: _ \<Rightarrow>\<^sub>0 _::comm_semiring_1))"
    and poly_of_focus_power: "poly_of_focus x (p ^ m) = poly_of_focus x (p::_ \<Rightarrow>\<^sub>0 _::comm_semiring_1) ^ m"
  by (simp_all add: poly_of_focus_def poly_of_pm_times focus_times poly_of_pm_prod focus_prod)

lemma flat_pm_of_poly_of_focus [simp]: "flat_pm_of_poly x (poly_of_focus x p) = p"
  by (simp add: flat_pm_of_poly_def poly_of_focus_def pm_of_poly_of_pm focus_in_Polys)

lemma poly_of_focus_flat_pm_of_poly:
  assumes "range (poly.coeff p) \<subseteq> P[- {x}]"
  shows "poly_of_focus x (flat_pm_of_poly x p) = p"
proof -
  from assms have "lookup (pm_of_poly x p) ` keys (pm_of_poly x p) \<subseteq> P[- {x}]"
    by (simp add: keys_pm_of_poly image_image) blast
  thus ?thesis by (simp add: flat_pm_of_poly_def poly_of_focus_def focus_flatten pm_of_poly_in_Polys)
qed

lemma flat_pm_of_poly_eq_zeroD:
  assumes "flat_pm_of_poly x p = 0" and "range (poly.coeff p) \<subseteq> P[- {x}]"
  shows "p = 0"
proof -
  from assms(2) have "p = poly_of_focus x (flat_pm_of_poly x p)"
    by (simp only: poly_of_focus_flat_pm_of_poly)
  also have "\<dots> = 0" by (simp add: assms(1))
  finally show ?thesis .
qed

lemma poly_poly_of_focus: "poly (poly_of_focus x p) a = poly_eval (\<lambda>_. a) (focus {x} p)"
  by (simp add: poly_of_focus_def poly_eq_poly_eval' focus_in_Polys)

corollary poly_poly_of_focus_monomial:
  "poly (poly_of_focus x p) (monomial 1 (Poly_Mapping.single x 1)) = (p::_ \<Rightarrow>\<^sub>0 _::comm_semiring_1)"
  unfolding poly_poly_of_focus poly_eval_focus by (rule poly_subst_id) simp

end (* theory *)
