(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section "Misc results for polynomials and sign variations"

theory BF_Misc imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  Sturm_Tarski.Sturm_Tarski
begin

subsection \<open>Induction on polynomial roots\<close>

(*adapted from the poly_root_induct in Polynomial.thy.*)
lemma poly_root_induct_alt [case_names 0 no_proots root]:
  fixes p :: "'a :: idom poly"
  assumes "Q 0"
  assumes "\<And>p. (\<And>a. poly p a \<noteq> 0) \<Longrightarrow> Q p"
  assumes "\<And>a p. Q p \<Longrightarrow> Q ([:-a, 1:] * p)"
  shows   "Q p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  have ?case when "p=0" using \<open>Q 0\<close> that by auto
  moreover have ?case when "\<nexists>a. poly p a = 0"
    using assms(2) that by blast
  moreover have ?case when "\<exists>a. poly p a = 0" "p\<noteq>0"
  proof -
    obtain a where "poly p a =0" using \<open>\<exists>a. poly p a = 0\<close> by auto
    then obtain q where pq:"p= [:-a,1:] * q" by (meson dvdE poly_eq_0_iff_dvd)
    then have "q\<noteq>0" using \<open>p\<noteq>0\<close> by auto
    then have "degree q<degree p" unfolding pq by (subst degree_mult_eq,auto)
    then have "Q q" using less by auto
    then show ?case using assms(3) unfolding pq by auto
  qed
  ultimately show ?case by auto
qed

subsection \<open>Misc\<close>

lemma lead_coeff_pderiv:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  shows "lead_coeff (pderiv p) = of_nat (degree p) * lead_coeff p"
  apply (auto simp:degree_pderiv coeff_pderiv)
  apply (cases "degree p")
  by (auto simp add: coeff_eq_0)

lemma gcd_degree_le_min:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "degree (gcd p q) \<le> min (degree p) (degree q)"
  by (simp add: assms(1) assms(2) dvd_imp_degree_le)

lemma lead_coeff_normalize_field:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  assumes "p\<noteq>0"
  shows "lead_coeff (normalize p) = 1"
  by (metis (no_types, lifting) assms coeff_normalize divide_self_if dvd_field_iff 
      is_unit_unit_factor leading_coeff_0_iff normalize_eq_0_iff normalize_idem)

lemma smult_normalize_field_eq:
  fixes p::"'a::{field,semidom_divide_unit_factor} poly"
  shows "p = smult (lead_coeff p) (normalize p)"
proof (rule poly_eqI)
  fix n
  have "unit_factor (lead_coeff p) = lead_coeff p"
    by (metis dvd_field_iff is_unit_unit_factor unit_factor_0)
  then show "coeff p n = coeff (smult (lead_coeff p) (normalize p)) n"
    by simp
qed

lemma lead_coeff_gcd_field:
  fixes p q::"'a::{field,semidom_divide_unit_factor,factorial_ring_gcd} poly"
  assumes "p\<noteq>0 \<or> q\<noteq>0"
  shows "lead_coeff (gcd p q) = 1"
  using assms by (metis gcd.normalize_idem gcd_eq_0_iff lead_coeff_normalize_field)

lemma poly_gcd_0_iff:
  "poly (gcd p q) x = 0 \<longleftrightarrow> poly p x=0 \<and> poly q x=0"
  by (simp add:poly_eq_0_iff_dvd)

lemma degree_eq_oneE:
  fixes p :: "'a::zero poly"
  assumes "degree p = 1"
  obtains a b where "p = [:a,b:]" "b\<noteq>0"
proof -
  obtain a b q where p:"p=pCons a (pCons b q)"
    by (metis pCons_cases)
  with assms have "q=0" by (cases "q = 0") simp_all
  with p have "p=[:a,b:]" by auto
  moreover then have "b\<noteq>0" using assms by auto
  ultimately show ?thesis ..
qed

subsection \<open>More results about sign variations (i.e. @{term changes}\<close>

lemma changes_0[simp]:"changes (0#xs) = changes xs"
  by (cases xs) auto

lemma changes_Cons:"changes (x#xs) = (if filter (\<lambda>x. x\<noteq>0) xs = [] then 
                            0 
                          else if x* hd (filter (\<lambda>x. x\<noteq>0) xs) < 0 then 
                            1 + changes xs 
                          else changes xs)"
  apply (induct xs)
  by auto

lemma changes_filter_eq:
  "changes (filter (\<lambda>x. x\<noteq>0) xs) = changes xs"
  apply (induct xs)
  by (auto simp add:changes_Cons)

lemma changes_filter_empty:
  assumes "filter (\<lambda>x. x\<noteq>0) xs = []"
  shows "changes xs = 0" "changes (a#xs) = 0" using assms
  apply (induct xs)
  apply auto
  by (metis changes_0 neq_Nil_conv)

lemma changes_append:
  assumes "xs\<noteq> [] \<and> ys\<noteq> [] \<longrightarrow> (last xs = hd ys \<and> last xs\<noteq>0)"
  shows "changes (xs@ys) = changes xs + changes ys"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have ?case when "xs=[]"
    using that Cons 
    apply (cases ys)
    by auto
  moreover have ?case when "ys=[]"
    using that Cons by auto
  moreover have ?case when "xs\<noteq>[]" "ys\<noteq>[]"
  proof -
    have "filter (\<lambda>x. x \<noteq> 0) xs \<noteq>[]"
      using that Cons 
      apply auto 
      by (metis (mono_tags, lifting) filter.simps(1) filter.simps(2) filter_append snoc_eq_iff_butlast)
    then have "changes (a # xs @ ys) = changes (a # xs) + changes ys"
      apply (subst (1 2) changes_Cons)
      using that Cons by auto
    then show ?thesis by auto
  qed
  ultimately show ?case by blast
qed

lemma changes_drop_dup:
  assumes "xs\<noteq> []" "ys\<noteq> [] \<longrightarrow> last xs=hd ys"
  shows "changes (xs@ys) = changes (xs@ tl ys)"
  using assms
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have ?case when "ys=[]"
    using that by simp
  moreover have ?case when "ys\<noteq>[]" "xs=[]"
    using that Cons
    apply auto
    by (metis changes.simps(3) list.exhaust_sel not_square_less_zero)
  moreover have ?case when "ys\<noteq>[]" "xs\<noteq>[]"
  proof -
    define ts ts' where "ts = filter (\<lambda>x. x \<noteq> 0) (xs @ ys)"
      and "ts' = filter (\<lambda>x. x \<noteq> 0) (xs @ tl ys)"
    have "(ts = [] \<longleftrightarrow> ts' = []) \<and> hd ts = hd ts'"
    proof (cases "filter (\<lambda>x. x \<noteq> 0) xs = []")
      case True
      then have "last xs = 0" using \<open>xs\<noteq>[]\<close> 
        by (metis (mono_tags, lifting) append_butlast_last_id append_is_Nil_conv 
            filter.simps(2) filter_append list.simps(3))
      then have "hd ys=0" using Cons(3)[rule_format, OF \<open>ys\<noteq>[]\<close>] \<open>xs\<noteq>[]\<close> by auto
      then have "filter (\<lambda>x. x \<noteq> 0) ys = filter (\<lambda>x. x \<noteq> 0) (tl ys)"
        by (metis (mono_tags, lifting) filter.simps(2) list.exhaust_sel that(1))
      then show ?thesis unfolding ts_def ts'_def by auto
    next
      case False
      then show ?thesis unfolding ts_def ts'_def by auto
    qed
    moreover have "changes (xs @ ys) = changes (xs @ tl ys)"
      apply (rule Cons(1))
      using that Cons(3) by auto
    moreover have "changes (a # xs @ ys) = (if ts = [] then 0 else if a * hd ts < 0 
            then 1 + changes (xs @ ys) else changes (xs @ ys))"
      using changes_Cons[of a "xs @ ys",folded ts_def] .
    moreover have "changes (a # xs @ tl ys) = (if ts' = [] then 0 else if a * hd ts' < 0 
            then 1 + changes (xs @ tl ys) else changes (xs @ tl ys))"
      using changes_Cons[of a "xs @ tl ys",folded ts'_def] .
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by blast
qed

(*
  TODO: the following lemmas contain duplicates of some lemmas in 
          Winding_Number_Eval/Missing_Algebraic.thy
  Will resolve later.  
*)

lemma Im_poly_of_real:
  "Im (poly p (of_real x)) = poly (map_poly Im p) x"
  apply (induct p)
  by (auto simp add:map_poly_pCons)
 
lemma Re_poly_of_real:
  "Re (poly p (of_real x)) = poly (map_poly Re p) x"
  apply (induct p)
  by (auto simp add:map_poly_pCons)

subsection \<open>More about @{term map_poly} and @{term of_real}\<close>

lemma of_real_poly_map_pCons[simp]:"map_poly of_real (pCons a p) = pCons (of_real a) (map_poly of_real p)" 
  by (simp add: map_poly_pCons)    
    
lemma of_real_poly_map_plus[simp]: "map_poly of_real (p + q) = map_poly of_real p +  map_poly of_real q" 
  apply (rule poly_eqI)
  by (auto simp add: coeff_map_poly)  
 
lemma of_real_poly_map_smult[simp]:"map_poly of_real (smult s p) = smult (of_real s) (map_poly of_real p)" 
  apply (rule poly_eqI)
  by (auto simp add: coeff_map_poly)    

lemma of_real_poly_map_mult[simp]:"map_poly of_real (p*q) = map_poly of_real p * map_poly of_real q"
  by (induct p,intro poly_eqI,auto)
    
lemma of_real_poly_map_poly:
  "of_real (poly p x) = poly (map_poly of_real p) (of_real x)" 
  by (induct p,auto)    

lemma of_real_poly_map_power:"map_poly of_real (p^n) = (map_poly of_real p) ^ n"
  by (induct n,auto)

(*FIXME: not duplicate*)
lemma of_real_poly_eq_iff [simp]: "map_poly of_real p = map_poly of_real q \<longleftrightarrow> p = q"
  by (auto simp: poly_eq_iff coeff_map_poly)

(*FIXME: not duplicate*)
lemma of_real_poly_eq_0_iff [simp]: "map_poly of_real p = 0 \<longleftrightarrow> p = 0"
  by (auto simp: poly_eq_iff coeff_map_poly)

subsection \<open>More about @{term order}\<close>

lemma order_multiplicity_eq:
  assumes "p\<noteq>0"
  shows "order a p = multiplicity [:-a,1:] p"
  by (metis assms multiplicity_eqI order_1 order_2)

lemma order_gcd:
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "order x (gcd p q) = min (order x p) (order x q)"
proof -
  have "prime [:- x, 1:]" 
    apply (auto simp add: prime_elem_linear_poly normalize_poly_def  intro!:primeI)
    by (simp add: pCons_one)
  then show ?thesis  
    using assms
    by (auto simp add:order_multiplicity_eq intro:multiplicity_gcd)
qed

lemma order_linear[simp]: "order x [:-a,1:] = (if x=a then 1 else 0)"
  by (auto simp add:order_power_n_n[where n=1,simplified] order_0I)
  
lemma map_poly_order_of_real:
  assumes "p\<noteq>0"
  shows "order (of_real t) (map_poly of_real p) = order t p" using assms
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  then have "order t p = 0" using order_root by blast
  moreover have "poly (map_poly of_real p) (of_real x) \<noteq>0" for x
    apply (subst of_real_poly_map_poly[symmetric])
    using no_proots order_root by simp
  then have "order (of_real t) (map_poly of_real p) = 0"
    using order_root by blast
  ultimately show ?case by auto
next
  case (root a p)
  define a1 where "a1=[:-a,1:]"
  have [simp]:"a1\<noteq>0" "p\<noteq>0" unfolding a1_def using root(2) by auto
  have "order (of_real t) (map_poly of_real a1) = order t a1"
    unfolding a1_def by simp
  then show ?case 
    apply (fold a1_def)
    by (simp add:order_mult root)
qed

lemma order_pcompose:
  assumes "pcompose p q\<noteq>0"
  shows "order x (pcompose p q) = order x (q-[:poly q x:]) * order (poly q x) p" 
  using \<open>pcompose p q\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have "order x (p \<circ>\<^sub>p q) = 0"
    apply (rule order_0I)
    using no_proots by (auto simp:poly_pcompose)
  moreover have "order (poly q x) p = 0"
    apply (rule order_0I)
    using no_proots by (auto simp:poly_pcompose)
  ultimately show ?case by auto
next
  case (root a p)
  define a1 where "a1=[:-a,1:]"
  have [simp]: "a1\<noteq>0" "p\<noteq>0" "a1 \<circ>\<^sub>p q \<noteq>0" "p \<circ>\<^sub>p q \<noteq> 0" 
    subgoal using root(2) unfolding a1_def by simp
    subgoal using root(2) by auto
    using root(2) by (fold a1_def,auto simp:pcompose_mult)
  have "order x ((a1 * p) \<circ>\<^sub>p q) = order x (a1  \<circ>\<^sub>p q) + order x (p \<circ>\<^sub>p q)"
    unfolding pcompose_mult by (auto simp: order_mult)
  also have "... = order x (q-[:poly q x:]) * (order (poly q x) a1 + order (poly q x) p)"
  proof -
    have "order x (a1  \<circ>\<^sub>p q) = order x (q-[:poly q x:]) * order (poly q x) a1"
      unfolding a1_def 
      apply (auto simp: pcompose_pCons algebra_simps diff_conv_add_uminus )
      by (simp add: order_0I)
    moreover have "order x (p \<circ>\<^sub>p q) = order x (q - [:poly q x:]) * order (poly q x) p"
      apply (rule root.hyps)
      by auto
    ultimately show ?thesis by (auto simp:algebra_simps)
  qed
  also have "... =  order x (q - [:poly q x:]) * order (poly q x) (a1 * p)"
    by (auto simp:order_mult)
  finally show ?case unfolding a1_def .
qed

subsection \<open>Polynomial roots / zeros\<close>

definition proots_within::"'a::comm_semiring_0 poly \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "proots_within p s = {x\<in>s. poly p x=0}"

abbreviation proots::"'a::comm_semiring_0 poly \<Rightarrow> 'a set" where
  "proots p \<equiv> proots_within p UNIV"

lemma proots_def: "proots p = {x. poly p x=0}" 
  unfolding proots_within_def by auto 

lemma proots_within_empty[simp]:
  "proots_within p {} = {}" unfolding proots_within_def by auto

lemma proots_within_0[simp]:
  "proots_within 0 s = s" unfolding proots_within_def by auto

lemma proots_withinI[intro,simp]:
  "poly p x=0 \<Longrightarrow> x\<in>s \<Longrightarrow> x\<in>proots_within p s"
  unfolding proots_within_def by auto

lemma proots_within_iff[simp]:
  "x\<in>proots_within p s \<longleftrightarrow> poly p x=0 \<and> x\<in>s"
  unfolding proots_within_def by auto

lemma proots_within_union:
  "proots_within p A \<union> proots_within p B = proots_within p (A \<union> B)"
  unfolding proots_within_def by auto

lemma proots_within_times:
  fixes s::"'a::{semiring_no_zero_divisors,comm_semiring_0} set"
  shows "proots_within (p*q) s = proots_within p s \<union> proots_within q s"
  unfolding proots_within_def by auto

lemma proots_within_gcd:
  fixes s::"'a::factorial_ring_gcd set"
  shows "proots_within (gcd p q) s= proots_within p s \<inter> proots_within q s"
  unfolding proots_within_def 
  by (auto simp add: poly_eq_0_iff_dvd) 

lemma proots_within_inter:
  "NO_MATCH UNIV s \<Longrightarrow> proots_within p s = proots p \<inter> s" 
  unfolding proots_within_def by auto

lemma proots_within_proots[simp]:
  "proots_within p s \<subseteq> proots p"
  unfolding proots_within_def by auto

lemma finite_proots[simp]: 
  fixes p :: "'a::idom poly"
  shows "p\<noteq>0 \<Longrightarrow> finite (proots_within p s)"
  unfolding proots_within_def using poly_roots_finite by fast

lemma proots_within_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_within [:-a,1:] s = (if a\<in>s then {a} else {})"
    "proots_within [:a,-1:] s = (if a\<in>s then {a} else {})"
  by (cases "a\<in>s",auto)

lemma proots_within_uminus[simp]:
  fixes p :: "'a::comm_ring poly"
  shows "proots_within (- p) s = proots_within p s"
  by auto

lemma proots_within_smult:
  fixes a::"'a::{semiring_no_zero_divisors,comm_semiring_0}"
  assumes "a\<noteq>0"
  shows "proots_within (smult a p) s = proots_within p s"
  unfolding proots_within_def using assms by auto 

subsection \<open>Polynomial roots counting multiplicities.\<close>

(*counting the number of proots WITH MULTIPLICITIES within a set*)
definition proots_count::"'a::idom poly \<Rightarrow> 'a set \<Rightarrow> nat" where
  "proots_count p s = (\<Sum>r\<in>proots_within p s. order r p)"  

lemma proots_count_emtpy[simp]:"proots_count p {} = 0"
  unfolding proots_count_def by auto

lemma proots_count_times:
  fixes s :: "'a::idom set"
  assumes "p*q\<noteq>0"
  shows "proots_count (p*q) s = proots_count p s + proots_count q s"
proof -
  define pts where "pts=proots_within p s" 
  define qts where "qts=proots_within q s"
  have [simp]: "finite pts" "finite qts" 
    using \<open>p*q\<noteq>0\<close> unfolding pts_def qts_def by auto
  have "(\<Sum>r\<in>pts \<union> qts. order r p) =  (\<Sum>r\<in>pts. order r p)" 
  proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
    show "\<forall>i\<in>pts \<union> qts - pts. order i p = 0" 
      unfolding pts_def qts_def proots_within_def using order_root by fastforce
  qed
  moreover have "(\<Sum>r\<in>pts \<union> qts. order r q) = (\<Sum>r\<in>qts. order r q)" 
  proof (rule comm_monoid_add_class.sum.mono_neutral_cong_right,simp_all)
    show "\<forall>i\<in>pts \<union> qts - qts. order i q = 0" 
      unfolding pts_def qts_def proots_within_def using order_root by fastforce
  qed
  ultimately show ?thesis unfolding proots_count_def
    apply (simp add:proots_within_times order_mult[OF \<open>p*q\<noteq>0\<close>] sum.distrib)
    apply (fold pts_def qts_def)
    by auto
qed

lemma proots_count_power_n_n:
  shows "proots_count ([:- a, 1:]^n) s = (if a\<in>s \<and> n>0 then n else 0)"
proof -
  have "proots_within ([:- a, 1:] ^ n) s= (if a\<in>s \<and> n>0 then {a} else {})"
    unfolding proots_within_def by auto
  thus ?thesis unfolding proots_count_def using order_power_n_n by auto
qed

lemma degree_proots_count:
  fixes p::"complex poly"
  shows "degree p = proots_count p UNIV"
proof (induct "degree p" arbitrary:p )
  case 0
  then obtain c where c_def:"p=[:c:]" using degree_eq_zeroE by auto
  then show ?case unfolding proots_count_def 
    apply (cases "c=0")
    by (auto intro!:sum.infinite simp add:infinite_UNIV_char_0 order_0I)
next
  case (Suc n)
  then have "degree p\<noteq>0" and "p\<noteq>0" by auto
  obtain z where "poly p z = 0" 
    using Fundamental_Theorem_Algebra.fundamental_theorem_of_algebra \<open>degree p\<noteq>0\<close> constant_degree[of p]
    by auto
  define onez where "onez=[:-z,1:]" 
  have [simp]: "onez\<noteq>0" "degree onez = 1" unfolding onez_def by auto
  obtain q where q_def:"p= onez * q" 
    using poly_eq_0_iff_dvd \<open>poly p z = 0\<close> dvdE unfolding onez_def by blast
  hence "q\<noteq>0" using \<open>p\<noteq>0\<close> by auto
  hence "n=degree q" using degree_mult_eq[of onez q] \<open>Suc n = degree p\<close> 
    apply (fold q_def)
    by auto
  hence "degree q = proots_count q UNIV" using Suc.hyps(1) by simp
  moreover have " Suc 0 = proots_count onez UNIV" 
    unfolding onez_def using proots_count_power_n_n[of z 1 UNIV]
    by auto
  ultimately show ?case 
    unfolding q_def using degree_mult_eq[of onez q] proots_count_times[of onez q UNIV] \<open>q\<noteq>0\<close>
    by auto
qed

lemma proots_count_smult:
  fixes a::"'a::{semiring_no_zero_divisors,idom}"
  assumes "a\<noteq>0"
  shows "proots_count (smult a p) s= proots_count p s"
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding proots_count_def
    using order_smult[OF assms] proots_within_smult[OF assms] by auto
qed


lemma proots_count_pCons_1_iff:
  fixes a::"'a::idom"
  shows "proots_count [:-a,1:] s = (if a\<in>s then 1 else 0)"
  unfolding proots_count_def 
  by (cases "a\<in>s",auto simp add:proots_within_pCons_1_iff order_power_n_n[of _ 1,simplified])

lemma proots_count_uminus[simp]:
  "proots_count (- p) s = proots_count p s"
  unfolding proots_count_def by simp

lemma card_proots_within_leq:
  assumes "p\<noteq>0"
  shows "proots_count p s \<ge> card (proots_within p s)" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case unfolding proots_within_def proots_count_def by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "card (proots_within ([:- a, 1:] * p) s) 
      \<le> card (proots_within [:- a, 1:] s)+card (proots_within p s)" 
    unfolding proots_within_times by (auto simp add:card_Un_le)
  also have "... \<le> 1+ proots_count p s"
  proof -
    have "card (proots_within [:- a, 1:] s) \<le> 1"
    proof (cases "a\<in>s")
      case True
      then have "proots_within [:- a, 1:] s = {a}" by auto
      then show ?thesis by auto
    next
      case False
      then have "proots_within [:- a, 1:] s = {}" by auto
      then show ?thesis by auto
    qed
    moreover have "card (proots_within p s) \<le> proots_count p s"
      apply (rule root.hyps)
      using root by auto
    ultimately show ?thesis by auto
  qed
  also have "... =  proots_count ([:- a,1:] * p) s"
    apply (subst proots_count_times)
    subgoal by (metis mult_eq_0_iff pCons_eq_0_iff root.prems zero_neq_one)  
    using root by (auto simp add:proots_count_pCons_1_iff)
  finally have "card (proots_within ([:- a, 1:] * p) s) \<le> proots_count ([:- a, 1:] * p) s" .
  then show ?case 
    by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral minus_pCons 
        mult_minus_left proots_count_uminus proots_within_uminus)
qed

(*FIXME: not duplicate*)
lemma proots_count_0_imp_empty:
  assumes "proots_count p s=0" "p\<noteq>0"
  shows "proots_within p s = {}"
proof -
  have "card (proots_within p s) = 0"
    using card_proots_within_leq[OF \<open>p\<noteq>0\<close>,of s] \<open>proots_count p s=0\<close> by auto
  moreover have "finite (proots_within p s)" using \<open>p\<noteq>0\<close> by auto
  ultimately show ?thesis by auto
qed

lemma proots_count_leq_degree:
  assumes "p\<noteq>0"
  shows "proots_count p s\<le> degree p" using assms
proof (induct rule:poly_root_induct[of _ "\<lambda>x. x\<in>s"])
  case 0
  then show ?case by auto
next
  case (no_roots p)
  then have "proots_within p s = {}" by auto
  then show ?case unfolding proots_count_def by auto
next
  case (root a p)
  have "proots_count ([:a, - 1:] * p) s = proots_count [:a, - 1:] s + proots_count p s"
    apply (subst proots_count_times)
    using root by auto
  also have "... = 1 + proots_count p s"
  proof -
    have "proots_count [:a, - 1:] s  =1"
      by (metis (no_types, lifting) add.inverse_inverse add.inverse_neutral minus_pCons 
          proots_count_pCons_1_iff proots_count_uminus root.hyps(1))
    then show ?thesis by auto
  qed
  also have "... \<le>  degree ([:a,-1:] * p)" 
    apply (subst degree_mult_eq)
    subgoal by auto
    subgoal using root by auto
    subgoal using root by (simp add: \<open>p \<noteq> 0\<close>)
    done
  finally show ?case .
qed

(*TODO: not a duplicate*)
lemma proots_count_union_disjoint:
  assumes "A \<inter> B = {}" "p\<noteq>0"
  shows "proots_count p (A \<union> B) = proots_count p A + proots_count p B"
  unfolding proots_count_def 
  apply (subst proots_within_union[symmetric])
  apply (subst sum.union_disjoint)
  using assms by auto

lemma proots_count_cong:
  assumes order_eq:"\<forall>x\<in>s. order x p = order x q" and "p\<noteq>0" and "q\<noteq>0"
  shows "proots_count p s = proots_count q s" unfolding proots_count_def
proof (rule sum.cong)
  have "poly p x = 0 \<longleftrightarrow> poly q x = 0" when "x\<in>s" for x
    using order_eq that by (simp add: assms(2) assms(3) order_root)
  then show "proots_within p s = proots_within q s" by auto
  show "\<And>x. x \<in> proots_within q s \<Longrightarrow> order x p = order x q"
    using order_eq by auto
qed

lemma proots_count_of_real:
  assumes "p\<noteq>0"
  shows "proots_count (map_poly of_real p) ((of_real::_\<Rightarrow>'a::{real_algebra_1,idom}) ` s) 
            = proots_count p s"
proof -
  define k where "k=(of_real::_\<Rightarrow>'a)"
  have "proots_within (map_poly of_real p) (k ` s) =k ` (proots_within p s)"
    unfolding proots_within_def k_def by (auto simp add:of_real_poly_map_poly[symmetric])
  then have "proots_count (map_poly of_real p) (k ` s) 
                = (\<Sum>r\<in>k ` (proots_within p s). order r (map_poly of_real p))"
    unfolding proots_count_def by simp
  also have "... = sum ((\<lambda>r. order r (map_poly of_real p)) \<circ> k) (proots_within p s)"
    apply (subst sum.reindex) 
    unfolding k_def by (auto simp add: inj_on_def)
  also have "... = proots_count p s" unfolding proots_count_def
    apply (rule sum.cong)
    unfolding k_def comp_def using \<open>p\<noteq>0\<close> by (auto simp add:map_poly_order_of_real) 
  finally show ?thesis unfolding k_def .
qed

(*Is field really necessary here?*)
lemma proots_pcompose:
  fixes p q::"'a::field poly"
  assumes "p\<noteq>0" "degree q=1"
  shows "proots_count (pcompose p q) s = proots_count p (poly q ` s)"
proof -
  obtain a b where ab:"q=[:a,b:]" "b\<noteq>0"
    using \<open>degree q=1\<close> degree_eq_oneE by metis
  define f where "f=(\<lambda>y. (y-a)/b)"
  have f_eq:"f (poly q x) = x" "poly q (f x) = x" for x
    unfolding f_def using ab by auto
  have "proots_count (p \<circ>\<^sub>p q) s = (\<Sum>r\<in> f ` proots_within p (poly q ` s). order r (p \<circ>\<^sub>p q))" 
    unfolding proots_count_def
    apply (rule arg_cong2[where f =sum])
    apply (auto simp:poly_pcompose proots_within_def f_eq)
    by (metis (mono_tags, lifting) f_eq(1) image_eqI mem_Collect_eq)
  also have "... = (\<Sum>x\<in>proots_within p (poly q ` s). order (f x) (p \<circ>\<^sub>p q))"
    apply (subst sum.reindex)
    subgoal unfolding f_def inj_on_def using \<open>b\<noteq>0\<close> by auto
    by simp
  also have "... = (\<Sum>x\<in>proots_within p (poly q ` s). order x p)"
  proof -
    have "p \<circ>\<^sub>p q \<noteq> 0" using assms(1) assms(2) pcompose_eq_0 by force
    moreover have "order (f x) (q - [:x:]) = 1" for x 
    proof -
      have "order (f x) (q - [:x:]) = order (f x) (smult b [:-((x - a) / b),1:])"
        unfolding f_def using ab by auto
      also have "... = 1"
        apply (subst order_smult)
        using \<open>b\<noteq>0\<close> unfolding f_def by auto
      finally show ?thesis .
    qed
    ultimately have "order (f x) (p \<circ>\<^sub>p q) = order x p" for x
      apply (subst order_pcompose)
      using f_eq by auto
    then show ?thesis by auto
  qed
  also have "... =  proots_count p (poly q ` s)"
    unfolding proots_count_def by auto
  finally show ?thesis .
qed

subsection \<open>Composition of a polynomial and a rational function\<close>

(*composition of a polynomial and a rational function. Maybe a more general version in the future?*)
definition fcompose::"'a ::field poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "fcompose p q r = fst (fold_coeffs (\<lambda>a (c,d). (d*[:a:] + q * c,r*d)) p (0,1))"

lemma fcompose_0 [simp]: "fcompose 0 q r = 0"
  by (simp add: fcompose_def)

lemma fcompose_const[simp]:"fcompose [:a:] q r = [:a:]"
  unfolding fcompose_def by (cases "a=0") auto

lemma fcompose_pCons: 
  "fcompose (pCons a p) q1 q2 = smult a (q2^(degree (pCons a p))) + q1 * fcompose p q1 q2"
proof (cases "p=0")
  case False
  define ff where "ff=(\<lambda>a (c, d). (d * [:a:] + q1 * c, q2 * d))"
  define fc where "fc=fold_coeffs ff p (0, 1)"
  have snd_ff:"snd fc = (if p=0 then 1 else q2^(degree p + 1))" unfolding fc_def
    apply (induct p)
    subgoal by simp
    subgoal for a p
      by (auto simp add:ff_def split:if_splits prod.splits)
    done

  have "fcompose (pCons a p) q1 q2 = fst (fold_coeffs ff (pCons a p) (0, 1))"
    unfolding fcompose_def ff_def by simp
  also have "... = fst (ff a fc)"
    using False unfolding fc_def by auto
  also have "... = snd fc * [:a:] + q1 * fst fc"
    unfolding ff_def by (auto split:prod.splits)
  also have "... = smult a (q2^(degree (pCons a p))) + q1 * fst fc"
    using snd_ff False by auto
  also have "... = smult a (q2^(degree (pCons a p))) + q1 * fcompose p q1 q2"
    unfolding fc_def ff_def fcompose_def by simp
  finally show ?thesis .
qed simp

lemma fcompose_uminus:
  "fcompose (-p) q r = - fcompose p q r"
  by (induct p) (auto simp:fcompose_pCons)

lemma fcompose_add_less:
  assumes "degree p1 > degree p2"
  shows "fcompose (p1+p2) q1 q2 
            = fcompose p1 q1 q2 + q2^(degree p1-degree p2) * fcompose p2 q1 q2"
  using assms
proof (induction p1 p2 rule: poly_induct2)
  case (pCons a1 p1 a2 p2)
  have ?case when "p2=0"
    using that by (simp add:fcompose_pCons smult_add_left)
  moreover have ?case when "p2\<noteq>0" "\<not> degree p2 < degree p1"
    using that pCons(2) by auto
  moreover have ?case when "p2\<noteq>0" "degree p2< degree p1"
  proof -
    define d1 d2 where "d1=degree (pCons a1 p1)" and "d2=degree (pCons a2 p2) "
    define fp1 fp2 where "fp1= fcompose p1 q1 q2" and "fp2=fcompose p2 q1 q2"

    have "fcompose (pCons a1 p1 + pCons a2 p2) q1 q2 
            = fcompose (pCons (a1+a2) (p1+p2)) q1 q2"
      by simp
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * fcompose (p1 + p2) q1 q2"
    proof -
      have "degree (pCons (a1 + a2) (p1 + p2)) = d1"
        unfolding d1_def using that degree_add_eq_left by fastforce
      then show ?thesis unfolding fcompose_pCons by simp
    qed
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * (fp1 + q2 ^ (d1 - d2) * fp2)"
    proof -
      have "degree p1 - degree p2 = d1 - d2"
        unfolding d1_def d2_def using that by simp
      then show ?thesis 
        unfolding pCons(1)[OF that(2),folded fp1_def fp2_def] by simp
    qed
    also have "... = fcompose (pCons a1 p1) q1 q2 + q2 ^ (d1 - d2) 
                        * fcompose (pCons a2 p2) q1 q2"
    proof -
      have "d1 > d2" unfolding d1_def d2_def using that by auto
      then show ?thesis
        unfolding fcompose_pCons
        apply (fold d1_def d2_def fp1_def fp2_def)
        by (simp add:algebra_simps smult_add_left power_add[symmetric])
    qed
    finally show ?thesis unfolding d1_def d2_def .
  qed
  ultimately show ?case by blast
qed simp

lemma fcompose_add_eq:
  assumes "degree p1 = degree p2"
  shows "q2^(degree p1 - degree (p1+p2)) * fcompose (p1+p2) q1 q2 
            = fcompose p1 q1 q2 + fcompose p2 q1 q2"
  using assms
proof (induction p1 p2 rule: poly_induct2)
  case (pCons a1 p1 a2 p2)
  have ?case when "p1+p2=0"
  proof -
    have "p2=-p1" using that by algebra
    then show ?thesis by (simp add:fcompose_pCons fcompose_uminus smult_add_left)
  qed
  moreover have ?case when "p1=0"
  proof -
    have "p2=0"
      using pCons(2) that by (auto split:if_splits)
    then show ?thesis using that by simp
  qed
  moreover have ?case when "p1\<noteq>0" "p1+p2\<noteq>0"
  proof -
    define d1 d2 dp where "d1=degree (pCons a1 p1)" and "d2=degree (pCons a2 p2)"
                            and "dp = degree p1 - degree (p1+p2)"
    define fp1 fp2 where "fp1= fcompose p1 q1 q2" and "fp2=fcompose p2 q1 q2"

    have "q2 ^ (degree (pCons a1 p1) - degree (pCons a1 p1 + pCons a2 p2)) *
             fcompose (pCons a1 p1 + pCons a2 p2) q1 q2 
                = q2 ^ dp * fcompose (pCons (a1+a2) (p1 +p2)) q1 q2"
      unfolding dp_def using that by auto
    also have "... = smult (a1 + a2) (q2 ^ d1) + q1 * (q2 ^ dp * fcompose (p1 + p2) q1 q2)"
    proof -
      have "degree p1 \<ge> degree (p1 + p2)" 
        by (metis degree_add_le degree_pCons_eq_if not_less_eq_eq order_refl pCons.prems zero_le)
      then show ?thesis 
        unfolding fcompose_pCons dp_def d1_def using that
        by (simp add:algebra_simps power_add[symmetric])
    qed
    also have "... =  smult (a1 + a2) (q2 ^ d1) + q1 * (fp1 + fp2)"
      apply (subst pCons(1)[folded dp_def fp1_def fp2_def])
      subgoal by (metis degree_pCons_eq_if diff_Suc_Suc diff_zero not_less_eq_eq pCons.prems zero_le)
      subgoal by simp
      done
    also have "... = fcompose (pCons a1 p1) q1 q2 + fcompose (pCons a2 p2) q1 q2"
    proof -
      have *:"d1 = degree (pCons a2 p2)"
        unfolding d1_def using pCons(2) by simp
      show ?thesis 
        unfolding fcompose_pCons
        apply (fold d1_def fp1_def fp2_def *)
        by (simp add:smult_add_left algebra_simps)
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by blast
qed simp

lemma fcompose_add_const:
  "fcompose ([:a:] + p) q1 q2 = smult a (q2 ^ degree p) + fcompose p q1 q2"
  apply (cases p)
  by (auto simp add:fcompose_pCons smult_add_left)

lemma fcompose_smult: "fcompose (smult a p) q1 q2 = smult a (fcompose p q1 q2)"
  by (induct p) (simp_all add:fcompose_pCons smult_add_right)

lemma fcompose_mult: "fcompose (p1*p2) q1 q2 = fcompose p1 q1 q2 * fcompose p2 q1 q2"
proof (induct p1)
  case 0
  then show ?case by simp
next
  case (pCons a p1)
  have ?case when "p1=0 \<or> p2=0" 
    using that by (auto simp add:fcompose_smult)
  moreover have ?case when "p1\<noteq>0" "p2\<noteq>0" "a=0"
    using that by (simp add:fcompose_pCons pCons)
  moreover have ?case when "p1\<noteq>0" "p2\<noteq>0" "a\<noteq>0"
  proof -
    have "fcompose (pCons a p1 * p2) q1 q2 
            = fcompose (pCons 0 (p1 * p2) + smult a p2) q1 q2"
      by (simp add:algebra_simps)
    also have "... =  fcompose (pCons 0 (p1 * p2)) q1 q2 
                        + q2 ^ (degree p1 +1) * fcompose (smult a p2) q1 q2"
    proof -
      have "degree (pCons 0 (p1 * p2)) > degree (smult a p2)"
        using that by (simp add: degree_mult_eq)
      from fcompose_add_less[OF this,of q1 q2] that 
      show ?thesis by (simp add:degree_mult_eq)
    qed
    also have "... = fcompose (pCons a p1) q1 q2 * fcompose p2 q1 q2"
      using that by (simp add:fcompose_pCons fcompose_smult pCons algebra_simps)
    finally show ?thesis .
  qed
  ultimately show ?case by blast
qed

lemma fcompose_poly:
  assumes "poly q2 x\<noteq>0"
  shows "poly p (poly q1 x/poly q2 x) = poly (fcompose p q1 q2) x / poly (q2^(degree p)) x"
  apply (induct p)
  using assms by (simp_all add:fcompose_pCons field_simps)

lemma poly_fcompose:
   assumes "poly q2 x\<noteq>0"
   shows "poly (fcompose p q1 q2) x = poly p (poly q1 x/poly q2 x) * (poly q2 x)^(degree p)"
  using fcompose_poly[OF assms] assms by (auto simp add:field_simps)
lemma poly_fcompose_0_denominator:
  assumes "poly q2 x=0"
  shows "poly (fcompose p q1 q2) x = poly q1 x ^ degree p * lead_coeff p"
  apply (induct p)
  using assms by (auto simp add:fcompose_pCons)

lemma fcompose_0_denominator:"fcompose p q1 0 = smult (lead_coeff p) (q1^degree p)"
  apply (induct p)
  by (auto simp:fcompose_pCons)

lemma fcompose_nzero:
  fixes p::"'a::field poly"
  assumes "p\<noteq>0" and "q2\<noteq>0" and nconst:"\<forall>c. q1 \<noteq> smult c q2"
      and infi:"infinite (UNIV::'a set)"
  shows "fcompose p q1 q2 \<noteq> 0" using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have False when "fcompose p q1 q2 = 0"
  proof -
    obtain x where "poly q2 x\<noteq>0" 
    proof -
      have "finite (proots q2)" using \<open>q2\<noteq>0\<close> by auto
      then have "\<exists>x. poly q2 x\<noteq>0" 
        by (meson UNIV_I ex_new_if_finite infi proots_withinI)
      then show ?thesis using that by auto
    qed
    define y where "y = poly q1 x / poly q2 x"
    have "poly p y = 0"
      using \<open>fcompose p q1 q2 = 0\<close> fcompose_poly[OF \<open>poly q2 x\<noteq>0\<close>,of p q1,folded y_def] 
      by simp
    then show False using no_proots(1) by auto
  qed
  then show ?case by auto
next
  case (root a p)
  have "fcompose [:- a, 1:] q1 q2 \<noteq> 0" 
    unfolding fcompose_def using nconst[rule_format,of a]
    by simp
  moreover have "fcompose p q1 q2 \<noteq> 0" 
    using root by fastforce
  ultimately show ?case unfolding fcompose_mult by auto
qed

subsection \<open>Bijection (@{term bij_betw}) and the number of polynomial roots\<close>

lemma proots_fcompose_bij_eq:
  fixes p::"'a::field poly"
  assumes bij:"bij_betw (\<lambda>x. poly q1 x/poly q2 x) A B" and "p\<noteq>0" 
      and nzero:"\<forall>x\<in>A. poly q2 x\<noteq>0"
      and max_deg: "max (degree q1) (degree q2) \<le> 1"
      and nconst:"\<forall>c. q1 \<noteq> smult c q2"
      and infi:"infinite (UNIV::'a set)"
  shows "proots_count p B = proots_count (fcompose p q1 q2) A"
  using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have "proots_count p B = 0"
  proof -
    have "proots_within p B = {}"
      using no_proots by auto
    then show ?thesis unfolding proots_count_def by auto
  qed
  moreover have "proots_count (fcompose p q1 q2) A = 0"
  proof -
    have "proots_within (fcompose p q1 q2) A = {}"
      using no_proots unfolding proots_within_def
      by (smt div_0 empty_Collect_eq fcompose_poly nzero)
    then show ?thesis unfolding proots_count_def by auto
  qed
  ultimately show ?case by auto
next
  case (root b p)
  have "proots_count ([:- b, 1:] * p) B = proots_count [:- b, 1:] B + proots_count p B"
    using proots_count_times[OF \<open>[:- b, 1:] * p \<noteq> 0\<close>] by simp
  also have "... = proots_count (fcompose [:- b, 1:] q1 q2) A 
                    + proots_count (fcompose p q1 q2) A" 
  proof -
    define g where "g=(\<lambda>x. poly q1 x/poly q2 x)"

    have "proots_count [:- b, 1:] B = proots_count (fcompose [:- b, 1:] q1 q2) A" 
    proof (cases "b\<in>B")
      case True
      then have "proots_count [:- b, 1:] B = 1"
        unfolding proots_count_pCons_1_iff by simp
      moreover have "proots_count (fcompose [:- b, 1:] q1 q2) A = 1"
      proof -
        obtain a where "b=g a" "a\<in>A"
          using bij[folded g_def] True 
          by (metis bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)
        define qq where "qq=q1 - smult b q2"
        have qq_0:"poly qq a=0" and qq_deg: "degree qq\<le>1" and \<open>qq\<noteq>0\<close>
          unfolding qq_def
          subgoal using \<open>b=g a\<close> nzero[rule_format,OF \<open>a\<in>A\<close>] unfolding g_def by auto
          subgoal using max_deg by (simp add: degree_diff_le)
          subgoal using nconst[rule_format,of b] by auto
          done
        have "proots_within qq A = {a}" 
        proof -
          have "a\<in>proots_within qq A" 
            using qq_0 \<open>a\<in>A\<close> by auto
          moreover have "card (proots_within qq A) = 1" 
          proof -
            have "finite (proots_within qq A)" using \<open>qq\<noteq>0\<close> by simp
            moreover have "proots_within qq A \<noteq> {}"
              using \<open>a\<in>proots_within qq A\<close> by auto
            ultimately have "card (proots_within qq A) \<noteq>0" by auto
            moreover have "card (proots_within qq A) \<le> 1" 
              by (meson \<open>qq \<noteq> 0\<close> card_proots_within_leq le_trans proots_count_leq_degree qq_deg)
            ultimately show ?thesis by auto
          qed
          ultimately show ?thesis by (metis card_1_singletonE singletonD)
        qed
        moreover have "order a qq=1" 
          by (metis One_nat_def \<open>qq \<noteq> 0\<close> le_antisym le_zero_eq not_less_eq_eq order_degree
                order_root qq_0 qq_deg)
        ultimately show ?thesis unfolding fcompose_def proots_count_def qq_def  
          by auto
      qed
      ultimately show ?thesis by auto
    next
      case False
      then have "proots_count [:- b, 1:] B  = 0"
        unfolding proots_count_pCons_1_iff by simp
      moreover have "proots_count (fcompose [:- b, 1:] q1 q2) A = 0"
      proof -
        have "proots_within (fcompose [:- b, 1:] q1 q2) A = {}"
        proof (rule ccontr)
          assume "proots_within (fcompose [:- b, 1:] q1 q2) A \<noteq> {}"
          then obtain a where "a\<in>A" "poly q1 a = b * poly q2 a"
            unfolding fcompose_def proots_within_def by auto
          then have "b = g a"
            unfolding g_def using nzero[rule_format,OF \<open>a\<in>A\<close>] by auto
          then have "b\<in>B" using \<open>a\<in>A\<close> bij[folded g_def] using bij_betwE by blast
          then show False using False by auto
        qed  
        then show ?thesis unfolding proots_count_def by auto
      qed      
      ultimately show ?thesis by simp
    qed
    moreover have "proots_count p B = proots_count (fcompose p q1 q2) A" 
      apply (rule root.hyps)
      using mult_eq_0_iff root.prems by blast
    ultimately show ?thesis by auto
  qed
  also have "... = proots_count (fcompose ([:- b, 1:] * p) q1 q2) A"
  proof (cases "A={}")
    case False
    have "fcompose [:- b, 1:] q1 q2 \<noteq>0" 
      using nconst[rule_format,of b] unfolding fcompose_def by auto
    moreover have "fcompose p q1 q2 \<noteq> 0" 
      apply (rule fcompose_nzero[OF _ _ nconst infi])
      subgoal using \<open>[:- b, 1:] * p \<noteq> 0\<close> by auto
      subgoal using nzero False by auto
      done
    ultimately show ?thesis unfolding fcompose_mult
      apply (subst proots_count_times)
      by auto
  qed auto
  finally show ?case .
qed

lemma proots_card_fcompose_bij_eq:
  fixes p::"'a::field poly"
  assumes bij:"bij_betw (\<lambda>x. poly q1 x/poly q2 x) A B" and "p\<noteq>0" 
      and nzero:"\<forall>x\<in>A. poly q2 x\<noteq>0"
      and max_deg: "max (degree q1) (degree q2) \<le> 1"
      and nconst:"\<forall>c. q1 \<noteq> smult c q2"
      and infi:"infinite (UNIV::'a set)"
  shows "card (proots_within p B) = card (proots_within (fcompose p q1 q2) A)"
  using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have "proots_within p B = {}" using no_proots by auto
  moreover have "proots_within (fcompose p q1 q2) A = {}" 
    using no_proots fcompose_poly 
    by (smt Collect_empty_eq divide_eq_0_iff nzero proots_within_def)
  ultimately show ?case by auto
next
  case (root b p)
  then have [simp]:"p\<noteq>0" by auto

  have ?case when "b\<notin>B \<or> poly p b=0"
  proof -
    have "proots_within ([:- b, 1:] * p) B = proots_within p B"
      using that by auto
    moreover have "proots_within (fcompose ([:- b, 1:] * p) q1 q2) A 
        = proots_within (fcompose p q1 q2) A"
      using that nzero unfolding fcompose_mult proots_within_times 
      apply (auto simp add: poly_fcompose)
      using bij bij_betwE by blast
    ultimately show ?thesis using root by auto
  qed
  moreover have ?case when "b\<in>B" "poly p b\<noteq>0"
  proof -
    define bb where "bb=[:- b, 1:]"
    have "card (proots_within (bb * p) B) = card {b} + card (proots_within p B)"
    proof -
      have "proots_within bb B = {b}" 
        using that unfolding bb_def by auto
      then show ?thesis unfolding proots_within_times
        apply (subst card_Un_disjoint)
        by (use that in auto)
    qed
    also have "... = 1 + card (proots_within (fcompose p q1 q2) A)"
      using root.hyps by simp
    also have "... = card (proots_within (fcompose (bb * p) q1 q2) A)"
      unfolding proots_within_times fcompose_mult
    proof (subst card_Un_disjoint) 
      obtain a where b_poly:"b=poly q1 a / poly q2 a" and "a\<in>A" 
        by (metis (no_types, lifting) \<open>b \<in> B\<close> bij bij_betwE bij_betw_the_inv_into 
            f_the_inv_into_f_bij_betw)
      define bbq pq where "bbq=fcompose bb q1 q2" and "pq=fcompose p q1 q2"
      have bbq_0:"poly bbq a=0" and bbq_deg: "degree bbq\<le>1" and "bbq\<noteq>0"
        unfolding bbq_def bb_def 
        subgoal using \<open>a \<in> A\<close> b_poly nzero poly_fcompose by fastforce
        subgoal by (metis (no_types, lifting) degree_add_le degree_pCons_eq_if degree_smult_le 
           dual_order.trans fcompose_const fcompose_pCons max.boundedE max_deg mult_cancel_left2 
           one_neq_zero one_poly_eq_simps(1) power.simps)
        subgoal by (metis \<open>a \<in> A\<close> \<open>poly (fcompose [:- b, 1:] q1 q2) a = 0\<close> fcompose_nzero infi 
                  nconst nzero one_neq_zero pCons_eq_0_iff)
        done
      show "finite (proots_within bbq A)" using \<open>bbq\<noteq>0\<close> by simp
      show "finite (proots_within pq A)" unfolding pq_def 
        by (metis \<open>a \<in> A\<close> \<open>p \<noteq> 0\<close> fcompose_nzero finite_proots infi nconst nzero poly_0 pq_def)
      have bbq_a:"proots_within bbq A = {a}"
      proof -
        have "a\<in>proots_within bbq A" 
          by (simp add: \<open>a \<in> A\<close> bbq_0)
        moreover have "card (proots_within bbq A) = 1" 
        proof -
          have "card (proots_within bbq A) \<noteq>0" 
            using \<open>a\<in>proots_within bbq A\<close> \<open>finite (proots_within bbq A)\<close>
            by auto
          moreover have "card (proots_within bbq A) \<le> 1" 
            by (meson \<open>bbq \<noteq> 0\<close> card_proots_within_leq le_trans proots_count_leq_degree bbq_deg)
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis by (metis card_1_singletonE singletonD)
      qed
      show "proots_within (bbq) A \<inter> proots_within (pq) A = {}" 
        using b_poly bbq_a fcompose_poly nzero pq_def that(2) by fastforce
      show "1 + card (proots_within pq A) = card (proots_within bbq A) + card (proots_within pq A)"
        using bbq_a by simp
    qed
    finally show ?thesis unfolding bb_def .
  qed
  ultimately show ?case by auto
qed 

lemma proots_pcompose_bij_eq:
  fixes p::"'a::idom poly"
  assumes bij:"bij_betw (\<lambda>x. poly q x) A B" and "p\<noteq>0" 
      and q_deg: "degree q = 1"
  shows "proots_count p B = proots_count (p \<circ>\<^sub>p q) A" using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  have "proots_count p B = 0"
  proof -
    have "proots_within p B = {}"
      using no_proots by auto
    then show ?thesis unfolding proots_count_def by auto
  qed
  moreover have "proots_count (p \<circ>\<^sub>p q) A = 0"
  proof -
    have "proots_within (p \<circ>\<^sub>p q) A = {}"
      using no_proots unfolding proots_within_def
      by (auto simp:poly_pcompose)
    then show ?thesis unfolding proots_count_def by auto
  qed
  ultimately show ?case by auto
next
  case (root b p)
  have "proots_count ([:- b, 1:] * p) B = proots_count [:- b, 1:] B + proots_count p B"
    using proots_count_times[OF \<open>[:- b, 1:] * p \<noteq> 0\<close>] by simp
  also have "... = proots_count ([:- b, 1:] \<circ>\<^sub>p q) A + proots_count (p \<circ>\<^sub>p q) A"
  proof -
    have "proots_count [:- b, 1:] B = proots_count ([:- b, 1:] \<circ>\<^sub>p q) A"
    proof (cases "b\<in>B")
      case True
      then have "proots_count [:- b, 1:] B = 1" 
        unfolding proots_count_pCons_1_iff by simp
      moreover have "proots_count ([:- b, 1:] \<circ>\<^sub>p q) A = 1" 
      proof -
        obtain a where "b=poly q a" "a\<in>A"
          using True bij by (metis bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)
        define qq where "qq=[:- b:] + q"
        have qq_0:"poly qq a=0" and qq_deg: "degree qq\<le>1" and \<open>qq\<noteq>0\<close>
          unfolding qq_def
          subgoal using \<open>b=poly q a\<close> by auto
          subgoal using q_deg by (simp add: degree_add_le)
          subgoal using q_deg add.inverse_unique by force
          done
        have "proots_within qq A = {a}" 
        proof -
          have "a\<in>proots_within qq A" 
            using qq_0 \<open>a\<in>A\<close> by auto
          moreover have "card (proots_within qq A) = 1" 
          proof -
            have "finite (proots_within qq A)" using \<open>qq\<noteq>0\<close> by simp
            moreover have "proots_within qq A \<noteq> {}"
              using \<open>a\<in>proots_within qq A\<close> by auto
            ultimately have "card (proots_within qq A) \<noteq>0" by auto
            moreover have "card (proots_within qq A) \<le> 1" 
              by (meson \<open>qq \<noteq> 0\<close> card_proots_within_leq le_trans proots_count_leq_degree qq_deg)
            ultimately show ?thesis by auto
          qed
          ultimately show ?thesis by (metis card_1_singletonE singletonD)
        qed
        moreover have "order a qq=1" 
          by (metis One_nat_def \<open>qq \<noteq> 0\<close> le_antisym le_zero_eq not_less_eq_eq order_degree
                order_root qq_0 qq_deg)
        ultimately show ?thesis unfolding pcompose_def proots_count_def qq_def  
          by auto
      qed
      ultimately show ?thesis by auto
    next
      case False
      then have "proots_count [:- b, 1:] B  = 0"
        unfolding proots_count_pCons_1_iff by simp
      moreover have "proots_count ([:- b, 1:] \<circ>\<^sub>p q) A = 0"
      proof -
        have "proots_within ([:- b, 1:] \<circ>\<^sub>p q) A = {}"
          unfolding pcompose_def 
          apply auto
          using False bij bij_betwE by blast
        then show ?thesis unfolding proots_count_def by auto
      qed      
      ultimately show ?thesis by simp
    qed
    moreover have "proots_count p B = proots_count (p \<circ>\<^sub>p q) A"
      apply (rule root.hyps)
      using \<open>[:- b, 1:] * p \<noteq> 0\<close> by auto
    ultimately show ?thesis by auto
  qed
  also have "... = proots_count (([:- b, 1:] * p) \<circ>\<^sub>p q) A"
    unfolding pcompose_mult
    apply (subst proots_count_times)
    subgoal by (metis (no_types, lifting) One_nat_def add.right_neutral degree_0 degree_mult_eq
      degree_pCons_eq_if degree_pcompose mult_eq_0_iff one_neq_zero one_pCons pcompose_mult
      q_deg root.prems)
    by simp
  finally show ?case .
qed

lemma proots_card_pcompose_bij_eq:
  fixes p::"'a::idom poly"
  assumes bij:"bij_betw (\<lambda>x. poly q x) A B" and "p\<noteq>0" 
      and q_deg: "degree q = 1"
  shows "card (proots_within p B) = card (proots_within (p \<circ>\<^sub>p q) A)" using \<open>p\<noteq>0\<close>
proof (induct p rule:poly_root_induct_alt)
  case 0
  then show ?case by auto
next
  case (no_proots p)
  have "proots_within p B = {}" using no_proots by auto
  moreover have "proots_within (p \<circ>\<^sub>p q) A = {}" using no_proots 
    by (simp add: poly_pcompose proots_within_def)
  ultimately show ?case by auto
next
  case (root b p)
  then have [simp]:"p\<noteq>0" by auto
  have ?case when "b\<notin>B \<or> poly p b=0"
  proof -
    have "proots_within ([:- b, 1:] * p) B = proots_within p B"
      using that by auto
    moreover have "proots_within (([:- b, 1:] * p) \<circ>\<^sub>p q) A = proots_within (p \<circ>\<^sub>p q) A"
      using that unfolding pcompose_mult proots_within_times
      apply (auto simp add: poly_pcompose)
      using bij bij_betwE by blast
    ultimately show ?thesis using root.hyps[OF \<open>p\<noteq>0\<close>] by auto
  qed
  moreover have ?case when "b\<in>B" "poly p b\<noteq>0"
  proof -
    define bb where "bb=[:- b, 1:]"
    have "card (proots_within (bb * p) B) = card {b} + card (proots_within p B)"
    proof -
      have "proots_within bb B = {b}" 
        using that unfolding bb_def by auto
      then show ?thesis unfolding proots_within_times
        apply (subst card_Un_disjoint)
        by (use that in auto)
    qed
    also have "... = 1 + card (proots_within (p \<circ>\<^sub>p q) A)"
      using root.hyps by simp
    also have "... = card (proots_within ((bb * p) \<circ>\<^sub>p q) A)"
      unfolding proots_within_times pcompose_mult
    proof (subst card_Un_disjoint) 
      obtain a where "b=poly q a" "a\<in>A" 
        by (metis \<open>b \<in> B\<close> bij bij_betwE bij_betw_the_inv_into f_the_inv_into_f_bij_betw)
      define bbq pq where "bbq=bb \<circ>\<^sub>p q" and "pq=p \<circ>\<^sub>p q"
      have bbq_0:"poly bbq a=0" and bbq_deg: "degree bbq\<le>1" and "bbq\<noteq>0"
        unfolding bbq_def bb_def poly_pcompose
        subgoal using \<open>b=poly q a\<close> by auto
        subgoal using q_deg by (simp add: degree_add_le degree_pcompose)
        subgoal using pcompose_eq_0 q_deg by fastforce
        done
      show "finite (proots_within bbq A)" using \<open>bbq\<noteq>0\<close> by simp
      show "finite (proots_within pq A)" unfolding pq_def 
        by (metis \<open>p \<noteq> 0\<close> finite_proots pcompose_eq_0 q_deg zero_less_one) 
      have bbq_a:"proots_within bbq A = {a}"
      proof -
        have "a\<in>proots_within bbq A" 
          unfolding bb_def proots_within_def poly_pcompose bbq_def 
          using \<open>b=poly q a\<close> \<open>a\<in>A\<close> by simp
        moreover have "card (proots_within bbq A) = 1" 
        proof -
          have "card (proots_within bbq A) \<noteq>0" 
            using \<open>a\<in>proots_within bbq A\<close> \<open>finite (proots_within bbq A)\<close>
            by auto
          moreover have "card (proots_within bbq A) \<le> 1" 
            by (meson \<open>bbq \<noteq> 0\<close> card_proots_within_leq le_trans proots_count_leq_degree bbq_deg)
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis by (metis card_1_singletonE singletonD)
      qed
      show "proots_within (bbq) A \<inter> proots_within (pq) A = {}" 
        using bbq_a \<open>b = poly q a\<close> that(2) unfolding pq_def by (simp add:poly_pcompose)
      show "1 + card (proots_within pq A) = card (proots_within bbq A) + card (proots_within pq A)"
        using bbq_a by simp
    qed
    finally show ?thesis unfolding bb_def .
  qed
  ultimately show ?case by auto
qed

end