(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in algebra\<close>

theory Missing_Algebraic imports
  "HOL-Computational_Algebra.Polynomial_Factorial"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  "HOL-Analysis.Analysis"
  Missing_Topology
  "Budan_Fourier.BF_Misc"
begin

subsection \<open>Misc\<close>

lemma poly_holomorphic_on[simp]:
  "(poly p) holomorphic_on s"
  apply (rule holomorphic_onI)
  apply (unfold field_differentiable_def)
  apply (rule_tac x="poly (pderiv p) x" in exI)
  by (simp add:has_field_derivative_at_within)

lemma order_zorder:
  fixes p::"complex poly" and z::complex
  assumes "p\<noteq>0"
  shows "order z p = nat (zorder (poly p) z)"
proof -
  define n where "n=nat (zorder (poly p) z)" 
  define h where "h=zor_poly (poly p) z"
  have "\<exists>w. poly p w \<noteq> 0" using assms poly_all_0_iff_0 by auto
  then obtain r where "0 < r" "cball z r \<subseteq> UNIV" and 
      h_holo: "h holomorphic_on cball z r" and
      poly_prod:"(\<forall>w\<in>cball z r. poly p w = h w * (w - z) ^ n \<and> h w \<noteq> 0)"
    using zorder_exist_zero[of "poly p" UNIV z,folded h_def] poly_holomorphic_on
    unfolding n_def by auto
  then have "h holomorphic_on ball z r"
    and "(\<forall>w\<in>ball z r. poly p w = h w * (w - z) ^ n)" 
    and "h z\<noteq>0"
    by auto
  then have "order z p = n" using \<open>p\<noteq>0\<close>
  proof (induct n arbitrary:p h)
    case 0
    then have "poly p z=h z" using \<open>r>0\<close> by auto 
    then have "poly p z\<noteq>0" using \<open>h z\<noteq>0\<close> by auto
    then show ?case using order_root by blast
  next
    case (Suc n)
    define sn where "sn=Suc n"
    define h' where "h'\<equiv> \<lambda>w. deriv h w * (w-z)+ sn * h w"
    have "(poly p has_field_derivative poly (pderiv p) w) (at w)" for w
      using poly_DERIV[of p w] .
    moreover have "(poly p has_field_derivative (h' w)*(w-z)^n ) (at w)" when "w\<in>ball z r" for w
    proof (subst DERIV_cong_ev[of w w "poly p" "\<lambda>w.  h w * (w - z) ^ Suc n" ],simp_all)
      show "\<forall>\<^sub>F x in nhds w. poly p x = h x * ((x - z) * (x - z) ^ n)"
        unfolding eventually_nhds using Suc(3) \<open>w\<in>ball z r\<close>
        apply (intro exI[where x="ball z r"])
        by auto
      next
        have "(h has_field_derivative deriv h w) (at w)" 
          using \<open>h holomorphic_on ball z r\<close> \<open>w\<in>ball z r\<close> holomorphic_on_imp_differentiable_at 
          by (simp add: holomorphic_derivI)
        then have "((\<lambda>w. h w * ((w - z) ^ sn)) 
                      has_field_derivative h' w * (w - z) ^ (sn - 1)) (at w)"
          unfolding h'_def
          apply (auto intro!: derivative_eq_intros simp add:field_simps)
          by (auto simp add:field_simps sn_def)
        then show "((\<lambda>w. h w * ((w - z) * (w - z) ^ n)) 
                      has_field_derivative h' w * (w - z) ^ n) (at w)"
          unfolding sn_def by auto
      qed
    ultimately have "\<forall>w\<in>ball z r. poly (pderiv p) w = h' w * (w - z) ^ n"
      using DERIV_unique by blast  
    moreover have "h' holomorphic_on ball z r"
      unfolding h'_def using \<open>h holomorphic_on ball z r\<close>
      by (auto intro!: holomorphic_intros)
    moreover have "h' z\<noteq>0" unfolding h'_def sn_def using \<open>h z \<noteq> 0\<close> of_nat_neq_0 by auto
    moreover have "pderiv p \<noteq> 0"  
    proof 
      assume "pderiv p = 0"
      obtain c where "p=[:c:]" using \<open>pderiv p = 0\<close> using pderiv_iszero by blast
      then have "c=0"
        using Suc(3)[rule_format,of z] \<open>r>0\<close> by auto
      then show False using \<open>p\<noteq>0\<close> using \<open>p=[:c:]\<close> by auto
    qed
    ultimately have "order z (pderiv p) = n" by (auto elim: Suc.hyps)
    moreover have "order z p \<noteq> 0"
      using Suc(3)[rule_format,of z] \<open>r>0\<close> order_root \<open>p\<noteq>0\<close> by auto
    ultimately show ?case using order_pderiv[OF \<open>pderiv p \<noteq> 0\<close>] by auto
  qed
  then show ?thesis unfolding n_def .
qed  

lemma pcompose_pCons_0:"pcompose p [:a:] = [:poly p a:]"
  apply (induct p)
  by (auto simp add:pcompose_pCons algebra_simps)       
   
lemma pcompose_coeff_0:
  "coeff (pcompose p q) 0 = poly p (coeff q 0)"
  apply (induct p)
  by (auto simp add:pcompose_pCons coeff_mult)  
    
lemma poly_field_differentiable_at[simp]:
  "poly p field_differentiable (at x within s)"
apply (unfold field_differentiable_def)
apply (rule_tac x="poly (pderiv p) x" in exI)
by (simp add:has_field_derivative_at_within)  
  
lemma deriv_pderiv:
  "deriv (poly p) = poly (pderiv p)"
apply (rule ext)  
apply (rule DERIV_imp_deriv)  
  using poly_DERIV . 
    
lemma lead_coeff_map_poly_nz:
  assumes "f (lead_coeff p) \<noteq>0" "f 0=0"
  shows "lead_coeff (map_poly f p) = f (lead_coeff p) "
proof -
  have "lead_coeff (Poly (map f (coeffs p))) = f (lead_coeff p)"
    by (metis (mono_tags, lifting) antisym assms(1) assms(2) coeff_0_degree_minus_1 coeff_map_poly 
        degree_Poly degree_eq_length_coeffs le_degree length_map map_poly_def)
  then show ?thesis
    by (simp add: map_poly_def)
qed 

lemma filterlim_poly_at_infinity:
  fixes p::"'a::real_normed_field poly"
  assumes "degree p>0"
  shows "filterlim (poly p) at_infinity at_infinity"
using assms
proof (induct p)
  case 0
  then show ?case by auto
next
  case (pCons a p)
  have ?case when "degree p=0"
  proof -
    obtain c where c_def:"p=[:c:]" using \<open>degree p = 0\<close> degree_eq_zeroE by blast
    then have "c\<noteq>0" using \<open>0 < degree (pCons a p)\<close> by auto
    then show ?thesis unfolding c_def 
      apply (auto intro!:tendsto_add_filterlim_at_infinity)
      apply (subst mult.commute)
      by (auto intro!:tendsto_mult_filterlim_at_infinity filterlim_ident)
  qed
  moreover have ?case when "degree p\<noteq>0"
  proof -
    have "filterlim (poly p) at_infinity at_infinity"
      using that by (auto intro:pCons)
    then show ?thesis 
      by (auto intro!:tendsto_add_filterlim_at_infinity filterlim_at_infinity_times filterlim_ident)
  qed
  ultimately show ?case by auto
qed  
       
lemma poly_divide_tendsto_aux:
  fixes p::"'a::real_normed_field poly"
  shows "((\<lambda>x. poly p x/x^(degree p)) \<longlongrightarrow> lead_coeff p) at_infinity"  
proof (induct p)
  case 0
  then show ?case by (auto intro:tendsto_eq_intros)
next
  case (pCons a p)
  have ?case when "p=0"
    using that by auto
  moreover have ?case when "p\<noteq>0"
  proof -
    define g where "g=(\<lambda>x. a/(x*x^degree p))"
    define f where "f=(\<lambda>x. poly p x/x^degree p)"
    have "\<forall>\<^sub>Fx in at_infinity. poly (pCons a p) x / x ^ degree (pCons a p) = g x + f x"
    proof (rule eventually_at_infinityI[of 1])
      fix x::'a assume "norm x\<ge>1"
      then have "x\<noteq>0" by auto
      then show "poly (pCons a p) x / x ^ degree (pCons a p) = g x + f x"
        using that unfolding g_def f_def by (auto simp add:field_simps)
    qed
    moreover have "((\<lambda>x. g x+f x) \<longlongrightarrow>  lead_coeff (pCons a p)) at_infinity"
    proof -
      have "(g \<longlongrightarrow>  0) at_infinity"
        unfolding g_def using filterlim_poly_at_infinity[of "monom 1 (Suc (degree p))"]
        apply (auto intro!:tendsto_intros tendsto_divide_0 simp add: degree_monom_eq)
        apply (subst filterlim_cong[where g="poly (monom 1 (Suc (degree p)))"])
        by (auto simp add:poly_monom)
      moreover have "(f \<longlongrightarrow>  lead_coeff (pCons a p)) at_infinity"
        using pCons \<open>p\<noteq>0\<close> unfolding f_def by auto
      ultimately show ?thesis by (auto intro:tendsto_eq_intros)
    qed
    ultimately show ?thesis by (auto dest:tendsto_cong)  
  qed
  ultimately show ?case by auto  
qed
  
lemma filterlim_power_at_infinity:
  assumes "n\<noteq>0"
  shows "filterlim (\<lambda>x::'a::real_normed_field. x^n) at_infinity at_infinity" 
  using filterlim_poly_at_infinity[of "monom 1 n"] assms
  apply (subst filterlim_cong[where g="poly (monom 1 n)"])
  by (auto simp add:poly_monom degree_monom_eq)
   
lemma poly_divide_tendsto_0_at_infinity: 
  fixes p::"'a::real_normed_field poly"
  assumes "degree p > degree q" 
  shows "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0 ) at_infinity" 
proof -
  define pp where "pp=(\<lambda>x. x^(degree p) / poly p x)"    
  define qq where "qq=(\<lambda>x. poly q x/x^(degree q))"
  define dd where "dd=(\<lambda>x::'a. 1/x^(degree p - degree q))"
  have "\<forall>\<^sub>Fx in at_infinity.  poly q x / poly p x = qq x * pp x * dd x"
  proof (rule eventually_at_infinityI[of 1])
    fix x::'a assume "norm x\<ge>1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x * pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps divide_simps power_diff) 
  qed
  moreover have "((\<lambda>x. qq x * pp x * dd x) \<longlongrightarrow> 0) at_infinity"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_infinity" 
      unfolding qq_def using poly_divide_tendsto_aux[of q] .
    moreover have "(pp \<longlongrightarrow> 1/lead_coeff p) at_infinity"
    proof -
      have "p\<noteq>0" using assms by auto
      then show ?thesis
        unfolding pp_def using poly_divide_tendsto_aux[of p] 
        apply (drule_tac tendsto_inverse)
        by (auto simp add:inverse_eq_divide)
    qed  
    moreover have "(dd \<longlongrightarrow> 0) at_infinity" 
      unfolding dd_def
      apply (rule tendsto_divide_0)
      by (auto intro!: filterlim_power_at_infinity simp add:assms)
    ultimately show ?thesis by (auto intro:tendsto_eq_intros)
  qed
  ultimately show ?thesis by (auto dest:tendsto_cong)
qed
    
lemma lead_coeff_list_def:
  "lead_coeff p= (if coeffs p=[] then 0 else last (coeffs p))"
by (simp add: last_coeffs_eq_coeff_degree)
  
lemma poly_linepath_comp: 
  fixes a::"'a::{real_normed_vector,comm_semiring_0,real_algebra_1}"
  shows "poly p o (linepath a b) = poly (p \<circ>\<^sub>p [:a, b-a:]) o of_real"
  apply rule
  by (auto simp add:poly_pcompose linepath_def scaleR_conv_of_real algebra_simps)

lemma poly_eventually_not_zero:
  fixes p::"real poly"
  assumes "p\<noteq>0"
  shows "eventually (\<lambda>x. poly p x\<noteq>0) at_infinity"
proof (rule eventually_at_infinityI[of "Max (norm ` {x. poly p x=0}) + 1"])
  fix x::real assume asm:"Max (norm ` {x. poly p x=0}) + 1 \<le> norm x" 
  have False when "poly p x=0"
  proof - 
    define S where "S=norm `{x. poly p x = 0}"
    have "norm x\<in>S" using that unfolding S_def by auto
    moreover have "finite S" using \<open>p\<noteq>0\<close> poly_roots_finite unfolding S_def by blast
    ultimately have "norm x\<le>Max S" by simp
    moreover have "Max S + 1 \<le> norm x" using asm unfolding S_def by simp
    ultimately show False by argo
  qed
  then show "poly p x \<noteq> 0" by auto
qed
    
subsection \<open>More about @{term degree}\<close>
   
lemma degree_div_less:
  fixes x y::"'a::field poly"
  assumes "degree x\<noteq>0" "degree y\<noteq>0"
  shows "degree (x div y) < degree x"
proof -
  have "x\<noteq>0" "y\<noteq>0" using assms by auto
  define q r where "q=x div y" and "r=x mod y"
  have *:"eucl_rel_poly x y (q, r)" unfolding q_def r_def 
    by (simp add: eucl_rel_poly)
  then have "r = 0 \<or> degree r < degree y" using \<open>y\<noteq>0\<close> unfolding eucl_rel_poly_iff by auto
  moreover have ?thesis when "r=0"
  proof -
    have "x = q * y" using * that unfolding eucl_rel_poly_iff by auto
    then have "q\<noteq>0" using \<open>x\<noteq>0\<close> \<open>y\<noteq>0\<close> by auto
    from degree_mult_eq[OF this \<open>y\<noteq>0\<close>] \<open>x = q * y\<close> 
    have "degree x = degree q +degree y" by auto
    then show ?thesis unfolding q_def using assms by auto
  qed
  moreover have ?thesis when "degree r<degree y"
  proof (cases "degree y>degree x")
    case True
    then have "q=0" unfolding q_def using div_poly_less by auto
    then show ?thesis unfolding q_def using assms(1) by auto
  next
    case False
    then have "degree x>degree r" using that by auto
    then have "degree x = degree (x-r)" using degree_add_eq_right[of "-r" x] by auto
    have "x-r = q*y" using * unfolding eucl_rel_poly_iff by auto
    then have "q\<noteq>0" using \<open>degree r < degree x\<close> by auto
    have "degree x = degree q +degree y" 
      using  degree_mult_eq[OF \<open>q\<noteq>0\<close> \<open>y\<noteq>0\<close>] \<open>x-r = q*y\<close> \<open>degree x = degree (x-r)\<close> by auto
    then show ?thesis unfolding q_def using assms by auto
  qed
  ultimately show ?thesis by auto
qed  
  
lemma map_poly_degree_eq:
  assumes "f (lead_coeff p) \<noteq>0"
  shows "degree (map_poly f p) = degree p"  
  using assms
  unfolding map_poly_def degree_eq_length_coeffs coeffs_Poly lead_coeff_list_def
  by (metis (full_types) last_conv_nth_default length_map no_trailing_unfold nth_default_coeffs_eq 
      nth_default_map_eq strip_while_idem)
  
lemma map_poly_degree_less:
  assumes "f (lead_coeff p) =0" "degree p\<noteq>0"
  shows "degree (map_poly f p) < degree p" 
proof -
  have "length (coeffs p) >1" 
    using \<open>degree p\<noteq>0\<close> by (simp add: degree_eq_length_coeffs)  
  then obtain xs x where xs_def:"coeffs p=xs@[x]" "length xs>0"  
    by (metis One_nat_def add.commute add_diff_cancel_left' append_Nil assms(2) 
        degree_eq_length_coeffs length_greater_0_conv list.size(3) list.size(4) not_less_zero
        rev_exhaust) 
  have "f x=0" using assms(1) by (simp add: lead_coeff_list_def xs_def(1))
  have "degree (map_poly f p) = length (strip_while ((=) 0) (map f (xs@[x]))) - 1" 
    unfolding map_poly_def degree_eq_length_coeffs coeffs_Poly
    by (subst xs_def,auto)
  also have "... = length (strip_while ((=) 0) (map f xs)) - 1"   
    using \<open>f x=0\<close> by simp
  also have "... \<le> length xs -1"
    using length_strip_while_le by (metis diff_le_mono length_map)
  also have "... < length (xs@[x]) - 1"
    using xs_def(2) by auto
  also have "... = degree p"
    unfolding degree_eq_length_coeffs xs_def by simp
  finally show ?thesis .
qed
  
lemma map_poly_degree_leq[simp]:
  shows "degree (map_poly f p) \<le> degree p"
  unfolding map_poly_def degree_eq_length_coeffs
  by (metis coeffs_Poly diff_le_mono length_map length_strip_while_le)  
    
subsection \<open>roots / zeros of a univariate function\<close>

definition roots_within::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "roots_within f s = {x\<in>s. f x = 0}"
  
abbreviation roots::"('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where
  "roots f \<equiv> roots_within f UNIV"

subsection \<open>The argument principle specialised to polynomials.\<close>

lemma argument_principle_poly:
  assumes "p\<noteq>0" and valid:"valid_path g" and loop: "pathfinish g = pathstart g" 
    and no_proots:"path_image g \<subseteq> - proots p"  
  shows "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
            (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"  
proof -
  have "contour_integral g (\<lambda>x. deriv (poly p) x / poly p x) = 2 * of_real pi * \<i> * 
          (\<Sum>x | poly p x = 0. winding_number g x * of_int (zorder (poly p) x))"
    apply (rule argument_principle[of UNIV "poly p" "{}" "\<lambda>_. 1" g,simplified,OF _ valid loop])
    using no_proots[unfolded proots_def] by (auto simp add:poly_roots_finite[OF \<open>p\<noteq>0\<close>] )
  also have "... =  2 * of_real pi * \<i> * (\<Sum>x\<in>proots p. winding_number g x * of_nat (order x p))"
  proof -
    have "nat (zorder (poly p) x) = order x p" when "x\<in>proots p" for x 
      using order_zorder[OF \<open>p\<noteq>0\<close>] that unfolding proots_def by auto
    then show ?thesis unfolding proots_def 
      apply (auto intro!:comm_monoid_add_class.sum.cong)
      by (metis assms(1) nat_eq_iff2 of_nat_nat order_root)
  qed
  finally show ?thesis . 
qed  
  
end
