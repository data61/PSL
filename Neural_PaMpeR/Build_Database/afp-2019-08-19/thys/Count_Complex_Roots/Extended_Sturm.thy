(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>An alternative Sturm sequences\<close>

theory Extended_Sturm imports 
  "Sturm_Tarski.Sturm_Tarski" 
  "Winding_Number_Eval.Cauchy_Index_Theorem"
begin 
  
text \<open>The main purpose of this theory is to provide an effective way to compute 
  @{term "cindexE a b f"} when @{term f} is a rational function. The idea is similar to and based
  on the evaluation of @{term cindex_poly} through @{thm cindex_poly_changes_itv_mods}.\<close>   
  
text \<open>
This alternative version of remainder sequences is inspired by the paper 
  "The Fundamental Theorem of Algebra made effective: 
  an elementary real-algebraic proof via Sturm chains" 
by Michael Eisermann.
\<close>  
  
hide_const Permutations.sign  
  
subsection \<open>Misc\<close>
   
lemma is_unit_pCons_ex_iff:
  fixes p::"'a::field poly"
  shows "is_unit p \<longleftrightarrow> (\<exists>a. a\<noteq>0 \<and> p=[:a:])"
  using is_unit_poly_iff is_unit_triv by auto

lemma poly_gcd_iff: 
  "poly (gcd p q) x=0 \<longleftrightarrow> poly p x=0 \<and> poly q x=0 "
  by (simp add: poly_eq_0_iff_dvd)
  
lemma eventually_poly_nz_at_within:
  fixes x :: "'a::{idom,euclidean_space} "
  assumes "p\<noteq>0" 
  shows "eventually (\<lambda>x. poly p x\<noteq>0) (at x within S)"     
proof -
  have "eventually (\<lambda>x. poly p x\<noteq>0) (at x within S) 
      = (\<forall>\<^sub>F x in (at x within S). \<forall>y\<in>proots p. x \<noteq> y)"
    apply (rule eventually_subst,rule eventuallyI)
    by (auto simp add:proots_def)
  also have "... = (\<forall>y\<in>proots p. \<forall>\<^sub>F x in (at x within S). x \<noteq> y)"
    apply (subst eventually_ball_finite_distrib)
    using \<open>p\<noteq>0\<close> by auto
  also have "..."
    unfolding eventually_at
    by (metis gt_ex not_less_iff_gr_or_eq zero_less_dist_iff) 
  finally show ?thesis .
qed
    
lemma sgn_power:
  fixes x::"'a::linordered_idom"
  shows "sgn (x^n) = (if n=0 then 1 else if even n then \<bar>sgn x\<bar> else sgn x)"
  apply (induct n)
  by (auto simp add:sgn_mult)

lemma poly_divide_filterlim_at_top: 
  fixes p q::"real poly"
  defines "ll\<equiv>( if degree q<degree p then 
                    at 0 
                else if degree q=degree p then 
                    nhds (lead_coeff q / lead_coeff p)
                else if sgn_pos_inf q * sgn_pos_inf p > 0 then 
                    at_top
                else 
                    at_bot)"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "filterlim (\<lambda>x. poly q x / poly p x) ll at_top"
proof -
  define pp where "pp=(\<lambda>x. poly p x / x^(degree p))"    
  define qq where "qq=(\<lambda>x. poly q x / x^(degree q))"
  define dd where "dd=(\<lambda>x::real. if degree p>degree q then 1/x^(degree p - degree q) else 
                                x^(degree q - degree p))"
  have divide_cong:"\<forall>\<^sub>Fx in at_top. poly q x / poly p x = qq x / pp x * dd x"
  proof (rule eventually_at_top_linorderI[of 1])
    fix x assume "(x::real)\<ge>1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x / pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps power_diff) 
  qed
  have qqpp_tendsto:"((\<lambda>x. qq x / pp x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_top"
      unfolding qq_def using poly_divide_tendsto_aux[of q]  
      by (auto elim!:filterlim_mono simp:at_top_le_at_infinity)
    moreover have "(pp \<longlongrightarrow> lead_coeff p) at_top"
      unfolding pp_def using poly_divide_tendsto_aux[of p]  
      by (auto elim!:filterlim_mono simp:at_top_le_at_infinity)
    ultimately show ?thesis using \<open>p\<noteq>0\<close> by (auto intro!:tendsto_eq_intros)
  qed
  
  have ?thesis when "degree q<degree p"
  proof -
    have "filterlim (\<lambda>x. poly q x / poly p x) (at 0) at_top"
    proof (rule filterlim_atI)
      show "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0) at_top"
        using poly_divide_tendsto_0_at_infinity[OF that]
        by (auto elim:filterlim_mono simp:at_top_le_at_infinity)
      have "\<forall>\<^sub>F x in at_top. poly q x \<noteq>0" "\<forall>\<^sub>F x in at_top. poly p x \<noteq>0"
        using poly_eventually_not_zero[OF \<open>q\<noteq>0\<close>] poly_eventually_not_zero[OF \<open>p\<noteq>0\<close>]
              filter_leD[OF at_top_le_at_infinity]
        by auto
      then show "\<forall>\<^sub>F x in at_top. poly q x / poly p x \<noteq> 0"
        apply eventually_elim
        by auto
    qed
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q=degree p"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
      using divide_cong qqpp_tendsto that unfolding dd_def
      by (auto dest:tendsto_cong)
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q>degree p" "sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_top"
    proof (subst filterlim_tendsto_pos_mult_at_top_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using that(2) unfolding sgn_pos_inf_def
        by (simp add: zero_less_divide_iff zero_less_mult_iff)
      show "filterlim dd at_top at_top"
        unfolding dd_def using that(1) 
        by (auto intro!:filterlim_pow_at_top simp:filterlim_ident)
    qed
    then have "LIM x at_top. poly q x / poly p x :> at_top" 
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis  when "degree q>degree p" "\<not> sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_top"
    proof (subst filterlim_tendsto_neg_mult_at_bot_iff[OF qqpp_tendsto])
      show "lead_coeff q / lead_coeff p < 0" 
        using that(2) \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_pos_inf_def
        by (metis divide_eq_0_iff divide_sgn leading_coeff_0_iff 
            linorder_neqE_linordered_idom sgn_divide sgn_greater)
      show "filterlim dd at_top at_top"
        unfolding dd_def using that(1) 
        by (auto intro!:filterlim_pow_at_top simp:filterlim_ident)
    qed
    then have "LIM x at_top. poly q x / poly p x :> at_bot" 
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  ultimately show ?thesis by linarith
qed

lemma poly_divide_filterlim_at_bot: 
  fixes p q::"real poly"
  defines "ll\<equiv>( if degree q<degree p then 
                    at 0 
                else if degree q=degree p then 
                    nhds (lead_coeff q / lead_coeff p)
                else if sgn_neg_inf q * sgn_neg_inf p > 0 then 
                    at_top
                else 
                    at_bot)"
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "filterlim (\<lambda>x. poly q x / poly p x) ll at_bot"
proof -
  define pp where "pp=(\<lambda>x. poly p x / x^(degree p))"    
  define qq where "qq=(\<lambda>x. poly q x / x^(degree q))"
  define dd where "dd=(\<lambda>x::real. if degree p>degree q then 1/x^(degree p - degree q) else 
                                x^(degree q - degree p))"
  have divide_cong:"\<forall>\<^sub>Fx in at_bot. poly q x / poly p x = qq x / pp x * dd x"
  proof (rule eventually_at_bot_linorderI[of "-1"])
    fix x assume "(x::real)\<le>-1"
    then have "x\<noteq>0" by auto
    then show "poly q x / poly p x = qq x / pp x * dd x"
      unfolding qq_def pp_def dd_def using assms 
      by (auto simp add:field_simps power_diff) 
  qed
  have qqpp_tendsto:"((\<lambda>x. qq x / pp x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
  proof -
    have "(qq \<longlongrightarrow> lead_coeff q) at_bot"
      unfolding qq_def using poly_divide_tendsto_aux[of q]  
      by (auto elim!:filterlim_mono simp:at_bot_le_at_infinity)
    moreover have "(pp \<longlongrightarrow> lead_coeff p) at_bot"
      unfolding pp_def using poly_divide_tendsto_aux[of p]  
      by (auto elim!:filterlim_mono simp:at_bot_le_at_infinity)
    ultimately show ?thesis using \<open>p\<noteq>0\<close> by (auto intro!:tendsto_eq_intros)
  qed
  
  have ?thesis when "degree q<degree p"
  proof -
    have "filterlim (\<lambda>x. poly q x / poly p x) (at 0) at_bot"
    proof (rule filterlim_atI)
      show "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> 0) at_bot"
        using poly_divide_tendsto_0_at_infinity[OF that]
        by (auto elim:filterlim_mono simp:at_bot_le_at_infinity)
      have "\<forall>\<^sub>F x in at_bot. poly q x \<noteq>0" "\<forall>\<^sub>F x in at_bot. poly p x \<noteq>0"
        using poly_eventually_not_zero[OF \<open>q\<noteq>0\<close>] poly_eventually_not_zero[OF \<open>p\<noteq>0\<close>]
              filter_leD[OF at_bot_le_at_infinity]
        by auto
      then show "\<forall>\<^sub>F x in at_bot. poly q x / poly p x \<noteq> 0"
        by eventually_elim auto
    qed
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q=degree p"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
      using divide_cong qqpp_tendsto that unfolding dd_def
      by (auto dest:tendsto_cong)
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis when "degree q>degree p" "sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    define cc where "cc=lead_coeff q / lead_coeff p"
    have "(cc > 0 \<and> even (degree q - degree p)) \<or> (cc<0 \<and> odd (degree q - degree p))"
    proof -
      have "even (degree q - degree p) \<longleftrightarrow> 
            (even (degree q) \<and> even (degree p)) \<or> (odd (degree q) \<and> odd (degree p))"
        using \<open>degree q>degree p\<close> by auto
      then show ?thesis
        using that \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_neg_inf_def cc_def zero_less_mult_iff 
          divide_less_0_iff zero_less_divide_iff 
        apply (simp add:if_split[of "(<) 0"] if_split[of "(>) 0"])
        by argo
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      when "cc>0" "even (degree q - degree p)"
    proof (subst filterlim_tendsto_pos_mult_at_top_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using \<open>cc>0\<close> unfolding cc_def by auto
      show "filterlim dd at_top at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_even simp:filterlim_ident)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      when "cc<0" "odd (degree q - degree p)"
    proof (subst filterlim_tendsto_neg_mult_at_top_iff[OF qqpp_tendsto])
      show "0 > lead_coeff q / lead_coeff p" using \<open>cc<0\<close> unfolding cc_def by auto
      show "filterlim dd at_bot at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_odd simp:filterlim_ident)
    qed
    ultimately have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_top at_bot"
      by blast
    then have "LIM x at_bot. poly q x / poly p x :> at_top"
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  moreover have ?thesis  when "degree q>degree p" "\<not> sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    define cc where "cc=lead_coeff q / lead_coeff p"
    have "(cc < 0 \<and> even (degree q - degree p)) \<or> (cc > 0 \<and> odd (degree q - degree p))"
    proof -
      have "even (degree q - degree p) \<longleftrightarrow> 
            (even (degree q) \<and> even (degree p)) \<or> (odd (degree q) \<and> odd (degree p))"
        using \<open>degree q>degree p\<close> by auto
      then show ?thesis
        using that \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> unfolding sgn_neg_inf_def cc_def zero_less_mult_iff 
          divide_less_0_iff zero_less_divide_iff
        apply (simp add:if_split[of "(<) 0"] if_split[of "(>) 0"])
        by (metis leading_coeff_0_iff linorder_neqE_linordered_idom)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      when "cc<0" "even (degree q - degree p)"
    proof (subst filterlim_tendsto_neg_mult_at_bot_iff[OF qqpp_tendsto])
      show "0 > lead_coeff q / lead_coeff p" using \<open>cc<0\<close> unfolding cc_def by auto
      show "filterlim dd at_top at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_even simp:filterlim_ident)
    qed
    moreover have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      when "cc>0" "odd (degree q - degree p)"
    proof (subst filterlim_tendsto_pos_mult_at_bot_iff[OF qqpp_tendsto])
      show "0 < lead_coeff q / lead_coeff p" using \<open>cc>0\<close> unfolding cc_def by auto
      show "filterlim dd at_bot at_bot"
        unfolding dd_def using \<open>degree q>degree p\<close> that(2)
        by (auto intro!:filterlim_pow_at_bot_odd simp:filterlim_ident)
    qed
    ultimately have "filterlim (\<lambda>x. (qq x / pp x) * dd x) at_bot at_bot"
      by blast
    then have "LIM x at_bot. poly q x / poly p x :> at_bot"
      using filterlim_cong[OF _ _ divide_cong] by blast
    then show ?thesis unfolding ll_def using that by auto
  qed
  ultimately show ?thesis by linarith
qed
        
subsection \<open>Alternative definition of cross\<close>
 
definition cross_alt :: "real poly \<Rightarrow>real poly \<Rightarrow> real \<Rightarrow> real \<Rightarrow> int" where
  "cross_alt p q a b=\<bar>sign (poly p a) - sign (poly q a)\<bar> - \<bar>sign (poly p b) - sign(poly q b)\<bar>"  

lemma cross_alt_coprime_0:
  assumes "coprime p q" "p=0\<or>q=0"
  shows "cross_alt p q a b=0" 
proof -
  have ?thesis when "p=0" 
  proof -
    have "is_unit q" using that \<open>coprime p q\<close> 
      by simp
    then obtain a where "a\<noteq>0" "q=[:a:]" using is_unit_pCons_ex_iff by blast
    then show ?thesis using that unfolding cross_alt_def by auto
  qed
  moreover have ?thesis when "q=0" 
  proof -
    have "is_unit p" using that \<open>coprime p q\<close> 
      by simp
    then obtain a where "a\<noteq>0" "p=[:a:]" using is_unit_pCons_ex_iff by blast
    then show ?thesis using that unfolding cross_alt_def by auto
  qed 
  ultimately show ?thesis using \<open>p=0\<or>q=0\<close> by auto
qed  
  
lemma cross_alt_0[simp]: "cross_alt 0 0 a b=0" unfolding cross_alt_def by auto 
  
lemma cross_alt_poly_commute:
  "cross_alt p q a b = cross_alt q p a b"
  unfolding cross_alt_def by auto
    
lemma cross_alt_clear_n:
  assumes "coprime p q"
  shows "cross_alt p q a b = cross_alt 1 (p*q) a b"
proof -
  have "\<bar>sign (poly p a) - sign (poly q a)\<bar>  = \<bar>1 - sign (poly p a) * sign (poly q a)\<bar>"
  proof (cases "poly p a=0 \<and> poly q a=0")
    case True
    then have False using assms using coprime_poly_0 by blast
    then show ?thesis by auto
  next
    case False
    then show ?thesis 
      unfolding Sturm_Tarski.sign_def
      by force
  qed
  moreover have "\<bar>sign (poly p b) - sign (poly q b)\<bar>  = \<bar>1 - sign (poly p b) * sign (poly q b)\<bar>"
  proof (cases "poly p b=0 \<and> poly q b=0")
    case True
    then have False using assms using coprime_poly_0 by blast
    then show ?thesis by auto
  next
    case False
    then show ?thesis 
      unfolding Sturm_Tarski.sign_def
      by force
  qed  
  ultimately show ?thesis 
    unfolding cross_alt_def      
    by (simp only:sign_times poly_mult poly_1 sign_simps)
qed   
  
subsection \<open>Alternative sign variation sequencse\<close>  
  
fun changes_alt:: "('a ::linordered_idom) list \<Rightarrow> int" where
  "changes_alt [] = 0"|
  "changes_alt [_] = 0" |
  "changes_alt (x1#x2#xs) = abs(sign x1 - sign x2) + changes_alt (x2#xs)"  
  
definition changes_alt_poly_at::"('a ::linordered_idom) poly list \<Rightarrow> 'a \<Rightarrow> int" where
  "changes_alt_poly_at ps a= changes_alt (map (\<lambda>p. poly p a) ps)"

definition changes_alt_itv_smods:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_alt_itv_smods a b p q= (let ps= smods p q 
                                    in changes_alt_poly_at ps a - changes_alt_poly_at ps b)"  
 
lemma changes_alt_itv_smods_rec:
  assumes "a<b" "coprime p q" 
  shows "changes_alt_itv_smods a b p q  = cross_alt p q a b + changes_alt_itv_smods a b q (-(p mod q))"
proof (cases "p = 0 \<or> q = 0 \<or> q dvd p")
  case True
  moreover have "p=0 \<or> q=0 \<Longrightarrow> ?thesis"
    using cross_alt_coprime_0[OF \<open>coprime p q\<close>] 
    unfolding changes_alt_itv_smods_def changes_alt_poly_at_def by fastforce
  moreover have "\<lbrakk>p\<noteq>0;q\<noteq>0;p mod q = 0\<rbrakk> \<Longrightarrow> ?thesis"  
    unfolding changes_alt_itv_smods_def changes_alt_poly_at_def cross_alt_def
    by (simp add:sign_times)
  ultimately show ?thesis
    by auto (auto elim: dvdE)
next
  case False
  hence "p\<noteq>0" "q\<noteq>0" "p mod q\<noteq>0" by auto
  then obtain ps where ps:"smods p q=p#q#-(p mod q)#ps" "smods q (-(p mod q)) = q#-(p mod q)#ps"
    by auto
  define changes_diff where "changes_diff\<equiv>\<lambda>x. changes_alt_poly_at (p#q#-(p mod q)#ps) x 
    - changes_alt_poly_at (q#-(p mod q)#ps) x"
  have "changes_diff a - changes_diff b=cross_alt p q a b" 
    unfolding changes_diff_def changes_alt_poly_at_def cross_alt_def by simp
  thus ?thesis unfolding changes_alt_itv_smods_def changes_diff_def changes_alt_poly_at_def ps 
    by force
qed  
  
subsection \<open>jumpF on polynomials\<close>

definition jumpF_polyR:: "real poly \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real" where
  "jumpF_polyR q p a = jumpF (\<lambda>x. poly q x / poly p x) (at_right a)"
  
definition jumpF_polyL:: "real poly \<Rightarrow> real poly \<Rightarrow> real \<Rightarrow> real" where
  "jumpF_polyL q p a = jumpF (\<lambda>x. poly q x / poly p x) (at_left a)"

definition jumpF_poly_top:: "real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "jumpF_poly_top q p = jumpF (\<lambda>x. poly q x / poly p x) at_top"

definition jumpF_poly_bot:: "real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "jumpF_poly_bot q p = jumpF (\<lambda>x. poly q x / poly p x) at_bot"

  
lemma jumpF_polyR_0[simp]: "jumpF_polyR 0 p a = 0" "jumpF_polyR q 0 a = 0" 
  unfolding jumpF_polyR_def by auto
    
lemma jumpF_polyL_0[simp]: "jumpF_polyL 0 p a = 0" "jumpF_polyL q 0 a = 0" 
  unfolding jumpF_polyL_def by auto
    
lemma jumpF_polyR_mult_cancel:
  assumes "p'\<noteq>0"
  shows "jumpF_polyR (p' * q) (p' * p) a = jumpF_polyR q p a"
unfolding jumpF_polyR_def
proof (rule jumpF_cong)
  obtain ub where "a < ub" "\<forall>z. a < z \<and> z \<le> ub \<longrightarrow> poly p' z \<noteq> 0"
    using next_non_root_interval[OF \<open>p'\<noteq>0\<close>,of a] by auto
  then show "\<forall>\<^sub>F x in at_right a. poly (p' * q) x / poly (p' * p) x = poly q x / poly p x"
    apply (unfold eventually_at_right)
    apply (intro exI[where x=ub])
    by auto
qed simp
  
lemma jumpF_polyL_mult_cancel:
  assumes "p'\<noteq>0"
  shows "jumpF_polyL (p' * q) (p' * p) a = jumpF_polyL q p a"
unfolding jumpF_polyL_def
proof (rule jumpF_cong)
  obtain lb where "lb < a" "\<forall>z. lb \<le> z \<and> z < a \<longrightarrow> poly p' z \<noteq> 0 "
    using last_non_root_interval[OF \<open>p'\<noteq>0\<close>,of a] by auto
  then show "\<forall>\<^sub>F x in at_left a. poly (p' * q) x / poly (p' * p) x = poly q x / poly p x"
    apply (unfold eventually_at_left)
    apply (intro exI[where x=lb])
    by auto
qed simp  
      
lemma jumpF_poly_noroot: 
  assumes "poly p a\<noteq>0"
  shows "jumpF_polyL q p a = 0" "jumpF_polyR q p a = 0" 
  subgoal unfolding jumpF_polyL_def using assms
    apply (intro jumpF_not_infinity)
    by (auto intro!:continuous_intros)  
  subgoal unfolding jumpF_polyR_def using assms
    apply (intro jumpF_not_infinity)
    by (auto intro!:continuous_intros)
  done
  

lemma jumpF_polyR_coprime:
  assumes "coprime p q"
  shows "jumpF_polyR q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                                if sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"
proof (cases "p=0 \<or> q=0 \<or> poly p x\<noteq>0")
  case True
  then show ?thesis using jumpF_poly_noroot by fastforce
next
  case False
  then have asm:"p\<noteq>0" "q\<noteq>0" "poly p x=0" by auto  
  then have "poly q x\<noteq>0" using assms using coprime_poly_0 by blast
  have ?thesis when "sign_r_pos p x \<longleftrightarrow> poly q x>0"
  proof -
    have "(poly p has_sgnx sgn (poly q x)) (at_right x)"
      by (metis False \<open>poly q x \<noteq> 0\<close> add.inverse_neutral has_sgnx_imp_sgnx less_not_sym 
          neg_less_iff_less poly_has_sgnx_values(2) sgn_if sign_r_pos_sgnx_iff that 
          trivial_limit_at_right_real zero_less_one)
    then have "LIM x at_right x. poly q x / poly p x :> at_top"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(3))
    then have "jumpF_polyR q p x = 1/2"
      unfolding jumpF_polyR_def jumpF_def by auto
    then show ?thesis using that False by auto
  qed
  moreover have ?thesis when "\<not> (sign_r_pos p x \<longleftrightarrow> poly q x>0)"
  proof -
    have "(poly p has_sgnx - sgn (poly q x)) (at_right x)"
    proof -
      have "(0::real) < 1 \<or> \<not> (1::real) < 0 \<and> sign_r_pos p x 
          \<or> (poly p has_sgnx - sgn (poly q x)) (at_right x)"
        by simp
      then show ?thesis
        by (metis (no_types) False \<open>poly q x \<noteq> 0\<close> add.inverse_inverse has_sgnx_imp_sgnx 
            neg_less_0_iff_less poly_has_sgnx_values(2) sgn_if sgn_less sign_r_pos_sgnx_iff 
            that trivial_limit_at_right_real)
    qed
    then have "LIM x at_right x. poly q x / poly p x :> at_bot"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(3)) 
    then have "jumpF_polyR q p x = - 1/2"
      unfolding jumpF_polyR_def jumpF_def by auto
    then show ?thesis using that False by auto  
  qed
  ultimately show ?thesis by auto
qed

lemma jumpF_polyL_coprime:
  assumes "coprime p q"
  shows "jumpF_polyL q p x = (if p \<noteq> 0 \<and> q \<noteq> 0 \<and> poly p x=0 then 
                if even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0 then 1/2 else - 1/2 else 0)"  
proof (cases "p=0 \<or> q=0 \<or> poly p x\<noteq>0")
  case True
  then show ?thesis using jumpF_poly_noroot by fastforce
next  
  case False
  then have asm:"p\<noteq>0" "q\<noteq>0" "poly p x=0" by auto  
  then have "poly q x\<noteq>0" using assms using coprime_poly_0 by blast
  have ?thesis when "even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0"
  proof -
    consider (lt) "poly q x>0" | (gt) " poly q x<0" using \<open>poly q x\<noteq>0\<close> by linarith
    then have "sgnx (poly p) (at_left x) = sgn (poly q x)"
      apply cases
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      done
    then have "(poly p has_sgnx sgn (poly q x)) (at_left x)"
      by (metis sgnx_able_poly(2) sgnx_able_sgnx)
    then have "LIM x at_left x. poly q x / poly p x :> at_top"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(2))   
    then have "jumpF_polyL q p x = 1/2"
      unfolding jumpF_polyL_def jumpF_def by auto
    then show ?thesis using that False by auto
  qed
  moreover have ?thesis when "\<not> (even (order x p) \<longleftrightarrow> sign_r_pos p x \<longleftrightarrow> poly q x>0)"
  proof -
    consider (lt) "poly q x>0" | (gt) " poly q x<0" using \<open>poly q x\<noteq>0\<close> by linarith
    then have "sgnx (poly p) (at_left x) = - sgn (poly q x)"
      apply cases
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      subgoal using that sign_r_pos_sgnx_iff poly_sgnx_values[OF \<open>p\<noteq>0\<close>,of x]
        apply (subst poly_sgnx_left_right[OF \<open>p\<noteq>0\<close>])
        by auto
      done
    then have "(poly p has_sgnx - sgn (poly q x)) (at_left x)"
      by (metis sgnx_able_poly(2) sgnx_able_sgnx)
    then have "LIM x at_left x. poly q x / poly p x :> at_bot"    
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "poly q x"])
      apply (auto simp add:\<open>poly q x\<noteq>0\<close>)
      by (metis asm(3) poly_tendsto(2))   
    then have "jumpF_polyL q p x = - 1/2"
      unfolding jumpF_polyL_def jumpF_def by auto
    then show ?thesis using that False by auto 
  qed
  ultimately show ?thesis by auto
qed    
    
lemma jumpF_times:
  assumes tendsto:"(f \<longlongrightarrow> c) F" and "c\<noteq>0" "F\<noteq>bot"
  shows "jumpF (\<lambda>x. f x * g x) F = sgn c * jumpF g F"  
proof -
  have "c>0 \<or> c<0" using \<open>c\<noteq>0\<close> by auto
  moreover have ?thesis when "c>0"
  proof -
    note filterlim_tendsto_pos_mult_at_top_iff[OF tendsto \<open>c>0\<close>,of g]
    moreover note filterlim_tendsto_pos_mult_at_bot_iff[OF tendsto \<open>c>0\<close>,of g]
    moreover have "sgn c = 1" using \<open>c>0\<close> by auto
    ultimately show ?thesis unfolding jumpF_def by auto
  qed
  moreover have ?thesis when "c<0"
  proof -
    define atbot where "atbot = filterlim g at_bot F"
    define attop where "attop = filterlim g at_top F"    
    have "jumpF (\<lambda>x. f x * g x) F = (if atbot then 1 / 2 else if attop then - 1 / 2 else 0)"
    proof -
      note filterlim_tendsto_neg_mult_at_top_iff[OF tendsto \<open>c<0\<close>,of g]
      moreover note filterlim_tendsto_neg_mult_at_bot_iff[OF tendsto \<open>c<0\<close>,of g]
      ultimately show ?thesis unfolding jumpF_def atbot_def attop_def by auto
    qed
    also have "... = - (if attop then 1 / 2 else if atbot then - 1 / 2 else 0)"
    proof -
      have False when atbot attop
        using filterlim_at_top_at_bot[OF _ _ \<open>F\<noteq>bot\<close>] that unfolding atbot_def attop_def by auto
      then show ?thesis by fastforce    
    qed
    also have "... = sgn c * jumpF g F"
      using \<open>c<0\<close> unfolding jumpF_def attop_def atbot_def by auto
    finally show ?thesis .
  qed
  ultimately show ?thesis by auto
qed

  
lemma jumpF_polyR_inverse_add:
  assumes "coprime p q"
  shows "jumpF_polyR q p x + jumpF_polyR p q x = jumpF_polyR 1 (q*p) x"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  have jumpF_add:
    "jumpF_polyR q p x= jumpF_polyR 1 (q*p) x" when "poly p x=0" "coprime p q" for p q
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    have "poly q x\<noteq>0" using that coprime_poly_0 by blast
    then have "q\<noteq>0" by auto
    moreover have "sign_r_pos p x = (0 < poly q x) \<longleftrightarrow> sign_r_pos (q * p) x"
      using sign_r_pos_mult[OF \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close>] sign_r_pos_rec[OF \<open>q\<noteq>0\<close>] \<open>poly q x\<noteq>0\<close>
      by auto
    ultimately show ?thesis using \<open>poly p x=0\<close>  
      unfolding jumpF_polyR_coprime[OF \<open>coprime p q\<close>,of x] jumpF_polyR_coprime[of "q*p" 1 x,simplified]
      by auto
  qed
  have False when "poly p x=0" "poly q x=0" 
    using \<open>coprime p q\<close> that coprime_poly_0 by blast
  moreover have ?thesis when "poly p x=0" "poly q x\<noteq>0" 
  proof -
    have "jumpF_polyR p q x = 0" using jumpF_poly_noroot[OF \<open>poly q x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly p x=0\<close> \<open>coprime p q\<close>] by auto
  qed
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x=0" 
  proof -
    have "jumpF_polyR q p x = 0" using jumpF_poly_noroot[OF \<open>poly p x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly q x=0\<close>,of p] \<open>coprime p q\<close> 
      by (simp add: ac_simps)
  qed  
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x\<noteq>0" 
    by (simp add: jumpF_poly_noroot(2) that(1) that(2))
  ultimately show ?thesis by auto
qed

lemma jumpF_polyL_inverse_add:
  assumes "coprime p q"
  shows "jumpF_polyL q p x + jumpF_polyL p q x = jumpF_polyL 1 (q*p) x"  
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by auto
next
  case False
  have jumpF_add:
    "jumpF_polyL q p x= jumpF_polyL 1 (q*p) x" when "poly p x=0" "coprime p q" for p q
  proof (cases "p=0")
    case True
    then show ?thesis by auto
  next
    case False
    have "poly q x\<noteq>0" using that coprime_poly_0 by blast
    then have "q\<noteq>0" by auto
    moreover have "sign_r_pos p x = (0 < poly q x) \<longleftrightarrow> sign_r_pos (q * p) x"
      using sign_r_pos_mult[OF \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close>] sign_r_pos_rec[OF \<open>q\<noteq>0\<close>] \<open>poly q x\<noteq>0\<close>
      by auto
    moreover have "order x p = order x (q * p)" 
      by (metis \<open>poly q x \<noteq> 0\<close> add_cancel_right_left divisors_zero order_mult order_root)
    ultimately show ?thesis using \<open>poly p x=0\<close>  
      unfolding jumpF_polyL_coprime[OF \<open>coprime p q\<close>,of x] jumpF_polyL_coprime[of "q*p" 1 x,simplified]
      by auto
  qed
  have False when "poly p x=0" "poly q x=0" 
    using \<open>coprime p q\<close> that coprime_poly_0 by blast
  moreover have ?thesis when "poly p x=0" "poly q x\<noteq>0" 
  proof -
    have "jumpF_polyL p q x = 0" using jumpF_poly_noroot[OF \<open>poly q x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly p x=0\<close> \<open>coprime p q\<close>] by auto
  qed
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x=0" 
  proof -
    have "jumpF_polyL q p x = 0" using jumpF_poly_noroot[OF \<open>poly p x\<noteq>0\<close>] by auto
    then show ?thesis using jumpF_add[OF \<open>poly q x=0\<close>,of p] \<open>coprime p q\<close> 
      by (simp add: ac_simps)
  qed  
  moreover have ?thesis when "poly p x\<noteq>0" "poly q x\<noteq>0" 
    by (simp add: jumpF_poly_noroot that(1) that(2))
  ultimately show ?thesis by auto
qed    
  

lemma jumpF_polyL_smult_1:
  "jumpF_polyL (smult c q) p x = sgn c * jumpF_polyL q p x"
proof (cases "c=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding jumpF_polyL_def 
    apply (subst jumpF_times[of "\<lambda>_. c",symmetric])
    by auto
qed  

lemma jumpF_polyR_smult_1:
  "jumpF_polyR (smult c q) p x = sgn c * jumpF_polyR q p x"
proof (cases "c=0")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    unfolding jumpF_polyR_def using False 
    apply (subst jumpF_times[of "\<lambda>_. c",symmetric])
    by auto
qed  
  

lemma
  shows jumpF_polyR_mod:"jumpF_polyR q p x = jumpF_polyR (q mod p) p x" and
        jumpF_polyL_mod:"jumpF_polyL q p x = jumpF_polyL (q mod p) p x"
proof -
  define f where "f=(\<lambda>x. poly (q div p) x)"
  define g where "g=(\<lambda>x. poly (q mod p) x / poly p x)"
  have jumpF_eq:"jumpF (\<lambda>x. poly q x / poly p x) (at y within S) = jumpF g (at y within S)" 
    when "p\<noteq>0" for y S
  proof -
    let ?F = "at y within S"
    have "\<forall>\<^sub>F x in at y within S. poly p x \<noteq> 0" 
      using eventually_poly_nz_at_within[OF \<open>p\<noteq>0\<close>,of y S] .
    then have "eventually (\<lambda>x. (poly q x / poly p x) = (f x+ g x)) ?F"
    proof (rule eventually_mono)
      fix x
      assume P: "poly p x \<noteq> 0"
      have "poly q x = poly (q div p * p + q mod p) x"
        by simp
      also have "\<dots> = f x * poly p x + poly (q mod p) x"
        by (simp only: poly_add poly_mult f_def g_def)
      moreover have "poly (q mod p) x = g x * poly p x"
        using P by (simp add: g_def)
      ultimately show "poly q x / poly p x = f x + g x"
        using P by simp
    qed
    then have "jumpF (\<lambda>x. poly q x / poly p x) ?F = jumpF (\<lambda>x. f x+ g x) ?F"
      by (intro jumpF_cong,auto)
    also have "... = jumpF g ?F"  
    proof -
      have "(f \<longlongrightarrow> f y) (at y within S)"
        unfolding f_def by (intro tendsto_intros)  
      from filterlim_tendsto_add_at_bot_iff[OF this,of g] filterlim_tendsto_add_at_top_iff[OF this,of g] 
      show ?thesis unfolding jumpF_def by auto
    qed
    finally show ?thesis .
  qed
  show "jumpF_polyR q p x = jumpF_polyR (q mod p) p x"
    apply (cases "p=0")
    subgoal by auto
    subgoal using jumpF_eq unfolding g_def jumpF_polyR_def by auto
    done
  show "jumpF_polyL q p x = jumpF_polyL (q mod p) p x"
    apply (cases "p=0")
    subgoal by auto
    subgoal using jumpF_eq unfolding g_def jumpF_polyL_def by auto
    done  
qed 


lemma jumpF_poly_top_0[simp]: "jumpF_poly_top 0 p = 0" "jumpF_poly_top q 0 = 0"
  unfolding jumpF_poly_top_def by auto

lemma jumpF_poly_bot_0[simp]: "jumpF_poly_bot 0 p = 0" "jumpF_poly_bot q 0 = 0"
  unfolding jumpF_poly_bot_def by auto

lemma jumpF_poly_top_code:
  "jumpF_poly_top q p = (if p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p then 
          if sgn_pos_inf q * sgn_pos_inf p > 0 then 1/2 else -1/2 else 0)"
proof (cases "p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p")
  case True
  have ?thesis when "sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at_top"
      using poly_divide_filterlim_at_top[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_top_def using that True by auto
  qed
  moreover have ?thesis when "\<not> sgn_pos_inf q * sgn_pos_inf p > 0"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at_bot"
      using poly_divide_filterlim_at_top[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = - 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_top_def using that True by auto
  qed
  ultimately show ?thesis by auto
next
  case False
  define P where "P= (\<not> (LIM x at_top. poly q x / poly p x :> at_bot) 
                      \<and> \<not> (LIM x at_top. poly q x / poly p x :> at_top))"
  have P when "p=0 \<or> q=0"
    unfolding P_def using that 
    by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p> degree q"
  proof -
    have "LIM x at_top. poly q x / poly p x :> at 0"
      using poly_divide_filterlim_at_top[OF that(1,2)] that(3) by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds simp:filterlim_at)
  qed 
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p = degree q"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_top"
      using poly_divide_filterlim_at_top[OF that(1,2)] using that by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  qed
  ultimately have P using False by fastforce
  then have "jumpF (\<lambda>x. poly q x / poly p x) at_top = 0"
    unfolding jumpF_def P_def by auto
  then show ?thesis unfolding jumpF_poly_top_def using False by presburger
qed

lemma jumpF_poly_bot_code:
  "jumpF_poly_bot q p = (if p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p then 
          if sgn_neg_inf q * sgn_neg_inf p > 0 then 1/2 else -1/2 else 0)"
proof (cases "p\<noteq>0 \<and> q\<noteq>0 \<and> degree q>degree p")
  case True
  have ?thesis when "sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at_top"
      using poly_divide_filterlim_at_bot[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_bot_def using that True by auto
  qed
  moreover have ?thesis when "\<not> sgn_neg_inf q * sgn_neg_inf p > 0"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at_bot"
      using poly_divide_filterlim_at_bot[of p q] True that by auto
    then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = - 1/2"
      unfolding jumpF_def by auto
    then show ?thesis unfolding jumpF_poly_bot_def using that True by auto
  qed
  ultimately show ?thesis by auto
next
  case False
  define P where "P= (\<not> (LIM x at_bot. poly q x / poly p x :> at_bot) 
                      \<and> \<not> (LIM x at_bot. poly q x / poly p x :> at_top))"
  have P when "p=0 \<or> q=0"
    unfolding P_def using that 
    by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p> degree q"
  proof -
    have "LIM x at_bot. poly q x / poly p x :> at 0"
      using poly_divide_filterlim_at_bot[OF that(1,2)] that(3) by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds simp:filterlim_at)
  qed 
  moreover have P when "p\<noteq>0" "q\<noteq>0" "degree p = degree q"
  proof -
    have "((\<lambda>x. poly q x / poly p x) \<longlongrightarrow> lead_coeff q / lead_coeff p) at_bot"
      using poly_divide_filterlim_at_bot[OF that(1,2)] using that by auto
    then show ?thesis unfolding P_def 
      by (auto elim!:filterlim_at_bot_nhds filterlim_at_top_nhds)
  qed
  ultimately have P using False by fastforce
  then have "jumpF (\<lambda>x. poly q x / poly p x) at_bot = 0"
    unfolding jumpF_def P_def by auto
  then show ?thesis unfolding jumpF_poly_bot_def using False by presburger
qed
  
subsection \<open>The extended Cauchy index on polynomials\<close>

definition cindex_polyE:: "real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> real poly \<Rightarrow> real" where
  "cindex_polyE a b q p = jumpF_polyR q p a + cindex_poly a b q p - jumpF_polyL q p b"
  
definition cindex_poly_ubd::"real poly \<Rightarrow> real poly \<Rightarrow> int" where
  "cindex_poly_ubd q p = (THE l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = of_int l))"
   
lemma cindex_polyE_0[simp]: "cindex_polyE a b 0 p = 0" "cindex_polyE a b q 0 = 0"
  unfolding cindex_polyE_def by auto
  
lemma cindex_polyE_mult_cancel:
  fixes p q p'::"real poly"
  assumes "p'\<noteq> 0"  
  shows "cindex_polyE a b (p' * q ) (p' * p) = cindex_polyE a b q p"
  unfolding cindex_polyE_def
  using cindex_poly_mult[OF \<open>p'\<noteq>0\<close>] jumpF_polyL_mult_cancel[OF \<open>p'\<noteq>0\<close>] 
    jumpF_polyR_mult_cancel[OF \<open>p'\<noteq>0\<close>] 
  by simp
  
lemma cindexE_eq_cindex_polyE: 
  assumes "a<b"
  shows "cindexE a b (\<lambda>x. poly q x/poly p x) = cindex_polyE a b q p"
proof (cases "p=0 \<or> q=0")
  case True
  then show ?thesis by (auto simp add: cindexE_constI)
next
  case False
  then have "p\<noteq>0" "q\<noteq>0" by auto
  define g where "g=gcd p q"
  define p' q' where "p'=p div g" and "q' = q div g"
  define f' where "f'=(\<lambda>x. poly q' x / poly p' x)"
  have "g\<noteq>0" using False g_def by auto  
  have pq_f:"p=g*p'" "q=g*q'" and "coprime p' q'"
    unfolding g_def p'_def q'_def 
    apply simp_all 
    using False div_gcd_coprime by blast    
  have "cindexE a b (\<lambda>x. poly q x/poly p x) = cindexE a b (\<lambda>x. poly q' x/poly p' x)" 
  proof -
    define f where "f=(\<lambda>x. poly q x / poly p x)"
    define f' where "f'=(\<lambda>x. poly q' x / poly p' x)"
    have "jumpF f (at_right x) = jumpF f' (at_right x)" for x
    proof (rule jumpF_cong)
      obtain ub where "x < ub" "\<forall>z. x < z \<and> z \<le> ub \<longrightarrow> poly g z \<noteq> 0"
        using next_non_root_interval[OF \<open>g\<noteq>0\<close>,of x] by auto
      then show "\<forall>\<^sub>F x in at_right x. f x = f' x" 
        unfolding eventually_at_right f_def f'_def pq_f
        apply (intro exI[where x=ub])
        by auto
    qed simp
    moreover have "jumpF f (at_left x) = jumpF f' (at_left x)" for x 
    proof (rule jumpF_cong)
      obtain lb where "lb < x" "\<forall>z. lb \<le> z \<and> z < x \<longrightarrow> poly g z \<noteq> 0 "
        using last_non_root_interval[OF \<open>g\<noteq>0\<close>,of x] by auto
      then show "\<forall>\<^sub>F x in at_left x. f x = f' x" 
        unfolding eventually_at_left f_def f'_def pq_f
        apply (intro exI[where x=lb])
        by auto    
    qed simp    
    ultimately show ?thesis unfolding cindexE_def
      apply (fold f_def f'_def)
      by auto
  qed
  also have "... = jumpF f' (at_right a) + real_of_int (cindex a b f') - jumpF f' (at_left b)" 
    unfolding f'_def 
    apply (rule cindex_eq_cindexE_divide)
    subgoal using \<open>a<b\<close> .
    subgoal using False poly_roots_finite pq_f(1) pq_f(2) by fastforce
    subgoal using \<open>coprime p' q'\<close> poly_gcd_iff by force
    subgoal by (auto intro:continuous_intros)
    subgoal by (auto intro:continuous_intros)
    done
  also have "... = cindex_polyE a b q' p'"
    using cindex_eq_cindex_poly unfolding cindex_polyE_def jumpF_polyR_def jumpF_polyL_def f'_def
    by auto
  also have "... = cindex_polyE a b q p"
    using cindex_polyE_mult_cancel[OF \<open>g\<noteq>0\<close>] unfolding pq_f by auto
  finally show ?thesis .
qed
 
lemma cindex_polyE_cross:
  fixes p::"real poly" and a b::real
  assumes "a<b" 
  shows "cindex_polyE a b 1 p = cross_alt 1 p a b / 2" 
proof (induct "degree p" arbitrary:p rule:nat_less_induct) 
  case induct:1
  have ?case when "p=0" 
    using that unfolding cross_alt_def by auto
  moreover have ?case when "p\<noteq>0" and noroot:"{x.  a< x\<and> x< b \<and> poly p x=0 } = {}"
  proof -
    have "cindex_polyE a b 1 p = jumpF_polyR 1 p a  - jumpF_polyL 1 p b" 
    proof -
      have "cindex_poly a b 1 p = 0" unfolding cindex_poly_def
        apply (rule sum.neutral)
        using that by auto
      then show ?thesis unfolding cindex_polyE_def by auto
    qed
    also have "... = cross_alt 1 p a b / 2"  
    proof -
      define f where "f = (\<lambda>x. 1 / poly p x)"
      define ja where "ja = jumpF f (at_right a)"  
      define jb where "jb = jumpF f (at_left b)"
      define right where "right = (\<lambda>R. R ja (0::real) \<or> (continuous (at_right a) f \<and> R (poly p a) 0))"
      define left where "left = (\<lambda>R. R jb (0::real) \<or> (continuous (at_left b) f \<and> R (poly p b) 0))" 
        
      note ja_alt=jumpF_polyR_coprime[of p 1 a,unfolded jumpF_polyR_def,simplified,folded f_def ja_def]
      note jb_alt=jumpF_polyL_coprime[of p 1 b,unfolded jumpF_polyL_def,simplified,folded f_def jb_def]  
      
      have [simp]:"0 < ja \<longleftrightarrow> jumpF_polyR 1 p a = 1/2" "0 > ja \<longleftrightarrow> jumpF_polyR 1 p a = -1/2"
           "0 < jb \<longleftrightarrow> jumpF_polyL 1 p b = 1/2" "0 > jb \<longleftrightarrow> jumpF_polyL 1 p b = -1/2"
        unfolding ja_def jb_def jumpF_polyR_def jumpF_polyL_def f_def jumpF_def
        by auto           
      have [simp]: 
          "poly p a \<noteq>0 \<Longrightarrow> continuous (at_right a) f"
          "poly p b \<noteq>0 \<Longrightarrow> continuous (at_left b) f"  
        unfolding f_def by (auto intro!: continuous_intros )  
      have not_right_left: False when "(right greater \<and> left less \<or> right less \<and> left greater)"
      proof - 
        have [simp]: "f a > 0 \<longleftrightarrow> poly p a > 0" "f a < 0 \<longleftrightarrow> poly p a < 0"
             "f b > 0 \<longleftrightarrow> poly p b > 0" "f b < 0 \<longleftrightarrow> poly p b < 0" 
           unfolding f_def by auto  
        have "continuous_on {a<..<b} f" 
          unfolding f_def using noroot by (auto intro!: continuous_intros)
        then have "\<exists>x>a. x < b \<and> f x = 0" 
          apply (elim jumpF_IVT[OF \<open>a<b\<close>,of f])
          using that unfolding right_def left_def by (fold ja_def jb_def,auto)
        then show False using noroot using f_def by auto
      qed
      have ?thesis when "poly p a>0 \<and> poly p b>0 \<or> poly p a<0 \<and> poly p b<0" 
        using that jumpF_poly_noroot unfolding cross_alt_def by auto
      moreover have False when "poly p a>0 \<and> poly p b<0 \<or> poly p a<0 \<and> poly p b>0" 
        apply (rule not_right_left)
        unfolding right_def left_def using that by auto
      moreover have ?thesis when "poly p a=0" "poly p b>0 \<or> poly p b <0" 
      proof -
        have "ja>0 \<or> ja < 0" using ja_alt \<open>p\<noteq>0\<close> \<open>poly p a=0\<close> by argo
        moreover have False when "ja > 0 \<and> poly p b<0 \<or> ja < 0 \<and> poly p b>0" 
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "ja >0 \<and> poly p b>0 \<or> ja < 0 \<and> poly p b<0"
          using that jumpF_poly_noroot \<open>poly p a=0\<close> unfolding cross_alt_def by auto 
        ultimately show ?thesis using that jumpF_poly_noroot unfolding cross_alt_def by auto 
      qed
      moreover have ?thesis when "poly p b=0" "poly p a>0 \<or> poly p a <0" 
      proof -
        have "jb>0 \<or> jb < 0" using jb_alt \<open>p\<noteq>0\<close> \<open>poly p b=0\<close> by argo
        moreover have False when "jb > 0 \<and> poly p a<0 \<or> jb < 0 \<and> poly p a>0" 
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "jb >0 \<and> poly p a>0 \<or> jb < 0 \<and> poly p a<0"
          using that jumpF_poly_noroot \<open>poly p b=0\<close> unfolding cross_alt_def by auto 
        ultimately show ?thesis using that jumpF_poly_noroot unfolding cross_alt_def by auto 
      qed  
      moreover have ?thesis when "poly p a=0" "poly p b=0"
      proof -
        have "jb>0 \<or> jb < 0" using jb_alt \<open>p\<noteq>0\<close> \<open>poly p b=0\<close> by argo
        moreover have "ja>0 \<or> ja < 0" using ja_alt \<open>p\<noteq>0\<close> \<open>poly p a=0\<close> by argo
        moreover have False when "ja>0 \<and> jb<0 \<or> ja<0 \<and> jb>0"
          apply (rule not_right_left)
          unfolding right_def left_def using that by fastforce
        moreover have ?thesis when "ja>0 \<and> jb>0 \<or> ja<0 \<and> jb<0"
          using that jumpF_poly_noroot \<open>poly p b=0\<close> \<open>poly p a=0\<close> 
          unfolding cross_alt_def by auto
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis by argo
    qed
    finally show ?thesis .
  qed    
  moreover have ?case when "p\<noteq>0" and no_empty:"{x.  a< x\<and> x< b \<and> poly p x=0 } \<noteq> {}"
  proof -
    define roots where "roots\<equiv>{x.  a< x\<and> x< b \<and> poly p x=0 }"
    have "finite roots" unfolding roots_def using poly_roots_finite[OF \<open>p\<noteq>0\<close>] by auto
    define max_r where "max_r\<equiv>Max roots"
    hence "poly p max_r=0" and "a<max_r" and "max_r<b" 
      using Max_in[OF \<open>finite roots\<close>] no_empty  unfolding roots_def by auto
    define max_rp where "max_rp\<equiv>[:-max_r,1:]^order max_r p"
    then obtain p' where p'_def:"p=p'*max_rp" and "\<not> [:-max_r,1:] dvd p'"  
      by (metis \<open>p\<noteq>0\<close> mult.commute order_decomp)
    hence "p'\<noteq>0" and "max_rp\<noteq>0" and max_r_nz:"poly p' max_r\<noteq>0"(*and "poly p' a\<noteq>0" and "poly p' b\<noteq>0" *)
      (*and  "poly max_rp a\<noteq>0" and "poly max_rp b\<noteq>0"*) 
      using \<open>p\<noteq>0\<close> by (auto simp add: dvd_iff_poly_eq_0)
        
    define max_r_sign where "max_r_sign\<equiv>if odd(order max_r p) then -1 else 1::int"
    define roots' where "roots'\<equiv>{x.  a< x\<and> x< b \<and> poly p' x=0}"
  
    have "cindex_polyE a b 1 p = jumpF_polyR 1 p a + (\<Sum>x\<in>roots. jump_poly 1 p x) - jumpF_polyL 1 p b"  
      unfolding cindex_polyE_def cindex_poly_def roots_def by (simp,meson)
    also have "... = max_r_sign * cindex_poly a b 1 p' + jump_poly 1 p max_r 
        + max_r_sign * jumpF_polyR 1 p' a - jumpF_polyL 1 p' b"
    proof -
      have "(\<Sum>x\<in>roots. jump_poly 1 p x) = max_r_sign * cindex_poly a b 1 p' + jump_poly 1 p max_r"  
      proof -
        have "(\<Sum>x\<in>roots. jump_poly 1 p x)= (\<Sum>x\<in>roots'. jump_poly 1 p x)+ jump_poly 1 p max_r"
        proof -
          have "roots = insert max_r roots'" 
            unfolding roots_def roots'_def p'_def 
            using \<open>poly p max_r=0\<close> \<open>a<max_r\<close> \<open>max_r<b\<close> \<open>p\<noteq>0\<close> order_root
            apply (subst max_rp_def)
            by auto
          moreover have "finite roots'" 
            unfolding roots'_def using poly_roots_finite[OF \<open>p'\<noteq>0\<close>] by auto 
          moreover have "max_r \<notin> roots'" 
            unfolding roots'_def using max_r_nz
            by auto
          ultimately show ?thesis using sum.insert[of roots' max_r] by auto   
        qed
        moreover have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = max_r_sign * cindex_poly a b 1 p'"
        proof -
          have "(\<Sum>x\<in>roots'. jump_poly 1 p x) = (\<Sum>x\<in>roots'. max_r_sign * jump_poly 1 p' x)"
          proof (rule sum.cong,rule refl)
            fix x assume "x \<in> roots'" 
            hence "x\<noteq>max_r" using max_r_nz unfolding roots'_def 
              by auto
            hence "poly max_rp x\<noteq>0" using poly_power_n_eq unfolding max_rp_def by auto
            hence "order x max_rp=0"  by (metis order_root)
            moreover have "jump_poly 1 max_rp x=0" 
              using \<open>poly max_rp x\<noteq>0\<close> by (metis jump_poly_not_root)
            moreover have "x\<in>roots"
              using \<open>x \<in> roots'\<close> unfolding roots_def roots'_def p'_def by auto
            hence "x<max_r" 
              using Max_ge[OF \<open>finite roots\<close>,of x] \<open>x\<noteq>max_r\<close> by (fold max_r_def,auto)
            hence "sign (poly max_rp x) = max_r_sign" 
              using \<open>poly max_rp x \<noteq> 0\<close> unfolding max_r_sign_def max_rp_def sign_def
              by (subst poly_power,simp add:linorder_class.not_less zero_less_power_eq)
            ultimately show "jump_poly 1 p x = max_r_sign * jump_poly 1 p' x" 
              using jump_poly_1_mult[of p' x max_rp]  unfolding p'_def 
              by (simp add: \<open>poly max_rp x \<noteq> 0\<close>)
          qed
          also have "... = max_r_sign * (\<Sum>x\<in>roots'. jump_poly 1 p' x)" 
            by (simp add: sum_distrib_left) 
          also have "... = max_r_sign * cindex_poly a b 1 p'"
            unfolding cindex_poly_def roots'_def by meson
          finally show ?thesis .
        qed
        ultimately show ?thesis by simp
      qed
      moreover have "jumpF_polyR 1 p a = max_r_sign * jumpF_polyR 1 p' a"
      proof -
        define f where "f = (\<lambda>x. 1 / poly max_rp x)"
        define g where "g = (\<lambda>x. 1 / poly p' x)"
        have "jumpF_polyR 1 p a = jumpF (\<lambda>x. f x * g x) (at_right a)"  
          unfolding jumpF_polyR_def f_def g_def p'_def 
          by (auto simp add:field_simps)
        also have "... = sgn (f a) * jumpF g (at_right a)" 
        proof (rule jumpF_times) 
          have [simp]: "poly max_rp a \<noteq>0" 
            unfolding max_rp_def using \<open>max_r>a\<close> by auto  
          show "(f \<longlongrightarrow> f a) (at_right a)" "f a \<noteq> 0"
            unfolding f_def by (auto intro:tendsto_intros)
        qed auto      
        also have "... = max_r_sign * jumpF_polyR 1 p' a"
        proof -
          have "sgn (f a) = max_r_sign" 
            unfolding max_r_sign_def f_def max_rp_def using \<open>a<max_r\<close>
            by (auto simp add:sgn_power)
          then show ?thesis unfolding jumpF_polyR_def g_def by auto
        qed
        finally show ?thesis .
      qed
      moreover have "jumpF_polyL 1 p b =  jumpF_polyL 1 p' b"
      proof -
        define f where "f = (\<lambda>x. 1 / poly max_rp x)"
        define g where "g = (\<lambda>x. 1 / poly p' x)"
        have "jumpF_polyL 1 p b = jumpF (\<lambda>x. f x * g x) (at_left b)"  
          unfolding jumpF_polyL_def f_def g_def p'_def 
          by (auto simp add:field_simps)
        also have "... = sgn (f b) * jumpF g (at_left b)" 
        proof (rule jumpF_times) 
          have [simp]: "poly max_rp b \<noteq>0" 
            unfolding max_rp_def using \<open>max_r<b\<close> by auto  
          show "(f \<longlongrightarrow> f b) (at_left b)" "f b \<noteq> 0"
            unfolding f_def by (auto intro:tendsto_intros)
        qed auto      
        also have "... = jumpF_polyL 1 p' b"
        proof -
          have "sgn (f b) = 1" 
            unfolding max_r_sign_def f_def max_rp_def using \<open>b>max_r\<close>
            by (auto simp add:sgn_power)
          then show ?thesis unfolding jumpF_polyL_def g_def by auto
        qed
        finally show ?thesis .
      qed 
      ultimately show ?thesis by auto
    qed
    also have "... = max_r_sign * cindex_polyE a b 1 p' + jump_poly 1 p max_r 
        + (max_r_sign - 1) * jumpF_polyL 1 p' b"
      unfolding cindex_polyE_def roots'_def by (auto simp add:algebra_simps)
    also have "... = max_r_sign * cross_alt 1 p' a b / 2 + jump_poly 1 p max_r 
        + (max_r_sign - 1) * jumpF_polyL 1 p' b"
    proof -
      have "degree max_rp>0" unfolding max_rp_def degree_linear_power
        using \<open>poly p max_r=0\<close> order_root \<open>p\<noteq>0\<close> by blast
      then have "degree p'<degree p" unfolding p'_def 
        using degree_mult_eq[OF \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>] by auto
      from induct[rule_format, OF this] 
      have "cindex_polyE a b 1 p' = real_of_int (cross_alt 1 p' a b) / 2" by auto
      then show ?thesis by auto
    qed
    also have "... = real_of_int (cross_alt 1 p a b) / 2"
    proof -
      have sjump_p:"jump_poly 1 p max_r = (if odd (order max_r p) then sign (poly p' max_r) else 0)"
      proof -
        note max_r_nz 
        moreover then have "poly max_rp max_r=0" 
          using \<open>poly p max_r = 0\<close> p'_def by auto
        ultimately have "jump_poly 1 p max_r = sign (poly p' max_r) * jump_poly 1 max_rp max_r"
          unfolding p'_def using jump_poly_1_mult[of p' max_r max_rp] 
          by auto
        also have "... = (if odd (order max_r max_rp) then sign (poly p' max_r) else 0)"  
        proof -
          have "sign_r_pos max_rp max_r"
            unfolding max_rp_def using sign_r_pos_power by auto
          then show ?thesis using \<open>max_rp\<noteq>0\<close> unfolding jump_poly_def by auto
        qed
        also have "... = (if odd (order max_r p) then sign (poly p' max_r) else 0)"
        proof -
          have "order max_r p'=0" by (simp add: \<open>poly p' max_r \<noteq> 0\<close> order_0I)
          then have "order max_r max_rp = order max_r p" 
            unfolding p'_def using \<open>p'\<noteq>0\<close> \<open>max_rp\<noteq>0\<close>
            apply (subst order_mult)
            by auto  
          then show ?thesis by auto
        qed
        finally show ?thesis .
      qed
      have ?thesis when "even (order max_r p)"
      proof -
        have "sign (poly p x) =  sign (poly p' x)" when "x\<noteq>max_r" for x
        proof -
          have "sign (poly max_rp x) = 1"
            unfolding max_rp_def using \<open>even (order max_r p)\<close> that 
            apply (simp add:sign_power )
            by (simp add: Sturm_Tarski.sign_def)
          then show ?thesis unfolding p'_def by (simp add:sign_times)
        qed    
        from this[of a] this[of b] \<open>a<max_r\<close> \<open>max_r<b\<close> 
        have "cross_alt 1 p' a b = cross_alt 1 p a b" 
          unfolding cross_alt_def by auto 
        then show ?thesis using that unfolding max_r_sign_def sjump_p by auto
      qed
      moreover have ?thesis when "odd (order max_r p)" 
      proof -
        let ?thesis2 = "sign (poly p' max_r) * 2 - cross_alt 1 p' a b - 4 * jumpF_polyL 1 p' b 
              = cross_alt 1 p a b"    
        have ?thesis2 when "poly p' b=0"
        proof -
          have "jumpF_polyL 1 p' b = 1/2 \<or> jumpF_polyL 1 p' b=-1/2"  
            using jumpF_polyL_coprime[of p' 1 b,simplified] \<open>p'\<noteq>0\<close> \<open>poly p' b=0\<close> by auto
          moreover have "poly p' max_r>0 \<or> poly p' max_r<0" 
            using max_r_nz by auto
          moreover have False when "poly p' max_r>0 \<and> jumpF_polyL 1 p' b=-1/2 
                \<or> poly p' max_r<0 \<and> jumpF_polyL 1 p' b=1/2"
          proof -
            define f where "f= (\<lambda>x. 1/ poly p' x)"
            have noroots:"poly p' x\<noteq>0" when "x\<in>{max_r<..<b}" for x
            proof (rule ccontr)
              assume " \<not> poly p' x \<noteq> 0"
              then have "poly p x =0" unfolding p'_def by auto
              then have "x\<in>roots" unfolding roots_def using that \<open>a<max_r\<close> by auto
              then have "x\<le>max_r" using Max_ge[OF \<open>finite roots\<close>] unfolding max_r_def by auto
              moreover have "x>max_r" using that by auto
              ultimately show False by auto
            qed  
            have "continuous_on {max_r<..<b} f"
              unfolding f_def using noroots by (auto intro!:continuous_intros)
            moreover have "continuous (at_right max_r) f" 
              unfolding f_def using max_r_nz
              by (auto intro!:continuous_intros)
            moreover have "f max_r>0 \<and> jumpF f (at_left b)<0 
                \<or> f max_r<0 \<and> jumpF f (at_left b)>0"
              using that unfolding f_def jumpF_polyL_def by auto  
            ultimately have "\<exists>x>max_r. x < b \<and> f x = 0"
              apply (intro jumpF_IVT[OF \<open>max_r<b\<close>])
              by auto
            then show False using noroots unfolding f_def by auto
          qed
          moreover have ?thesis when "poly p' max_r>0 \<and> jumpF_polyL 1 p' b=1/2
              \<or> poly p' max_r<0 \<and> jumpF_polyL 1 p' b=-1/2"
          proof -
            have "poly max_rp a < 0" "poly max_rp b>0"
              unfolding max_rp_def using \<open>odd (order max_r p)\<close> \<open>a<max_r\<close> \<open>max_r<b\<close>
              by (simp_all add:zero_less_power_eq)
            then have "cross_alt 1 p a b = - cross_alt 1 p' a b" 
              unfolding cross_alt_def p'_def using \<open>poly p' b=0\<close> 
              apply (simp add:sign_times)
              by (simp add: Sturm_Tarski.sign_def)
            with that show ?thesis by auto
          qed
          ultimately show ?thesis by blast  
        qed
        moreover have ?thesis2 when "poly p' b\<noteq>0"
        proof -
          have [simp]:"jumpF_polyL 1 p' b = 0" 
            using jumpF_polyL_coprime[of p' 1 b,simplified] \<open>poly p' b\<noteq>0\<close> by auto 
          have [simp]:"poly max_rp a < 0" "poly max_rp b>0"
            unfolding max_rp_def using \<open>odd (order max_r p)\<close> \<open>a<max_r\<close> \<open>max_r<b\<close>
            by (simp_all add:zero_less_power_eq)
          have "poly p' b>0 \<or> poly p' b<0" 
            using \<open>poly p' b\<noteq>0\<close> by auto
          moreover have "poly p' max_r>0 \<or> poly p' max_r<0" 
            using max_r_nz by auto
          moreover have ?thesis when "poly p' b>0 \<and> poly p' max_r>0 "  
            using that unfolding cross_alt_def p'_def
            apply (simp add:sign_times)
            by (simp add: Sturm_Tarski.sign_def)
          moreover have ?thesis when "poly p' b<0 \<and> poly p' max_r<0"      
            using that unfolding cross_alt_def p'_def
            apply (simp add:sign_times)
            by (simp add: Sturm_Tarski.sign_def)  
          moreover have False when "poly p' b>0 \<and> poly p' max_r<0 \<or> poly p' b<0 \<and> poly p' max_r>0"
          proof -
            have "\<exists>x>max_r. x < b \<and> poly p' x = 0"
              apply (rule poly_IVT[OF \<open>max_r<b\<close>,of p'])
              using that mult_less_0_iff by blast
            then obtain x where "max_r<x" "x<b" "poly p x=0" unfolding p'_def by auto
            then have "x\<in>roots" using \<open>a<max_r\<close> unfolding roots_def by auto
            then have "x\<le>max_r" unfolding max_r_def using Max_ge[OF \<open>finite roots\<close>] by auto    
            then show False using \<open>max_r<x\<close> by auto
          qed
          ultimately show ?thesis by blast
        qed
        ultimately have ?thesis2 by auto 
        then show ?thesis unfolding max_r_sign_def sjump_p using that by simp
      qed
      ultimately show ?thesis by auto
    qed
    finally show ?thesis . 
  qed
  ultimately show ?case by fast
qed      
     
lemma cindex_polyE_inverse_add:
  fixes p q::"real poly" 
  assumes cp:"coprime p q"
  shows "cindex_polyE a b q p + cindex_polyE a b p q=cindex_polyE a b 1 (q*p)"
  unfolding cindex_polyE_def
  using cindex_poly_inverse_add[OF cp,symmetric] jumpF_polyR_inverse_add[OF cp,symmetric] 
    jumpF_polyL_inverse_add[OF cp,symmetric]
  by auto    

lemma cindex_polyE_inverse_add_cross:
  fixes p q::"real poly"
  assumes "a < b" "coprime p q" 
  shows "cindex_polyE a b q p  + cindex_polyE a b p q = cross_alt p q a b / 2" 
  apply (subst cindex_polyE_inverse_add[OF \<open>coprime p q\<close>])
  apply (subst cindex_polyE_cross[OF \<open>a<b\<close>])
  apply (subst mult.commute)  
  apply (subst cross_alt_clear_n[OF \<open>coprime p q\<close>])
  by simp
      
lemma cindex_polyE_smult_1: 
  fixes p q::"real poly" and c::real
  shows "cindex_polyE a b (smult c q) p =  (sgn c) * cindex_polyE a b q p"
  unfolding cindex_polyE_def jumpF_polyL_smult_1 jumpF_polyR_smult_1 cindex_poly_smult_1 
  by (auto simp add:sgn_sign_eq[symmetric] algebra_simps)    

lemma cindex_polyE_mod:
  fixes p q::"real poly" 
  shows "cindex_polyE a b q p =  cindex_polyE a b (q mod p) p"
  unfolding cindex_polyE_def
  apply (subst cindex_poly_mod)
  apply (subst jumpF_polyR_mod)
  apply (subst jumpF_polyL_mod)
  by simp

lemma cindex_polyE_rec:
  fixes p q::"real poly"
  assumes "a < b" "coprime p q"
  shows "cindex_polyE a b q p  = cross_alt q p a b/2  +  cindex_polyE a b (- (p mod q)) q"  
proof -
  note cindex_polyE_inverse_add_cross[OF assms]
  moreover have "cindex_polyE a b (- (p mod q)) q = - cindex_polyE a b p q"
    using cindex_polyE_mod cindex_polyE_smult_1[of a b "-1"]
    by auto
  ultimately show ?thesis by (auto simp add:field_simps cross_alt_poly_commute)
qed    
  
lemma cindex_polyE_changes_alt_itv_mods: 
  assumes "a<b" "coprime p q"
  shows "cindex_polyE a b q p = changes_alt_itv_smods a b p q / 2" using \<open>coprime p q\<close>
proof (induct "smods p q" arbitrary:p q)
  case Nil
  then have "p=0" by (metis smods_nil_eq)
  then show ?case by (simp add:changes_alt_itv_smods_def changes_alt_poly_at_def) 
next
  case (Cons x xs)
  then have "p\<noteq>0" by auto
  have ?case when "q=0" 
    using that by (simp add:changes_alt_itv_smods_def changes_alt_poly_at_def)
  moreover have ?case when "q\<noteq>0"
  proof -
    define r where "r\<equiv>- (p mod q)"
    obtain ps where ps:"smods p q=p#q#ps" "smods q r=q#ps" and "xs=q#ps"
      unfolding r_def using \<open>q\<noteq>0\<close> \<open>p\<noteq>0\<close> \<open>x # xs = smods p q\<close> 
      by (metis list.inject smods.simps)
    from Cons.prems \<open>q \<noteq> 0\<close> have "coprime q r" 
      by (simp add: r_def ac_simps)
    then have "cindex_polyE a b r q = real_of_int (changes_alt_itv_smods a b q r) / 2"
      apply (rule_tac Cons.hyps(1))
      using ps \<open>xs=q#ps\<close> by simp_all  
    moreover have "changes_alt_itv_smods a b p q = cross_alt p q a b + changes_alt_itv_smods a b q r" 
      using changes_alt_itv_smods_rec[OF \<open>a<b\<close> \<open>coprime p q\<close>,folded r_def] .
    moreover have "cindex_polyE a b q p = real_of_int (cross_alt q p a b) / 2 + cindex_polyE a b r q"
      using cindex_polyE_rec[OF \<open>a<b\<close> \<open>coprime p q\<close>,folded r_def] .
    ultimately show ?case 
      by (auto simp add:field_simps cross_alt_poly_commute)
  qed
  ultimately show ?case by blast
qed
  
lemma cindex_poly_ubd_eventually:
  shows "\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = of_int (cindex_poly_ubd q p)" 
proof -
  define f where "f=(\<lambda>x. poly q x/poly p x)"
  obtain R where R_def: "R>0" "proots p \<subseteq> {-R<..<R}"
    if "p\<noteq>0" 
  proof (cases "p=0")
    case True
    then show ?thesis using that[of 1] by auto
  next
    case False
    then have "finite (proots p)" by auto
    from finite_ball_include[OF this,of 0] 
    obtain r where "r>0" and r_ball:"proots p \<subseteq> ball 0 r"
      by auto
    have "proots p \<subseteq> {-r<..<r}"
    proof 
      fix x assume "x \<in> proots p"
      then have "x\<in>ball 0 r" using r_ball by auto
      then have "abs x<r" using mem_ball_0 by auto
      then show "x \<in> {- r<..<r}" using \<open>r>0\<close> by auto
    qed
    then show ?thesis using that[of r] False \<open>r>0\<close> by auto
  qed
  define l where "l=(if p=0  then 0 else cindex_poly (-R) R q p)"  
  define P where "P=(\<lambda>l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r f = of_int l))"
  have "P l " 
  proof (cases "p=0 ")
    case True
    then show ?thesis
      unfolding P_def f_def l_def using True
      by (auto intro!: eventuallyI cindexE_constI)
  next
    case False
    have "P l" unfolding P_def
    proof (rule eventually_at_top_linorderI[of R])  
      fix r assume "R \<le> r" 
      then have "cindexE (- r) r f =  cindex_polyE (-r) r q p"
        unfolding f_def using R_def[OF \<open>p\<noteq>0\<close>] by (auto intro: cindexE_eq_cindex_polyE)
      also have "... = of_int (cindex_poly (- r) r q p)"
      proof -
        have "jumpF_polyR q p (- r) = 0"
          apply (rule jumpF_poly_noroot)
          using \<open>R\<le>r\<close> R_def[OF \<open>p\<noteq>0\<close>] by auto
        moreover have "jumpF_polyL q p r = 0"
          apply (rule jumpF_poly_noroot)
          using \<open>R\<le>r\<close> R_def[OF \<open>p\<noteq>0\<close>] by auto
        ultimately show ?thesis unfolding cindex_polyE_def by auto
      qed  
      also have "... = of_int (cindex_poly (- R) R q p)"
      proof -
        define rs where "rs={x. poly p x = 0 \<and> - r < x \<and> x < r}"
        define Rs where "Rs={x. poly p x = 0 \<and> - R < x \<and> x < R}"
        have "rs=Rs" 
          using R_def[OF \<open>p\<noteq>0\<close>] \<open>R\<le>r\<close> unfolding rs_def Rs_def by force    
        then show ?thesis
          unfolding cindex_poly_def by (fold rs_def Rs_def,auto)
      qed
      also have "... = of_int l" unfolding l_def using False by auto
      finally show "cindexE (- r) r f = real_of_int l" .
    qed
    then show ?thesis unfolding P_def by auto
  qed
  moreover have "x=l" when "P x" for x 
  proof -
    have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int x"
         "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int l"
      using \<open>P x\<close> \<open>P l\<close> unfolding P_def by auto
    from eventually_conj[OF this] 
    have "\<forall>\<^sub>F r::real in at_top. real_of_int x = real_of_int l"
      by (elim eventually_mono,auto)
    then have "real_of_int x = real_of_int l" by auto
    then show ?thesis by simp
  qed
  ultimately have "P (THE x. P x)" using theI[of P l] by blast
  then show ?thesis unfolding P_def f_def cindex_poly_ubd_def by auto 
qed
  
lemma cindex_poly_ubd_0:
  assumes "p=0 \<or> q=0"
  shows "cindex_poly_ubd q p = 0"  
proof -
  have "\<forall>\<^sub>F r in at_top. cindexE (-r) r (\<lambda>x. poly q x/poly p x) = 0"
    apply (rule eventuallyI)
    using assms by (auto intro:cindexE_constI)
  from eventually_conj[OF this cindex_poly_ubd_eventually[of q p]]
  have "\<forall>\<^sub>F r::real in at_top.  (cindex_poly_ubd q p) = (0::int)"
    apply (elim eventually_mono)
    by auto
  then show ?thesis by auto
qed
  
lemma cindex_poly_ubd_code:
  shows "cindex_poly_ubd q p = changes_R_smods p q"
proof (cases "p=0")
  case True
  then show ?thesis using cindex_poly_ubd_0 by auto
next
  case False
  define ps where "ps\<equiv>smods p q"
  have "p\<in>set ps" using ps_def \<open>p\<noteq>0\<close> by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
      and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
      and "lb<0"
    using root_list_lb[OF no_0_in_smods,of p q,folded ps_def] 
    by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
      and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
      and "ub>0"
    using root_list_ub[OF no_0_in_smods,of p q,folded ps_def] 
    by auto
  define f where "f=(\<lambda>t. poly q t/ poly p t)"
  define P where "P=(\<lambda>l. (\<forall>\<^sub>F r in at_top. cindexE (-r) r f = of_int l))"
  have "P (changes_R_smods p q)" unfolding P_def
  proof (rule eventually_at_top_linorderI[of "max \<bar>lb\<bar> \<bar>ub\<bar> + 1"])
    fix r assume r_asm:"r\<ge>max \<bar>lb\<bar> \<bar>ub\<bar> + 1"
    have "cindexE (- r) r f =  cindex_polyE (-r) r q p"
      unfolding f_def using r_asm by (auto intro: cindexE_eq_cindex_polyE)
    also have "... = of_int (cindex_poly (- r) r q p)"
    proof -
      have "jumpF_polyR q p (- r) = 0"
        apply (rule jumpF_poly_noroot)
        using r_asm lb[rule_format,OF \<open>p\<in>set ps\<close>,of "-r"] by linarith
      moreover have "jumpF_polyL q p r = 0"
        apply (rule jumpF_poly_noroot)
        using r_asm ub[rule_format,OF \<open>p\<in>set ps\<close>,of "r"] by linarith
      ultimately show ?thesis unfolding cindex_polyE_def by auto
    qed
    also have "... = of_int (changes_itv_smods (- r) r p q)"
      apply (rule cindex_poly_changes_itv_mods[THEN arg_cong])
      using r_asm lb[rule_format,OF \<open>p\<in>set ps\<close>,of "-r"] ub[rule_format,OF \<open>p\<in>set ps\<close>,of "r"]
      by linarith+
    also have "... = of_int (changes_R_smods p q)"
    proof -
      have "map (sgn \<circ> (\<lambda>p. poly p (-r))) ps = map sgn_neg_inf ps"
          and "map (sgn \<circ> (\<lambda>p. poly p r)) ps = map sgn_pos_inf ps"
        using lb_sgn[THEN spec,of "-r",simplified] ub_sgn[THEN spec,of r,simplified] r_asm 
        by auto
      hence "changes_poly_at ps (-r)=changes_poly_neg_inf ps
          \<and> changes_poly_at ps r=changes_poly_pos_inf ps"
        unfolding changes_poly_neg_inf_def changes_poly_at_def changes_poly_pos_inf_def
        by (subst (1 3)  changes_map_sgn_eq,metis map_map)
      thus ?thesis unfolding changes_R_smods_def changes_itv_smods_def ps_def
        by metis
    qed
    finally show "cindexE (- r) r f =  of_int (changes_R_smods p q)" .
  qed
  moreover have "x = changes_R_smods p q" when "P x" for x 
  proof -
    have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int (changes_R_smods p q)" 
        "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = real_of_int x"
      using \<open>P (changes_R_smods p q)\<close> \<open>P x\<close> unfolding P_def by auto
    from eventually_conj[OF this] 
    have "\<forall>\<^sub>F (r::real) in at_top. of_int x = of_int (changes_R_smods p q)"
      by (elim eventually_mono,auto)
    then have "of_int x = of_int (changes_R_smods p q)" 
      using eventually_const_iff by auto
    then show ?thesis using of_int_eq_iff by blast
  qed
  ultimately have "(THE x. P x) = changes_R_smods p q" 
    using the_equality[of P "changes_R_smods p q"] by blast
  then show ?thesis unfolding cindex_poly_ubd_def P_def f_def by auto
qed  


lemma cindexE_ubd_poly: "cindexE_ubd (\<lambda>x. poly q x/poly p x) = cindex_poly_ubd q p"
proof (cases "p=0")
  case True
  then show ?thesis using cindex_poly_ubd_0 unfolding cindexE_ubd_def 
    by auto
next
  case False
  define mx mn where "mx = Max {x. poly p x = 0}" and "mn = Min {x. poly p x=0}"
  define rr where "rr= 1+ (max \<bar>mx\<bar> \<bar>mn\<bar>)"
  have rr:"-rr < x \<and> x< rr" when "poly p x = 0 " for x
  proof -
    have "finite {x. poly p x = 0}" using \<open>p\<noteq>0\<close> poly_roots_finite by blast
    then have "mn \<le> x" "x\<le>mx"
      using Max_ge Min_le that unfolding mn_def mx_def by simp_all
    then show ?thesis unfolding rr_def by auto
  qed
  define f where "f=(\<lambda>x. poly q x / poly p x)"
  have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindexE_ubd f"
  proof (rule eventually_at_top_linorderI[of rr])
    fix r assume "r\<ge>rr"
    define R1 R2 where "R1={x. jumpF f (at_right x) \<noteq> 0 \<and> - r \<le> x \<and> x < r}"
                       and "R2 = {x. jumpF f (at_right x) \<noteq> 0}"
    define L1 L2 where "L1={x. jumpF f (at_left x) \<noteq> 0 \<and> - r < x \<and> x \<le> r}"
                       and "L2={x. jumpF f (at_left x) \<noteq> 0}"
    have "R1=R2"
    proof -
      have "jumpF f (at_right x) = 0" when "\<not> (- r \<le> x \<and> x < r)" for x 
      proof -
        have "jumpF f (at_right x) = jumpF_polyR q p x"
          unfolding f_def jumpF_polyR_def by simp
        also have "... = 0"
          apply (rule jumpF_poly_noroot)
          using  that \<open>r\<ge>rr\<close> by (auto dest:rr)
        finally show ?thesis .
      qed
      then show ?thesis unfolding R1_def R2_def by blast
    qed
    moreover have "L1=L2"
    proof -
      have "jumpF f (at_left x) = 0" when "\<not> (- r < x \<and> x \<le> r)" for x 
      proof -
        have "jumpF f (at_left x) = jumpF_polyL q p x"
          unfolding f_def jumpF_polyL_def by simp
        also have "... = 0"
          apply (rule jumpF_poly_noroot)
          using that \<open>r\<ge>rr\<close> by (auto dest:rr)
        finally show ?thesis .
      qed
      then show ?thesis unfolding L1_def L2_def by blast
    qed
    ultimately show "cindexE (- r) r f = cindexE_ubd f" 
      unfolding cindexE_def cindexE_ubd_def
      apply (fold R1_def R2_def L1_def L2_def)
      by auto
  qed
  moreover have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindex_poly_ubd q p"
    using cindex_poly_ubd_eventually unfolding f_def by auto
  ultimately have "\<forall>\<^sub>F r in at_top. cindexE (- r) r f = cindexE_ubd f 
                          \<and> cindexE (- r) r f = cindex_poly_ubd q p"
    using eventually_conj by auto
  then have "\<forall>\<^sub>F (r::real) in at_top. cindexE_ubd f = cindex_poly_ubd q p"
    by (elim eventually_mono) auto
  then show ?thesis unfolding f_def by auto
qed
  
end
