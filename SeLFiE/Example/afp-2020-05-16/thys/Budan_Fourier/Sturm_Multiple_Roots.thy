(*
    Title:      Extension of Sturm's theorem for multiple roots
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Extension of Sturm's theorem for multiple roots\<close>

theory Sturm_Multiple_Roots 
  imports
    BF_Misc
begin

text \<open>The classic Sturm's theorem is used to count real roots WITHOUT multiplicity of a polynomial within 
  an interval. Surprisingly, we can also extend Sturm's theorem to count real roots WITH 
  multiplicity by modifying the signed remainder sequence, which seems to be overlooked by many
  textbooks. 

  Our formal proof is inspired by Theorem 10.5.6 in 
    Rahman, Q.I., Schmeisser, G.: Analytic Theory of Polynomials. Oxford University Press (2002).
\<close>

subsection \<open>More results for @{term smods}\<close>

lemma last_smods_gcd:
  fixes p q ::"real poly"
  defines "pp \<equiv> last (smods p q)" 
  assumes "p\<noteq>0"
  shows "pp = smult (lead_coeff pp) (gcd p q)"
  using \<open>p\<noteq>0\<close> unfolding pp_def
proof (induct "smods p q" arbitrary:p q rule:length_induct)
  case 1
  have ?case when "q=0"
    using that smult_normalize_field_eq \<open>p\<noteq>0\<close> by auto
  moreover have ?case when "q\<noteq>0"
  proof -
    define r where "r= - (p mod q)"
    have smods_cons:"smods p q = p # smods q r"
      unfolding r_def using \<open>p\<noteq>0\<close> by simp
    have "last (smods q r) = smult (lead_coeff (last (smods q r))) (gcd q r)"
      apply (rule 1(1)[rule_format,of "smods q r" q r])
      using smods_cons \<open>q\<noteq>0\<close> by auto
    moreover have "gcd p q = gcd q r"
      unfolding r_def by (simp add: gcd.commute that)
    ultimately show ?thesis unfolding smods_cons using \<open>q\<noteq>0\<close>
      by simp
  qed
  ultimately show ?case by argo
qed

lemma last_smods_nzero:
  assumes "p\<noteq>0"
  shows "last (smods p q) \<noteq>0"
  by (metis assms last_in_set no_0_in_smods smods_nil_eq)

subsection \<open>Alternative signed remainder sequences\<close>

function smods_ext::"real poly \<Rightarrow> real poly \<Rightarrow> real poly list" where 
  "smods_ext p q = (if p=0 then [] else
                      (if p mod q \<noteq> 0  
                        then Cons p (smods_ext q (-(p mod q))) 
                        else Cons p (smods_ext q (pderiv q)))
                   )"
  by auto
termination
  apply (relation "measure (\<lambda>(p,q).if p=0 then 0 else if q=0 then 1 else 2+degree q)")
  using degree_mod_less by (auto simp add:degree_pderiv pderiv_eq_0_iff)

lemma smods_ext_prefix:
  fixes p q::"real poly"
  defines "pp \<equiv> last (smods p q)" 
  assumes "p\<noteq>0" "q\<noteq>0"
  shows "smods_ext p q = smods p q @ tl (smods_ext pp (pderiv pp))"
  unfolding pp_def using assms(2,3)
proof (induct "smods_ext p q" arbitrary:p q rule:length_induct)
  case 1
  have ?case when "p mod q \<noteq>0"
  proof -
    define pp where "pp=last (smods q (- (p mod q)))"
    have smods_cons:"smods p q = p# smods q (- (p mod q))"
      using \<open>p\<noteq>0\<close> by auto
    then have pp_last:"pp=last (smods p q)" unfolding pp_def
      by (simp add: "1.prems"(2) pp_def)
    have smods_ext_cons:"smods_ext p q = p # smods_ext q (- (p mod q))"
      using that \<open>p\<noteq>0\<close> by auto
    have "smods_ext q (- (p mod q)) = smods q (- (p mod q)) @ tl (smods_ext pp (pderiv pp))"
      apply (rule 1(1)[rule_format,of "smods_ext q (- (p mod q))" q "- (p mod q)",folded pp_def])
      using smods_ext_cons \<open>q\<noteq>0\<close> that by auto
    then show ?thesis unfolding pp_last
      apply (subst smods_cons)
      apply (subst smods_ext_cons)
      by auto
  qed
  moreover have ?case when "p mod q =0" "pderiv q = 0"
  proof -
    have "smods p q = [p,q]"
      using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> that by auto
    moreover have "smods_ext p q = [p,q]"
      using that \<open>p\<noteq>0\<close> by auto
    ultimately show ?case using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> that(1) by auto
  qed
  moreover have ?case when "p mod q =0" "pderiv q \<noteq> 0"
  proof -
    have smods_cons:"smods p q = [p,q]"
      using \<open>p\<noteq>0\<close> \<open>q\<noteq>0\<close> that by auto
    have smods_ext_cons:"smods_ext p q = p#smods_ext q (pderiv q)"
      using that \<open>p\<noteq>0\<close> by auto
    show ?case unfolding smods_cons smods_ext_cons
      apply (simp del:smods_ext.simps)
      by (simp add: "1.prems"(2))
  qed
  ultimately show ?case by argo
qed

lemma no_0_in_smods_ext: "0\<notin>set (smods_ext p q)"
  apply (induct "smods_ext p q" arbitrary:p q)
   apply simp
  by (metis list.distinct(1) list.inject set_ConsD smods_ext.simps)

subsection \<open>Sign variations on the alternative signed remainder sequences\<close>

definition changes_itv_smods_ext:: "real \<Rightarrow> real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_itv_smods_ext a b p q= (let ps= smods_ext p q in changes_poly_at ps a 
        - changes_poly_at ps b)"

definition changes_gt_smods_ext:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_gt_smods_ext a p q= (let ps= smods_ext p q in changes_poly_at ps a 
        - changes_poly_pos_inf ps)"

definition changes_le_smods_ext:: "real \<Rightarrow>real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_le_smods_ext b p q= (let ps= smods_ext p q in changes_poly_neg_inf ps 
        - changes_poly_at ps b)"

definition changes_R_smods_ext:: "real poly \<Rightarrow> real poly \<Rightarrow>  int" where
  "changes_R_smods_ext p q= (let ps= smods_ext p q in changes_poly_neg_inf ps 
        - changes_poly_pos_inf ps)"

subsection \<open>Extension of Sturm's theorem for multiple roots\<close>

theorem sturm_ext_interval:
  assumes "a<b" "poly p a\<noteq>0" "poly p b\<noteq>0"
  shows "proots_count p {x. a<x \<and> x<b} = changes_itv_smods_ext a b p (pderiv p)"
  using assms(2,3)
proof (induct "smods_ext p (pderiv p)" arbitrary:p rule:length_induct)
  case 1
  have "p\<noteq>0" using \<open>poly p a \<noteq> 0\<close> by auto 
  have ?case when "pderiv p=0"
  proof -
    obtain c where "p=[:c:]" "c\<noteq>0"
      using \<open>p\<noteq>0\<close> \<open>pderiv p = 0\<close> pderiv_iszero by force
    then have "proots_count p {x. a < x \<and> x < b} = 0"
      unfolding proots_count_def by auto
    moreover have "changes_itv_smods_ext a b p (pderiv p) = 0"
      unfolding changes_itv_smods_ext_def using \<open>p=[:c:]\<close> \<open>c\<noteq>0\<close> by auto
    ultimately show ?thesis by auto
  qed
  moreover have ?case when "pderiv p\<noteq>0"
  proof -
    define pp where "pp = last (smods p (pderiv p))"
    define lp where "lp = lead_coeff pp"
    define S where "S={x. a < x \<and> x< b}"

    have prefix:"smods_ext p (pderiv p) = smods p (pderiv p) @ tl (smods_ext pp (pderiv pp))"
      using smods_ext_prefix[OF \<open>p\<noteq>0\<close> \<open>pderiv p\<noteq>0\<close>,folded pp_def] .
    have pp_gcd:"pp = smult lp (gcd p (pderiv p))"
      using last_smods_gcd[OF \<open>p\<noteq>0\<close>,of "pderiv p",folded pp_def lp_def] .
    have "pp\<noteq>0" "lp\<noteq>0" unfolding pp_def lp_def
      subgoal by (rule last_smods_nzero[OF \<open>p\<noteq>0\<close>])
      subgoal using \<open>last (smods p (pderiv p)) \<noteq> 0\<close> by auto
      done
    have "poly pp a\<noteq>0" "poly pp b \<noteq> 0"
      unfolding pp_gcd using \<open>poly p a\<noteq>0\<close> \<open>poly p b\<noteq>0\<close> \<open>lp\<noteq>0\<close> 
      by (simp_all add:poly_gcd_0_iff)

    have "proots_count pp S = changes_itv_smods_ext a b pp (pderiv pp)" unfolding S_def
    proof (rule 1(1)[rule_format,of "smods_ext pp (pderiv pp)" pp])
      show "length (smods_ext pp (pderiv pp)) < length (smods_ext p (pderiv p))"
        unfolding prefix by (simp add: \<open>p \<noteq> 0\<close> that)
    qed (use \<open>poly pp a\<noteq>0\<close> \<open>poly pp b\<noteq>0\<close> in simp_all)
    moreover have "proots_count p S = card (proots_within p S) + proots_count pp S"
    proof -
      have "(\<Sum>r\<in>proots_within p S. order r p) = (\<Sum>r\<in> proots_within p S. order r pp + 1)"
      proof (rule sum.cong)
        fix x assume "x \<in> proots_within p S"
        have "order x pp = order x (gcd p (pderiv p))"
          unfolding pp_gcd using \<open>lp\<noteq>0\<close> by (simp add:order_smult)
        also have "... = min (order x p) (order x (pderiv p))"
          apply (subst order_gcd)
          using \<open>p\<noteq>0\<close> \<open>pderiv p\<noteq>0\<close> by simp_all
        also have "... = order x (pderiv p)"
          apply (subst order_pderiv)
          using \<open>pderiv p\<noteq>0\<close> \<open>p \<noteq> 0\<close> \<open>x \<in> proots_within p S\<close> order_root by auto
        finally have "order x pp = order x (pderiv p)" .
        moreover have "order x p = order x (pderiv p) + 1"
          apply (subst order_pderiv)
          using \<open>pderiv p\<noteq>0\<close> \<open>p \<noteq> 0\<close> \<open>x \<in> proots_within p S\<close> order_root by auto
        ultimately show "order x p = order x pp + 1" by auto
      qed simp
      also have "... = card (proots_within p S) + (\<Sum>r\<in> proots_within p S. order r pp)"
        apply (subst sum.distrib)
        by auto
      also have "... = card (proots_within p S) + (\<Sum>r\<in> proots_within pp S. order r pp)"
      proof -
        have "(\<Sum>r\<in>proots_within p S. order r pp) = (\<Sum>r\<in>proots_within pp S. order r pp)"
          apply (rule sum.mono_neutral_right)
          subgoal using \<open>p\<noteq>0\<close> by auto
          subgoal unfolding pp_gcd using \<open>lp\<noteq>0\<close> by (auto simp:poly_gcd_0_iff)
          subgoal unfolding pp_gcd using \<open>lp\<noteq>0\<close> 
            apply (auto simp:poly_gcd_0_iff order_smult)
            apply (subst order_gcd)
            by (auto simp add: order_root)
          done
        then show ?thesis by simp
      qed
      finally show ?thesis unfolding proots_count_def .
    qed
    moreover have "card (proots_within p S) = changes_itv_smods a b p (pderiv p)" 
      using sturm_interval[OF \<open>a<b\<close> \<open>poly p a\<noteq>0\<close> \<open>poly p b\<noteq>0\<close>,symmetric] 
      unfolding S_def proots_within_def 
      by (auto intro!:arg_cong[where f=card])
    moreover have "changes_itv_smods_ext a b p (pderiv p) 
            = changes_itv_smods a b p (pderiv p) + changes_itv_smods_ext a b pp (pderiv pp)"
    proof -
      define xs ys where "xs=smods p (pderiv p)" and "ys=smods_ext pp (pderiv pp)"
      have xys: "xs\<noteq>[]" "ys\<noteq>[]" "last xs=hd ys" "poly (last xs) a\<noteq>0" "poly (last xs) b\<noteq>0"
        subgoal unfolding xs_def using \<open>p\<noteq>0\<close> by auto
        subgoal unfolding ys_def using \<open>pp\<noteq>0\<close> by auto
        subgoal using \<open>pp\<noteq>0\<close> unfolding xs_def ys_def 
          apply (fold pp_def)
          by auto
        subgoal using \<open>poly pp a\<noteq>0\<close> unfolding pp_def xs_def .
        subgoal using \<open>poly pp b\<noteq>0\<close> unfolding pp_def xs_def .
        done
      have "changes_poly_at (xs @ tl ys) a = changes_poly_at xs a + changes_poly_at ys a"
      proof -
        have "changes_poly_at (xs @ tl ys) a  = changes_poly_at (xs @ ys) a"
          unfolding changes_poly_at_def
          apply (simp add:map_tl)
          apply (subst changes_drop_dup[symmetric])
          using that xys by (auto simp add: hd_map last_map)
        also have "... = changes_poly_at xs a + changes_poly_at ys a"
          unfolding changes_poly_at_def
          apply (subst changes_append[symmetric])
          using xys by (auto simp add: hd_map last_map)
        finally show ?thesis .
      qed
      moreover have "changes_poly_at (xs @ tl ys) b = changes_poly_at xs b + changes_poly_at ys b"
      proof -
        have "changes_poly_at (xs @ tl ys) b  = changes_poly_at (xs @ ys) b"
          unfolding changes_poly_at_def
          apply (simp add:map_tl)
          apply (subst changes_drop_dup[symmetric])
          using that xys by (auto simp add: hd_map last_map)
        also have "... = changes_poly_at xs b + changes_poly_at ys b"
          unfolding changes_poly_at_def
          apply (subst changes_append[symmetric])
          using xys by (auto simp add: hd_map last_map)
        finally show ?thesis .
      qed
      ultimately show ?thesis unfolding changes_itv_smods_ext_def changes_itv_smods_def
        apply (fold xs_def ys_def,unfold prefix[folded xs_def ys_def] Let_def)
        by auto
    qed
    ultimately show "proots_count p S = changes_itv_smods_ext a b p (pderiv p)"
      by auto
  qed
  ultimately show ?case by argo
qed

theorem sturm_ext_above:
  assumes "poly p a\<noteq>0" 
  shows "proots_count p {x. a<x} = changes_gt_smods_ext a p (pderiv p)"
proof -
  define ps where "ps\<equiv>smods_ext p (pderiv p)"
  have "p\<noteq>0" and "p\<in>set ps" using \<open>poly p a\<noteq>0\<close> ps_def by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
    and "ub>a"
    using root_list_ub[OF no_0_in_smods_ext,of p "pderiv p",folded ps_def]
    by auto
  have "proots_count p {x. a<x} = proots_count p {x. a<x \<and> x<ub}"
    unfolding proots_count_def
    apply (rule sum.cong)
    by (use ub \<open>p\<in>set ps\<close> in auto)
  moreover have "changes_gt_smods_ext a p (pderiv p) = changes_itv_smods_ext a ub p (pderiv p)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
      using ub_sgn[THEN spec,of ub,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps ub=changes_poly_pos_inf ps"
      unfolding changes_poly_pos_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_gt_smods_ext_def changes_itv_smods_ext_def ps_def
      by metis
  qed
  moreover have "poly p ub\<noteq>0" using ub \<open>p\<in>set ps\<close> by auto
  ultimately show ?thesis using sturm_ext_interval[OF \<open>ub>a\<close> assms] by auto
qed

theorem sturm_ext_below:
  assumes "poly p b\<noteq>0" 
  shows "proots_count p {x. x<b} = changes_le_smods_ext b p (pderiv p)"
proof -
  define ps where "ps\<equiv>smods_ext p (pderiv p)"
  have "p\<noteq>0" and "p\<in>set ps" using \<open>poly p b\<noteq>0\<close> ps_def by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
    and "lb<b"
    using root_list_lb[OF no_0_in_smods_ext,of p "pderiv p",folded ps_def] 
    by auto
  have "proots_count p {x. x<b} = proots_count p {x. lb<x \<and> x<b}"
    unfolding proots_count_def by (rule sum.cong,insert lb \<open>p\<in>set ps\<close>,auto)
  moreover have "changes_le_smods_ext b p (pderiv p) = changes_itv_smods_ext lb b p (pderiv p)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
      using lb_sgn[THEN spec,of lb,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)
    hence "changes_poly_at ps lb=changes_poly_neg_inf ps"
      unfolding changes_poly_neg_inf_def changes_poly_at_def
      by (subst changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_le_smods_ext_def changes_itv_smods_ext_def ps_def
      by metis
  qed
  moreover have "poly p lb\<noteq>0" using lb \<open>p\<in>set ps\<close> by auto
  ultimately show ?thesis using sturm_ext_interval[OF \<open>lb<b\<close> _ assms] by auto
qed

theorem sturm_ext_R: 
  assumes "p\<noteq>0"
  shows "proots_count p UNIV = changes_R_smods_ext p (pderiv p)"
proof - 
  define ps where "ps\<equiv>smods_ext p (pderiv p)"
  have "p\<in>set ps" using ps_def \<open>p\<noteq>0\<close> by auto
  obtain lb where lb:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x>lb"
    and lb_sgn:"\<forall>x\<le>lb. \<forall>p\<in>set ps. sgn (poly p x) = sgn_neg_inf p"
    and "lb<0"
    using root_list_lb[OF no_0_in_smods_ext,of p "pderiv p",folded ps_def] 
    by auto
  obtain ub where ub:"\<forall>p\<in>set ps. \<forall>x. poly p x=0 \<longrightarrow> x<ub"
    and ub_sgn:"\<forall>x\<ge>ub. \<forall>p\<in>set ps. sgn (poly p x) = sgn_pos_inf p"
    and "ub>0"
    using root_list_ub[OF no_0_in_smods_ext,of p "pderiv p",folded ps_def] 
    by auto
  have "proots_count p UNIV = proots_count p {x. lb<x \<and> x<ub}"
    unfolding proots_count_def by (rule sum.cong,insert lb ub \<open>p\<in>set ps\<close>,auto)
  moreover have "changes_R_smods_ext p (pderiv p) = changes_itv_smods_ext lb ub p (pderiv p)"
  proof -
    have "map (sgn \<circ> (\<lambda>p. poly p lb)) ps = map sgn_neg_inf ps"
      and "map (sgn \<circ> (\<lambda>p. poly p ub)) ps = map sgn_pos_inf ps"
      using lb_sgn[THEN spec,of lb,simplified] ub_sgn[THEN spec,of ub,simplified] 
      by (metis (mono_tags, lifting) comp_def list.map_cong0)+
    hence "changes_poly_at ps lb=changes_poly_neg_inf ps
          \<and> changes_poly_at ps ub=changes_poly_pos_inf ps"
      unfolding changes_poly_neg_inf_def changes_poly_at_def changes_poly_pos_inf_def
      by (subst (1 3)  changes_map_sgn_eq,metis map_map)
    thus ?thesis unfolding changes_R_smods_ext_def changes_itv_smods_ext_def ps_def
      by metis
  qed
  moreover have "poly p lb\<noteq>0" and "poly p ub\<noteq>0" using lb ub \<open>p\<in>set ps\<close> by auto
  moreover have "lb<ub" using \<open>lb<0\<close> \<open>0<ub\<close> by auto
  ultimately show ?thesis using sturm_ext_interval by auto
qed

end