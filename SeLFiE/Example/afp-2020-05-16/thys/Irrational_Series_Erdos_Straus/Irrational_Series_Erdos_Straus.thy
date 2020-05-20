(* Title:      Irrational_Series_Erdos_Straus.thy
   Author:     Angeliki Koutsoukou-Argyraki and Wenda Li, University of Cambridge, UK.

We formalise certain irrationality criteria for infinite series by P. Erdos and E.G. Straus.
In particular, we formalise Theorem 2.1, Corollary 2.10 and Theorem 3.1 in [1]. The latter is an 
application of Theorem 2.1 involving the prime numbers.

References:
[1]  P. Erdos and E.G. Straus, On the irrationality of certain series, Pacific Journal of 
Mathematics, Vol. 55, No 1, 1974  https://projecteuclid.org/euclid.pjm/1102911140
*)

theory "Irrational_Series_Erdos_Straus" imports
  Prime_Number_Theorem.Prime_Number_Theorem
  Prime_Distribution_Elementary.PNT_Consequences
begin

section \<open>Miscellaneous\<close>

lemma suminf_comparison:
  assumes "summable f" and "\<forall>n. norm (g n) \<le> f n"
  shows "suminf g \<le> suminf f"
proof (rule suminf_le)
  show "\<forall>n. g n \<le> f n" 
    apply rule
    subgoal for n using assms(2)[rule_format,of n] by auto
    done
  show "summable g" 
    apply (rule summable_comparison_test'[OF \<open>summable f\<close>, of 0])
    using assms(2) by auto
  show "summable f" using assms(1) .
qed

lemma tendsto_of_int_diff_0:
  assumes "(\<lambda>n. f n - of_int(g n)) \<longlonglongrightarrow> (0::real)" "\<forall>\<^sub>F n in sequentially. f n > 0"
  shows "\<forall>\<^sub>F n in sequentially. 0 \<le> g n"
proof -
  have "\<forall>\<^sub>F n in sequentially. \<bar>f n - of_int(g n)\<bar> < 1 / 2" 
    using assms(1)[unfolded tendsto_iff,rule_format,of "1/2"] by auto
  then show ?thesis using assms(2)
    apply eventually_elim
    by linarith
qed

lemma eventually_mono_sequentially:
  assumes "eventually P sequentially"
  assumes "\<And>x. P (x+k) \<Longrightarrow> Q (x+k)"
  shows "eventually Q sequentially"
  using sequentially_offset[OF assms(1),of k]
  apply (subst eventually_sequentially_seg[symmetric,of _ k])
  apply (elim eventually_mono)
  by fact

lemma frequently_eventually_at_top:
  fixes P Q::"'a::linorder \<Rightarrow> bool"
  assumes "frequently P at_top" "eventually Q at_top"
  shows "frequently (\<lambda>x. P x \<and> (\<forall>y\<ge>x. Q y) ) at_top"
  using assms
  unfolding frequently_def eventually_at_top_linorder 
  by (metis (mono_tags, hide_lams) le_cases order_trans)

lemma eventually_at_top_mono:
  fixes P Q::"'a::linorder \<Rightarrow> bool"
  assumes event_P:"eventually P at_top"
  assumes PQ_imp:"\<And>x. x\<ge>z \<Longrightarrow> \<forall>y\<ge>x. P y \<Longrightarrow> Q x"
  shows "eventually Q at_top"
proof -
  obtain N where N_P:"\<forall>n\<ge>N. P n"
    using event_P[unfolded eventually_at_top_linorder] by auto
  define N' where "N' = max N z"
  have "Q x" when "x\<ge>N'" for x 
    apply (rule PQ_imp)
    using N_P that unfolding N'_def by auto
  then show ?thesis unfolding eventually_at_top_linorder
    by auto
qed

lemma frequently_at_top_elim:
  fixes P Q::"'a::linorder \<Rightarrow> bool"
  assumes "\<exists>\<^sub>Fx in at_top. P x"
  assumes "\<And>i. P i \<Longrightarrow> \<exists>j>i. Q j"
  shows "\<exists>\<^sub>Fx in at_top. Q x"
  using assms unfolding frequently_def eventually_at_top_linorder 
  by (meson leD le_cases less_le_trans)

lemma less_Liminf_iff:
  fixes X :: "_ \<Rightarrow> _ :: complete_linorder"
  shows "Liminf F X < C \<longleftrightarrow> (\<exists>y<C. frequently (\<lambda>x. y \<ge> X x) F)"
  apply (subst Not_eq_iff[symmetric])
  apply (simp add:not_less not_frequently not_le le_Liminf_iff)
  by force

lemma sequentially_even_odd_imp:
  assumes "\<forall>\<^sub>F N in sequentially. P (2*N)" "\<forall>\<^sub>F N in sequentially. P (2*N+1)"
  shows "\<forall>\<^sub>F n in sequentially. P n"
proof -
  obtain N where N_P:"\<forall>x\<ge>N.  P (2 * x) \<and> P (2 * x + 1)"
    using eventually_conj[OF assms] 
    unfolding eventually_at_top_linorder by auto
  define N' where "N'=2*N "
  have "P n" when "n\<ge>2*N" for n
  proof -
    define n' where "n'= n div 2"
    then have "n'\<ge>N" using that by auto
    then have "P (2 * n') \<and> P (2 * n' + 1)"
      using N_P by auto
    then show ?thesis unfolding n'_def
      apply (cases "even n")
      by auto
  qed
  then show ?thesis unfolding eventually_at_top_linorder by auto
qed


section \<open>Theorem 2.1 and Corollary 2.10\<close>

context
  fixes a b ::"nat\<Rightarrow>int "
  assumes a_pos:"\<forall> n. a n >0 " and a_large:"\<forall>\<^sub>F n in sequentially. a n > 1" 
    and ab_tendsto: "(\<lambda>n. \<bar>b n\<bar> / (a (n-1)*a n)) \<longlonglongrightarrow> 0"
begin

private lemma aux_series_summable: "summable (\<lambda>n. b n / (\<Prod>k\<le>n. a k))" 
proof -
  have "\<forall>e>0. \<forall>\<^sub>F x in sequentially. \<bar>b x\<bar> / (a (x-1) * a x) < e"
    using ab_tendsto[unfolded tendsto_iff] 
    apply (simp add:of_int_abs[symmetric] abs_mult del:of_int_abs)
    by (subst (asm) (2) abs_of_pos,use \<open>\<forall> n. a n > 0\<close> in auto)+                 
  from this[rule_format,of 1]
  have "\<forall>\<^sub>F x in sequentially. \<bar>real_of_int(b x)\<bar> < (a (x-1) * a x)"
    using \<open>\<forall> n. a n >0\<close> by auto
  moreover have "\<forall>n. (\<Prod>k\<le>n. real_of_int (a k)) > 0" 
    using a_pos by (auto intro!:linordered_semidom_class.prod_pos)
  ultimately have "\<forall>\<^sub>F n in sequentially. \<bar>b n\<bar> / (\<Prod>k\<le>n. a k) 
                        < (a (n-1) * a n) / (\<Prod>k\<le>n. a k)"
    apply (elim eventually_mono)
    by (auto simp add:field_simps)
  moreover have "\<bar>b n\<bar> / (\<Prod>k\<le>n. a k) = norm (b n / (\<Prod>k\<le>n. a k))" for n 
    using \<open>\<forall>n. (\<Prod>k\<le>n. real_of_int (a k)) > 0\<close>[rule_format,of n] by auto
  ultimately have "\<forall>\<^sub>F n in sequentially. norm (b n / (\<Prod>k\<le>n. a k)) 
                        < (a (n-1) * a n) / (\<Prod>k\<le>n. a k)"
    by algebra
  moreover have "summable (\<lambda>n. (a (n-1) * a n) / (\<Prod>k\<le>n. a k))" 
  proof -
    obtain s where a_gt_1:"\<forall> n\<ge>s. a n >1"
      using a_large[unfolded eventually_at_top_linorder] by auto
    define cc where "cc= (\<Prod>k<s. a k)"
    have "cc>0" 
      unfolding cc_def
      apply (rule linordered_semidom_class.prod_pos)
      using a_pos by auto
    have "(\<Prod>k\<le>n+s. a k) \<ge> cc * 2^n" for n
    proof -
      have "prod a {s..<Suc (s + n)} \<ge> 2^n"
      proof (induct n)
        case 0
        then show ?case using a_gt_1 by auto
      next
        case (Suc n)
        moreover have "a (s + Suc n) \<ge> 2" 
          using a_gt_1 by (smt le_add1)
        ultimately show ?case 
          apply (subst prod.atLeastLessThan_Suc,simp)
          using mult_mono'[of 2 "a (Suc (s + n))" " 2 ^ n" "prod a {s..<Suc (s + n)}",simplified] 
          by (simp add: mult.commute)
      qed
      moreover have "prod a {0..(n + s)} =
            prod a {..<s} * prod a {s..<Suc (s + n)} "
        using prod.atLeastLessThan_concat[of 0 s "s+n+1" a,simplified]
        apply (simp add: atLeastLessThanSuc_atLeastAtMost algebra_simps
            atLeast0LessThan)
        by (smt a_gt_1 le_add2 lessThan_atLeast0 mult.left_commute prod.last_plus zero_le)
      ultimately show ?thesis
        using \<open>cc>0\<close> unfolding cc_def by (simp add: atLeast0AtMost)
    qed
    then have "1/(\<Prod>k\<le>n+s. a k) \<le> 1/(cc * 2^n)" for n
    proof -
      assume asm:"\<And>n. cc * 2 ^ n \<le> prod a {..n + s}"
      then have "real_of_int (cc * 2 ^ n) \<le> prod a {..n + s}" using of_int_le_iff by blast
      moreover have "prod a {..n + s} >0" using \<open>cc>0\<close> by (simp add: a_pos prod_pos)
      ultimately show ?thesis using \<open>cc>0\<close> 
        by (auto simp:field_simps simp del:of_int_prod)
    qed
    moreover have "summable (\<lambda>n. 1/(cc * 2^n))"
    proof -
      have "summable (\<lambda>n. 1/(2::int)^n)"
        using summable_geometric[of "1/(2::int)"] by (simp add:power_one_over)
      from summable_mult[OF this,of "1/cc"] show ?thesis by auto
    qed
    ultimately have "summable (\<lambda>n. 1 / (\<Prod>k\<le>n+s. a k))"
      apply (elim summable_comparison_test'[where N=0])
      apply (unfold real_norm_def, subst abs_of_pos)
      by (auto simp add: \<open>\<forall>n. 0 < (\<Prod>k\<le>n. real_of_int (a k))\<close>)
    then have "summable (\<lambda>n. 1 / (\<Prod>k\<le>n. a k))"
      apply (subst summable_iff_shift[where k=s,symmetric])
      by simp
    then have "summable (\<lambda>n. (a (n+1) * a (n+2)) / (\<Prod>k\<le>n+2. a k))"
    proof -
      assume asm:"summable (\<lambda>n. 1 / real_of_int (prod a {..n}))"
      have "1 / real_of_int (prod a {..n}) = (a (n+1) * a (n+2)) / (\<Prod>k\<le>n+2. a k)" for n 
      proof -
        have "a (Suc (Suc n)) \<noteq> 0" "a (Suc n) \<noteq>0" 
          using a_pos by (metis less_irrefl)+
        then show ?thesis 
          by (simp add: atLeast0_atMost_Suc atMost_atLeast0)
      qed
      then show ?thesis using asm by auto
    qed
    then show "summable (\<lambda>n. (a (n-1) * a n) / (\<Prod>k\<le>n. a k))"
      apply (subst summable_iff_shift[symmetric,of _ 2])
      by auto
  qed
  ultimately show ?thesis 
    apply (elim summable_comparison_test_ev[rotated])
    by (simp add: eventually_mono)
qed

private fun get_c::"(nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int)" where
  "get_c a' b' B N 0 = round (B * b' N / a' N)"|
  "get_c a' b' B N (Suc n) = get_c a' b' B N n * a' (n+N) - B * b' (n+N)"

lemma ab_rationality_imp:
  assumes ab_rational:"(\<Sum>n. (b n / (\<Prod>i \<le> n. a i))) \<in> \<rat>"
  shows "\<exists> (B::int)>0. \<exists> c::nat\<Rightarrow> int.
            (\<forall>\<^sub>F n in sequentially. B*b n = c n * a n - c(n+1) \<and> \<bar>c(n+1)\<bar><a n/2)
            \<and> (\<lambda>n. c (Suc n) / a n) \<longlonglongrightarrow> 0"
proof -
  have [simp]:"a n \<noteq> 0" for n using a_pos by (metis less_numeral_extra(3))
  obtain A::int and B::int where 
    AB_eq:"(\<Sum>n. real_of_int (b n) / real_of_int (prod a {..n})) = A / B" and "B>0"
  proof -
    obtain q::rat where "(\<Sum>n. real_of_int (b n) / real_of_int (prod a {..n})) = real_of_rat q"
      using ab_rational by (rule Rats_cases) simp
    moreover obtain A::int and B::int where "q = Rat.Fract A B" "B > 0" "coprime A B"
      by (rule Rat_cases) auto
    ultimately show ?thesis by (auto intro!: that[of A B] simp:of_rat_rat)
  qed  
  define f where "f = (\<lambda>n.  b n / real_of_int (prod a {..n}))"
  define R where "R = (\<lambda>N. (\<Sum>n. B*b (n+N+1) / prod a {N..n+N+1}))"
  have all_e_ubound:"\<forall>e>0. \<forall>\<^sub>F M in sequentially. \<forall>n. \<bar>B*b (n+M+1) / prod a {M..n+M+1}\<bar> < e/4 * 1/2^n"
  proof safe
    fix e::real assume "e>0"
    obtain N where N_a2: "\<forall>n \<ge> N. a n \<ge> 2" 
      and N_ba: "\<forall>n \<ge> N. \<bar>b n\<bar> / (a (n-1) * a n)  < e/(4*B)"
    proof -
      have "\<forall>\<^sub>F n in sequentially. \<bar>b n\<bar> / (a (n - 1) * a n) < e/(4*B)" 
        using order_topology_class.order_tendstoD[OF ab_tendsto,of "e/(4*B)"] \<open>B>0\<close> \<open>e>0\<close>
        by auto
      moreover have "\<forall>\<^sub>F n in sequentially. a n \<ge> 2"
        using a_large by (auto elim: eventually_mono)
      ultimately have "\<forall>\<^sub>F n in sequentially. \<bar>b n\<bar> / (a (n - 1) * a n) < e/(4*B) \<and> a n \<ge> 2" 
        by eventually_elim auto
      then show ?thesis unfolding eventually_at_top_linorder using that
        by auto
    qed
    have geq_N_bound:"\<bar>B*b (n+M+1) / prod a {M..n+M+1}\<bar> < e/4 * 1/2^n" when "M\<ge>N" for n M   
    proof -
      define D where "D = B*b (n+M+1)/ (a (n+M) * a (n+M+1))"
      have "\<bar>B*b (n+M+1) / prod a {M..n+M+1}\<bar> = \<bar>D / prod a {M..<n+M}\<bar>"
      proof -
        have "{M..n+M+1} = {M..<n+M} \<union> {n+M,n+M+1}" by auto
        then have "prod a {M..n+M+1} = a (n+M) * a (n+M+1)* prod a {M..<n+M}" by simp
        then show ?thesis unfolding D_def by (simp add:algebra_simps)
      qed
      also have "... <  \<bar>e/4 * (1/prod a {M..<n+M})\<bar>"
      proof -
        have "\<bar>D\<bar> < e/ 4" 
          unfolding D_def using N_ba[rule_format, of "n+M+1"] \<open>B>0\<close> \<open>M \<ge> N\<close> \<open>e>0\<close> a_pos
          by (auto simp:field_simps abs_mult abs_of_pos)
        from mult_strict_right_mono[OF this,of "1/prod a {M..<n+M}"] a_pos \<open>e>0\<close>
        show ?thesis 
          apply (auto simp:abs_prod abs_mult prod_pos)
          by (subst (2) abs_of_pos,auto)+
      qed
      also have "... \<le> e/4 * 1/2^n"
      proof -
        have "prod a {M..<n+M} \<ge> 2^n"
        proof (induct n)
          case 0
          then show ?case by simp
        next
          case (Suc n)
          then show ?case 
            using \<open>M\<ge>N\<close> by (simp add: N_a2 mult.commute mult_mono' prod.atLeastLessThan_Suc)
        qed
        then have "real_of_int (prod a {M..<n+M}) \<ge> 2^n" 
          using numeral_power_le_of_int_cancel_iff by blast
        then show ?thesis using \<open>e>0\<close> by (auto simp add:divide_simps)
      qed
      finally show ?thesis .
    qed
    show "\<forall>\<^sub>F M in sequentially. \<forall>n. \<bar>real_of_int (B * b (n + M + 1)) 
                / real_of_int (prod a {M..n + M + 1})\<bar> < e / 4 * 1 / 2 ^ n"
      apply (rule eventually_sequentiallyI[of N])
      using geq_N_bound by blast
  qed
  have R_tendsto_0:"R \<longlonglongrightarrow> 0"
  proof (rule tendstoI)
    fix e::real assume "e>0"
    show "\<forall>\<^sub>F x in sequentially. dist (R x) 0 < e" using all_e_ubound[rule_format,OF \<open>e>0\<close>]
    proof eventually_elim
      case (elim M)
      define g where "g = (\<lambda>n. B*b (n+M+1) / prod a {M..n+M+1})"
      have g_lt:"\<bar>g n\<bar> < e/4 * 1/2^n" for n
        using elim unfolding g_def by auto
      have g_abs_summable:"summable (\<lambda>n. \<bar>g n\<bar>)"
      proof -
        have "summable (\<lambda>n. e/4 * 1/2^n)" 
          using summable_geometric[of "1/2",THEN summable_mult,of "e/4",simplified]
          by (auto simp add:algebra_simps power_divide)
        then show ?thesis 
          apply (elim summable_comparison_test')
          using g_lt less_eq_real_def by auto
      qed
      have "\<bar>\<Sum>n. g n\<bar> \<le> (\<Sum>n. \<bar>g n\<bar>)" by (rule summable_rabs[OF g_abs_summable])
      also have "... \<le>(\<Sum>n. e/4 * 1/2^n)"
      proof (rule suminf_comparison)
        show "summable (\<lambda>n. e/4 * 1/2^n)" 
          using summable_geometric[of "1/2",THEN summable_mult,of "e/4",simplified]
          by (auto simp add:algebra_simps power_divide)
        show "\<forall>n. norm \<bar>g n\<bar> \<le> e / 4 * 1 / 2 ^ n" using g_lt less_eq_real_def by auto
      qed
      also have "... = (e/4) * (\<Sum>n. (1/2)^n)"
        apply (subst suminf_mult[symmetric])
        subgoal 
          apply (rule complete_algebra_summable_geometric)
          by simp
        subgoal by (auto simp:algebra_simps power_divide)
        done
      also have "... = e/2" by (simp add:suminf_geometric[of "1/2"])
      finally have "\<bar>\<Sum>n. g n\<bar> \<le> e / 2" .
      then show "dist (R M) 0 < e" unfolding R_def g_def using \<open>e>0\<close> by auto
    qed
  qed

  obtain N where R_N_bound:"\<forall>M \<ge> N. \<bar>R M\<bar> \<le>  1 / 4"
    and N_geometric:"\<forall>M\<ge>N. \<forall>n. \<bar>real_of_int (B * b (n + M + 1)) / (prod a {M..n + M + 1})\<bar> < 1 / 2 ^ n"
  proof -
    obtain N1 where N1:"\<forall>M \<ge> N1. \<bar>R M\<bar> \<le>  1 / 4"
      using metric_LIMSEQ_D[OF R_tendsto_0,of "1/4"] all_e_ubound[rule_format,of 4,unfolded eventually_sequentially]
      by (auto simp:less_eq_real_def)
    obtain N2 where N2:"\<forall>M\<ge>N2. \<forall>n. \<bar>real_of_int (B * b (n + M + 1)) 
                          / (prod a {M..n + M + 1})\<bar> < 1 / 2 ^ n"
      using all_e_ubound[rule_format,of 4,unfolded eventually_sequentially]
      by (auto simp:less_eq_real_def)
    define N where "N=max N1 N2"
    show ?thesis using that[of N] N1 N2 unfolding N_def by simp
  qed

  define C where "C = B * prod a {..<N} * (\<Sum>n<N. f n)"
  have "summable f"
    unfolding f_def using aux_series_summable .
  have "A * prod a {..<N} = C + B * b N / a N  + R N" 
  proof -
    have "A * prod a {..<N} = B * prod a {..<N} * (\<Sum>n. f n)"
      unfolding AB_eq f_def using \<open>B>0\<close> by auto
    also have "... = B * prod a {..<N} * ((\<Sum>n<N+1. f n) + (\<Sum>n. f (n+N+1)))"
      using suminf_split_initial_segment[OF \<open>summable f\<close>, of "N+1"] by auto
    also have "... = B * prod a {..<N} * ((\<Sum>n<N. f n) + f N + (\<Sum>n. f (n+N+1)))"
      using sum.atLeast0_lessThan_Suc by simp
    also have "... = C + B * b N / a N + (\<Sum>n. B*b (n+N+1) / prod a {N..n+N+1})"
    proof -
      have "B * prod a {..<N} * f N = B * b N / a N" 
      proof -
        have "{..N} =  {..<N} \<union> {N}" using ivl_disj_un_singleton(2) by blast
        then show ?thesis unfolding f_def by auto
      qed
      moreover have "B * prod a {..<N} * (\<Sum>n. f (n+N+1)) = (\<Sum>n. B*b (n+N+1) / prod a {N..n+N+1})"
      proof -
        have "summable (\<lambda>n. f (n + N + 1))" 
          using \<open>summable f\<close> summable_iff_shift[of f "N+1"] by auto
        moreover have "prod a {..<N} * f (n + N + 1) = b (n + N + 1) / prod a {N..n + N + 1}" for n
        proof -
          have "{..n + N + 1} = {..<N} \<union> {N..n + N + 1}" by auto
          then show ?thesis 
            unfolding f_def
            apply simp
            apply (subst prod.union_disjoint)
            by auto
        qed
        ultimately show ?thesis 
          apply (subst suminf_mult[symmetric])
          by (auto simp add: mult.commute mult.left_commute)
      qed
      ultimately show ?thesis unfolding C_def by (auto simp:algebra_simps)
    qed
    also have "... = C +B * b N / a N  + R N"
      unfolding R_def by simp
    finally show ?thesis .
  qed
  have R_bound:"\<bar>R M\<bar> \<le> 1 / 4" and R_Suc:"R (Suc M) = a M * R M - B * b (Suc M) / a (Suc M)" 
    when "M \<ge> N" for M
  proof -
    define g where "g = (\<lambda>n. B*b (n+M+1) / prod a {M..n+M+1})"
    have g_abs_summable:"summable (\<lambda>n. \<bar>g n\<bar>)"
    proof -
      have "summable (\<lambda>n.(1::real)/2^n)" 
        using summable_geometric[of "(1::real)/2",simplified] 
        by (auto elim!: back_subst[of "summable"] simp:field_simps)
      moreover have "\<bar>g n\<bar> < 1/2^n" for n
        using N_geometric[rule_format,OF that] unfolding g_def by simp
      ultimately show ?thesis 
        apply (elim summable_comparison_test')
        using less_eq_real_def by auto
    qed
    show "\<bar>R M\<bar> \<le> 1 / 4" using R_N_bound[rule_format,OF that] .
    have "R M = (\<Sum>n. g n)" unfolding R_def g_def by simp
    also have "... = g 0 + (\<Sum>n. g (Suc n))"
      apply (subst suminf_split_head)
      using summable_rabs_cancel[OF g_abs_summable] by auto
    also have "... = g 0 + 1/a M * (\<Sum>n. a M * g (Suc n))"
      apply (subst suminf_mult)
      by (auto simp add: g_abs_summable summable_Suc_iff summable_rabs_cancel)
    also have "... = g 0 + 1/a M * R (Suc M)"
    proof -
      have "a M * g (Suc n) = B * b (n + M + 2) / prod a {Suc M..n + M + 2}" for n
      proof -
        have "{M..Suc (Suc (M + n))} = {M} \<union> {Suc M..Suc (Suc (M + n))}" by auto
        then show ?thesis 
          unfolding g_def using \<open>B>0\<close> by (auto simp add:algebra_simps)
      qed
      then have "(\<Sum>n. a M * g (Suc n)) = R (Suc M)"
        unfolding R_def by auto
      then show ?thesis by auto
    qed
    finally have "R M = g 0 + 1 / a M * R (Suc M)" .
    then have "R (Suc M) = a M * R M - g 0 * a M" 
      by (auto simp add:algebra_simps)
    moreover have "{M..Suc M} = {M,Suc M}" by auto
    ultimately show "R (Suc M) = a M * R M - B * b (Suc M) / a (Suc M)" 
      unfolding g_def by auto
  qed

  define c where "c = (\<lambda>n. if n\<ge>N then get_c a b B N (n-N) else undefined)"
  have c_rec:"c (n+1) = c n * a n -  B * b n" when "n \<ge> N" for n
    unfolding c_def using that by (auto simp:Suc_diff_le)
  have c_R:"c (Suc n) / a n = R n" when "n \<ge> N" for n
    using that
  proof (induct rule:nat_induct_at_least)
    case base
    have "\<bar> c (N+1) / a N \<bar> \<le> 1/2" 
    proof -
      have "c N = round (B * b N / a N)" unfolding c_def by simp
      moreover have "c (N+1) / a N = c N - B * b N / a N"
        using a_pos[rule_format,of N]
        by (auto simp add:c_rec[of N,simplified] divide_simps)
      ultimately show ?thesis using of_int_round_abs_le by auto
    qed        
    moreover have "\<bar>R N\<bar> \<le> 1 / 4" using R_bound[of N] by simp
    ultimately have "\<bar>c (N+1) / a N - R N \<bar> < 1" by linarith
    moreover have "c (N+1) / a N - R N \<in> \<int>"
    proof -
      have "c (N+1) / a N = c N - B * b N / a N"
        using a_pos[rule_format,of N]
        by (auto simp add:c_rec[of N,simplified] divide_simps)
      moreover have " B * b N / a N + R N \<in> \<int>" 
      proof -
        have "C = B * (\<Sum>n<N. prod a {..<N} * (b n / prod a {..n}))"
          unfolding C_def f_def by (simp add:sum_distrib_left algebra_simps)
        also have "... = B * (\<Sum>n<N. prod a {n<..<N} * b n)"
        proof -
          have "{..<N} = {n<..<N} \<union> {..n}" if "n<N" for n 
            by (simp add: ivl_disj_un_one(1) sup_commute that)
          then show ?thesis
            using \<open>B>0\<close> 
            apply simp
            apply (subst prod.union_disjoint)
            by auto
        qed
        finally have "C = real_of_int (B * (\<Sum>n<N. prod a {n<..<N} * b n))" .
        then have "C \<in> \<int>" using Ints_of_int by blast
        moreover note \<open>A * prod a {..<N} = C + B * b N / a N  + R N\<close>
        ultimately show ?thesis 
          by (metis Ints_diff Ints_of_int add.assoc add_diff_cancel_left')
      qed
      ultimately show ?thesis by (simp add: diff_diff_add)
    qed
    ultimately have "c (N+1) / a N - R N = 0"
      by (metis Ints_cases less_irrefl of_int_0 of_int_lessD)
    then show ?case by simp
  next
    case (Suc n)
    have "c (Suc (Suc n)) / a (Suc n) = c (Suc n) - B * b (Suc n) / a (Suc n)"
      apply (subst c_rec[of "Suc n",simplified])
      using \<open>N \<le> n\<close> by (auto simp add: divide_simps)
    also have "... = a n * R n - B * b (Suc n) / a (Suc n)"  
      using Suc by (auto simp: divide_simps)
    also have "... = R (Suc n)"
      using R_Suc[OF \<open>N \<le> n\<close>] by simp
    finally  show ?case .
  qed
  have ca_tendsto_zero:"(\<lambda>n. c (Suc n) / a n) \<longlonglongrightarrow> 0"
    using R_tendsto_0 
    apply (elim filterlim_mono_eventually)
    using c_R by (auto intro!:eventually_sequentiallyI[of N])
  have ca_bound:"\<bar>c (n + 1)\<bar> < a n / 2" when "n \<ge> N" for n
  proof -
    have "\<bar>c (Suc n)\<bar> / a n  = \<bar>c (Suc n) / a n\<bar>" using a_pos[rule_format,of n] by auto
    also have "... = \<bar>R n\<bar>" using c_R[OF that] by auto
    also have "... < 1/2" using R_bound[OF that] by auto
    finally have "\<bar>c (Suc n)\<bar> / a n < 1/2" .
    then show ?thesis using a_pos[rule_format,of n] by auto
  qed

(* (* the following part corresponds to (2.7) (2.8) in the original paper, but turns out to be
        not necessary. *)
  have c_round:"c n = round (B * b n / a n)" when "n \<ge> N" for n
  proof (cases "n=N")
    case True
    then show ?thesis unfolding c_def by simp
  next
    case False
    with \<open>n\<ge>N\<close> obtain n' where n_Suc:"n=Suc n'" and "n' \<ge> N" 
      by (metis le_eq_less_or_eq lessE less_imp_le_nat)
    have "B * b n / a n = c n - R n"
    proof -
      have "R n = c n - B * b n / a n"
        using c_R[OF \<open>n'\<ge>N\<close>,symmetric,folded n_Suc] R_Suc[OF \<open>n'\<ge>N\<close>,folded n_Suc]
        by (auto simp:field_simps)
      then show ?thesis by (auto simp:field_simps)
    qed
    then have "\<bar>B * b n / a n - c n\<bar> = \<bar>R n\<bar>" by auto
    then have "\<bar>B * b n / a n - c n\<bar> < 1/2" using R_bound[OF \<open>n \<ge> N\<close>] by auto
    from round_unique'[OF this] show ?thesis by auto
  qed
  *)
  show "\<exists>B>0. \<exists>c. (\<forall>\<^sub>F n in sequentially. B * b n = c n * a n - c (n + 1) 
            \<and> real_of_int \<bar>c (n + 1)\<bar> < a n / 2) \<and> (\<lambda>n. c (Suc n) / a n) \<longlonglongrightarrow> 0"
    unfolding eventually_at_top_linorder
    apply (rule exI[of _ B],use \<open>B>0\<close> in simp)
    apply (intro exI[of _c] exI[of _ N])
    using c_rec ca_bound ca_tendsto_zero 
    by fastforce
qed

private lemma imp_ab_rational:
  assumes "\<exists> (B::int)>0. \<exists> c::nat\<Rightarrow> int.
              (\<forall>\<^sub>F n in sequentially. B*b n = c n * a n - c(n+1) \<and> \<bar>c(n+1)\<bar><a n/2)"
  shows "(\<Sum>n. (b n / (\<Prod>i \<le> n. a i))) \<in> \<rat>"
proof -
  obtain B::int and c::"nat\<Rightarrow>int" and N::nat where "B>0" and  
    large_n:"\<forall>n\<ge>N. B * b n = c n * a n - c (n + 1) \<and> real_of_int \<bar>c (n + 1)\<bar> < a n / 2
                      \<and> a n\<ge>2"
  proof -
    obtain B c where "B>0" and event1:"\<forall>\<^sub>F n in sequentially. B * b n = c n * a n - c (n + 1) 
              \<and> real_of_int \<bar>c (n + 1)\<bar> < real_of_int (a n) / 2"
      using assms by auto
    from eventually_conj[OF event1 a_large,unfolded eventually_at_top_linorder]
    obtain N where "\<forall>n\<ge>N. (B * b n = c n * a n - c (n + 1) 
                        \<and> real_of_int \<bar>c (n + 1)\<bar> < real_of_int (a n) / 2) \<and> 2 \<le> a n"
      by fastforce
    then show ?thesis using that[of B N c] \<open>B>0\<close> by auto
  qed
  define f where "f=(\<lambda>n. real_of_int (b n) / real_of_int (prod a {..n}))"
  define S where "S = (\<Sum>n. f n)"
  have "summable f"
    unfolding f_def by (rule aux_series_summable)
  define C where "C=B*prod a {..<N} * (\<Sum>n<N. f n)"
  have "B*prod a {..<N} * S = C + real_of_int (c N)" 
  proof -
    define h1 where "h1= (\<lambda>n. (c (n+N) * a (n+N)) / prod a {N..n+N})"
    define h2 where "h2 = (\<lambda>n. c (n+N+1) / prod a {N..n+N})"
    have f_h12:"B*prod a {..<N}*f (n+N) = h1 n - h2 n" for n 
    proof -
      define g1 where "g1 = (\<lambda>n. B * b (n+N))"
      define g2 where "g2 = (\<lambda>n. prod a {..<N} / prod a {..n + N})"
      have "B*prod a {..<N}*f (n+N) = (g1 n * g2 n)"
        unfolding f_def g1_def g2_def by (auto simp:algebra_simps)
      moreover have "g1 n = c (n+N) * a (n+N) - c (n+N+1)" 
        using large_n[rule_format,of "n+N"] unfolding g1_def by auto
      moreover have "g2 n = (1/prod a {N..n+N})" 
      proof -
        have "prod a ({..<N} \<union> {N..n + N}) = prod a {..<N} * prod a {N..n + N}"
          apply (rule prod.union_disjoint[of "{..<N}" "{N..n+N}" a])
          by auto
        moreover have "prod a ({..<N} \<union> {N..n + N}) = prod a {..n+N}"
          by (simp add: ivl_disj_un_one(4))
        ultimately show ?thesis 
          unfolding g2_def
          apply simp
          using a_pos by (metis less_irrefl)
      qed
      ultimately have "B*prod a {..<N}*f (n+N) = (c (n+N) * a (n+N) - c (n+N+1)) / prod a {N..n+N}"
        by auto
      also have "... = h1 n - h2 n"
        unfolding h1_def h2_def by (auto simp:algebra_simps diff_divide_distrib)
      finally show ?thesis by simp
    qed
    have "B*prod a {..<N} * S = B*prod a {..<N} * ((\<Sum>n<N. f n) + (\<Sum>n. f (n+N)))"
      using suminf_split_initial_segment[OF \<open>summable f\<close>,of N] 
      unfolding S_def by (auto simp:algebra_simps)
    also have "... = C + B*prod a {..<N}*(\<Sum>n. f (n+N))"
      unfolding C_def by (auto simp:algebra_simps)
    also have "... = C + (\<Sum>n. h1 n - h2 n)"
      apply (subst suminf_mult[symmetric])
      subgoal using \<open>summable f\<close> by (simp add: summable_iff_shift)
      subgoal using f_h12 by auto
      done
    also have "... = C + h1 0"
    proof -
      have "(\<lambda>n. \<Sum>i\<le>n. h1 i - h2 i) \<longlonglongrightarrow> (\<Sum>i. h1 i - h2 i)"
      proof (rule summable_LIMSEQ')
        have "(\<lambda>i. h1 i - h2 i) = (\<lambda>i.  real_of_int (B * prod a {..<N}) * f (i + N))"
          using f_h12 by auto
        then show "summable (\<lambda>i. h1 i - h2 i)"
          using \<open>summable f\<close> by (simp add: summable_iff_shift summable_mult)
      qed
      moreover have "(\<Sum>i\<le>n. h1 i - h2 i)  = h1 0 - h2 n" for n
      proof (induct n)
        case 0
        then show ?case by simp
      next
        case (Suc n)
        have "(\<Sum>i\<le>Suc n. h1 i - h2 i) = (\<Sum>i\<le>n. h1 i - h2 i) + h1 (n+1) - h2 (n+1)"
          by auto
        also have "... =  h1 0 - h2 n + h1 (n+1) - h2 (n+1)" using Suc by auto
        also have "... = h1 0 - h2 (n+1)"
        proof -
          have "h2 n = h1 (n+1)"
            unfolding h2_def h1_def 
            apply (auto simp:prod.nat_ivl_Suc')
            using a_pos by (metis less_numeral_extra(3))
          then show ?thesis by auto
        qed
        finally show ?case by simp
      qed
      ultimately have "(\<lambda>n. h1 0 - h2 n) \<longlonglongrightarrow> (\<Sum>i. h1 i - h2 i)" by simp
      then have "h2 \<longlonglongrightarrow> (h1 0 -  (\<Sum>i. h1 i - h2 i))"
        apply (elim metric_tendsto_imp_tendsto)
        by (auto intro!:eventuallyI simp add:dist_real_def)
      moreover have "h2 \<longlonglongrightarrow> 0"
      proof -
        have h2_n:"\<bar>h2 n\<bar> < (1 / 2)^(n+1)" for n 
        proof -
          have "\<bar>h2 n\<bar> = \<bar>c (n + N + 1)\<bar> / prod a {N..n + N}"
            unfolding h2_def abs_divide
            using a_pos by (simp add: abs_of_pos prod_pos)
          also have "... < (a (N+n) / 2) / prod a {N..n + N}"
            unfolding h2_def
            apply (rule divide_strict_right_mono)
            subgoal using large_n[rule_format,of "N+n"] by (auto simp add:algebra_simps)
            subgoal using a_pos by (simp add: prod_pos)
            done
          also have "... = 1 / (2*prod a {N..<n + N})"
            apply (subst ivl_disj_un(6)[of N "n+N",symmetric])
            using a_pos[rule_format,of "N+n"] by (auto simp add:algebra_simps)
          also have "... \<le> (1/2)^(n+1)"
          proof (induct n)
            case 0
            then show ?case by auto
          next
            case (Suc n)
            define P where "P=1 / real_of_int (2 * prod a {N..<n + N})"
            have "1 / real_of_int (2 * prod a {N..<Suc n + N}) = P / a (n+N)"
              unfolding P_def by (auto simp add: prod.atLeastLessThan_Suc)
            also have "... \<le>  ( (1 / 2) ^ (n + 1) ) / a (n+N) "
              apply (rule divide_right_mono)
              subgoal unfolding P_def using Suc by auto
              subgoal by (simp add: a_pos less_imp_le)
              done
            also have "... \<le> ( (1 / 2) ^ (n + 1) ) / 2 "
              apply (rule divide_left_mono)
              using large_n[rule_format,of "n+N",simplified] by auto
            also have "... = (1 / 2) ^ (n + 2)" by auto
            finally show ?case by simp
          qed
          finally show ?thesis .
        qed
        have "(\<lambda>n. (1 / 2)^(n+1)) \<longlonglongrightarrow> (0::real)" 
          using tendsto_mult_right_zero[OF LIMSEQ_abs_realpow_zero2[of "1/2",simplified],of "1/2"]
          by auto
        then show ?thesis 
          apply (elim Lim_null_comparison[rotated])
          using h2_n less_eq_real_def by (auto intro!:eventuallyI)
      qed
      ultimately have "(\<Sum>i. h1 i - h2 i) = h1 0"
        using LIMSEQ_unique by fastforce
      then show ?thesis by simp
    qed
    also have "... = C + c N"
      unfolding h1_def using a_pos 
      by auto (metis less_irrefl)
    finally show ?thesis . 
  qed
  then have "S = (C + real_of_int (c N)) / (B*prod a {..<N})" 
    by (metis \<open>0 < B\<close> a_pos less_irrefl mult.commute mult_pos_pos 
        nonzero_mult_div_cancel_right of_int_eq_0_iff prod_pos)
  moreover have "... \<in> \<rat>"
    unfolding C_def f_def by (intro Rats_divide Rats_add Rats_mult Rats_of_int Rats_sum)
  ultimately show "S \<in> \<rat>" by auto
qed

theorem theorem_2_1_Erdos_Straus :
  "(\<Sum>n. (b n / (\<Prod>i \<le> n. a i))) \<in> \<rat> \<longleftrightarrow> (\<exists> (B::int)>0. \<exists> c::nat\<Rightarrow> int.
            (\<forall>\<^sub>F n in sequentially. B*b n = c n * a n - c(n+1) \<and> \<bar>c(n+1)\<bar><a n/2))"
  using ab_rationality_imp imp_ab_rational by auto

text\<open>The following is a Corollary to Theorem 2.1.  \<close>

corollary corollary_2_10_Erdos_Straus:
  assumes ab_event:"\<forall>\<^sub>F n in sequentially. b n > 0 \<and> a (n+1) \<ge> a n" 
    and ba_lim_leq:"lim (\<lambda>n. (b(n+1) - b n )/a n) \<le> 0" 
    and ba_lim_exist:"convergent (\<lambda>n. (b(n+1) - b n )/a n)"
    and "liminf (\<lambda>n. a n / b n) = 0 "
  shows "(\<Sum>n. (b n / (\<Prod>i \<le> n. a i))) \<notin> \<rat>"
proof 
  assume "(\<Sum>n. (b n / (\<Prod>i \<le> n. a i))) \<in> \<rat>"
  then obtain B c where "B>0" and abc_event:"\<forall>\<^sub>F n in sequentially. B * b n = c n * a n - c (n + 1) 
          \<and> \<bar>c (n + 1)\<bar> < a n / 2" and ca_vanish: "(\<lambda>n. c (Suc n) / a n) \<longlonglongrightarrow> 0"
    using ab_rationality_imp by auto

  have bac_close:"(\<lambda>n. B * b n / a n - c n) \<longlonglongrightarrow> 0"
  proof -
    have "\<forall>\<^sub>F n in sequentially. B * b n - c n * a n + c (n + 1) = 0"
      using abc_event by (auto elim!:eventually_mono)
    then have "\<forall>\<^sub>F n in sequentially. (B * b n - c n * a n + c (n+1)) / a n = 0 "
      apply eventually_elim
      by auto
    then have "\<forall>\<^sub>F n in sequentially. B * b n / a n - c n  + c (n + 1) / a n = 0"
      apply eventually_elim
      using a_pos by (auto simp:divide_simps) (metis less_irrefl)
    then have "(\<lambda>n. B * b n / a n - c n  + c (n + 1) / a n) \<longlonglongrightarrow> 0"
      by (simp add: eventually_mono tendsto_iff)
    from tendsto_diff[OF this ca_vanish]  
    show ?thesis by auto
  qed

  have c_pos:"\<forall>\<^sub>F n in sequentially. c n > 0" 
  proof -
    from bac_close have *:"\<forall>\<^sub>F n in sequentially. c n \<ge> 0"
      apply (elim tendsto_of_int_diff_0)
      using ab_event a_large apply (eventually_elim) 
      using \<open>B>0\<close> by auto 
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (\<forall>\<^sub>F n in sequentially. c n > 0)"
      moreover have "\<forall>\<^sub>F n in sequentially. c (Suc n) \<ge> 0 \<and> c n\<ge>0"
        using * eventually_sequentially_Suc[of "\<lambda>n. c n\<ge>0"] 
        by (metis (mono_tags, lifting) eventually_at_top_linorder le_Suc_eq)
      ultimately have "\<exists>\<^sub>F n in sequentially. c n = 0 \<and> c (Suc n) \<ge> 0"
        using eventually_elim2 frequently_def by fastforce
      moreover have "\<forall>\<^sub>F n in sequentially. b n > 0 \<and> B * b n = c n * a n - c (n + 1)"
        using ab_event abc_event by eventually_elim auto
      ultimately have "\<exists>\<^sub>F n in sequentially. c n = 0 \<and> c (Suc n) \<ge> 0 \<and> b n > 0 
                          \<and> B * b n = c n * a n - c (n + 1)"
        using frequently_eventually_frequently by fastforce
      from frequently_ex[OF this] 
      obtain n where "c n = 0" "c (Suc n) \<ge> 0" "b n > 0" 
        "B * b n = c n * a n - c (n + 1)"
        by auto
      then have "B * b n \<le> 0" by auto
      then show False using \<open>b n>0\<close> \<open>B > 0\<close> using mult_pos_pos not_le by blast
    qed
  qed

  have bc_epsilon:"\<forall>\<^sub>F n in sequentially. b (n+1) / b n >  (c (n+1) - \<epsilon>) / c n" when "\<epsilon>>0" "\<epsilon><1" for \<epsilon>::real
  proof -
    have "\<forall>\<^sub>F x in sequentially. \<bar>c (Suc x) / a x\<bar> < \<epsilon> / 2"
      using ca_vanish[unfolded tendsto_iff,rule_format, of "\<epsilon>/2"] \<open>\<epsilon>>0\<close> by auto
    moreover then have "\<forall>\<^sub>F x in sequentially. \<bar>c (x+2) / a (x+1)\<bar> < \<epsilon> / 2"
      apply (subst (asm) eventually_sequentially_Suc[symmetric])
      by simp
    moreover have "\<forall>\<^sub>F n in sequentially. B * b (n+1) = c (n+1) * a (n+1) - c (n + 2)"
      using abc_event
      apply (subst (asm) eventually_sequentially_Suc[symmetric])
      by (auto elim:eventually_mono)
    moreover have "\<forall>\<^sub>F n in sequentially. c n > 0 \<and> c (n+1) > 0 \<and> c (n+2) > 0"
    proof -
      have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc n)"
        using c_pos by (subst eventually_sequentially_Suc) simp
      moreover then have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc (Suc n))"
        using c_pos by (subst eventually_sequentially_Suc) simp
      ultimately show ?thesis using c_pos by eventually_elim auto
    qed
    ultimately show ?thesis using ab_event abc_event 
    proof eventually_elim
      case (elim n)
      define \<epsilon>\<^sub>0 \<epsilon>\<^sub>1 where "\<epsilon>\<^sub>0 = c (n+1) / a n" and "\<epsilon>\<^sub>1 = c (n+2) / a (n+1)"
      have "\<epsilon>\<^sub>0 > 0" "\<epsilon>\<^sub>1 > 0" "\<epsilon>\<^sub>0 < \<epsilon>/2" "\<epsilon>\<^sub>1 < \<epsilon>/2" using a_pos elim by (auto simp add: \<epsilon>\<^sub>0_def \<epsilon>\<^sub>1_def)
      have "(\<epsilon> - \<epsilon>\<^sub>1) * c n > 0"
        apply (rule mult_pos_pos)
        using \<open>\<epsilon>\<^sub>1 > 0\<close> \<open>\<epsilon>\<^sub>1 < \<epsilon>/2\<close> \<open>\<epsilon>>0\<close> elim by auto
      moreover have "\<epsilon>\<^sub>0 * (c (n+1) - \<epsilon>) > 0"
        apply (rule mult_pos_pos[OF \<open>\<epsilon>\<^sub>0 > 0\<close>])
        using elim(4) that(2) by linarith
      ultimately have "(\<epsilon> - \<epsilon>\<^sub>1) * c n + \<epsilon>\<^sub>0 * (c (n+1) - \<epsilon>) > 0" by auto
      moreover have "c n - \<epsilon>\<^sub>0 > 0" using \<open>\<epsilon>\<^sub>0 < \<epsilon> / 2\<close> elim(4) that(2) by linarith
      moreover have "c n > 0" by (simp add: elim(4))
      ultimately have "(c (n+1) - \<epsilon>) / c n < (c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0)"
        by (auto simp add: field_simps)
      also have "... \<le> (c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0) * (a (n+1) / a n)"
      proof -
        have "(c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0) > 0" 
          by (smt \<open>0 < (\<epsilon> - \<epsilon>\<^sub>1) * real_of_int (c n)\<close> \<open>0 < real_of_int (c n) - \<epsilon>\<^sub>0\<close> 
              divide_pos_pos elim(4) mult_le_0_iff of_int_less_1_iff that(2))
        moreover have "(a (n+1) / a n) \<ge> 1" 
          using a_pos elim(5) by auto
        ultimately show ?thesis by (metis mult_cancel_left1 real_mult_le_cancel_iff2)
      qed
      also have "... = (B * b (n+1)) / (B * b n)"
      proof -
        have "B * b n = c n * a n - c (n + 1)"
          using elim by auto
        also have "... = a n * (c n - \<epsilon>\<^sub>0)"
          using a_pos[rule_format,of n] unfolding \<epsilon>\<^sub>0_def by (auto simp:field_simps)
        finally have "B * b n = a n * (c n - \<epsilon>\<^sub>0)" .
        moreover have "B * b (n+1) = a (n+1) * (c (n+1) - \<epsilon>\<^sub>1)" 
          unfolding \<epsilon>\<^sub>1_def 
          using a_pos[rule_format,of "n+1"] 
          apply (subst \<open>B * b (n + 1) = c (n + 1) * a (n + 1) - c (n + 2)\<close>)
          by (auto simp:field_simps)
        ultimately show ?thesis by (simp add: mult.commute)
      qed
      also have "... = b (n+1) / b n" 
        using \<open>B>0\<close> by auto
      finally show ?case .
    qed
  qed

  have eq_2_11:"\<exists>\<^sub>F n in sequentially. b (n+1) > b n + (1 - \<epsilon>)^2 * a n / B" 
    when "\<epsilon>>0" "\<epsilon><1" "\<not> (\<forall>\<^sub>F n in sequentially. c (n+1) \<le> c n)"  for \<epsilon>::real
  proof -
    have "\<exists>\<^sub>F x in sequentially. c x < c (Suc x) " using that(3) 
      by (simp add:not_eventually frequently_elim1)
    moreover have "\<forall>\<^sub>F x in sequentially. \<bar>c (Suc x) / a x\<bar> < \<epsilon>"
      using ca_vanish[unfolded tendsto_iff,rule_format, of \<epsilon>] \<open>\<epsilon>>0\<close> by auto
    moreover have "\<forall>\<^sub>F n in sequentially. c n > 0 \<and> c (n+1) > 0"
    proof -
      have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc n)"
        using c_pos by (subst eventually_sequentially_Suc) simp
      then show ?thesis using c_pos by eventually_elim auto
    qed
    ultimately show ?thesis  using ab_event abc_event bc_epsilon[OF \<open>\<epsilon>>0\<close> \<open>\<epsilon><1\<close>] 
    proof (elim frequently_rev_mp,eventually_elim)
      case (elim n)
      then have "c (n+1) / a n < \<epsilon>" 
        using a_pos[rule_format,of n] by auto
      also have "... \<le> \<epsilon> * c n" using elim(7) that(1) by auto
      finally have "c (n+1) / a n < \<epsilon> * c n" .
      then have "c (n+1) / c n < \<epsilon> * a n" 
        using a_pos[rule_format,of n] elim by (auto simp:field_simps)
      then have "(1 - \<epsilon>) * a n < a n - c (n+1) / c n"
        by (auto simp:algebra_simps)
      then have "(1 - \<epsilon>)^2 * a n / B < (1 - \<epsilon>) * (a n - c (n+1) / c n) / B"
        apply (subst (asm) real_mult_less_iff1[symmetric, of "(1-\<epsilon>)/B"])
        using \<open>\<epsilon><1\<close> \<open>B>0\<close> by (auto simp:divide_simps power2_eq_square)
      then have "b n + (1 - \<epsilon>)^2 * a n / B < b n + (1 - \<epsilon>) * (a n - c (n+1) / c n) / B"
        using \<open>B>0\<close> by auto
      also have "... = b n + (1 - \<epsilon>) * ((c n *a n - c (n+1)) / c n) / B"
        using elim by (auto simp:field_simps)
      also have "... = b n + (1 - \<epsilon>) * (b n / c n)"
      proof -
        have "B * b n = c n * a n - c (n + 1)" using elim by auto
        from this[symmetric] show ?thesis
          using \<open>B>0\<close> by simp
      qed
      also have "... = (1+(1-\<epsilon>)/c n) * b n"
        by (auto simp:algebra_simps)
      also have "... = ((c n+1-\<epsilon>)/c n) * b n"
        using elim by (auto simp:divide_simps)
      also have "... \<le> ((c (n+1) -\<epsilon>)/c n) * b n"
      proof -
        define cp where "cp = c n+1"
        have "c (n+1) \<ge> cp" unfolding cp_def using \<open>c n < c (Suc n)\<close> by auto
        moreover have "c n>0" "b n>0" using elim by auto
        ultimately show ?thesis 
          apply (fold cp_def)
          by (auto simp:divide_simps)
      qed
      also have "... < b (n+1)"
        using elim by (auto simp:divide_simps)
      finally show ?case .
    qed
  qed

  have "\<forall>\<^sub>F n in sequentially. c (n+1) \<le> c n"
  proof (rule ccontr)
    assume "\<not> (\<forall>\<^sub>F n in sequentially. c (n + 1) \<le> c n)"
    from eq_2_11[OF _ _ this,of "1/2"]
    have "\<exists>\<^sub>F n in sequentially. b (n+1) > b n + 1/4 * a n / B" 
      by (auto simp:algebra_simps power2_eq_square)
    then have *:"\<exists>\<^sub>F n in sequentially. (b (n+1) - b n) / a n > 1 / (B * 4)" 
      apply (elim frequently_elim1)
      subgoal for n
        using a_pos[rule_format,of n] by (auto simp:field_simps)
      done
    define f where "f = (\<lambda>n. (b (n+1) - b n) / a n)"
    have "f \<longlonglongrightarrow> lim f"
      using convergent_LIMSEQ_iff ba_lim_exist unfolding f_def by auto
    from this[unfolded tendsto_iff,rule_format, of "1 / (B*4)"] 
    have "\<forall>\<^sub>F x in sequentially. \<bar>f x - lim f\<bar> < 1 / (B * 4)"
      using \<open>B>0\<close> by (auto simp:dist_real_def)
    moreover have "\<exists>\<^sub>F n in sequentially. f n > 1 / (B * 4)" 
      using * unfolding f_def by auto
    ultimately have "\<exists>\<^sub>F n in sequentially. f n > 1 / (B * 4) \<and> \<bar>f n - lim f\<bar> < 1 / (B * 4)"
      by (auto elim:frequently_eventually_frequently[rotated])
    from frequently_ex[OF this] 
    obtain n where "f n > 1 / (B * 4)" "\<bar>f n - lim f\<bar> < 1 / (B * 4)"
      by auto
    moreover have "lim f \<le> 0" using ba_lim_leq unfolding f_def by auto
    ultimately show False by linarith
  qed
  then obtain N where N_dec:"\<forall>n\<ge>N. c (n+1) \<le> c n" by (meson eventually_at_top_linorder)
  define max_c where "max_c = (MAX n \<in> {..N}. c n)"
  have max_c:"c n \<le> max_c" for n
  proof (cases "n\<le>N")
    case True
    then show ?thesis unfolding max_c_def by simp
  next
    case False
    then have "n\<ge>N" by auto
    then have "c n\<le>c N" 
    proof (induct rule:nat_induct_at_least)
      case base
      then show ?case by simp
    next
      case (Suc n)
      then have "c (n+1) \<le> c n" using N_dec by auto
      then show ?case using \<open>c n \<le> c N\<close> by auto
    qed
    moreover have "c N \<le> max_c" unfolding max_c_def by auto
    ultimately show ?thesis by auto
  qed
  have "max_c > 0 " 
  proof -
    obtain N where "\<forall>n\<ge>N. 0 < c n" 
      using c_pos[unfolded eventually_at_top_linorder] by auto
    then have "c N > 0" by auto
    then show ?thesis using max_c[of N] by simp
  qed
  have ba_limsup_bound:"1/(B*(B+1)) \<le> limsup (\<lambda>n. b n/a n)" 
    "limsup (\<lambda>n. b n/a n) \<le> max_c / B + 1 / (B+1)"
  proof -
    define f where "f = (\<lambda>n. b n/a n)"
    from tendsto_mult_right_zero[OF bac_close,of "1/B"] 
    have "(\<lambda>n. f n - c n / B) \<longlonglongrightarrow> 0"
      unfolding f_def using  \<open>B>0\<close> by (auto simp:algebra_simps)
    from this[unfolded tendsto_iff,rule_format,of "1/(B+1)"]
    have "\<forall>\<^sub>F x in sequentially. \<bar>f x - c x / B\<bar> < 1 / (B+1)"
      using \<open>B>0\<close> by auto
    then have *:"\<forall>\<^sub>F n in sequentially. 1/(B*(B+1)) \<le> ereal (f n) \<and> ereal (f n) \<le> max_c / B + 1 / (B+1)" 
      using c_pos
    proof eventually_elim
      case (elim n)
      then have "f n - c n / B < 1 / (B+1)" by auto
      then have "f n < c n / B + 1 / (B+1)" by simp
      also have "... \<le> max_c / B + 1 / (B+1)"
        using max_c[of n] using \<open>B>0\<close> by (auto simp:divide_simps)
      finally have *:"f n < max_c / B + 1 / (B+1)" .

      have "1/(B*(B+1)) = 1/B - 1 / (B+1)" 
        using \<open>B>0\<close> by (auto simp:divide_simps)
      also have "... \<le> c n/B - 1 / (B+1)" 
        using \<open>0 < c n\<close> \<open>B>0\<close> by (auto,auto simp:divide_simps)
      also have "... < f n" using elim by auto
      finally have "1/(B*(B+1)) < f n" .
      with * show ?case by simp
    qed
    show "limsup f \<le> max_c / B + 1 / (B+1)"
      apply (rule Limsup_bounded)
      using * by (auto elim:eventually_mono)
    have "1/(B*(B+1)) \<le> liminf f"
      apply (rule Liminf_bounded)
      using * by (auto elim:eventually_mono)
    also have "liminf f \<le> limsup f" by (simp add: Liminf_le_Limsup)
    finally show "1/(B*(B+1)) \<le> limsup f" .
  qed

  have "0 < inverse (ereal (max_c / B + 1 / (B+1)))"
    using \<open>max_c > 0\<close> \<open>B>0\<close> 
    by (simp add: pos_add_strict)
  also have "... \<le> inverse (limsup (\<lambda>n. b n/a n))"
  proof (rule ereal_inverse_antimono[OF _ ba_limsup_bound(2)])
    have "0<1/(B*(B+1))" using \<open>B>0\<close> by auto
    also have "... \<le> limsup (\<lambda>n. b n/a n)" using ba_limsup_bound(1) .
    finally show "0\<le>limsup (\<lambda>n. b n/a n)" using zero_ereal_def by auto
  qed 
  also have "... = liminf (\<lambda>n. inverse (ereal ( b n/a n)))"
    apply (subst Liminf_inverse_ereal[symmetric])
    using a_pos ab_event by (auto elim!:eventually_mono simp:divide_simps)
  also have "... = liminf (\<lambda>n. ( a n/b n))"
    apply (rule Liminf_eq)
    using a_pos ab_event 
    apply (auto elim!:eventually_mono) 
    by (metis less_int_code(1))
  finally have "liminf (\<lambda>n. ( a n/b n)) > 0" .
  then show False using \<open>liminf (\<lambda>n. a n / b n) = 0\<close> by simp
qed

end

section\<open>Some auxiliary results on the prime numbers. \<close>

lemma nth_prime_nonzero[simp]:"nth_prime n \<noteq> 0"
  by (simp add: prime_gt_0_nat prime_nth_prime)

lemma nth_prime_gt_zero[simp]:"nth_prime n >0"
  by (simp add: prime_gt_0_nat prime_nth_prime)

lemma ratio_of_consecutive_primes:
  "(\<lambda>n. nth_prime (n+1)/nth_prime n) \<longlonglongrightarrow>1"
proof -
  define f where "f=(\<lambda>x. real (nth_prime (Suc x)) /real (nth_prime x))"
  define g where "g=(\<lambda>x. (real x * ln (real x)) 
                              / (real (Suc x) * ln (real (Suc x))))"
  have p_n:"(\<lambda>x. real (nth_prime x) / (real x * ln (real x))) \<longlonglongrightarrow> 1"
    using nth_prime_asymptotics[unfolded asymp_equiv_def,simplified] .
  moreover have p_sn:"(\<lambda>n. real (nth_prime (Suc n)) 
                        / (real (Suc n) * ln (real (Suc n)))) \<longlonglongrightarrow> 1"
    using nth_prime_asymptotics[unfolded asymp_equiv_def,simplified
        ,THEN LIMSEQ_Suc] .
  ultimately have "(\<lambda>x. f x * g x) \<longlonglongrightarrow> 1"
    using tendsto_divide[OF p_sn p_n] 
    unfolding f_def g_def by (auto simp:algebra_simps)
  moreover have "g \<longlonglongrightarrow> 1" unfolding g_def
    by real_asymp
  ultimately have "(\<lambda>x. if g x = 0 then 0 else f x) \<longlonglongrightarrow> 1"
    apply (drule_tac tendsto_divide[OF _ \<open>g \<longlonglongrightarrow> 1\<close>])
    by auto
  then have "f \<longlonglongrightarrow> 1"
  proof (elim filterlim_mono_eventually)
    have "\<forall>\<^sub>F x in sequentially. (if g (x+3) = 0 then 0 
                else f (x+3)) = f (x+3)" 
      unfolding g_def by auto
    then show "\<forall>\<^sub>F x in sequentially. (if g x = 0 then 0 else f x) = f x"
      apply (subst (asm) eventually_sequentially_seg)
      by simp
  qed auto
  then show ?thesis unfolding f_def by auto
qed

lemma nth_prime_double_sqrt_less:
  assumes "\<epsilon> > 0"
  shows "\<forall>\<^sub>F n in sequentially. (nth_prime (2*n) - nth_prime n) 
            / sqrt (nth_prime n) < n powr (1/2+\<epsilon>)"
proof -
  define pp ll where 
    "pp=(\<lambda>n. (nth_prime (2*n) - nth_prime n) / sqrt (nth_prime n))" and
    "ll=(\<lambda>x::nat. x * ln x)"
  have pp_pos:"pp (n+1) > 0" for n
    unfolding pp_def by simp

  have "(\<lambda>x. nth_prime (2 * x)) \<sim>[sequentially] (\<lambda>x. (2 * x) * ln (2 * x))"
    using nth_prime_asymptotics[THEN asymp_equiv_compose
        ,of "(*) 2" sequentially,unfolded comp_def]
    using mult_nat_left_at_top pos2 by blast
  also have "... \<sim>[sequentially] (\<lambda>x. 2 *x * ln x)"
    by real_asymp
  finally have "(\<lambda>x. nth_prime (2 * x)) \<sim>[sequentially] (\<lambda>x. 2 *x * ln x)" .
  from this[unfolded asymp_equiv_def, THEN tendsto_mult_left,of 2]
  have "(\<lambda>x. nth_prime (2 * x) / (x * ln x)) \<longlonglongrightarrow> 2"
    unfolding asymp_equiv_def by auto
  moreover have *:"(\<lambda>x. nth_prime x / (x * ln x)) \<longlonglongrightarrow> 1"
    using nth_prime_asymptotics unfolding asymp_equiv_def by auto
  ultimately    
  have "(\<lambda>x. (nth_prime (2 * x) - nth_prime x) / ll x) \<longlonglongrightarrow> 1"
    unfolding ll_def
    apply -
    apply (drule (1) tendsto_diff)
    apply (subst of_nat_diff,simp)
    by (subst diff_divide_distrib,simp)
  moreover have "(\<lambda>x. sqrt (nth_prime x) / sqrt (ll x)) \<longlonglongrightarrow> 1"
    unfolding ll_def
    using tendsto_real_sqrt[OF *] 
    by (auto simp: real_sqrt_divide)
  ultimately have "(\<lambda>x. pp x * (sqrt (ll x) / (ll x))) \<longlonglongrightarrow> 1"
    apply -
    apply (drule (1) tendsto_divide,simp)
    by (auto simp:field_simps of_nat_diff pp_def)
  moreover have "\<forall>\<^sub>F x in sequentially. sqrt (ll x) / ll x = 1/sqrt (ll x)"
    apply (subst eventually_sequentially_Suc[symmetric])
    by (auto intro!:eventuallyI simp:ll_def divide_simps)
  ultimately have "(\<lambda>x. pp x / sqrt (ll x)) \<longlonglongrightarrow> 1"
    apply (elim filterlim_mono_eventually)
    by (auto elim!:eventually_mono) (metis mult.right_neutral times_divide_eq_right)
  moreover have "(\<lambda>x. sqrt (ll x) / x powr (1/2+\<epsilon>)) \<longlonglongrightarrow> 0"
    unfolding ll_def using \<open>\<epsilon>>0\<close> by real_asymp
  ultimately have "(\<lambda>x. pp x / x powr (1/2+\<epsilon>) * 
                      (sqrt (ll x) / sqrt (ll x))) \<longlonglongrightarrow> 0"
    apply -
    apply (drule (1) tendsto_mult)
    by (auto elim:filterlim_mono_eventually)
  moreover have "\<forall>\<^sub>F x in sequentially. sqrt (ll x) / sqrt (ll x) = 1"
    apply (subst eventually_sequentially_Suc[symmetric])
    by (auto intro!:eventuallyI simp:ll_def )
  ultimately have "(\<lambda>x. pp x / x powr (1/2+\<epsilon>)) \<longlonglongrightarrow> 0"
    apply (elim filterlim_mono_eventually)
    by (auto elim:eventually_mono)
  from tendstoD[OF this, of 1,simplified]
  show "\<forall>\<^sub>F x in sequentially. pp x < x powr (1 / 2 + \<epsilon>)"
    apply (elim eventually_mono_sequentially[of _ 1])
    using pp_pos by auto
qed


section \<open>Theorem 3.1\<close>

text\<open>Theorem 3.1 is an application of Theorem 2.1 with the sequences considered involving 
the prime numbers.\<close>

theorem theorem_3_10_Erdos_Straus:
  fixes a::"nat \<Rightarrow> int"
  assumes a_pos:"\<forall> n. a n >0" and "mono a"
    and nth_1:"(\<lambda>n. nth_prime n / (a n)^2) \<longlonglongrightarrow> 0"
    and nth_2:"liminf (\<lambda>n. a n / nth_prime n) = 0"
  shows "(\<Sum>n. (nth_prime n / (\<Prod>i \<le> n. a i))) \<notin> \<rat>"
proof
  assume asm:"(\<Sum>n. (nth_prime n / (\<Prod>i \<le> n. a i))) \<in> \<rat>"

  have a2_omega:"(\<lambda>n. (a n)^2) \<in> \<omega>(\<lambda>x. x * ln x)"
  proof -
    have "(\<lambda>n. real (nth_prime n)) \<in> o(\<lambda>n. real_of_int ((a n)\<^sup>2))"
      apply (rule smalloI_tendsto[OF nth_1])
      using a_pos by (metis (mono_tags, lifting) less_int_code(1) 
          not_eventuallyD of_int_0_eq_iff zero_eq_power2)
    moreover have "(\<lambda>x. real (nth_prime x)) \<in> \<Omega>(\<lambda>x. real x * ln (real x))"
      using nth_prime_bigtheta
      by blast
    ultimately show ?thesis 
      using landau_omega.small_big_trans smallo_imp_smallomega by blast
  qed

  have a_gt_1:"\<forall>\<^sub>F n in sequentially. 1 < a n" 
  proof -
    have "\<forall>\<^sub>F x in sequentially. \<bar>x * ln x\<bar> \<le> (a x)\<^sup>2"
      using a2_omega[unfolded smallomega_def,simplified,rule_format,of 1]
      by auto
    then have "\<forall>\<^sub>F x in sequentially. \<bar>(x+3) * ln (x+3)\<bar> \<le> (a (x+3))\<^sup>2" 
      apply (subst (asm) eventually_sequentially_seg[symmetric, of _ 3])
      by simp
    then have "\<forall>\<^sub>F n in sequentially. 1 < a ( n+3)" 
    proof (elim eventually_mono)
      fix x
      assume "\<bar>real (x + 3) * ln (real (x + 3))\<bar> \<le> real_of_int ((a (x + 3))\<^sup>2)"
      moreover have "\<bar>real (x + 3) * ln (real (x + 3))\<bar> > 3"
      proof -
        have "ln (real (x + 3)) > 1"
          apply simp using ln3_gt_1 ln_gt_1 by force
        moreover have "real(x+3) \<ge> 3" by simp
        ultimately have "(x+3)*ln (real (x + 3)) > 3*1 "
          apply (rule_tac mult_le_less_imp_less)
          by auto
        then show ?thesis by auto
      qed
      ultimately have "real_of_int ((a (x + 3))\<^sup>2) > 3"
        by auto
      then show "1 < a (x + 3)" 
        by (smt Suc3_eq_add_3 a_pos add.commute of_int_1 one_power2)
    qed
    then show ?thesis 
      apply (subst eventually_sequentially_seg[symmetric, of _ 3])
      by auto
  qed

  obtain B::int and c where 
    "B>0" and Bc_large:"\<forall>\<^sub>F n in sequentially. B * nth_prime n 
                = c n * a n - c (n + 1) \<and> \<bar>c (n + 1)\<bar> <  a n / 2"
    and ca_vanish: "(\<lambda>n. c (Suc n) / real_of_int (a n)) \<longlonglongrightarrow> 0"
  proof -
    note a_gt_1
    moreover have "(\<lambda>n. real_of_int \<bar>int (nth_prime n)\<bar> 
                    / real_of_int (a (n - 1) * a n)) \<longlonglongrightarrow> 0" 
    proof -
      define f where "f=(\<lambda>n. nth_prime (n+1) / (a n * a (n+1)))"
      define g where "g=(\<lambda>n. 2*nth_prime n / (a n)^2)"
      have "\<forall>\<^sub>F x in sequentially. norm (f x) \<le> g x"
      proof -
        have "\<forall>\<^sub>F n in sequentially. nth_prime (n+1) < 2*nth_prime n" 
          using ratio_of_consecutive_primes[unfolded tendsto_iff
              ,rule_format,of 1,simplified]
          apply (elim eventually_mono)
          by (auto simp :divide_simps dist_norm)
        moreover have "\<forall>\<^sub>F n in sequentially. real_of_int (a n * a (n+1))
                           \<ge> (a n)^2"
          apply (rule eventuallyI)
          using \<open>mono a\<close> by (auto simp:power2_eq_square a_pos incseq_SucD)
        ultimately show ?thesis unfolding f_def g_def
          apply eventually_elim
          apply (subst norm_divide)
          apply (rule_tac linordered_field_class.frac_le)
          using a_pos[rule_format, THEN order.strict_implies_not_eq ]
          by auto
      qed
      moreover have "g \<longlonglongrightarrow> 0 " 
        using nth_1[THEN tendsto_mult_right_zero,of 2] unfolding g_def 
        by auto
      ultimately have "f \<longlonglongrightarrow> 0" 
        using Lim_null_comparison[of f g sequentially]
        by auto
      then show ?thesis
        unfolding f_def
        by (rule_tac LIMSEQ_imp_Suc) auto
    qed
    moreover have "(\<Sum>n. real_of_int (int (nth_prime n)) 
                    / real_of_int (prod a {..n})) \<in> \<rat>" 
      using asm by simp
    ultimately have "\<exists>B>0. \<exists>c. (\<forall>\<^sub>F n in sequentially.
              B * int (nth_prime n) = c n * a n - c (n + 1) \<and>
              real_of_int \<bar>c (n + 1)\<bar> < real_of_int (a n) / 2) \<and>
          (\<lambda>n. real_of_int (c (Suc n)) / real_of_int (a n)) \<longlonglongrightarrow> 0"
      using ab_rationality_imp[OF a_pos,of nth_prime] by fast
    then show thesis 
      apply clarify
      apply (rule_tac c=c and B=B in that)
      by auto
  qed

  have bac_close:"(\<lambda>n. B * nth_prime n / a n - c n) \<longlonglongrightarrow> 0"
  proof -
    have "\<forall>\<^sub>F n in sequentially. B * nth_prime n - c n * a n + c (n + 1) = 0"
      using Bc_large by (auto elim!:eventually_mono)
    then have "\<forall>\<^sub>F n in sequentially. (B * nth_prime n - c n * a n + c (n+1)) / a n = 0 "
      apply eventually_elim
      by auto
    then have "\<forall>\<^sub>F n in sequentially. B * nth_prime n / a n - c n  + c (n + 1) / a n = 0"
      apply eventually_elim
      using a_pos by (auto simp:divide_simps) (metis less_irrefl)
    then have "(\<lambda>n. B * nth_prime n / a n - c n  + c (n + 1) / a n) \<longlonglongrightarrow> 0"
      by (simp add: eventually_mono tendsto_iff)
    from tendsto_diff[OF this ca_vanish]  
    show ?thesis by auto
  qed

  have c_pos:"\<forall>\<^sub>F n in sequentially. c n > 0" 
  proof -
    from bac_close have *:"\<forall>\<^sub>F n in sequentially. c n \<ge> 0"
      apply (elim tendsto_of_int_diff_0)
      using a_gt_1 apply (eventually_elim) 
      using \<open>B>0\<close> by auto 
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (\<forall>\<^sub>F n in sequentially. c n > 0)"
      moreover have "\<forall>\<^sub>F n in sequentially. c (Suc n) \<ge> 0 \<and> c n\<ge>0"
        using * eventually_sequentially_Suc[of "\<lambda>n. c n\<ge>0"] 
        by (metis (mono_tags, lifting) eventually_at_top_linorder le_Suc_eq)
      ultimately have "\<exists>\<^sub>F n in sequentially. c n = 0 \<and> c (Suc n) \<ge> 0"
        using eventually_elim2 frequently_def by fastforce
      moreover have "\<forall>\<^sub>F n in sequentially. nth_prime n > 0 
                        \<and> B * nth_prime n = c n * a n - c (n + 1)"
        using Bc_large by eventually_elim auto
      ultimately have "\<exists>\<^sub>F n in sequentially. c n = 0 \<and> c (Suc n) \<ge> 0 
          \<and> B * nth_prime n = c n * a n - c (n + 1)"
        using frequently_eventually_frequently by fastforce
      from frequently_ex[OF this] 
      obtain n where "c n = 0" "c (Suc n) \<ge> 0"
        "B * nth_prime n = c n * a n - c (n + 1)"
        by auto
      then have "B * nth_prime n \<le> 0" by auto
      then show False using \<open>B > 0\<close> 
        by (simp add: mult_le_0_iff)
    qed
  qed

  have B_nth_prime:"\<forall>\<^sub>F n in sequentially. nth_prime n > B" 
  proof -
    have "\<forall>\<^sub>F x in sequentially. B+1 \<le> nth_prime x"
      using nth_prime_at_top[unfolded filterlim_at_top_ge[where c="nat B+1"]
          ,rule_format,of "nat B + 1",simplified] 

      apply (elim eventually_mono)
      using \<open>B>0\<close> by auto
    then show ?thesis 
      apply (elim eventually_mono)
      by auto
  qed

  have bc_epsilon:"\<forall>\<^sub>F n in sequentially. nth_prime (n+1) 
            / nth_prime n >  (c (n+1) - \<epsilon>) / c n" when "\<epsilon>>0" "\<epsilon><1" for \<epsilon>::real
  proof -
    have "\<forall>\<^sub>F x in sequentially. \<bar>c (Suc x) / a x\<bar> < \<epsilon> / 2"
      using ca_vanish[unfolded tendsto_iff,rule_format, of "\<epsilon>/2"] \<open>\<epsilon>>0\<close> by auto
    moreover then have "\<forall>\<^sub>F x in sequentially. \<bar>c (x+2) / a (x+1)\<bar> < \<epsilon> / 2"
      apply (subst (asm) eventually_sequentially_Suc[symmetric])
      by simp
    moreover have "\<forall>\<^sub>F n in sequentially. B * nth_prime (n+1) = c (n+1) * a (n+1) - c (n + 2)"
      using Bc_large
      apply (subst (asm) eventually_sequentially_Suc[symmetric])
      by (auto elim:eventually_mono)
    moreover have "\<forall>\<^sub>F n in sequentially. c n > 0 \<and> c (n+1) > 0 \<and> c (n+2) > 0"
    proof -
      have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc n)"
        using c_pos by (subst eventually_sequentially_Suc) simp
      moreover then have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc (Suc n))"
        using c_pos by (subst eventually_sequentially_Suc) simp
      ultimately show ?thesis using c_pos by eventually_elim auto
    qed
    ultimately show ?thesis using Bc_large
    proof eventually_elim
      case (elim n)
      define \<epsilon>\<^sub>0 \<epsilon>\<^sub>1 where "\<epsilon>\<^sub>0 = c (n+1) / a n" and "\<epsilon>\<^sub>1 = c (n+2) / a (n+1)"
      have "\<epsilon>\<^sub>0 > 0" "\<epsilon>\<^sub>1 > 0" "\<epsilon>\<^sub>0 < \<epsilon>/2" "\<epsilon>\<^sub>1 < \<epsilon>/2" 
        using a_pos elim \<open>mono a\<close>
        by (auto simp add: \<epsilon>\<^sub>0_def \<epsilon>\<^sub>1_def abs_of_pos)
      have "(\<epsilon> - \<epsilon>\<^sub>1) * c n > 0"
        apply (rule mult_pos_pos)
        using \<open>\<epsilon>\<^sub>1 > 0\<close> \<open>\<epsilon>\<^sub>1 < \<epsilon>/2\<close> \<open>\<epsilon>>0\<close> elim by auto
      moreover have "\<epsilon>\<^sub>0 * (c (n+1) - \<epsilon>) > 0"
        apply (rule mult_pos_pos[OF \<open>\<epsilon>\<^sub>0 > 0\<close>])
        using elim(4) that(2) by linarith
      ultimately have "(\<epsilon> - \<epsilon>\<^sub>1) * c n + \<epsilon>\<^sub>0 * (c (n+1) - \<epsilon>) > 0" by auto
      moreover have "c n - \<epsilon>\<^sub>0 > 0" using \<open>\<epsilon>\<^sub>0 < \<epsilon> / 2\<close> elim(4) that(2) by linarith
      moreover have "c n > 0" by (simp add: elim(4))
      ultimately have "(c (n+1) - \<epsilon>) / c n < (c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0)"
        by (auto simp add:field_simps)
      also have "... \<le> (c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0) * (a (n+1) / a n)"
      proof -
        have "(c (n+1) - \<epsilon>\<^sub>1) / (c n -  \<epsilon>\<^sub>0) > 0" 
          by (smt \<open>0 < (\<epsilon> - \<epsilon>\<^sub>1) * real_of_int (c n)\<close> \<open>0 < real_of_int (c n) - \<epsilon>\<^sub>0\<close> 
              divide_pos_pos elim(4) mult_le_0_iff of_int_less_1_iff that(2))
        moreover have "(a (n+1) / a n) \<ge> 1" 
          using a_pos \<open>mono a\<close> by (simp add: mono_def)
        ultimately show ?thesis by (metis mult_cancel_left1 real_mult_le_cancel_iff2)
      qed
      also have "... = (B * nth_prime (n+1)) / (B * nth_prime n)"
      proof -
        have "B * nth_prime n = c n * a n - c (n + 1)"
          using elim by auto
        also have "... = a n * (c n - \<epsilon>\<^sub>0)"
          using a_pos[rule_format,of n] unfolding \<epsilon>\<^sub>0_def by (auto simp:field_simps)
        finally have "B * nth_prime n = a n * (c n - \<epsilon>\<^sub>0)" .
        moreover have "B * nth_prime (n+1) = a (n+1) * (c (n+1) - \<epsilon>\<^sub>1)" 
          unfolding \<epsilon>\<^sub>1_def 
          using a_pos[rule_format,of "n+1"] 
          apply (subst \<open>B * nth_prime (n + 1) = c (n + 1) * a (n + 1) - c (n + 2)\<close>)
          by (auto simp:field_simps)
        ultimately show ?thesis by (simp add: mult.commute)
      qed
      also have "... = nth_prime (n+1) / nth_prime n" 
        using \<open>B>0\<close> by auto
      finally show ?case .
    qed
  qed


  have c_ubound:"\<forall>x. \<exists>n. c n > x"
  proof (rule ccontr)
    assume " \<not> (\<forall>x. \<exists>n. x < c n)"
    then obtain ub where "\<forall>n. c n \<le> ub" "ub > 0"
      by (meson dual_order.trans int_one_le_iff_zero_less le_cases not_le)
    define pa where "pa = (\<lambda>n. nth_prime n / a n)"
    have pa_pos:"\<And>n. pa n > 0" unfolding pa_def by (simp add: a_pos)
    have "liminf (\<lambda>n. 1 / pa n) = 0"
      using nth_2 unfolding pa_def by auto
    then have "(\<exists>y<ereal (real_of_int B / real_of_int (ub + 1)). 
      \<exists>\<^sub>F x in sequentially. ereal (1 / pa x) \<le> y)"
      apply (subst less_Liminf_iff[symmetric])
      using \<open>0 < B\<close> \<open>0 < ub\<close> by auto
    then have "\<exists>\<^sub>F x in sequentially. 1 / pa x < B/(ub+1)"
      by (meson frequently_mono le_less_trans less_ereal.simps(1))
    then have "\<exists>\<^sub>F x in sequentially. B*pa x > (ub+1)"
      apply (elim frequently_elim1)
      by (metis \<open>0 < ub\<close> mult.left_neutral of_int_0_less_iff pa_pos pos_divide_less_eq 
          pos_less_divide_eq times_divide_eq_left zless_add1_eq)
    moreover have "\<forall>\<^sub>F x in sequentially. c x \<le> ub"
      using \<open>\<forall>n. c n \<le> ub\<close> by simp
    ultimately have "\<exists>\<^sub>F x in sequentially. B*pa x - c x > 1"
      apply (elim frequently_rev_mp eventually_mono)
      by linarith
    moreover have "(\<lambda>n. B * pa n - c n) \<longlonglongrightarrow>0" 
      unfolding pa_def using bac_close by auto
    from tendstoD[OF this,of 1] 
    have "\<forall>\<^sub>F n in sequentially.  \<bar>B * pa n - c n\<bar> < 1"
      by auto
    ultimately have "\<exists>\<^sub>F x in sequentially. B*pa x - c x > 1 \<and> \<bar>B * pa x - c x\<bar> < 1"
      using frequently_eventually_frequently by blast
    then show False 
      by (simp add: frequently_def)
  qed

  have eq_2_11:"\<forall>\<^sub>F n in sequentially. c (n+1)>c n \<longrightarrow> 
                  nth_prime (n+1) > nth_prime n + (1 - \<epsilon>)^2 * a n / B" 
    when "\<epsilon>>0" "\<epsilon><1" for \<epsilon>::real
  proof -
    have "\<forall>\<^sub>F x in sequentially. \<bar>c (Suc x) / a x\<bar> < \<epsilon>"
      using ca_vanish[unfolded tendsto_iff,rule_format, of \<epsilon>] \<open>\<epsilon>>0\<close> by auto
    moreover have "\<forall>\<^sub>F n in sequentially. c n > 0 \<and> c (n+1) > 0"
    proof -
      have "\<forall>\<^sub>F n in sequentially. 0 < c (Suc n)"
        using c_pos by (subst eventually_sequentially_Suc) simp
      then show ?thesis using c_pos by eventually_elim auto
    qed
    ultimately show ?thesis  using Bc_large bc_epsilon[OF \<open>\<epsilon>>0\<close> \<open>\<epsilon><1\<close>] 
    proof (eventually_elim, rule_tac impI)
      case (elim n)
      assume "c n < c (n + 1)"
      have "c (n+1) / a n < \<epsilon>" 
        using a_pos[rule_format,of n] using elim(1,2) by auto
      also have "... \<le> \<epsilon> * c n" using elim(2) that(1) by auto
      finally have "c (n+1) / a n < \<epsilon> * c n" .
      then have "c (n+1) / c n < \<epsilon> * a n" 
        using a_pos[rule_format,of n] elim by (auto simp:field_simps)
      then have "(1 - \<epsilon>) * a n < a n - c (n+1) / c n"
        by (auto simp:algebra_simps)
      then have "(1 - \<epsilon>)^2 * a n / B < (1 - \<epsilon>) * (a n - c (n+1) / c n) / B"
        apply (subst (asm) real_mult_less_iff1[symmetric, of "(1-\<epsilon>)/B"])
        using \<open>\<epsilon><1\<close> \<open>B>0\<close> by (auto simp:divide_simps power2_eq_square)
      then have "nth_prime n + (1 - \<epsilon>)^2 * a n / B < nth_prime n + (1 - \<epsilon>) * (a n - c (n+1) / c n) / B"
        using \<open>B>0\<close> by auto
      also have "... = nth_prime n + (1 - \<epsilon>) * ((c n *a n - c (n+1)) / c n) / B"
        using elim by (auto simp:field_simps)
      also have "... = nth_prime n + (1 - \<epsilon>) * (nth_prime n / c n)"
      proof -
        have "B * nth_prime n = c n * a n - c (n + 1)" using elim by auto
        from this[symmetric] show ?thesis
          using \<open>B>0\<close> by simp
      qed
      also have "... = (1+(1-\<epsilon>)/c n) * nth_prime n"
        by (auto simp:algebra_simps)
      also have "... = ((c n+1-\<epsilon>)/c n) * nth_prime n"
        using elim by (auto simp:divide_simps)
      also have "... \<le> ((c (n+1) -\<epsilon>)/c n) * nth_prime n"
      proof -
        define cp where "cp = c n+1"
        have "c (n+1) \<ge> cp" unfolding cp_def using \<open>c n < c (n + 1)\<close> by auto
        moreover have "c n>0" "nth_prime n>0" using elim by auto
        ultimately show ?thesis 
          apply (fold cp_def)
          by (auto simp:divide_simps)
      qed
      also have "... < nth_prime (n+1)"
        using elim by (auto simp:divide_simps)
      finally show "real (nth_prime n) + (1 - \<epsilon>)\<^sup>2 * real_of_int (a n) 
          / real_of_int B < real (nth_prime (n + 1))" .
    qed
  qed

  have c_neq_large:"\<forall>\<^sub>F n in sequentially. c (n+1) \<noteq> c n"
  proof (rule ccontr)
    assume "\<not> (\<forall>\<^sub>F n in sequentially. c (n + 1) \<noteq> c n)"
    then have that:"\<exists>\<^sub>F n in sequentially. c (n + 1) = c n"
      unfolding frequently_def .
    have "\<forall>\<^sub>F x in sequentially. (B * int (nth_prime x) = c x * a x - c (x + 1) 
        \<and> \<bar>real_of_int (c (x + 1))\<bar> < real_of_int (a x) / 2) \<and> 0 < c x \<and> B < int (nth_prime x)
        \<and> (c (x+1)>c x \<longrightarrow> nth_prime (x+1) > nth_prime x +  a x / (2* B))"
      using Bc_large c_pos B_nth_prime eq_2_11[of "1-1/ sqrt 2",simplified]
      by eventually_elim (auto simp:divide_simps)
    then have "\<exists>\<^sub>F m in sequentially. nth_prime (m+1) > (1+1/(2*B))*nth_prime m"
    proof (elim frequently_eventually_at_top[OF that, THEN frequently_at_top_elim])
      fix n
      assume "c (n + 1) = c n \<and>
           (\<forall>y\<ge>n. (B * int (nth_prime y) = c y * a y - c (y + 1) \<and>
                    \<bar>real_of_int (c (y + 1))\<bar> < real_of_int (a y) / 2) \<and>
                   0 < c y \<and> B < int (nth_prime y) \<and> (c y < c (y + 1) \<longrightarrow>
                   real (nth_prime y) + real_of_int (a y) / real_of_int (2 * B)
                   < real (nth_prime (y + 1))))"
      then have "c (n + 1) = c n" 
        and Bc_eq:"\<forall>y\<ge>n. B * int (nth_prime y) = c y * a y - c (y + 1) \<and> 0 < c y 
                            \<and> \<bar>real_of_int (c (y + 1))\<bar> < real_of_int (a y) / 2 
                            \<and> B < int (nth_prime y)
                            \<and> (c y < c (y + 1) \<longrightarrow>
                   real (nth_prime y) + real_of_int (a y) / real_of_int (2 * B)
                   < real (nth_prime (y + 1)))"
        by auto
      obtain m where "n<m" "c m \<le> c n" "c n<c (m+1)" 
      proof -
        have "\<exists>N. N > n \<and> c N > c n"
          using c_ubound[rule_format, of "MAX x\<in>{..n}. c x"] 
          by (metis Max_ge atMost_iff dual_order.trans finite_atMost finite_imageI image_eqI 
              linorder_not_le order_refl)
        then obtain N where "N>n" "c N>c n" by auto
        define A m where "A={m. n<m \<and> (m+1)\<le>N \<and> c (m+1) > c n}" and "m = Min A"
        have "finite A" unfolding A_def
          by (metis (no_types, lifting) A_def add_leE finite_nat_set_iff_bounded_le mem_Collect_eq)
        moreover have "N-1\<in>A" unfolding A_def 
          using \<open>c n < c N\<close> \<open>n < N\<close> \<open>c (n + 1) = c n\<close>
          by (smt Suc_diff_Suc Suc_eq_plus1 Suc_leI Suc_pred  add.commute 
              add_diff_inverse_nat add_leD1 diff_is_0_eq' mem_Collect_eq nat_add_left_cancel_less
              zero_less_one)
        ultimately have "m\<in>A"
          using Min_in unfolding m_def by auto
        then have "n<m"  "c n<c (m+1)" "m>0"
          unfolding m_def A_def by auto
        moreover have "c m \<le> c n"
        proof (rule ccontr)
          assume " \<not> c m \<le> c n"
          then have "m-1\<in>A" using \<open>m\<in>A\<close> \<open>c (n + 1) = c n\<close>
            unfolding A_def 
            by auto (smt One_nat_def Suc_eq_plus1 Suc_lessI less_diff_conv)
          from  Min_le[OF \<open>finite A\<close> this,folded m_def] \<open>m>0\<close> show False by auto
        qed
        ultimately show ?thesis using that[of m] by auto
      qed
      have "(1 + 1 / (2 * B)) * nth_prime m < nth_prime m + a m / (2*B)"
      proof -
        have "nth_prime m < a m"
        proof -
          have "B * int (nth_prime m) < c m * (a m - 1)"
            using Bc_eq[rule_format,of m] \<open>c m \<le> c n\<close> \<open>c n < c (m + 1)\<close> \<open>n < m\<close> 
            by (auto simp:algebra_simps)
          also have "... \<le> c n * (a m - 1)"
            by (simp add: \<open>c m \<le> c n\<close> a_pos mult_right_mono)
          finally have "B * int (nth_prime m) < c n * (a m - 1)" .
          moreover have "c n\<le>B" 
          proof -
            have " B * int (nth_prime n) = c n * (a n - 1)" "B < int (nth_prime n)"
              and c_a:"\<bar>real_of_int (c (n + 1))\<bar> < real_of_int (a n) / 2"
              using Bc_eq[rule_format,of n] \<open>c (n + 1) = c n\<close> by (auto simp:algebra_simps)
            from this(1) have " c n dvd (B * int (nth_prime n))"
              by simp
            moreover have "coprime (c n) (int (nth_prime n))"
            proof -
              have "c n < int (nth_prime n)" 
              proof (rule ccontr)
                assume "\<not> c n < int (nth_prime n)"
                then have asm:"c n \<ge> int (nth_prime n)" by auto
                then have "a n > 2 * nth_prime n"
                  using c_a \<open>c (n + 1) = c n\<close> by auto
                then have "a n -1 \<ge> 2 * nth_prime n"
                  by simp
                then have "a n - 1 > 2 * B"
                  using \<open>B < int (nth_prime n)\<close> by auto
                from mult_le_less_imp_less[OF asm this] \<open>B>0\<close>
                have "int (nth_prime n) * (2 * B) < c n * (a n - 1)"
                  by auto
                then show False using \<open>B * int (nth_prime n) = c n * (a n - 1)\<close>
                  by (smt \<open>0 < B\<close> \<open>B < int (nth_prime n)\<close> combine_common_factor 
                      mult.commute mult_pos_pos)
              qed
              then have "\<not> nth_prime n dvd c n" 
                by (simp add: Bc_eq zdvd_not_zless)
              then have "coprime (int (nth_prime n)) (c n)" 
                by (auto intro!:prime_imp_coprime_int)
              then show ?thesis using coprime_commute by blast
            qed
            ultimately have "c n dvd B"
              using coprime_dvd_mult_left_iff by auto
            then show ?thesis using \<open>0 < B\<close> zdvd_imp_le by blast
          qed
          moreover have "c n > 0 " using Bc_eq by blast
          ultimately show ?thesis
            using \<open>B>0\<close> by (smt a_pos mult_mono)
        qed
        then show ?thesis using \<open>B>0\<close> by (auto simp:field_simps)
      qed
      also have "... < nth_prime (m+1)"
        using Bc_eq[rule_format, of m] \<open>n<m\<close> \<open>c m \<le> c n\<close> \<open>c n < c (m+1)\<close>
        by linarith
      finally show "\<exists>j>n. (1 + 1 / real_of_int (2 * B)) * real (nth_prime j)
                       < real (nth_prime (j + 1))" using \<open>m>n\<close> by auto
    qed
    then have "\<exists>\<^sub>F m in sequentially. nth_prime (m+1)/nth_prime m > (1+1/(2*B))"
      by (auto elim:frequently_elim1 simp:field_simps)
    moreover have "\<forall>\<^sub>F m in sequentially. nth_prime (m+1)/nth_prime m < (1+1/(2*B))"
      using ratio_of_consecutive_primes[unfolded tendsto_iff,rule_format,of "1/(2*B)"]
        \<open>B>0\<close>
      unfolding dist_real_def
      by (auto elim!:eventually_mono simp:algebra_simps)
    ultimately show False by (simp add: eventually_mono frequently_def)
  qed

  have c_gt_half:"\<forall>\<^sub>F N in sequentially. card {n\<in>{N..<2*N}.  c n > c (n+1)} > N / 2"
  proof -
    define h where "h=(\<lambda>n. (nth_prime (2*n) - nth_prime n) 
                              /  sqrt (nth_prime n))"
    have "\<forall>\<^sub>F n in sequentially. h n < n / 2"
    proof -
      have "\<forall>\<^sub>F n in sequentially. h n < n powr (5/6)"
        using nth_prime_double_sqrt_less[of "1/3"]
        unfolding h_def by auto
      moreover have "\<forall>\<^sub>F n in sequentially. n powr (5/6) < (n /2)"
        by real_asymp
      ultimately show ?thesis 
        by eventually_elim auto 
    qed
    moreover have "\<forall>\<^sub>F n in sequentially. sqrt (nth_prime n) / a n < 1 / (2*B)"
      using nth_1[THEN tendsto_real_sqrt,unfolded tendsto_iff
          ,rule_format,of "1/(2*B)"] \<open>B>0\<close> a_pos
      by (auto simp:real_sqrt_divide abs_of_pos)
    ultimately have "\<forall>\<^sub>F x in sequentially. c (x+1) \<noteq> c x
        \<and> sqrt (nth_prime x) / a x < 1 / (2*B)
        \<and>  h x < x / 2
        \<and> (c (x+1)>c x \<longrightarrow> nth_prime (x+1) > nth_prime x +  a x / (2* B))"
      using c_neq_large B_nth_prime eq_2_11[of "1-1/ sqrt 2",simplified]
      by eventually_elim (auto simp:divide_simps)
    then show ?thesis
    proof (elim eventually_at_top_mono)
      fix N assume "N\<ge>1" and N_asm:"\<forall>y\<ge>N. c (y + 1) \<noteq> c y \<and>
               sqrt (real (nth_prime y)) / real_of_int (a y)
               < 1 / real_of_int (2 * B) \<and>  h y < y / 2 \<and>
               (c y < c (y + 1) \<longrightarrow>
                real (nth_prime y) + real_of_int (a y) / real_of_int (2 * B)
                < real (nth_prime (y + 1)))"

      define S where "S={n \<in> {N..<2 * N}. c n < c (n + 1)}"
      define g where "g=(\<lambda>n. (nth_prime (n+1) - nth_prime n) 
                              /  sqrt (nth_prime n))"
      define f where "f=(\<lambda>n. nth_prime (n+1) - nth_prime n)"
      have g_gt_1:"g n>1" when "n\<ge>N" "c n < c (n + 1)" for n
      proof -
        have "nth_prime n + sqrt (nth_prime n) < nth_prime (n+1)"
        proof -
          have "nth_prime n + sqrt (nth_prime n) < nth_prime n + a n / (2*B)"
            using N_asm[rule_format,OF \<open>n\<ge>N\<close>] a_pos
            by (auto simp:field_simps)
          also have "... < nth_prime (n+1)"
            using N_asm[rule_format,OF \<open>n\<ge>N\<close>] \<open>c n < c (n + 1)\<close> by auto
          finally show ?thesis .
        qed
        then show ?thesis unfolding g_def 
          using \<open>c n < c (n + 1)\<close> by auto
      qed
      have g_geq_0:"g n \<ge> 0" for n 
        unfolding g_def  by auto

      have "finite S" "\<forall>x\<in>S. x\<ge>N \<and> c x<c (x+1)"
        unfolding S_def by auto
      then have "card S \<le> sum g S" 
      proof (induct S)
        case empty
        then show ?case by auto
      next
        case (insert x F)
        moreover have "g x>1" 
        proof -
          have "c x < c (x+1)" "x\<ge>N" using insert(4) by auto
          then show ?thesis using g_gt_1 by auto
        qed
        ultimately show ?case by simp
      qed
      also have "... \<le> sum g {N..<2*N}"
        apply (rule sum_mono2)
        unfolding S_def using g_geq_0 by auto
      also have "... \<le> sum (\<lambda>n. f n/sqrt (nth_prime N)) {N..<2*N}"
        apply (rule sum_mono)
        unfolding f_def g_def by (auto intro!:divide_left_mono)
      also have "... = sum f {N..<2*N} / sqrt (nth_prime N)"
        unfolding sum_divide_distrib[symmetric] by auto
      also have "... = (nth_prime (2*N) - nth_prime N) / sqrt (nth_prime N)"
      proof -
        have "sum f {N..<2 * N} = nth_prime (2 * N) - nth_prime N"   
        proof (induct N)
          case 0
          then show ?case by simp
        next
          case (Suc N)
          have ?case if "N=0"
          proof -
            have "sum f {Suc N..<2 * Suc N} = sum f {1}"
              using that by (simp add: numeral_2_eq_2)
            also have "... = nth_prime 2 - nth_prime 1"
              unfolding f_def by (simp add:numeral_2_eq_2)
            also have "... = nth_prime (2 * Suc N) - nth_prime (Suc N)"
              using that by auto
            finally show ?thesis .
          qed
          moreover have ?case if "N\<noteq>0"
          proof -
            have "sum f {Suc N..<2 * Suc N} = sum f {N..<2 * Suc N} - f N"
              apply (subst (2) sum.atLeast_Suc_lessThan)
              using that by auto
            also have "... = sum f {N..<2 * N}+ f (2*N) + f(2*N+1) - f N"
              by auto
            also have "... = nth_prime (2 * Suc N) - nth_prime (Suc N)"
              using Suc unfolding f_def by auto
            finally show ?thesis .
          qed
          ultimately show ?case by blast
        qed
        then show ?thesis by auto
      qed
      also have "... = h N"
        unfolding h_def by auto
      also have "... < N/2"
        using N_asm by auto
      finally have "card S < N/2" .

      define T where "T={n \<in> {N..<2 * N}. c n > c (n + 1)}"
      have "T \<union> S = {N..<2 * N}" "T \<inter> S = {}" "finite T"
        unfolding T_def S_def using N_asm by fastforce+

      then have "card T + card S = card {N..<2 * N}"
        using card_Un_disjoint \<open>finite S\<close> by metis
      also have "... = N"
        by simp
      finally have "card T + card S = N" .
      with \<open>card S < N/2\<close> 
      show "card T > N/2" by linarith
    qed
  qed

  text\<open>Inequality (3.5) in the original paper required a slight modification: \<close>

  have a_gt_plus:"\<forall>\<^sub>F n in sequentially. c n > c (n+1) \<longrightarrow>a (n+1) > a n + (a n - c(n+1) - 1) / c (n+1)"
  proof -
    note a_gt_1[THEN eventually_all_ge_at_top] c_pos[THEN eventually_all_ge_at_top]
    moreover have "\<forall>\<^sub>F n in sequentially. 
              B * int (nth_prime (n+1)) = c (n+1) * a (n+1) - c (n + 2)"
      using Bc_large 
      apply (subst (asm) eventually_sequentially_Suc[symmetric])
      by (auto elim:eventually_mono)
    moreover have "\<forall>\<^sub>F n in sequentially. 
                        B * int (nth_prime n) = c n * a n - c (n + 1) \<and> \<bar>c (n + 1)\<bar> <  a n / 2"
      using Bc_large by (auto elim:eventually_mono)
    ultimately show ?thesis 
      apply (eventually_elim)
    proof (rule impI)
      fix n 
      assume "\<forall>y\<ge>n. 1 < a y" "\<forall>y\<ge>n. 0 < c y"
        and
        Suc_n_eq:"B * int (nth_prime (n + 1)) = c (n + 1) * a (n + 1) - c (n + 2)" and
        "B * int (nth_prime n) = c n * a n - c (n + 1) \<and>
                real_of_int \<bar>c (n + 1)\<bar> < real_of_int (a n) / 2" 
        and "c (n + 1) < c n"
      then have n_eq:"B * int (nth_prime n) = c n * a n - c (n + 1)" and 
        c_less_a: "real_of_int \<bar>c (n + 1)\<bar> < real_of_int (a n) / 2" 
        by auto
      from \<open>\<forall>y\<ge>n. 1 < a y\<close> \<open>\<forall>y\<ge>n. 0 < c y\<close> 
      have *:"a n>1" "a (n+1) > 1" "c n > 0" 
        "c (n+1) > 0"  "c (n+2) > 0"
        by auto
      then have "(1+1/c (n+1))* (a n - 1)/a (n+1) = (c (n+1)+1) * ((a n - 1) / (c (n+1) * a (n+1)))"
        by (auto simp:field_simps)
      also have "... \<le> c n * ((a n - 1) / (c (n+1) * a (n+1)))"
        apply (rule mult_right_mono)
        subgoal using \<open>c (n + 1) < c n\<close> by auto
        subgoal by (smt \<open>0 < c (n + 1)\<close> a_pos divide_nonneg_pos mult_pos_pos of_int_0_le_iff 
              of_int_0_less_iff)
        done
      also have "... = (c n * (a n - 1)) / (c (n+1) * a (n+1))" by auto
      also have "... < (c n * (a n - 1)) / (c (n+1) * a (n+1)  - c (n+2))"
        apply (rule divide_strict_left_mono)
        subgoal using \<open>c (n+2) > 0\<close> by auto
        unfolding Suc_n_eq[symmetric] using * \<open>B>0\<close> by auto
      also have "... < (c n * a n - c (n+1)) / (c (n+1) * a (n+1)  - c (n+2))"
        apply (rule frac_less)
        unfolding Suc_n_eq[symmetric] using * \<open>B>0\<close> \<open>c (n + 1) < c n\<close> 
        by (auto simp:algebra_simps)
      also have "... = nth_prime n / nth_prime (n+1)"
        unfolding Suc_n_eq[symmetric] n_eq[symmetric] using \<open>B>0\<close> by auto
      also have "... < 1" by auto
      finally have "(1 + 1 / real_of_int (c (n + 1))) * real_of_int (a n - 1) 
        / real_of_int (a (n + 1)) < 1 " .
      then show "a n + (a n - c (n + 1) - 1) /  (c (n + 1)) < (a (n + 1))"
        using * by (auto simp:field_simps)
    qed
  qed
  have a_gt_1:"\<forall>\<^sub>F n in sequentially. c n > c (n+1) \<longrightarrow> a (n+1) > a n + 1"
    using Bc_large a_gt_plus c_pos[THEN eventually_all_ge_at_top]
    apply eventually_elim
  proof (rule impI)
    fix n assume  
      "c (n + 1) < c n \<longrightarrow> a n +  (a n - c (n + 1) - 1) / c (n + 1) <  a (n + 1)" 
      "c (n + 1) < c n" and B_eq:"B * int (nth_prime n) = c n * a n - c (n + 1) \<and>
         \<bar>real_of_int (c (n + 1))\<bar> < real_of_int (a n) / 2" and c_pos:"\<forall>y\<ge>n. 0 < c y"
    from this(1,2) 
    have "a n +  (a n - c (n + 1) - 1) / c (n + 1) <  a (n + 1)" by auto
    moreover have "a n - 2 * c (n+1) > 0"
      using B_eq c_pos[rule_format,of "n+1"] by auto
    then have "a n - 2 * c (n+1) \<ge> 1" by simp
    then have "(a n - c (n + 1) - 1) / c (n + 1) \<ge> 1"
      using c_pos[rule_format,of "n+1"] by (auto simp:field_simps)
    ultimately show "a n + 1 < a (n + 1)" by auto
  qed

  text\<open>The following corresponds to inequality (3.6) in the paper, which had to be
        slightly corrected:  \<close>

  have a_gt_sqrt:"\<forall>\<^sub>F n in sequentially. c n > c (n+1) \<longrightarrow> a (n+1) > a n + (sqrt n - 2)"
  proof -
    have a_2N:"\<forall>\<^sub>F N in sequentially. a (2*N) \<ge> N /2 +1" 
      using c_gt_half a_gt_1[THEN eventually_all_ge_at_top] 
    proof eventually_elim
      case (elim N)
      define S where "S={n \<in> {N..<2 * N}. c (n + 1) < c n}"
      define f where "f = (\<lambda>n. a (Suc n) - a n)"

      have f_1:"\<forall>x\<in>S. f x\<ge>1" and f_0:"\<forall>x. f x\<ge>0"
        subgoal using elim unfolding S_def f_def by auto
        subgoal using \<open>mono a\<close>[THEN incseq_SucD] unfolding f_def by auto
        done
      have "N / 2 < card S" 
        using elim unfolding S_def by auto
      also have "... \<le> sum f S" 
        unfolding of_int_sum
        apply (rule sum_bounded_below[of _ 1,simplified])
        using f_1 by auto
      also have "... \<le> sum f {N..<2 * N}" 
        unfolding of_int_sum
        apply (rule sum_mono2)
        unfolding S_def using f_0 by auto
      also have "... = a (2*N) - a N" 
        unfolding of_int_sum f_def of_int_diff
        apply (rule sum_Suc_diff')
        by auto
      finally have "N / 2 < a (2*N) - a N" .
      then show ?case using a_pos[rule_format,of N] by linarith
    qed

    have a_n4:"\<forall>\<^sub>F n in sequentially. a n > n/4" 
    proof -
      obtain N where a_N:"\<forall>n\<ge>N. a (2*n) \<ge> n /2+1"
        using a_2N unfolding eventually_at_top_linorder by auto
      have "a n>n/4" when "n\<ge>2*N" for n 
      proof -
        define n' where "n'=n div 2"
        have "n'\<ge>N" unfolding n'_def using that by auto
        have "n/4 < n' /2+1"
          unfolding n'_def by auto
        also have "... \<le> a (2*n')"
          using a_N \<open>n'\<ge>N\<close> by auto
        also have "... \<le>a n" unfolding n'_def
          apply (cases "even n")
          subgoal by simp
          subgoal by (simp add: assms(2) incseqD)
          done
        finally show ?thesis .
      qed
      then show ?thesis
        unfolding eventually_at_top_linorder by auto
    qed

    have c_sqrt:"\<forall>\<^sub>F n in sequentially. c n < sqrt n / 4"
    proof -
      have "\<forall>\<^sub>F x in sequentially. x>1" by simp
      moreover have "\<forall>\<^sub>F x in sequentially. real (nth_prime x) / (real x * ln (real x)) < 2"
        using nth_prime_asymptotics[unfolded asymp_equiv_def,THEN order_tendstoD(2),of 2]
        by simp
      ultimately have "\<forall>\<^sub>F n in sequentially. c n < B*8 *ln n + 1" using a_n4 Bc_large
      proof eventually_elim
        case (elim n)
        from this(4) have "c n=(B*nth_prime n+c (n+1))/a n"
          using a_pos[rule_format,of n] 
          by (auto simp:divide_simps)
        also have "... = (B*nth_prime n)/a n+c (n+1)/a n"
          by (auto simp:divide_simps)
        also have "... < (B*nth_prime n)/a n + 1"
        proof -
          have "c (n+1)/a n < 1" using elim(4) by auto
          then show ?thesis by auto
        qed
        also have "... < B*8 * ln n + 1"
        proof -
          have "B*nth_prime n < 2*B*n*ln n"
            using \<open>real (nth_prime n) / (real n * ln (real n)) < 2\<close> \<open>B>0\<close> \<open> 1 < n\<close> 
            by (auto simp:divide_simps)
          moreover have "real n / 4 < real_of_int (a n)" by fact
          ultimately have "(B*nth_prime n) / a n < (2*B*n*ln n) / (n/4)"
            apply (rule_tac frac_less)
            using \<open>B>0\<close> \<open> 1 < n\<close>  by auto
          also have "... = B*8 * ln n"
            using \<open> 1 < n\<close> by auto
          finally show ?thesis by auto
        qed
        finally show ?case .
      qed
      moreover have "\<forall>\<^sub>F n in sequentially. B*8 *ln n + 1 < sqrt n / 4"
        by real_asymp
      ultimately show ?thesis 
        by eventually_elim auto
    qed

    have 
      "\<forall>\<^sub>F n in sequentially. 0 < c (n+1)"
      "\<forall>\<^sub>F n in sequentially. c (n+1) < sqrt (n+1) / 4"
      "\<forall>\<^sub>F n in sequentially. n > 4"
      "\<forall>\<^sub>F n in sequentially. (n - 4) / sqrt (n + 1) + 1 > sqrt n"
      subgoal using c_pos[THEN eventually_all_ge_at_top]    
        by eventually_elim auto
      subgoal using  c_sqrt[THEN eventually_all_ge_at_top] 
        by eventually_elim (use le_add1 in blast)
      subgoal by simp
      subgoal 
        by real_asymp
      done
    then show ?thesis using a_gt_plus a_n4
      apply eventually_elim
    proof (rule impI)
      fix n assume asm:"0 < c (n + 1)" "c (n + 1) < sqrt (real (n + 1)) / 4" and
        a_ineq:"c (n + 1) < c n \<longrightarrow> a n +  (a n - c (n + 1) - 1) /  c (n + 1) < a (n + 1)" 
        "c (n + 1) < c n"  and "n / 4 < a n" "n > 4" 
        and n_neq:" sqrt (real n) < real (n - 4) / sqrt (real (n + 1)) + 1"

      have "(n-4) / sqrt(n+1) = (n/4 - 1)/ (sqrt (real (n + 1)) / 4)"
        using \<open>n>4\<close> by (auto simp:divide_simps)
      also have "... < (a n - 1) /  c (n + 1)" 
        apply (rule frac_less)
        using \<open>n > 4\<close> \<open>n / 4 < a n\<close> \<open>0 < c (n + 1)\<close> \<open>c (n + 1) < sqrt (real (n + 1)) / 4\<close>
        by auto
      also have "... - 1 = (a n - c (n + 1) - 1) /  c (n + 1)"
        using \<open>0 < c (n + 1)\<close> by (auto simp:field_simps)
      also have "a n + ... < a (n+1)"
        using a_ineq by auto
      finally have "a n + ((n - 4) / sqrt (n + 1) - 1) < a (n + 1)" by simp
      moreover have "(n - 4) / sqrt (n + 1) - 1 > sqrt n - 2"
        using n_neq[THEN diff_strict_right_mono,of 2] \<open>n>4\<close> 
        by (auto simp:algebra_simps of_nat_diff) 
      ultimately show "real_of_int (a n) + (sqrt (real n) - 2) < real_of_int (a (n + 1))"
        by argo
    qed
  qed

  text\<open>The following corresponds to inequality $ a_{2N} > N^{3/2}/2$ in the paper,
 which had to be slightly corrected: \<close>

  have a_2N_sqrt:"\<forall>\<^sub>F N in sequentially. a (2*N) >  real N * (sqrt (real N)/2 - 1)"
    using c_gt_half a_gt_sqrt[THEN eventually_all_ge_at_top] eventually_gt_at_top[of 4]
  proof eventually_elim
    case (elim N)
    define S where "S={n \<in> {N..<2 * N}. c (n + 1) < c n}"
    define f where "f = (\<lambda>n. a (Suc n) - a n)"

    have f_N:"\<forall>x\<in>S. f x\<ge>sqrt N - 2"
    proof 
      fix x assume "x\<in>S"
      then have "sqrt (real x) - 2 < f x" "x\<ge>N"
        using elim unfolding S_def f_def by auto
      moreover have "sqrt x - 2 \<ge> sqrt N - 2"
        using \<open>x\<ge>N\<close> by simp
      ultimately show  "sqrt (real N) - 2 \<le> real_of_int (f x)" by argo
    qed
    have f_0:"\<forall>x. f x\<ge>0"
      using \<open>mono a\<close>[THEN incseq_SucD] unfolding f_def by auto

    have "(N / 2)  * (sqrt N - 2) < card S * (sqrt N - 2)" 
      apply (rule mult_strict_right_mono)
      subgoal using elim unfolding S_def by auto
      subgoal using \<open>N>4\<close> 
        by (metis diff_gt_0_iff_gt numeral_less_real_of_nat_iff real_sqrt_four real_sqrt_less_iff)
      done
    also have "...  \<le> sum f S" 
      unfolding of_int_sum
      apply (rule sum_bounded_below)
      using f_N by auto
    also have "... \<le> sum f {N..<2 * N}" 
      unfolding of_int_sum
      apply (rule sum_mono2)
      unfolding S_def using f_0 by auto
    also have "... = a (2*N) - a N" 
      unfolding of_int_sum f_def of_int_diff
      apply (rule sum_Suc_diff')
      by auto
    finally have "real N / 2 * (sqrt (real N) - 2) < real_of_int (a (2 * N) - a N)" 
      .              
    then have "real N / 2 * (sqrt (real N) - 2) < a (2 * N)"
      using a_pos[rule_format,of N] by linarith
    then show ?case by (auto simp:field_simps)
  qed

  text\<open>The following part is required to derive the final contradiction of the proof.\<close>

  have a_n_sqrt:"\<forall>\<^sub>F n in sequentially. a n > (((n-1)/2) powr (3/2) - (n-1)) /2"
  proof (rule sequentially_even_odd_imp)
    define f where "f=(\<lambda>N. ((real (2 * N - 1) / 2) powr (3 / 2) - real (2 * N - 1)) / 2)"
    define g where "g=(\<lambda>N. real N * (sqrt (real N) / 2 - 1))"
    have "\<forall>\<^sub>F N in sequentially. g N > f N"
      unfolding f_def g_def
      by real_asymp
    moreover have "\<forall>\<^sub>F N in sequentially. a (2 * N) > g N"
      unfolding g_def using a_2N_sqrt .
    ultimately show "\<forall>\<^sub>F N in sequentially. f N < a (2 * N)"
      by eventually_elim auto
  next
    define f where "f=(\<lambda>N. ((real (2 * N + 1 - 1) / 2) powr (3 / 2) 
                                  - real (2 * N + 1 - 1)) / 2)"
    define g where "g=(\<lambda>N. real N * (sqrt (real N) / 2 - 1))"
    have "\<forall>\<^sub>F N in sequentially. g N = f N"
      using eventually_gt_at_top[of 0]
      apply eventually_elim
      unfolding f_def g_def
      by (auto simp:algebra_simps powr_half_sqrt[symmetric] powr_mult_base)
    moreover have "\<forall>\<^sub>F N in sequentially. a (2 * N) > g N"
      unfolding g_def using a_2N_sqrt .
    moreover have "\<forall>\<^sub>F N in sequentially. a (2 * N + 1) \<ge> a (2*N)"
      apply (rule eventuallyI)
      using \<open>mono a\<close> by (simp add: incseqD)
    ultimately show "\<forall>\<^sub>F N in sequentially. f N < (a (2 * N + 1))"
      apply eventually_elim
      by auto
  qed

  have a_nth_prime_gt:"\<forall>\<^sub>F n in sequentially. a n / nth_prime n > 1"
  proof -
    define f where "f=(\<lambda>n::nat. (((n-1)/2) powr (3/2) - (n-1)) /2)"
    have "\<forall>\<^sub>F x in sequentially. real (nth_prime x) / (real x * ln (real x)) < 2"
      using nth_prime_asymptotics[unfolded asymp_equiv_def,THEN order_tendstoD(2),of 2]
      by simp
    from this[] eventually_gt_at_top[of 1]
    have "\<forall>\<^sub>F n in sequentially. real (nth_prime n)   < 2*(real n * ln n)"
      apply eventually_elim
      by (auto simp:field_simps)
    moreover have *:"\<forall>\<^sub>F N in sequentially. f N >0 "
      unfolding f_def
      by real_asymp
    moreover have " \<forall>\<^sub>F n in sequentially. f n < a n"
      using a_n_sqrt unfolding f_def .
    ultimately have "\<forall>\<^sub>F n in sequentially. a n / nth_prime n 
                    > f n / (2*(real n * ln n))"
      apply eventually_elim
      apply (rule frac_less2)
      by auto
    moreover have "\<forall>\<^sub>F n in sequentially.
        (f n)/ (2*(real n * ln n)) > 1"
      unfolding f_def 
      by real_asymp
    ultimately show ?thesis 
      by eventually_elim argo
  qed

  have a_nth_prime_lt:"\<exists>\<^sub>F n in sequentially. a n / nth_prime n < 1"
  proof -
    have "liminf (\<lambda>x. a x / nth_prime x) < 1"
      using nth_2 by auto
    from this[unfolded less_Liminf_iff]
    show ?thesis
      apply (auto elim!:frequently_elim1)
      by (meson divide_less_eq_1 ereal_less_eq(7) leD leI 
          nth_prime_nonzero of_nat_eq_0_iff of_nat_less_0_iff order.trans)
  qed

  from a_nth_prime_gt a_nth_prime_lt show False 
    by (simp add: eventually_mono frequently_def) 
qed

section\<open>Acknowledgements\<close>

text\<open>A.K.-A. and W.L. were supported by the ERC Advanced Grant ALEXANDRIA (Project 742178)
 funded by the European Research Council and led by Professor Lawrence Paulson
 at the University of Cambridge, UK.\<close>

end