(* Title:     Transcendence_Series.thy
   Authors:   Angeliki Koutsoukou-Argyraki and Wenda Li, University of Cambridge
*)

section \<open>The transcendence of certain infinite series\<close>
theory "Transcendence_Series" imports
    "HOL-Analysis.Multivariate_Analysis"
    "HOL-Computational_Algebra.Polynomial"
    Prime_Number_Theorem.Prime_Number_Theorem_Library
begin

text \<open>
We formalise the proofs of two transcendence criteria by J. Han\v{c}l and P. Rucki that
assert the transcendence of the sums of certain infinite series built up by sequences that 
fulfil certain properties (Theorems 2.1 and 2.2 in \cite{hancl2005}, HanclRucki1 and HanclRucki2 
here respectively). Both proofs make use of Roth's celebrated theorem on diophantine approximations 
to algebraic numbers from 1955 \cite{roth_1955} which we assume and implement within the locale 
RothsTheorem.

A small mistake was detected in the original proof of Theorem 2.1, and the authors suggested
to us a fix for the problem (in communication by email). 
Our formalised proof incorporates this correction (see the Remark in the proof of HanclRucki1).
\<close>

subsection \<open>Misc\<close>

lemma powr_less_inverse_iff:
  fixes x y z::real
  assumes "x>0""y>0""z>0"
  shows "x powr y < z \<longleftrightarrow> x < z powr (inverse y)"
proof
  assume "x powr y < z"
  from powr_less_mono2[OF _ _ this,of "inverse y"] 
  show "x < z powr inverse y" 
    using assms by (auto simp:powr_powr)
next
  assume *:"x < z powr inverse y"
  from powr_less_mono2[OF _ _ *,of y] show "x powr y < z"
    using assms by (auto simp:powr_powr)
qed

lemma powr_less_inverse_iff':
  fixes x y z::real
  assumes "x>0""y>0""z>0"
  shows "z< x powr y \<longleftrightarrow> z powr (inverse y) < x"
  using powr_less_inverse_iff[symmetric,of _ "inverse y"] assms by auto

lemma powr_less_eq_inverse_iff:
  fixes x y z::real
  assumes "x>0""y>0""z>0"
  shows "x powr y \<le> z \<longleftrightarrow> x \<le> z powr (inverse y)"
  by (meson assms(1) assms(2) assms(3) not_less powr_less_inverse_iff')

lemma powr_less_eq_inverse_iff':
  fixes x y z::real
  assumes "x>0""y>0""z>0"
  shows "z\<le> x powr y \<longleftrightarrow> z powr (inverse y) \<le> x"
  by (simp add: assms(1) assms(2) assms(3) powr_less_eq_inverse_iff)

lemma tendsto_PInfty_mono:
  assumes "(ereal o f) \<longlonglongrightarrow> \<infinity>" "\<forall>\<^sub>F x in sequentially. f x \<le> g x"
  shows "(ereal o g) \<longlonglongrightarrow> \<infinity>"
  using assms unfolding comp_def tendsto_PInfty_eq_at_top
  by (elim filterlim_at_top_mono, simp)

lemma limsup_infinity_imp_Inf_many:
  assumes "limsup f = \<infinity>"
  shows "(\<forall> m. (\<exists>\<^sub>\<infinity>i. f i > ereal m))" unfolding INFM_nat
proof (clarify,rule ccontr)
  fix m k assume "\<not> (\<exists>n>k. ereal m < f n)"
  then have "\<forall>n>k. f n \<le> ereal m" by auto
  then have "\<forall>\<^sub>F n in sequentially. f n \<le> ereal m"
    using eventually_at_top_dense by blast
  then have "limsup f \<le> ereal m" using Limsup_bounded by auto
  then show False using assms by simp
qed

lemma snd_quotient_plus_leq:
  defines "de\<equiv>(snd o quotient_of)"
  shows "de (x+y) \<le> de x * de y "
proof -                                
  obtain x1 x2 y1 y2 where xy: "quotient_of x = (x1,x2)" "quotient_of y=(y1,y2)"
    by (meson surj_pair)
  have "x2>0" "y2>0" using xy quotient_of_denom_pos by blast+
  then show ?thesis
    unfolding de_def comp_def rat_plus_code xy 
    apply (auto split:prod.split simp:Rat.normalize_def Let_def)
    by (smt div_by_1 gcd_pos_int int_div_less_self mult_eq_0_iff mult_sign_intros(1))
qed

lemma quotient_of_inj: "inj quotient_of"
  unfolding inj_def by (simp add: quotient_of_inject)

lemma infinite_inj_imageE:
  assumes "infinite A" "inj_on f A" "f ` A \<subseteq> B"
  shows "infinite B"
  using assms inj_on_finite by blast

lemma incseq_tendsto_limsup:
  fixes f::"nat \<Rightarrow> 'a::{complete_linorder,linorder_topology}"
  assumes "incseq f"
  shows "f \<longlonglongrightarrow> limsup f"
  using LIMSEQ_SUP assms convergent_def convergent_ereal tendsto_Limsup 
          trivial_limit_sequentially by blast

subsection \<open>Main proofs\<close>

text \<open>Since the proof of Roths theorem has not been formalized yet, we implement it into a locale 
      and used it as an assumption.\<close>
locale RothsTheorem = 
  assumes RothsTheorem:"\<forall>\<xi> \<kappa>. algebraic \<xi> \<and> \<xi> \<notin> \<rat> \<and> infinite {(p,q). q>0 \<and> 
            coprime p q \<and> \<bar>\<xi> - of_int p / of_int q\<bar> < 1 / q powr \<kappa>} \<longrightarrow> \<kappa> \<le> 2"

theorem (in RothsTheorem) HanclRucki1:
  fixes a b ::"nat\<Rightarrow>int" and \<delta> ::real 
  defines "aa\<equiv>(\<lambda>n. real_of_int (a n))" and "bb\<equiv>(\<lambda>n. real_of_int (b n))"
  assumes a_pos:"\<forall> k. a k >0" and b_pos:"\<forall> k. b k >0" and "\<delta> >0"
      and limsup_infy:"limsup (\<lambda> k. aa (k+1)/(\<Prod>i = 0..k. aa i)powr(2+\<delta>)*(1/bb (k+1))) = \<infinity>" 
      and liminf_1:"liminf (\<lambda>k. aa (k+1) / aa k * bb k / bb (k+1)) > 1"
  shows "\<not> algebraic(suminf  (\<lambda> k. bb k / aa k))" 
proof -
  have summable:"summable (\<lambda> k. bb k / aa k)" 
  proof (rule ratio_test_convergence)
    have [simp]:"aa k>0" "bb k>0" for k
      unfolding aa_def bb_def using a_pos b_pos by auto
    show "\<forall>\<^sub>F n in sequentially. 0 < bb n / aa n"
      apply (rule eventuallyI)
      by auto
    show "1 < liminf (\<lambda>n. ereal (bb n / aa n / (bb (Suc n) / aa (Suc n))))" 
      using liminf_1 by (auto simp:algebra_simps) 
  qed
  have [simp]: "aa k>0" "bb k>0" for k unfolding aa_def bb_def 
    by (auto simp add: a_pos b_pos)
  have ab_1:"aa k\<ge>1" "bb k\<ge>1" for k
    unfolding aa_def bb_def using a_pos b_pos 
    by (auto simp add: int_one_le_iff_zero_less)

  define B where "B=liminf (\<lambda>x. ereal (aa (x + 1) / aa x * bb x / bb (x + 1)))"
  define M where "M= (case B of ereal m \<Rightarrow> (m+1)/2 | _ \<Rightarrow> 2)"
  have "M > 1" "M < B"
    using liminf_1 unfolding M_def 
    apply (fold B_def)
    by (cases B,auto)+

  text \<open>
Remark:
In the original proof of Theorem 2.1 in \cite{hancl2005}
it was claimed in p.534 that from assumption (3) (i.e. @{thm liminf_1}),
we obtain that:
$\forall A>1~\exists k_0~ \forall k > k_0~ \frac{1}{A} \frac{b_k}{ a_k} > \frac{ b_{k+1}}{ a_{k+1}} $,
 however note the counterexample  where
$a_{k+1}= k (a_1 a_2 ... a_k)^{\lceil 2+ \delta \rceil}$ if k is odd, and
$a_{k+1} = 2 a_k$ otherwise, with $b_k =1$ for all $k$.
In commmunication by email the authors suggested to replace the claim 
$\forall A>1~\exists k_0~ \forall k > k_0~ \frac{1}{A} \frac{b_k}{ a_k} > \frac{ b_{k+1}}{ a_{k+1}} $
with
$\exists A>1~\exists k_0~ \forall k > k_0~ \frac{1}{A} \frac{b_k}{ a_k} > \frac{ b_{k+1}}{ a_{k+1}} $
which solves the problem and the proof proceeds as in the paper.
The witness for $\exists A>1 $ is denoted by $M$ here.\<close>

  have bb_aa_event:"\<forall>\<^sub>F k in sequentially. (1/M)*(bb k / aa k)> bb(k+1)/ aa (k+1)"
    using less_LiminfD[OF \<open>M < B\<close>[unfolded B_def],simplified] 
    apply eventually_elim
    using \<open>M > 1\<close> by (auto simp:divide_simps algebra_simps)

  have bb_aa_p:"\<forall>\<^sub>F k in sequentially. \<forall>p. bb(k+p)/ aa (k+p) \<le> (1/M^p)*(bb k / aa k)" 
  proof -
    obtain k0 where k0_ineq:
        "\<forall>n\<ge>k0. bb (n + 1) / aa (n + 1) < 1 / M * (bb n / aa n)" 
      using bb_aa_event unfolding eventually_sequentially
      by auto
    have "bb(k+p)/ aa (k+p) \<le> (1/M^p)*(bb k / aa k)" when "k\<ge>k0" for p k
    proof (induct p)
      case 0
      then show ?case by auto
    next
      case (Suc p)
      have " bb (k + Suc p) / aa (k + Suc p)  < 1 / M * (bb (k+p) / aa (k+p))"
        using k0_ineq[rule_format,of "k+p"] that by auto
      also have "... \<le> 1 / M ^(Suc p) * (bb k / aa k)"
        using Suc \<open>M>1\<close> by (auto simp add:field_simps)
      finally show ?case by auto
    qed
    then show ?thesis unfolding eventually_sequentially by auto
  qed

  define \<xi> where "\<xi> = suminf (\<lambda> k. bb k / aa k)"
  have \<xi>_Inf_many:"\<exists>\<^sub>\<infinity> k. \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar> <  1 / prod aa {0..k} powr (2 + \<delta>)" 
  proof -
    have "\<bar>\<xi> - (\<Sum>i = 0..k. bb i / aa i)\<bar> = \<bar>\<Sum>i. bb (i+(k+1)) / aa (i+(k+1))\<bar>"
      for k
      unfolding \<xi>_def
      apply (subst suminf_minus_initial_segment[of _ "k+1",OF summable])
      using atLeast0AtMost lessThan_Suc_atMost by auto
    
    moreover have "\<exists>\<^sub>\<infinity> k. \<bar>\<Sum>i. bb(i+(k+1))/ aa (i+(k+1))\<bar>
                            <  1 / prod aa {0..k} powr (2 + \<delta>)" 
    proof -
      define P where "P = (\<lambda> i. \<forall>p. bb (i + 1 + p) / aa (i + 1 + p)
                                          \<le> 1 / M ^ p * (bb (i + 1) / aa (i + 1)))"
      define Q where "Q= (\<lambda> i. ereal (M / (M - 1)) 
                    < ereal (aa (i + 1) / prod aa {0..i} powr (2 + \<delta>) * (1 / bb (i + 1))))"
      have "\<forall>\<^sub>\<infinity> i. P i"
        using bb_aa_p[THEN sequentially_offset, of 1] cofinite_eq_sequentially
        unfolding P_def by auto
      moreover have "\<exists>\<^sub>\<infinity>i. Q i"
        using limsup_infy[THEN limsup_infinity_imp_Inf_many,rule_format,of "(M / (M -1))"]
        unfolding Q_def .
      moreover have "\<bar>\<Sum>i. bb(i+(k+1))/ aa (i+(k+1))\<bar>
                            <  1 / prod aa {0..k} powr (2 + \<delta>)"
        when "P k" "Q k" for k
      proof -
        have summable_M:"summable (\<lambda>i. 1 / M ^ i)"
          apply (rule summable_ratio_test[of "1/M"])
          using \<open>M>1\<close> by auto
        
        have "(\<Sum>i. bb (i + (k + 1)) / aa (i + (k + 1))) \<ge> 0"
          apply (rule suminf_nonneg)
          subgoal using summable_ignore_initial_segment[OF summable,of "k+1"] by auto 
          subgoal by (simp add: less_imp_le)
          done
        then have "\<bar>\<Sum>i. bb (i + (k + 1)) / aa (i + (k + 1))\<bar> 
                      = (\<Sum>i. bb (i + (k + 1)) / aa (i + (k + 1)))"
          by auto
        also have "... \<le> (\<Sum>i. 1 / M ^ i * (bb (k + 1) / aa (k + 1)))"
          apply (rule suminf_le)
          subgoal using that(1) unfolding P_def by (auto simp add:algebra_simps)
          subgoal using summable_ignore_initial_segment[OF summable,of "k+1"] by auto
          subgoal using summable_mult2[OF summable_M,of " bb (k + 1) / aa (k + 1)"] 
            by auto
          done
        also have "... = (bb (k + 1) / aa (k + 1)) * (\<Sum>i. 1 / M ^ i)"
          using suminf_mult2[OF summable_M,of " bb (k + 1) / aa (k + 1)"]
          by (auto simp:algebra_simps)
        also have "... = (bb (k + 1) / aa (k + 1)) * (\<Sum>i. (1 / M) ^ i)"
          using \<open>M>1\<close> by (auto simp: field_simps)
        also have "... = (bb (k + 1) / aa (k + 1)) * (M / (M -1))"
          apply (subst suminf_geometric) 
          using \<open>M>1\<close>  by (auto simp: field_simps)
        also have "... < (bb (k + 1) / aa (k + 1)) * (aa (k + 1) / 
                            prod aa {0..k} powr (2 + \<delta>) * (1 / bb (k + 1)))"
          apply (subst mult_less_cancel_left_pos)
          using that(2) unfolding Q_def by auto
        also have "... = 1/ prod aa {0..k} powr (2 + \<delta>)"
          using ab_1[of "Suc k"] by auto
        finally show ?thesis .
      qed
      ultimately show ?thesis by (smt INFM_conjI INFM_mono)
    qed
    ultimately show ?thesis by auto
  qed

  define pq where "pq = (\<lambda>k. quotient_of (\<Sum>i=0..k. of_int (b i) / of_int (a i)))"
  define p q where "p = fst \<circ> pq" and "q = snd \<circ> pq"
  have coprime_pq:"coprime (p k) (q k)"
        and q_pos:"q k > 0" and pq_sum:"p k / q k = (\<Sum>i=0..k. b i / a i)" for k
  proof -
    have eq: "quotient_of (\<Sum>i=0..k. of_int (b i) / of_int (a i)) = (p k, q k)"
      by (simp add: p_def q_def pq_def)
    from quotient_of_coprime[OF eq] show "coprime (p k) (q k)" .
    from quotient_of_denom_pos[OF eq] show "q k > 0" .
    have "(\<Sum>i=0..k. b i / a i) = of_rat (\<Sum>i=0..k. of_int (b i) / of_int (a i))"
      by (simp add: of_rat_sum of_rat_divide)
    also have "(\<Sum>i=0..k. rat_of_int (b i) / rat_of_int (a i)) =
                 rat_of_int (p k) / rat_of_int (q k)"
      using quotient_of_div[OF eq] by simp
    finally show "p k / q k = (\<Sum>i=0..k. b i / a i)" by (simp add:of_rat_divide)
  qed

  have \<xi>_Inf_many2:"\<exists>\<^sub>\<infinity> k. \<bar>\<xi> - p k / q k\<bar> 
                        <  1 / q k powr (2 + \<delta>)"
    using \<xi>_Inf_many
  proof (elim INFM_mono)
    fix k assume asm:"\<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar> < 1 / prod aa {0..k} powr (2 + \<delta>)"
    have "\<bar>\<xi> - real_of_int (p k) / real_of_int (q k)\<bar> 
              = \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar>"
      using pq_sum unfolding aa_def bb_def by auto
    also have "... < 1 / prod aa {0..k} powr (2 + \<delta>)"
      using asm by auto
    also have "... \<le> 1 / q k powr (2 + \<delta>)"
    proof -
      have "q k \<le> prod aa {0..k}"
      proof (induct k)
        case 0
        then show ?case unfolding q_def pq_def aa_def 
          apply (simp add:rat_divide_code of_int_rat quotient_of_Fract)
          using ab_1[of 0,unfolded aa_def bb_def] unfolding Let_def normalize_def 
          apply auto
          by (metis div_by_1 gcd_pos_int less_imp_le less_trans nonneg1_imp_zdiv_pos_iff 
                not_less zdiv_mono2)  
      next
        case (Suc k)
        define de where "de=snd \<circ> quotient_of"
        have "real_of_int (q (Suc k)) 
                  = de (\<Sum>i=0..Suc k. of_int (b i) / of_int (a i))"
          unfolding q_def pq_def de_def by simp
        also have "... = de ((\<Sum>i=0..k. of_int (b i) / of_int (a i)) 
                                + of_int (b (Suc k)) / of_int (a (Suc k)))"
          by simp
        also have "... \<le> de (\<Sum>i=0..k. of_int (b i) / of_int (a i)) 
                                * de (of_int (b (Suc k)) / of_int (a (Suc k)))"          
          using snd_quotient_plus_leq[folded de_def] by presburger
        also have "... = q k * de (of_int (b (Suc k)) / of_int (a (Suc k)))"
          unfolding q_def pq_def de_def by auto
        also have "... = q k * snd (Rat.normalize (b (Suc k), a (Suc k)))"
          by (simp add:rat_divide_code of_int_rat quotient_of_Fract de_def)
        also have "... \<le> q k * aa (Suc k)"
          using ab_1[of "Suc k"] q_pos[of "k"] 
          unfolding normalize_def aa_def bb_def Let_def
          apply auto
          by (metis div_by_1 int_one_le_iff_zero_less less_trans 
                  nonneg1_imp_zdiv_pos_iff not_less zdiv_mono2 zero_less_one)
        also have "... \<le>  prod aa {0..k} * aa (Suc k)"
          using Suc ab_1[of "Suc k"] by auto
        also have "... = prod aa {0..Suc k}"
          by (simp add: prod.atLeast0_atMost_Suc)
        finally show ?case .
      qed 
      then show ?thesis 
        by (smt \<open>0 < \<delta>\<close> frac_le of_int_0 of_int_le_iff powr_gt_zero 
                  powr_mono2 q_pos)
    qed
    finally show "\<bar>\<xi> - real_of_int (p k) / real_of_int (q k)\<bar> < 1 / real_of_int (q k) powr (2 + \<delta>)" .
  qed

  define pqs where "pqs={(p, q). q>0 \<and> coprime p q 
      \<and> \<bar>\<xi> - real_of_int p / real_of_int q\<bar> < 1 / q powr (2 + \<delta>)}"
  have \<xi>_infinite:"infinite pqs"
  proof -
    define A where "A={k. \<bar>\<xi> -  (p k) /  (q k)\<bar> < 1 / (q k) powr (2 + \<delta>)}" 
    have "\<exists>\<^sub>\<infinity> k. \<bar>\<xi> - p k / q k\<bar> <  1 / q k powr (2 + \<delta>)"
      using \<xi>_Inf_many2 .
    then have "infinite A"
      unfolding Inf_many_def A_def by auto
    moreover have "inj_on (\<lambda>k. (p k, q k)) A"
    proof -
      define g where "g=(\<lambda>i. rat_of_int (b i) / rat_of_int (a i))"
      define f where "f=(\<lambda>k. \<Sum>i = 0..k. g i)"
      have g_pos:"g i>0" for i
        unfolding g_def by (simp add: a_pos b_pos)
      have "strict_mono f" unfolding strict_mono_def f_def
      proof safe
        fix x y::nat assume "x < y"
        then have "sum g {0..y} - sum g {0..x} = sum g {x<..y}" 
          apply (subst  Groups_Big.sum_diff[symmetric])
          by (auto intro:arg_cong2[where f=sum])
        also have "... > 0"
          apply (rule ordered_comm_monoid_add_class.sum_pos)
          using \<open>x<y\<close> g_pos by auto
        finally have "sum g {0..y} - sum g {0..x} >0" .
        then show "sum g {0..x} < sum g {0..y}" by auto
      qed
      then have "inj f" using strict_mono_imp_inj_on by auto
      then have "inj (quotient_of o f)" by (simp add: inj_compose quotient_of_inj)
      then have "inj (\<lambda>k. (p k, q k))"
        unfolding f_def p_def q_def pq_def comp_def
        apply (fold g_def)
        by auto
      then show ?thesis by (auto elim:subset_inj_on)
    qed
    moreover have "(\<lambda>k. (p k, q k)) ` A \<subseteq> pqs"
      unfolding A_def pqs_def using coprime_pq q_pos by auto
    ultimately show ?thesis
      apply (elim infinite_inj_imageE)
      by auto
  qed
  moreover have "finite pqs" if "\<xi> \<in> \<rat>"
  proof -
    obtain m n where \<xi>_mn:"\<xi> = (of_int m / of_int n)" and "coprime m n" "n>0"
    proof -
      obtain m n where mn:"\<bar>\<xi>\<bar> = (of_nat m / of_nat n)" "coprime m n" "n\<noteq>0"
        using Rats_abs_nat_div_natE[OF \<open>\<xi> \<in> \<rat>\<close> Rats_abs_nat_div_natE]
        by metis
      define m' and n'::int 
        where "m'=(if \<xi> > 0 then nat m else -nat m)" and "n'=nat n"
      then have "\<xi> = (of_int m' / of_int n')" "coprime m' n'" "n'>0"
        using mn by auto
      then show ?thesis using that by auto
    qed
    have "pqs \<subseteq> {(m,n)} \<union> {x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n }"
    proof (rule subsetI)
      fix x assume "x \<in> pqs"
      define p q where "p=fst x" and "q=snd x"
      have "q>0" "coprime p q" and pq_less:"\<bar>\<xi> - p / q\<bar> < 1 / q powr (2 + \<delta>)"
        using \<open>x\<in>pqs\<close> unfolding p_def q_def pqs_def by auto
      have q_lt_n:"q<n" when "m\<noteq>p \<or> n\<noteq>q" 
      proof -
        have "m * q \<noteq> n * p" using that \<open>coprime m n\<close> \<open>coprime p q\<close> \<open>q>0\<close> \<open>n>0\<close> 
          by (metis eq_rat(1) fst_conv int_one_le_iff_zero_less mult.commute normalize_stable 
                not_one_le_zero quotient_of_Fract snd_conv)
        then have "1/(n*q) \<le> \<bar>m/n - p/q\<bar>"
          using \<open>q>0\<close> \<open>n>0\<close>  
          apply (auto simp:field_simps)
          by (metis add_diff_cancel_left' diff_diff_eq2 diff_zero less_irrefl not_le of_int_diff 
                of_int_lessD of_int_mult)
        also have "...  < 1 / q powr (2 + \<delta>)"
          using pq_less unfolding \<xi>_mn by auto
        also have "... \<le> 1 / q ^2"
        proof -
          have "real_of_int (q\<^sup>2) = q powr 2"
            apply (subst powr_numeral)
            unfolding power2_eq_square using \<open>q>0\<close> by auto
          also have "... \<le> q powr (2 + \<delta>)"
            apply (rule powr_mono)
            using \<open>q>0\<close> \<open>\<delta>>0\<close> by auto
          finally have "real_of_int (q\<^sup>2) \<le> real_of_int q powr (2 + \<delta>)" .
          moreover have "real_of_int q powr (2 + \<delta>) > 0" using \<open>0 < q\<close> by auto
          ultimately show ?thesis by (auto simp:field_simps)
        qed 
        finally have " 1 /  (n * q) < 1 / q\<^sup>2" .
        then show ?thesis  using \<open>q>0\<close> \<open>n>0\<close> 
          unfolding power2_eq_square by (auto simp:field_simps)
      qed
      moreover have "- \<bar>m\<bar> - 1 \<le> p \<and> p \<le> \<bar>m\<bar> + 1" when "m\<noteq>p \<or> n\<noteq>q" 
      proof -
        define qn where "qn=q/n"
        have "0<qn" "qn<1" unfolding qn_def using q_lt_n[OF \<open>m\<noteq>p \<or> n\<noteq>q\<close>] \<open>q>0\<close> by auto

        have "\<bar>m/n - p / q\<bar> < 1 / q powr (2 + \<delta>)" using pq_less unfolding \<xi>_mn by simp
        then have "\<bar>p / q - m/n\<bar> < 1 / q powr (2 + \<delta>)" by simp
        then have " m/n- 1 / q powr (2 + \<delta>) < p/q \<and> p/q < m/n + 1 / q powr (2 + \<delta>)"
          unfolding abs_diff_less_iff by auto
        then have "qn*m- q / q powr (2 + \<delta>) < p \<and> p < qn*m + q / q powr (2 + \<delta>)"
          unfolding qn_def using \<open>q>0\<close> by (auto simp:field_simps)
        moreover have "- \<bar>m\<bar> - 1 \<le> qn*m- q / q powr (2 + \<delta>)"
        proof -
          have "- \<bar>m\<bar> \<le> qn*m" using \<open>0<qn\<close> \<open>qn<1\<close> 
            apply (cases "m\<ge>0")
            subgoal 
              apply simp 
              by (meson less_eq_real_def mult_nonneg_nonneg neg_le_0_iff_le of_int_0_le_iff order_trans)
            subgoal by simp
            done
          moreover have "- 1 \<le> - q / q powr (2 + \<delta>)" 
          proof -
            have "q = q powr 1" using \<open>0 < q\<close> by auto
            also have "... \<le>q powr (2 + \<delta>)"
              apply (rule powr_mono)
              using \<open>q>0\<close> \<open>\<delta>>0\<close> by auto
            finally have "q \<le> q powr (2 + \<delta>)" .
            then show ?thesis using \<open>0 < q\<close> by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover have "qn*m + q / q powr (2 + \<delta>) \<le> \<bar>m\<bar> + 1"
        proof -
          have "qn*m \<le> \<bar>m\<bar>" using \<open>0<qn\<close> \<open>qn<1\<close> 
            apply (cases "m\<ge>0")
            subgoal by (simp add: mult_left_le_one_le)
            subgoal by (smt of_int_0_le_iff zero_le_mult_iff)
            done
          moreover have "q / q powr (2 + \<delta>) \<le> 1"
          proof -
            have "q = q powr 1" using \<open>0 < q\<close> by auto
            also have "... \<le>q powr (2 + \<delta>)"
              apply (rule powr_mono)
              using \<open>q>0\<close> \<open>\<delta>>0\<close> by auto
            finally have "q \<le> q powr (2 + \<delta>)" .
            then show ?thesis using \<open>0 < q\<close> by auto
          qed
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show "x \<in> {(m, n)} \<union> {x \<in> pqs. - \<bar>m\<bar> - 1 \<le> fst x \<and> fst x \<le> \<bar>m\<bar> + 1 
                          \<and> 0 < snd x \<and> snd x < n}" 
        using \<open>x \<in> pqs\<close> \<open>q>0\<close> unfolding p_def q_def by force
    qed
    moreover have "finite {x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n }" 
    proof -
      have "finite ({- \<bar>m\<bar> - 1..\<bar>m\<bar> +1} \<times> {0<..<n})" by blast
      moreover have "{x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n } \<subseteq> 
                ({- \<bar>m\<bar> - 1..\<bar>m\<bar> +1} \<times> {0<..<n})"
        by auto
      ultimately show ?thesis 
        apply (elim rev_finite_subset)
        by blast
    qed
    ultimately show ?thesis using finite_subset by auto
  qed
  ultimately show ?thesis 
    apply (fold \<xi>_def)
    using RothsTheorem[rule_format,of \<xi> "2 + \<delta>",folded pqs_def] \<open>\<delta> >0\<close> by auto
qed


theorem (in RothsTheorem) HanclRucki2: 
  fixes a b ::"nat\<Rightarrow>int" and \<delta> \<epsilon> ::real 
  defines "aa\<equiv>(\<lambda>n. real_of_int (a n))" and "bb\<equiv>(\<lambda>n. real_of_int (b n))"
  assumes a_pos:"\<forall> k. a k >0" and b_pos:"\<forall> k. b k >0" and "\<delta> >0"
    and "\<epsilon> >0" 
    and limsup_infi:"limsup (\<lambda> k.(aa (k+1)/(\<Prod>i = 0..k. aa i)powr(2+(2/\<epsilon>) + \<delta>))
          * (1/(bb (k+1)))) = \<infinity>"
    and ratio_large:"\<forall> k. ( k \<ge> t \<longrightarrow>  (( aa(k+1)/bb( k+1)) ) powr(1/(1+\<epsilon>)) 
              \<ge>  (( aa k/bb k) powr(1/(1+\<epsilon>)))+1)"
  shows "\<not> algebraic(suminf (\<lambda> k. bb k /aa k))  "
proof-
  have aa_bb_pos[simp]:"aa k>0" "bb k>0" for k
    unfolding aa_def bb_def using a_pos b_pos by auto
  have summable:"summable (\<lambda> k. bb k / aa k)"
  proof -
    define c0 where "c0\<equiv>(aa t/bb t) powr(1/(1+\<epsilon>)) - t"
    have ab_k:"(aa k / bb k) powr(1/(1+\<epsilon>)) \<ge> k + c0" when "k\<ge>t" for k
      using that
    proof (induct k)
      case 0
      then show ?case unfolding c0_def by simp
    next
      case (Suc k)
      have ?case when "\<not> t\<le>k"
      proof -
        have "t = Suc k" using that Suc.prems by linarith
        then show ?thesis unfolding c0_def by auto
      qed
      moreover have ?case when "t \<le> k"
      proof -
        have "(aa(k+1)/bb(k+1)) powr(1/(1+\<epsilon>))
              \<ge> ( aa k/bb k) powr(1/(1+\<epsilon>))+1" 
          using ratio_large[rule_format,OF that] by blast
        then show ?thesis using Suc(1)[OF that] by simp
      qed
      ultimately show ?case by auto
    qed
    have "summable (\<lambda>k. 1 / (k + c0) powr (1+\<epsilon>))"
    proof -
      have "c0 + t > 0" unfolding c0_def
        using aa_bb_pos[of t] by (simp,linarith)
      then have "summable (\<lambda>k. 1 / (k + (c0+t)) powr (1+\<epsilon>))"
        using summable_hurwitz_zeta_real[of "1+\<epsilon>" "c0+t"]
        apply (subst (asm) powr_minus_divide)
        using \<open>\<epsilon>>0\<close> by auto
      then show ?thesis
        apply (rule_tac summable_offset[of _ t])
        by (auto simp:algebra_simps)
    qed
    moreover have "bb k / aa k \<le> 1 / (k + c0) powr (1+\<epsilon>)" when "k\<ge>t" for k
    proof -
      have "(aa t / bb t) powr (1 / (1 + \<epsilon>)) > 0"
        apply simp
        by (metis \<open>\<And>k. 0 < aa k\<close> \<open>\<And>k. 0 < bb k\<close> less_numeral_extra(3))
      then have "k + c0 >0" unfolding c0_def using that by linarith 
      then have "aa k / bb k \<ge> (k + c0) powr (1+\<epsilon>)" 
        using ab_k[OF that] 
        apply (subst (asm) powr_less_eq_inverse_iff')
        using \<open>\<epsilon> >0\<close> by auto
      then have "inverse (aa k / bb k) \<le> inverse ((k + c0) powr (1+\<epsilon>))" 
        apply (elim le_imp_inverse_le)
        using \<open>k + c0 >0\<close> by auto
      then show ?thesis by (simp add: inverse_eq_divide)
    qed
    ultimately show ?thesis 
      apply (elim summable_comparison_test'[where N=t])
      using aa_bb_pos by (simp add: less_eq_real_def)
  qed

  have 7:"\<exists>\<^sub>\<infinity> k. 1 / (M powr (\<epsilon>/(1+\<epsilon>)) * (\<Prod>i = 0..k. aa i)
                  powr(2+ \<delta> * \<epsilon> / (1+\<epsilon>))) > (bb (k+1) / aa(k+1)) powr (\<epsilon> / (1+\<epsilon>))"
      when "M > 0" for M
  proof -
    define tt where "tt= (\<lambda>i. prod aa {0..i} powr (2 + 2 / \<epsilon> + \<delta>))"
    have tt_pos:"tt i > 0" for i 
      unfolding tt_def
      apply(subst powr_gt_zero,induct i)
      subgoal by (metis aa_bb_pos(1) order_less_irrefl prod_pos)
      subgoal by (metis \<open>\<And>k. 0 < aa k\<close> order_less_irrefl prod_pos)
      done
    have "\<exists>\<^sub>\<infinity>i. M < (aa (i + 1) / tt i * (1 / bb (i + 1)))"
      using limsup_infinity_imp_Inf_many[OF limsup_infi,rule_format,of M]
      unfolding tt_def by auto
    then have "\<exists>\<^sub>\<infinity>i. 1 / (M * tt i) > (bb (i+1) / aa (i+1))"
      apply (elim INFM_mono)
      using \<open>M>0\<close> tt_pos by (auto simp:divide_simps algebra_simps)
    then have "\<exists>\<^sub>\<infinity>i. (1 / (M * tt i)) powr (\<epsilon>/(1+\<epsilon>)) 
                        > (bb (i+1) / aa (i+1)) powr (\<epsilon>/(1+\<epsilon>))"
      apply (elim INFM_mono powr_less_mono2[rotated 2])
      by (simp_all add: assms(6) pos_add_strict less_eq_real_def)
    moreover have "tt i  powr (\<epsilon>/(1+\<epsilon>)) = prod aa {0..i} powr (2 + \<delta> * \<epsilon> / (1+\<epsilon>))"
        for i
      unfolding tt_def
      apply (auto simp:powr_powr)
      using \<open>\<epsilon>>0\<close> by (simp add:divide_simps,simp add:algebra_simps)
    ultimately show ?thesis 
      apply (elim INFM_mono)
      by (smt nonzero_mult_div_cancel_left powr_divide powr_mult powr_one_eq_one
                that tt_pos zero_less_divide_iff)
  qed

  have 8:"\<forall>\<^sub>F k in sequentially. \<forall>s.  (( aa(k+s)/bb( k+s))) \<ge> 
                    ((( aa k/bb k) powr(1/(1+\<epsilon>))) +s)powr(1+\<epsilon>)" 
    using eventually_ge_at_top[of t]
  proof eventually_elim
    case (elim k)
    define ff where "ff=(\<lambda>k. (aa k / bb k) powr (1 / (1 + \<epsilon>)))"
    have 11:"ff k+s \<le> ff (k+s)" for s
    proof (induct s)
      case 0
      then show ?case unfolding ff_def by auto
    next
      case (Suc s)
      then have "ff k + Suc s \<le> ff (k+Suc s)"
        using ratio_large[rule_format,of "k+s"] \<open> t \<le> k\<close> unfolding ff_def by auto
      then show ?case by simp
    qed
    then have "(ff k+s) powr (1+\<epsilon>) \<le> ff (k+s) powr (1+\<epsilon>)" for s
      apply (rule powr_mono2[of "1+\<epsilon>",rotated 2])
      unfolding ff_def using \<open>\<epsilon>>0\<close> by auto
    then show ?case unfolding ff_def using \<open>\<epsilon>>0\<close> 
      apply (auto simp add:powr_powr)
      by (simp add: a_pos aa_def b_pos bb_def le_less)
  qed

  have 9: "(\<Sum>r. 1/((z+real r)powr(1+\<epsilon>))) \<le> 1/(\<epsilon> *(z-1) powr \<epsilon>)" 
      "summable (\<lambda>i. 1/((z+ real i)powr(1+\<epsilon>)))"
    when "z>1" for z
  proof -
    define f where "f= (\<lambda>r. 1/((z+ r)powr(1+\<epsilon>)))"
    have "((\<lambda>x. f (x - 1)) has_integral ((z-1) powr - \<epsilon>) / \<epsilon>) {0..}"
    proof -
       have "((\<lambda>x. (z-1 + x) powr (- 1 - \<epsilon>)) has_integral ((z-1) powr - \<epsilon>) / \<epsilon>) {0<..}"
        using powr_has_integral_at_top[of 0 "z-1" "- 1 - \<epsilon>",simplified] \<open>z>1\<close> \<open>\<epsilon>>0\<close>
        by auto
      then have "((\<lambda>x. (z-1 + x) powr (- 1 - \<epsilon>)) has_integral ((z-1) powr - \<epsilon>) / \<epsilon>) {0..}"
        apply (subst (asm) has_integral_closure[symmetric])
        by (auto simp add: negligible_convex_frontier)
      then show ?thesis 
        apply (rule has_integral_cong[THEN iffD1, rotated 1])
        unfolding f_def by (smt powr_minus_divide)
    qed
    moreover have "\<And>x. 0 \<le> x \<Longrightarrow> 0 \<le> f (x - 1)" unfolding f_def by simp
    moreover have "\<And>x y. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> f (y - 1) \<le> f (x - 1)" unfolding f_def 
      by (smt assms(6) frac_le powr_mono2 powr_nonneg_iff that)
    ultimately have "summable (\<lambda>i. f (real i))" "(\<Sum>i. f (real i)) \<le> (z - 1) powr - \<epsilon> / \<epsilon>"
      using decreasing_sum_le_integral[of "\<lambda>x. f (x-1)" "((z-1) powr - \<epsilon>) / \<epsilon>",simplified]
      by auto
    moreover have "(z - 1) powr - \<epsilon> / \<epsilon> = 1/(\<epsilon> *(z-1) powr \<epsilon>)"
      by (simp add: powr_minus_divide)
    ultimately show "(\<Sum>i. f (real i)) \<le> 1/(\<epsilon> *(z-1) powr \<epsilon>)" by auto
    show "summable (\<lambda>i. f (real i))" using \<open>summable (\<lambda>i. f (real i))\<close> .
  qed

  have u:"(\<lambda>k.( aa k / bb k)) \<longlonglongrightarrow> \<infinity>" 
  proof -
    define ff where "ff\<equiv>(\<lambda>x. ereal (aa x / bb x))"
    have "limsup ff =  \<infinity>" 
    proof -
      define tt where "tt= (\<lambda>i. prod aa {0..i} powr (2 + 2 / \<epsilon> + \<delta>))"
      have "tt i \<ge> 1" for i
        unfolding tt_def
        apply (rule ge_one_powr_ge_zero)
        subgoal 
          apply (rule linordered_nonzero_semiring_class.prod_ge_1)
          by (simp add: a_pos aa_def int_one_le_iff_zero_less)
        subgoal by (simp add: \<open>\<epsilon>>0\<close> \<open>\<delta>>0\<close> less_imp_le)
        done
      then have "limsup (\<lambda>x.  (aa (x + 1) / tt x * (1 / bb (x + 1))))
                  \<le> limsup (\<lambda>x.  aa (x + 1) / bb (x + 1))"
        apply (intro Limsup_mono eventuallyI)
        apply (auto simp add:field_simps order.order_iff_strict)
        by (metis aa_bb_pos(1) div_by_1 frac_less2 less_irrefl less_numeral_extra(1) 
            not_le)
      also have "... = limsup (\<lambda>x.  aa x / bb x)"
        by (subst limsup_shift,simp)
      finally have "limsup (\<lambda>x. ereal (aa (x + 1) / tt x * (1 / bb (x + 1))))
                      \<le> limsup (\<lambda>x. ereal (aa x / bb x))" .
      moreover have "limsup (\<lambda>x. ereal (aa (x + 1) / tt x * (1 / bb (x + 1))))
                        = \<infinity>" using limsup_infi unfolding tt_def by auto
      ultimately show ?thesis 
        unfolding ff_def using ereal_infty_less_eq2(1) by blast
    qed
    then have "limsup (\<lambda>k. ff (k+t)) =  \<infinity>" 
      by (simp add: limsup_shift_k)
    moreover have "incseq (\<lambda>k. ff (k+t))"
    proof (rule incseq_SucI)
      fix k::nat 
      define gg where "gg\<equiv>(\<lambda>x. (aa x / bb x))"
      have "(gg (k+t)) powr (1 / (1 + \<epsilon>)) + 1 
                \<le> (gg (Suc (k+t))) powr (1 / (1 + \<epsilon>))"
        using ratio_large[rule_format, of "k+t",simplified] unfolding gg_def
        by auto
      then have "(gg (k+t)) powr (1 / (1 + \<epsilon>))
                      \<le> (gg (Suc (k+t))) powr (1 / (1 + \<epsilon>))"
        by auto
      then have "gg (k+t)\<le> gg (Suc (k+t))"
        by (smt aa_bb_pos(1) aa_bb_pos(2) assms(6) divide_pos_pos gg_def 
                powr_less_mono2)
      then show "ff (k + t) \<le> ff (Suc k + t)" 
        unfolding gg_def ff_def by auto
    qed
    ultimately have "(\<lambda>k. ff (k+t)) \<longlonglongrightarrow> \<infinity>" using incseq_tendsto_limsup
      by fastforce
    then show ?thesis unfolding ff_def 
      unfolding tendsto_def
      apply (subst eventually_sequentially_seg[symmetric,of _ t])
      by simp
  qed

  define \<xi> where "\<xi> = suminf (\<lambda> k. bb k / aa k)"
  have 10:"\<forall>\<^sub>F k in sequentially. \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar> 
                        < 2 / \<epsilon> * (bb (k+1) / aa (k+1)) powr (\<epsilon> / (1+\<epsilon>))" 
    using 8[THEN sequentially_offset,of 1] eventually_ge_at_top[of t]
            u[unfolded tendsto_PInfty,rule_format,THEN sequentially_offset
                        ,of "(2 powr (1/\<epsilon>) / (2 powr (1/\<epsilon>) - 1)) powr (1+\<epsilon>)" 1]
  proof eventually_elim
    case (elim k)
    define tt where "tt=(aa (k + 1) / bb (k + 1)) powr (1 / (1 + \<epsilon>))"
    have "tt>1"
    proof -
      have "(aa k / bb k) powr (1 / (1 + \<epsilon>)) > 0"
        by (metis a_pos aa_def b_pos bb_def divide_eq_0_iff less_irrefl 
                of_int_eq_0_iff powr_gt_zero)
      then show ?thesis using ratio_large[rule_format,OF \<open>k\<ge>t\<close>] unfolding tt_def by argo
    qed
    have "\<bar>\<xi> - (\<Sum>i = 0..k. bb i / aa i)\<bar> = \<bar>\<Sum>i. bb (i+(k+1)) / aa (i+(k+1))\<bar>"
      unfolding \<xi>_def
      apply (subst suminf_minus_initial_segment[of _ "k+1",OF summable])
      using atLeast0AtMost lessThan_Suc_atMost by auto
    also have "... = (\<Sum>i. bb (i+(k+1)) / aa (i+(k+1)))"
    proof -
      have "(\<Sum>i. bb (i+(k+1)) / aa (i+(k+1))) > 0"
        apply (rule suminf_pos)
        subgoal using summable[THEN summable_ignore_initial_segment,of "k+1"] .
        subgoal by (simp add: a_pos aa_def b_pos bb_def)
        done
      then show ?thesis by auto
    qed
    also have "... \<le> (\<Sum>i. 1 / (tt + i) powr (1 + \<epsilon>))"
    proof (rule suminf_le)
      define ff where "ff=(\<lambda>k n. (aa (k+1) / bb (k+1)) powr (1 / (1 + \<epsilon>)) + real n)"
      have "bb (n + (k + 1)) / aa (n + (k + 1)) \<le> 1 / (ff k n) powr (1 + \<epsilon>)" for n
      proof -
        have "ff k n powr (1 + \<epsilon>) \<le> aa (k + n +1 ) / bb (k + n+1 )"
          using elim(1)[rule_format,of n] unfolding ff_def by auto
        moreover have "ff k n powr (1 + \<epsilon>) > 0" 
          unfolding ff_def by (smt elim(2) of_nat_0_le_iff powr_gt_zero ratio_large)
        ultimately have "1 / ff k n powr (1 + \<epsilon>) \<ge>  bb (k + (n + 1)) / aa (k + (n + 1))"
          apply (drule_tac le_imp_inverse_le)
          by (auto simp add: inverse_eq_divide)
        then show ?thesis by (auto simp:algebra_simps)
      qed
      then show " \<forall>n. bb (n + (k + 1)) / aa (n + (k + 1)) \<le> 1 / (tt + real n) powr (1 + \<epsilon>)"
        unfolding ff_def tt_def by auto
      show "summable (\<lambda>i. bb (i + (k + 1)) / aa (i + (k + 1)))" 
        using summable[THEN summable_ignore_initial_segment,of "k+1"] .
      show "summable (\<lambda>x. 1 / (tt + real x) powr (1 + \<epsilon>))" 
        using 9(2)[OF \<open>tt>1\<close>] .
    qed
    also have "... \<le> 1/(\<epsilon> *(tt-1) powr \<epsilon>)" 
      using 9[OF \<open>tt>1\<close>] by simp
    also have "... < 2 / (\<epsilon> *tt powr \<epsilon>)"
    proof -
      have "((2 powr (1/\<epsilon>) / (2 powr (1/\<epsilon>) - 1)) powr (1 + \<epsilon>)) < (aa (k+1) / bb (k+1))"
        using elim(3) by auto
      then have "2 powr (1/\<epsilon>) / (2 powr (1/\<epsilon>) - 1) < tt"
        unfolding tt_def 
        apply (drule_tac powr_less_mono2[rotated 2,where a="1/ (1 + \<epsilon>)"])
        using \<open>\<epsilon>>0\<close> apply (auto simp:powr_powr )
        by (subst (asm) powr_one,auto simp add:field_simps)
      then have " tt < (tt-1) * (2 powr (1/\<epsilon>))"
        using \<open>\<epsilon>>0\<close> by (auto simp:divide_simps algebra_simps) 
      then have "tt powr \<epsilon> < 2 * (tt - 1) powr \<epsilon>"
        apply (drule_tac powr_less_mono2[rotated 2,where a="\<epsilon>"])
        using \<open>\<epsilon>>0\<close> \<open>tt>1\<close> by (auto simp:powr_powr powr_mult)
      then show ?thesis 
        using \<open>\<epsilon>>0\<close> \<open>tt>1\<close> by (auto simp:divide_simps)
    qed
    also have "... =  2 / \<epsilon> * (bb (k + 1) / aa (k + 1)) powr (\<epsilon> / (1 + \<epsilon>))"
      unfolding tt_def 
      using \<open>\<epsilon>>0\<close> 
      by (auto simp:powr_powr divide_simps algebra_simps powr_divide less_imp_le)
    finally show ?case .
  qed

  define pq where "pq = (\<lambda>k. quotient_of (\<Sum>i=0..k. of_int (b i) / of_int (a i)))"
  define p q where "p = fst \<circ> pq" and "q = snd \<circ> pq"
  have coprime_pq:"coprime (p k) (q k)"
        and q_pos:"q k > 0" and pq_sum:"p k / q k = (\<Sum>i=0..k. b i / a i)" for k
  proof -
    have eq: "quotient_of (\<Sum>i=0..k. of_int (b i) / of_int (a i)) = (p k, q k)"
      by (simp add: p_def q_def pq_def)
    from quotient_of_coprime[OF eq] show "coprime (p k) (q k)" .
    from quotient_of_denom_pos[OF eq] show "q k > 0" .
    have "(\<Sum>i=0..k. b i / a i) = of_rat (\<Sum>i=0..k. of_int (b i) / of_int (a i))"
      by (simp add: of_rat_sum of_rat_divide)
    also have "(\<Sum>i=0..k. rat_of_int (b i) / rat_of_int (a i)) =
                 rat_of_int (p k) / rat_of_int (q k)"
      using quotient_of_div[OF eq] by simp
    finally show "p k / q k = (\<Sum>i=0..k. b i / a i)" by (simp add:of_rat_divide)
  qed

  have \<xi>_Inf_many:"\<exists>\<^sub>\<infinity> k. \<bar>\<xi> - p k / q k\<bar> <  1 / q k powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
  proof -
    have *:"\<exists>\<^sub>\<infinity>k. (bb (Suc k) / aa (Suc k)) powr (\<epsilon> / (1 + \<epsilon>))
              < \<epsilon> / (2 * prod aa {0..k} powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)))"
      using 7[of "(2 / \<epsilon>) powr ((1+\<epsilon>)/ \<epsilon>)"] \<open>\<epsilon>>0\<close> 
      by (auto simp:powr_powr)
    have **:"\<forall>\<^sub>\<infinity>k. \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar>
                < 2 / \<epsilon> * (bb (k + 1) / aa (k + 1)) powr (\<epsilon> / (1 + \<epsilon>))"
      using 10[unfolded cofinite_eq_sequentially[symmetric]] .
    from INFM_conjI[OF * **] show ?thesis 
    proof (elim INFM_mono)
      fix k assume asm:"(bb (Suc k) / aa (Suc k)) powr (\<epsilon> / (1 + \<epsilon>))
                         < \<epsilon> / (2 * prod aa {0..k} powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))) \<and>
                          \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar> 
                        < 2 / \<epsilon> * (bb (k + 1) / aa (k + 1)) powr (\<epsilon> / (1 + \<epsilon>))"
      have "\<bar>\<xi> - real_of_int (p k) / real_of_int (q k)\<bar> 
              = \<bar>\<xi> - (\<Sum>k = 0..k. bb k / aa k)\<bar>"
        using pq_sum unfolding aa_def bb_def by auto
      also have "... < (2 / \<epsilon>) * (bb (k+1) / aa (k+1)) powr (\<epsilon> / (1+\<epsilon>))"
        using asm by auto
      also have "... <  (2 / \<epsilon>) * (\<epsilon> / (2 * prod aa {0..k} powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))))"
        apply (rule mult_strict_left_mono)
        using asm \<open>\<epsilon>>0\<close> by auto
      also have "... = 1/ prod aa {0..k} powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
        using \<open>\<epsilon>>0\<close> by auto
      also have "... \<le> 1 / q k powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
      proof -
        have "q k \<le> prod aa {0..k}"
        proof (induct k)
          case 0
          then show ?case unfolding q_def pq_def aa_def 
            apply (simp add:rat_divide_code of_int_rat quotient_of_Fract)
            using aa_bb_pos[of 0,unfolded aa_def bb_def] unfolding Let_def normalize_def 
            apply auto
            by (metis div_by_1 less_imp_le less_trans nonneg1_imp_zdiv_pos_iff 
                not_less zdiv_mono2)  
        next
          case (Suc k)
          define de where "de=snd \<circ> quotient_of"
          have "real_of_int (q (Suc k)) 
                  = de (\<Sum>i=0..Suc k. of_int (b i) / of_int (a i))"
            unfolding q_def pq_def de_def by simp
          also have "... = de ((\<Sum>i=0..k. of_int (b i) / of_int (a i)) 
                                + of_int (b (Suc k)) / of_int (a (Suc k)))"
            by simp
          also have "... \<le> de (\<Sum>i=0..k. of_int (b i) / of_int (a i)) 
                                * de (of_int (b (Suc k)) / of_int (a (Suc k)))"          
            using snd_quotient_plus_leq[folded de_def] by presburger
          also have "... = q k * de (of_int (b (Suc k)) / of_int (a (Suc k)))"
            unfolding q_def pq_def de_def by auto
          also have "... = q k * snd (Rat.normalize (b (Suc k), a (Suc k)))"
            by (simp add:rat_divide_code of_int_rat quotient_of_Fract de_def)
          also have "... \<le> q k * aa (Suc k)"
            using aa_bb_pos[of "Suc k"] q_pos[of "k"] 
            unfolding normalize_def aa_def bb_def Let_def
            apply auto
            by (metis div_by_1 int_one_le_iff_zero_less less_trans 
                  nonneg1_imp_zdiv_pos_iff not_less zdiv_mono2 zero_less_one)
          also have "... \<le>  prod aa {0..k} * aa (Suc k)"
            using Suc aa_bb_pos[of "Suc k"] by auto
          also have "... = prod aa {0..Suc k}"
            by (simp add: prod.atLeast0_atMost_Suc)
          finally show ?case .
        qed 
        then show ?thesis
          apply (rule_tac divide_left_mono)
          apply (rule powr_mono2)
          using \<open>\<delta>>0\<close> \<open>\<epsilon>>0\<close> q_pos[of k] 
           apply (auto simp:powr_mult[symmetric])
          by (metis aa_bb_pos(1) less_irrefl)
      qed 
      finally show "\<bar>\<xi> -  p k / q k\<bar> < 1 /  q k powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" .
    qed
  qed

  define pqs where "pqs={(p, q). q>0 \<and> coprime p q \<and> \<bar>\<xi> - real_of_int p / real_of_int q\<bar> 
                  < 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))}"
  have \<xi>_infinite:"infinite pqs"
  proof -
    define A where "A={k. \<bar>\<xi> -  (p k) /  (q k)\<bar> < 1 / (q k) powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))}" 
    note \<xi>_Inf_many
    then have "infinite A"
      unfolding Inf_many_def A_def by auto
    moreover have "inj_on (\<lambda>k. (p k, q k)) A"
    proof -
      define g where "g=(\<lambda>i. rat_of_int (b i) / rat_of_int (a i))"
      define f where "f=(\<lambda>k. \<Sum>i = 0..k. g i)"
      have g_pos:"g i>0" for i
        unfolding g_def by (simp add: a_pos b_pos)
      have "strict_mono f" unfolding strict_mono_def f_def
      proof safe
        fix x y::nat assume "x < y"
        then have "sum g {0..y} - sum g {0..x} = sum g {x<..y}" 
          apply (subst  Groups_Big.sum_diff[symmetric])
          by (auto intro:arg_cong2[where f=sum])
        also have "... > 0"
          apply (rule ordered_comm_monoid_add_class.sum_pos)
          using \<open>x<y\<close> g_pos by auto
        finally have "sum g {0..y} - sum g {0..x} >0" .
        then show "sum g {0..x} < sum g {0..y}" by auto
      qed
      then have "inj f" using strict_mono_imp_inj_on by auto
      then have "inj (quotient_of o f)" by (simp add: inj_compose quotient_of_inj)
      then have "inj (\<lambda>k. (p k, q k))"
        unfolding f_def p_def q_def pq_def comp_def
        apply (fold g_def)
        by auto
      then show ?thesis by (auto elim:subset_inj_on)
    qed
    moreover have "(\<lambda>k. (p k, q k)) ` A \<subseteq> pqs"
      unfolding A_def pqs_def using coprime_pq q_pos by auto
    ultimately show ?thesis
      apply (elim infinite_inj_imageE)
      by auto
  qed
  moreover have "finite pqs" if "\<xi> \<in> \<rat>"
  proof -
    obtain m n where \<xi>_mn:"\<xi> = (of_int m / of_int n)" and "coprime m n" "n>0"
    proof -
      obtain m n where mn:"\<bar>\<xi>\<bar> = (of_nat m / of_nat n)" "coprime m n" "n\<noteq>0"
        using Rats_abs_nat_div_natE[OF \<open>\<xi> \<in> \<rat>\<close> Rats_abs_nat_div_natE]
        by metis
      define m' and n'::int 
        where "m'=(if \<xi> > 0 then nat m else -nat m)" and "n'=nat n"
      then have "\<xi> = (of_int m' / of_int n')" "coprime m' n'" "n'>0"
        using mn by auto
      then show ?thesis using that by auto
    qed
    have "pqs \<subseteq> {(m,n)} \<union> {x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n }"
    proof (rule subsetI)
      fix x assume "x \<in> pqs"
      define p q where "p=fst x" and "q=snd x"
      have "q>0" "coprime p q" and pq_less:"\<bar>\<xi> - p / q\<bar> 
          < 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
        using \<open>x\<in>pqs\<close> unfolding p_def q_def pqs_def by auto
      have q_lt_n:"q<n" when "m\<noteq>p \<or> n\<noteq>q" 
      proof -
        have "m * q \<noteq> n * p" using that \<open>coprime m n\<close> \<open>coprime p q\<close> \<open>q>0\<close> \<open>n>0\<close> 
          by (metis eq_rat(1) fst_conv int_one_le_iff_zero_less mult.commute normalize_stable 
                not_one_le_zero quotient_of_Fract snd_conv)
        then have "1/(n*q) \<le> \<bar>m/n - p/q\<bar>"
          using \<open>q>0\<close> \<open>n>0\<close>  
          apply (auto simp:field_simps)
          by (metis add_diff_cancel_left' diff_diff_eq2 diff_zero less_irrefl not_le of_int_diff 
                of_int_lessD of_int_mult)
        also have "...  < 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
          using pq_less unfolding \<xi>_mn by auto
        also have "... \<le> 1 / q ^2"
        proof -
          have "real_of_int (q\<^sup>2) = q powr 2"
            apply (subst powr_numeral)
            unfolding power2_eq_square using \<open>q>0\<close> by auto
          also have "... \<le> q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
            apply (rule powr_mono)
            using \<open>q>0\<close> \<open>\<delta>>0\<close> \<open>\<epsilon>>0\<close> by auto
          finally have "real_of_int (q\<^sup>2) 
                          \<le> real_of_int q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" .
          moreover have "real_of_int q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)) > 0" using \<open>0 < q\<close> by auto
          ultimately show ?thesis by (auto simp:field_simps)
        qed 
        finally have " 1 /  (n * q) < 1 / q\<^sup>2" .
        then show ?thesis  using \<open>q>0\<close> \<open>n>0\<close> 
          unfolding power2_eq_square by (auto simp:field_simps)
      qed
      moreover have "- \<bar>m\<bar> - 1 \<le> p \<and> p \<le> \<bar>m\<bar> + 1" when "m\<noteq>p \<or> n\<noteq>q" 
      proof -
        define qn where "qn=q/n"
        have "0<qn" "qn<1" unfolding qn_def using q_lt_n[OF \<open>m\<noteq>p \<or> n\<noteq>q\<close>] \<open>q>0\<close> by auto

        have "\<bar>m/n - p / q\<bar> < 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" 
          using pq_less unfolding \<xi>_mn by simp
        then have "\<bar>p / q - m/n\<bar> < 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" by simp
        then have " m/n- 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)) 
            < p/q \<and> p/q < m/n + 1 / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
          unfolding abs_diff_less_iff by auto
        then have "qn*m- q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)) < p 
            \<and> p < qn*m + q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
          unfolding qn_def using \<open>q>0\<close> by (auto simp:field_simps)
        moreover have "- \<bar>m\<bar> - 1 \<le> qn*m- q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
        proof -
          have "- \<bar>m\<bar> \<le> qn*m" using \<open>0<qn\<close> \<open>qn<1\<close> 
            apply (cases "m\<ge>0")
            subgoal 
              apply simp 
              by (meson less_eq_real_def mult_nonneg_nonneg neg_le_0_iff_le of_int_0_le_iff 
                          order_trans)
            subgoal by simp
            done
          moreover have "- 1 \<le> - q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" 
          proof -
            have "q = q powr 1" using \<open>0 < q\<close> by auto
            also have "... \<le>q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
              apply (rule powr_mono)
              using \<open>q>0\<close> \<open>\<delta>>0\<close> \<open>\<epsilon>>0\<close> by auto
            finally have "q \<le> q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" .
            then show ?thesis using \<open>0 < q\<close> by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover have "qn*m + q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)) \<le> \<bar>m\<bar> + 1"
        proof -
          have "qn*m \<le> \<bar>m\<bar>" using \<open>0<qn\<close> \<open>qn<1\<close> 
            apply (cases "m\<ge>0")
            subgoal by (simp add: mult_left_le_one_le)
            subgoal by (smt of_int_0_le_iff zero_le_mult_iff)
            done
          moreover have "q / q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>)) \<le> 1"
          proof -
            have "q = q powr 1" using \<open>0 < q\<close> by auto
            also have "... \<le>q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))"
              apply (rule powr_mono)
              using \<open>q>0\<close> \<open>\<delta>>0\<close> \<open>\<epsilon>>0\<close> by auto
            finally have "q \<le> q powr (2 + \<delta> * \<epsilon> / (1 + \<epsilon>))" .
            then show ?thesis using \<open>0 < q\<close> by auto
          qed
          ultimately show ?thesis by auto
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show "x \<in> {(m, n)} \<union> {x \<in> pqs. - \<bar>m\<bar> - 1 \<le> fst x \<and> fst x \<le> \<bar>m\<bar> + 1 
                          \<and> 0 < snd x \<and> snd x < n}" 
        using \<open>x \<in> pqs\<close> \<open>q>0\<close> unfolding p_def q_def by force
    qed
    moreover have "finite {x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n }" 
    proof -
      have "finite ({- \<bar>m\<bar> - 1..\<bar>m\<bar> +1} \<times> {0<..<n})" by blast
      moreover have "{x. x \<in>pqs \<and> - \<bar>m\<bar> - 1 \<le>fst x \<and> fst x \<le> \<bar>m\<bar> + 1 \<and> 0<snd x \<and> snd x < n } \<subseteq> 
                ({- \<bar>m\<bar> - 1..\<bar>m\<bar> +1} \<times> {0<..<n})"
        by auto
      ultimately show ?thesis 
        apply (elim rev_finite_subset)
        by blast
    qed
    ultimately show ?thesis using finite_subset by auto
  qed
  ultimately show ?thesis 
    apply (fold \<xi>_def)
    using RothsTheorem[rule_format,of \<xi> "2 + \<delta> * \<epsilon> / (1 + \<epsilon>)",folded pqs_def] 
      \<open>\<delta> >0\<close> \<open>\<epsilon>>0\<close> 
    apply (auto simp:divide_simps )
    by (meson mult_le_0_iff not_less)
qed

subsection\<open> Acknowledgements\<close>

text\<open>A.K.-A. and W.L. were supported by the ERC Advanced Grant ALEXANDRIA (Project 742178)
 funded by the European Research Council and led by Professor Lawrence Paulson
 at the University of Cambridge, UK. Thanks to Iosif Pinelis for his clarification on
MathOverflow regarding the summmability of the series in @{thm [source] RothsTheorem.HanclRucki2}
@{url "https://mathoverflow.net/questions/323069/why-is-this-series-summable"}
and to Manuel Eberl for his helpful comments.\<close>

end