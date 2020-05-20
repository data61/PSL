(*
  File: Irrationality_J_Hancl.thy
  Authors:  Angeliki Koutsoukou-Argyraki and Wenda Li,
            Computer Laboratory, University of Cambridge, UK.
  Email: ak2110@cam.ac.uk, wl302@cam.ac.uk  
*)

section \<open>Irrational Rapidly Convergent Series\<close>
theory Irrationality_J_Hancl
  imports "HOL-Analysis.Analysis" "HOL-Decision_Procs.Approximation"
begin

text \<open>This is the formalisation of a proof by J. Hancl, in particular of the proof of his Theorem 3 in
the paper: Irrational Rapidly Convergent Series, Rend. Sem. Mat. Univ. Padova, Vol 107 (2002).

The statement asserts the irrationality of the sum of a series consisting of rational numbers
defined using sequences that fulfill certain properties. Even though the statement
is number-theoretic, the proof uses only arguments from introductory Analysis.\<close>

text \<open>We show the central result (theorem Hancl3) by proof by contradiction, by making use of some of 
 the auxiliary lemmas. To this end, assuming that the sum is a rational number, for a quantity 
 $\textrm{ALPHA}(n)$ we show that $\textrm{ALPHA}(n) \geq 1$ for all $n \in \mathbb{N}$. After that we show that we can find an 
  $n \in \mathbb{N}$ for which $\textrm{ALPHA}(n) < 1$ which yields a contradiction and we thus conclude that the 
  sum of the series is a rational number. We finally give an immediate application of theorem Hancl3
 for a specific series (corollary Hancl3corollary, requiring lemma
 summable\_ln\_plus) which corresponds to Corollary 2 in the original
paper by J. Hancl. 
\<close>

hide_const floatarith.Max

subsection \<open>Misc\<close>

lemma filterlim_sequentially_iff:
  "filterlim f F1 sequentially \<longleftrightarrow> filterlim (\<lambda>x. f (x+k)) F1 sequentially"
  unfolding filterlim_iff
  apply (subst eventually_sequentially_seg)
  by auto

lemma filterlim_realpow_sequentially_at_top:
  "(x::real) > 1 \<Longrightarrow> filterlim ((^) x) at_top sequentially"
  apply (rule LIMSEQ_divide_realpow_zero[THEN filterlim_inverse_at_top,of _ 1,simplified])
  by auto

lemma filterlim_at_top_powr_real:
  fixes g::"'b \<Rightarrow> real"
  assumes "filterlim f at_top F" "(g \<longlongrightarrow> g') F" "g'>1"
  shows "filterlim (\<lambda>x. g x powr f x) at_top F"
proof -
  have "filterlim (\<lambda>x. ((g'+1)/2) powr f x) at_top F" 
  proof (subst filterlim_at_top_gt[of _ _ 1],rule+)
    fix Z assume "Z>(1::real)"
    have "\<forall>\<^sub>F x in F. ln Z \<le> ln (((g' + 1) / 2) powr f x)"
      using assms(1)[unfolded filterlim_at_top,rule_format,of "ln Z / ln ((g' + 1) / 2)"]
      apply (eventually_elim)
      using \<open>g'>1\<close> by (auto simp:ln_powr divide_simps)
    then show "\<forall>\<^sub>F x in F. Z \<le> ((g' + 1) / 2) powr f x"
      apply (eventually_elim)
      apply (subst (asm) ln_le_cancel_iff)
      using \<open>Z>1\<close> \<open>g'>1\<close> by auto
  qed
  moreover have "\<forall>\<^sub>F x in F. ((g'+1)/2) powr f x \<le> g x powr f x" 
  proof -
    have "\<forall>\<^sub>F x in F. g x > (g'+1)/2"
      apply (rule order_tendstoD[OF assms(2)])
      using \<open>g'>1\<close> by auto
    moreover have "\<forall>\<^sub>F x in F. f x>0" 
      using assms(1)[unfolded filterlim_at_top_dense,rule_format,of 0] .
    ultimately show ?thesis
      apply eventually_elim
      using \<open>g'>1\<close> by (auto intro!: powr_mono2)
  qed
  ultimately show ?thesis using filterlim_at_top_mono by fast
qed

lemma powrfinitesum:
  fixes a::real and s::nat assumes  "s \<le> n"
  shows " (\<Prod>j=s..(n::nat).(a powr (2^j)))  = a powr (\<Sum>j=s..(n::nat).(2^j)) "
  using \<open>s \<le> n\<close> 
proof(induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have ?case when "s\<le>n" using Suc.hyps 
    by (metis Suc.prems add.commute linorder_not_le powr_add prod.nat_ivl_Suc' sum.cl_ivl_Suc that)
  moreover have ?case when "s=Suc n"   
  proof-
    have "(\<Prod>j = s..Suc n. a powr 2 ^ j) =(a powr 2 ^(Suc n))  " 
      using \<open>s=Suc n\<close> by simp
    also have "(a powr 2 ^(Suc n) ) =  a powr sum ((^) 2) {s..Suc n}   " using that by auto
    ultimately show " (\<Prod>j = s..Suc n. a powr 2 ^ j) = a powr sum ((^) 2) {s..Suc n}"
      using \<open>s\<le>Suc n\<close> by linarith
  qed
  ultimately show ?case using \<open>s\<le>Suc n\<close> by linarith
qed

lemma summable_ratio_test_tendsto:
  fixes f :: "nat \<Rightarrow> 'a::banach"
  assumes "c < 1" and "\<forall>n. f n\<noteq>0" and "(\<lambda>n. norm (f (Suc n)) / norm (f n)) \<longlonglongrightarrow> c"
  shows "summable f"
proof -
  obtain N where N_dist:"\<forall>n\<ge>N. dist (norm (f (Suc n)) / norm (f n)) c < (1-c)/2"
    using assms unfolding tendsto_iff eventually_sequentially 
    by (meson diff_gt_0_iff_gt zero_less_divide_iff zero_less_numeral)
  have "norm (f (Suc n)) / norm (f n) \<le> (1+c)/2" when "n\<ge>N" for n
    using N_dist[rule_format,OF that] \<open>c<1\<close> 
    apply (auto simp add:field_simps dist_norm)
    by argo
  then have "norm (f (Suc n))  \<le> (1+c)/2 * norm (f n)" when "n\<ge>N" for n
    using that assms(2)[rule_format, of n] by (auto simp add:divide_simps)
  moreover have "(1+c)/2 < 1" using \<open>c<1\<close> by auto 
  ultimately show ?thesis
    using summable_ratio_test[of _ N f] by blast
qed

lemma summable_ln_plus:
  fixes f::"nat \<Rightarrow> real" 
  assumes "summable f" "\<forall>n. f n>0"
  shows "summable (\<lambda>n. ln (1+f n))"
proof (rule summable_comparison_test_ev[OF _ assms(1)])
  have "ln (1 + f n) > 0" for n by (simp add: assms(2) ln_gt_zero)
  moreover have "ln (1 + f n) \<le> f n" for n 
    apply (rule ln_add_one_self_le_self2)
    using assms(2)[rule_format,of n] by auto 
  ultimately show "\<forall>\<^sub>F n in sequentially. norm (ln (1 + f n)) \<le> f n"
    by (auto intro!: eventuallyI simp add:less_imp_le) 
qed

lemma suminf_real_offset_le:
  fixes f :: "nat \<Rightarrow> real"
  assumes f: "\<And>i. 0 \<le> f i" and "summable f"
  shows "(\<Sum>i. f (i + k)) \<le> suminf f"
proof -
  have "(\<lambda>n. \<Sum>i<n. f (i + k)) \<longlonglongrightarrow> (\<Sum>i. f (i + k))"
    using summable_sums[OF \<open>summable f\<close>] 
    by (simp add: assms(2) summable_LIMSEQ summable_ignore_initial_segment)
  moreover have "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> (\<Sum>i. f i)"
    using summable_sums[OF \<open>summable f\<close>] by (simp add: sums_def atLeast0LessThan f)
  then have "(\<lambda>n. \<Sum>i<n + k. f i) \<longlonglongrightarrow> (\<Sum>i. f i)"
    by (rule LIMSEQ_ignore_initial_segment)
  ultimately show ?thesis
  proof (rule LIMSEQ_le, safe intro!: exI[of _ k])
    fix n assume "k \<le> n"
    have "(\<Sum>i<n. f (i + k)) = (\<Sum>i<n. (f \<circ> (\<lambda>i. i + k)) i)"
      by simp
    also have "\<dots> = (\<Sum>i\<in>(\<lambda>i. i + k) ` {..<n}. f i)"
      by (subst sum.reindex) auto
    also have "\<dots> \<le> sum f {..<n + k}"
      by (intro sum_mono2) (auto simp: f)
    finally show "(\<Sum>i<n. f (i + k)) \<le> sum f {..<n + k}" .
  qed
qed



lemma factt:
  fixes s n ::nat assumes "s \<le> n" 
  shows " (\<Sum>i=s..n. 2^i) < (2^(n+1) :: real) " using assms
proof (induct n)
  case 0
  show ?case by  auto 
next
  case (Suc n)
  have ?case when  "s=n+1" using that by auto
  moreover have ?case when  "s \<noteq> n+1" 
  proof -
    have"(\<Sum>i=s..(n+1). 2^i ) = (\<Sum>i=s..n. 2^i ) + (2::real)^(n+1) "
      using sum.cl_ivl_Suc \<open>s \<le> Suc n \<close>
      by (auto simp add:add.commute)
    also have "... < (2) ^ (n +1) + (2)^(n+1)" 
    proof -
      have "s \<le>n" using that  \<open>s \<le> Suc n \<close> by auto
      then show ?thesis
        using Suc.hyps \<open>s \<le> n\<close> by linarith
    qed
    also have "... = 2^(n+2)" by simp
    finally show "(\<Sum>i=s..(Suc n). 2^i )< (2::real)^(Suc n+1)" by auto
  qed
  ultimately show ?case by blast
qed

subsection \<open>Auxiliary lemmas and the main proof\<close>

lemma showpre7:
  fixes a b ::"nat\<Rightarrow>int " and q p::int
  assumes "q>0" and "p>0"and a: "\<forall>n. a n>0" and "\<forall>n. b n>0" and 
    assumerational:"(\<lambda> n. b (n+1) / a (n+1) )  sums (p/q)"
  shows "q*((\<Prod>j=1..n. of_int( a j)))*(suminf (\<lambda>(j::nat). (b (j+n+1)/ a (j+n+1 )))) 
        = ((\<Prod>j=1..n. of_int( a j)))*(p -q* (\<Sum>j=1..n. b j / a j))       " 
proof -
  define aa where "aa=(\<Prod>j = 1..n. real_of_int (a j))"
  define ff where "ff=(\<lambda>i. real_of_int (b (i+1)) / real_of_int (a (i+1)))"

  have "(\<Sum>j. ff (j+n)) =  (\<Sum>n. ff n) - sum ff {..<n}"
    apply (rule suminf_minus_initial_segment)
    using assumerational unfolding ff_def by (simp add: sums_summable)
  also have "... = p/q - sum ff {..<n}"
    using assumerational unfolding ff_def by (simp add: sums_iff)
  also have "... = p/q - (\<Sum>j=1..n. ff (j-1))"
  proof -
    have "sum ff {..<n} = (\<Sum>j=1..n. ff (j-1))"
      apply (subst sum_bounds_lt_plus1[symmetric])
      by simp
    then show ?thesis unfolding ff_def by auto
  qed
  finally have "(\<Sum>j. ff (j + n)) = p / q - (\<Sum>j = 1..n. ff (j - 1))" .
  then have "q*(\<Sum>j. ff (j + n)) = p - q*(\<Sum>j = 1..n. ff (j - 1))"
    using \<open>q>0\<close> by (auto simp add:field_simps)
  then have "aa*q*(\<Sum>j. ff (j + n)) = aa*(p - q*(\<Sum>j = 1..n. ff (j - 1)))" 
    by auto
  then show ?thesis unfolding aa_def ff_def by auto
qed

lemma show7:
  fixes d::"nat\<Rightarrow>real" and a b::"nat\<Rightarrow>int " and q p::int
  assumes "q \<ge>1" and "p \<ge> 1" and a: "\<forall>n. a n \<ge> 1" and "\<forall>n. b n \<ge> 1"
    and assumerational:"(\<lambda> n. b (n+1) / a (n+1) ) sums (p/q)"
  shows "q*((\<Prod>j=1..n. of_int( a j)))*( suminf (\<lambda> (j::nat). (b (j+n+1)/ a (j+n+1 )))) \<ge> 1 "
    (is "?L \<ge> _")
proof-
  define LL where "LL=?L"
  define aa where "aa=(\<Prod>j = 1..n. real_of_int (a j))"
  define ff where "ff=(\<lambda>i. real_of_int (b (i+1)) / real_of_int (a (i+1)))"

  have "?L > 0"
  proof -
    have "aa > 0"
      unfolding aa_def using a
      apply (induct n,auto)
      by (simp add: int_one_le_iff_zero_less prod_pos)
    moreover have "(\<Sum>j. ff (j + n)) > 0"
    proof (rule suminf_pos)
      have "summable ff" unfolding ff_def using assumerational
        using summable_def by blast
      then show " summable (\<lambda>j. ff (j + n))" using summable_iff_shift[of ff n] by auto
      show " \<forall>i. 0 < ff (i + n)" unfolding ff_def using a assms(4) int_one_le_iff_zero_less by auto
    qed
    ultimately show ?thesis unfolding aa_def ff_def using \<open>q\<ge>1\<close> by auto
  qed
  moreover have "?L \<in> \<int>"
  proof -
    have "?L = aa *(p -q* ( \<Sum>j=1..n. b j / a j))"
      unfolding aa_def
      apply (rule showpre7)
      using assms int_one_le_iff_zero_less by auto
    also have "... = aa * p - q * (\<Sum>j=1..n. aa * b j / a j)"
      by (auto simp add:algebra_simps sum_distrib_left)
    also have "... = prod a {1..n} * p - q * (\<Sum>j = 1..n. b j * prod a ({1..n} - {j}))"
    proof -
      have "(\<Sum>j=1..n. aa * b j / a j) = (\<Sum>j=1..n. b j * prod a ({1..n} - {j}))"
        unfolding of_int_sum
      proof (rule sum.cong)
        fix x assume "x \<in> {1..n}"
        then have "(\<Prod>i = 1..n. real_of_int (a i)) = a x * (\<Prod>i\<in>{1..n} - {x}. real_of_int (a i))"
          apply (rule_tac prod.remove)
          by auto
        then have "aa / real_of_int (a x) = prod a ({1..n} - {x})"
          unfolding aa_def using a[rule_format,of x] by (auto simp add:field_simps)
        then show "aa * b x / a x = b x * prod a ({1..n} - {x})"
          by (metis mult.commute of_int_mult times_divide_eq_right)
      qed simp
      moreover have "aa * p = (\<Prod>j = 1..n.  (a j)) *  p"
        unfolding aa_def by auto
      ultimately show ?thesis by force
    qed
    also have "... \<in> \<int>" using Ints_of_int by blast
    finally show ?thesis .
  qed
  ultimately show ?thesis 
    apply (fold LL_def)
    by (metis Ints_cases int_one_le_iff_zero_less not_less of_int_0_less_iff of_int_less_1_iff)
qed

lemma show8:
  fixes d ::"nat\<Rightarrow>real " and a :: "nat\<Rightarrow>int" and s k::nat 
  assumes "A > 1" and d: "\<forall>n. d n> 1"  and a:"\<forall>n. a n>0" and "s>0"
    and "convergent_prod d"
    and assu2: "\<forall>n \<ge> s. ( A/ (of_int (a n)) powr(1/of_int (2^n)))> prodinf (\<lambda>j. d(n +j))"
  shows "\<forall>n\<ge>s. prodinf (\<lambda>j. d(j+n)) < A/(Max ((\<lambda>(j::nat). 
                  (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n}))"
proof(rule,rule)
  fix n assume "s \<le> n"
  define sp where "sp = (\<lambda>n. prodinf (\<lambda>j. d(j+n)))"
  define ff where "ff = (\<lambda>(j::nat). (real_of_int (a j)) powr(1 /of_int (2^j)))"
  have "sp i \<ge> sp n" when "i\<le>n" for i
  proof -
    have "(\<Prod>j. d (j + i)) = (\<Prod>ia. d (ia + (n - i) + i)) * (\<Prod>ia<n - i. d (ia + i))"
      apply (rule prodinf_split_initial_segment) 
      subgoal using \<open>convergent_prod d\<close> convergent_prod_iff_shift[of d i] by simp
      subgoal for j using d[rule_format,of "j+i"] by auto
      done
    then have "sp i = sp n * (\<Prod>j<n - i. d (i + j))"
      unfolding sp_def using \<open>n\<ge>i\<close> by (auto simp:algebra_simps)
    moreover have "sp i>1" "sp n>1" 
      unfolding sp_def using convergent_prod_iff_shift \<open>convergent_prod d\<close> d 
      by (auto intro!:less_1_prodinf)
    moreover have "(\<Prod>j<n - i. d (i + j)) \<ge>1" 
      apply (rule prod_ge_1)
      using d less_imp_le by auto
    ultimately show ?thesis by auto
  qed
  moreover have "\<forall>j\<ge>s. A / ff j > sp j" 
    unfolding ff_def sp_def using assu2 by (auto simp:algebra_simps)
  ultimately have "\<forall>j. s\<le>j \<and> j\<le>n \<longrightarrow> A / ff j > sp n" by force
  then show "sp n< A / Max (ff ` {s..n})" 
    by (metis (mono_tags, hide_lams) Max_in \<open>n\<ge>s\<close> atLeastAtMost_iff empty_iff 
        finite_atLeastAtMost finite_imageI imageE image_is_empty order_refl)
qed

lemma auxiliary1_9:
  fixes d ::"nat\<Rightarrow>real" and a::"nat\<Rightarrow>int " and s m::nat 
  assumes d: "\<forall>n. d n> 1"  and a: "\<forall>n. a n>0" and "s>0" and "n \<ge> m" and " m \<ge> s"
    and auxifalse_assu: "\<forall>n\<ge>m. (of_int (a (n+1))) powr(1 /of_int (2^(n+1))) <
              (d (n+1))* (Max ((\<lambda> (j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n} ))"
  shows "(of_int (a (n+1))) powr(1 /of_int (2^(n+1))) <
    (\<Prod>j=(m+1)..(n+1). d j) * (Max ((\<lambda> (j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..m}))"
proof-
  define ff where "ff = (\<lambda>(j::nat). (real_of_int (a j)) powr(1 /of_int (2^j)))"
  have [simp]:"ff j > 0" for j
    unfolding ff_def by (metis a less_numeral_extra(3) of_int_0_less_iff powr_gt_zero)

  have ff_asm:"ff (n+1) < d (n+1) * Max (ff ` {s..n})" when "n\<ge>m" for n
    using auxifalse_assu that unfolding ff_def by simp
  from \<open>n\<ge>m\<close>
  have Q: "(Max( ff ` {s..n} )) \<le> (\<Prod>j=(m+1)..n. d j)* (Max (ff ` {s..m}))"
  proof(induct n)
    case 0
    then show ?case using \<open>m\<ge>s\<close> by simp 
  next
    case (Suc n)
    have ?case when "m=Suc n"
      using that by auto
    moreover have ?case when "m\<noteq>Suc n" 
    proof -
      have "m \<le> n" using that Suc(2) by simp
      then have IH:"Max (ff ` {s..n}) \<le> prod d {m + 1..n} * Max (ff ` {s..m})"
        using Suc(1) by linarith
      have "Max (ff ` {s..Suc n}) = Max (ff ` {s..n} \<union> {ff (Suc n)})"
        using Suc.prems assms(5) atLeastAtMostSuc_conv by auto
      also have "... = max (Max (ff ` {s..n})) (ff (Suc n))"
        using Suc.prems assms(5) max_def sup_assoc that by auto
      also have "... \<le> max (Max (ff ` {s..n})) (d (n+1) * Max (ff ` {s..n}))"
        apply (rule max.mono)
        using ff_asm[of n] \<open> m \<le> Suc n\<close> that \<open>s\<le>m\<close> by auto
      also have "... \<le> Max (ff ` {s..n}) * max 1 (d (n+1))"
      proof -
        have "Max (ff ` {s..n}) \<ge>0" 
          by (metis (mono_tags, hide_lams) Max_in \<open>\<And>j. 0 < ff j\<close> \<open>m \<le> n\<close> assms(5) 
              atLeastAtMost_iff empty_iff finite_atLeastAtMost finite_imageI imageE 
              image_is_empty less_eq_real_def)
        then show ?thesis using max_mult_distrib_right 
          by (simp add: max_mult_distrib_right mult.commute)
      qed
      also have "... = Max (ff ` {s..n}) * d (n+1)"
        using d[rule_format, of "n+1"] by auto
      also have "... \<le>  prod d {m + 1..n} * Max (ff ` {s..m}) * d (n+1)"
        using IH d[rule_format, of "n+1"] by auto
      also have "... = prod d {m + 1..n+1} * Max (ff ` {s..m})"
        using \<open>n\<ge>m\<close> by (simp add:prod.nat_ivl_Suc' algebra_simps)
      finally show ?case by simp
    qed
    ultimately show ?case by blast
  qed
  then have "d (n+1) * Max (ff ` {s..n} ) \<le> (\<Prod>j=(m+1)..(n+1). d j)* (Max (ff ` {s..m}))"
    using \<open>m\<le>n\<close> d[rule_format,of "Suc n"] by (simp add:prod.nat_ivl_Suc')
  then show ?thesis using ff_asm[of n] \<open>s\<le>m\<close> \<open>m\<le>n\<close> unfolding ff_def by auto
qed

lemma show9:
  fixes d ::"nat\<Rightarrow>real " and a :: "nat\<Rightarrow>int " and s ::nat and A::real
  assumes   "A > 1" and  d: "\<forall>n. d n> 1"  and a: "\<forall>n. a n>0" and "s>0"  
    and assu1: "(( \<lambda> n. (of_int (a n)) powr(1 /of_int (2^n)))\<longlongrightarrow> A) sequentially "
    and "convergent_prod d"
    and 8: "\<forall>n\<ge>s. prodinf (\<lambda>j. d( n+j)) 
                  < A/(Max ((\<lambda>(j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n})) "
  shows "\<forall>m \<ge>s. \<exists>n\<ge>m.  ( (of_int (a (n+1))) powr(1 /of_int (2^(n+1))) \<ge>
          (d (n+1))* (Max ( ( \<lambda> (j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n} )))"
proof (rule ccontr)
  define ff where "ff = (\<lambda>(j::nat). (real_of_int (a j)) powr(1 /of_int (2^j)))"
  assume assumptioncontra: " \<not> (\<forall>m \<ge>s. \<exists>n\<ge>m.  ( (ff (n+1)) \<ge> (d (n+1))* (Max ( ff  ` {s..n}))))"

  then obtain  t where "t\<ge>s" and
    ttt: "  \<forall>n\<ge>t.  ( (ff (n+1)) < (d (n+1))* (Max ( ff ` {s..n} ) ))"               
    by fastforce
  define B where "B=prodinf (\<lambda>j. d(t+1+j))"
  have "B>0" unfolding B_def 
    apply (rule less_0_prodinf)
    subgoal using convergent_prod_iff_shift[of d "t+1"] \<open>convergent_prod d\<close> 
      by (auto simp:algebra_simps)
    subgoal using d le_less_trans zero_le_one by blast
    done

  have "A \<le> B * Max ( ff ` {s..t})"
  proof (rule tendsto_le[of sequentially "\<lambda>n. (\<Prod>j=(t+1)..(n+1). d j) * Max ( ff ` {s..t})" _ 
        "\<lambda>n. ff (n+1)"])
    show "(\<lambda>n. ff (n + 1)) \<longlonglongrightarrow> A"
      using assu1[folded ff_def] LIMSEQ_ignore_initial_segment by blast
    have "(\<lambda>n. prod d {t + 1..n + 1}) \<longlonglongrightarrow> B"
    proof -
      have "(\<lambda>n. \<Prod>i\<le>n. d (t + 1 + i)) \<longlonglongrightarrow> B"
        apply (rule convergent_prod_LIMSEQ[of "(\<lambda>j. d(t+1+j))",folded B_def])
        using \<open>convergent_prod d\<close> convergent_prod_iff_shift[of d "t+1"] by (simp add:algebra_simps)
      then have "(\<lambda>n. \<Prod>i\<in>{0..n}. d (i+(t + 1))) \<longlonglongrightarrow> B"
        using atLeast0AtMost by (auto simp:algebra_simps)
      then have "(\<lambda>n. prod d {(t + 1)..n + (t + 1)}) \<longlonglongrightarrow> B" 
        apply (subst (asm) prod.shift_bounds_cl_nat_ivl[symmetric])
        by simp
      from seq_offset_neg[OF this,of "t"]
      show "(\<lambda>n. prod d {t + 1..n+1}) \<longlonglongrightarrow> B"
        apply (elim Lim_transform)
        apply (rule LIMSEQ_I)
        apply (rule exI[where x="t+1"])
        by auto
    qed
    then show "(\<lambda>n. prod d {t + 1..n + 1} * Max (ff ` {s..t})) \<longlonglongrightarrow> B * Max (ff ` {s..t})" 
      by (auto intro:tendsto_eq_intros)
    have "\<forall>\<^sub>F n in sequentially. (ff (n+1)) < (\<Prod>j=(t+1)..(n+1). d j) * (Max ( ff ` {s..t}))"
      unfolding eventually_sequentially ff_def
      using auxiliary1_9[OF d a \<open>s>0\<close> _ \<open>t\<ge>s\<close> ttt[unfolded ff_def]]
      by blast
    then show "\<forall>\<^sub>F n in sequentially. (ff (n+1)) \<le> (\<Prod>j=(t+1)..(n+1). d j) * (Max ( ff ` {s..t}))"
      by (eventually_elim,simp)
  qed simp
  also have "... \<le> B * Max ( ff ` {s..t+1})"
  proof -
    have "Max (ff ` {s..t}) \<le> Max (ff ` {s..t + 1})"
      apply (rule Max_mono)
      using \<open>t\<ge>s\<close> by auto
    then show ?thesis using \<open>B>0\<close> by auto
  qed
  finally have "A \<le> B * Max (ff ` {s..t + 1})" 
    unfolding B_def .
  moreover have "B < A / Max (ff ` {s..t + 1})"
    using 8[rule_format, of "t+1",folded ff_def B_def] \<open>s\<le>t\<close> by auto
  moreover have "Max (ff ` {s..t+1})>0"
    using \<open>A \<le> B * Max (ff ` {s..t + 1})\<close> \<open>B>0\<close> \<open>A>1\<close>
      zero_less_mult_pos [of B "Max (ff ` {s..Suc t})"]
    by simp
  ultimately show False by (auto simp add:field_simps)
qed

lemma show10:
  fixes d ::"nat\<Rightarrow>real " and  a ::"nat\<Rightarrow>int " and s::nat
  assumes d: "\<forall>n. d n> 1" and a: "\<forall>n. a n>0"  and " s>0"
    and 9: "\<forall>m \<ge>s. \<exists>n\<ge>m.  ((of_int (a (n+1))) powr(1 /of_int (2^(n+1))) \<ge>
          (d (n+1))* (Max ((\<lambda>(j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n} )))"
  shows "\<forall>m\<ge>s. \<exists>n\<ge>m. (((d (n+1))powr(2^(n+1))) * (\<Prod>j=1..n. of_int( a j)) * 
            (1/ (\<Prod>j=1..s-1. (of_int( a j) )))) \<le> (a (n+1)) "
proof (rule,rule)
  fix m assume "s \<le> m" 
  from 9[rule_format,OF this]
  obtain n where "n\<ge>m" and asm_9:"( (of_int (a (n+1))) powr(1 /of_int (2^(n+1))) \<ge>
          (d (n+1))* (Max ( ( \<lambda> (j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n} )))"
    by auto
  with \<open>s\<le>m\<close> have "s\<le>n" by auto

  have prod:"(\<Prod>j=1..n. real_of_int( a j)) * ( 1/ (\<Prod>j=1..s-1. (of_int( a j) )))
          = (\<Prod>j=s..n. of_int( a j))"
  proof -
    define f where "f= (\<lambda>j. real_of_int( a j))"
    have "{Suc 0..n}= {Suc 0..s - Suc 0} \<union> {s..n}" using \<open>n\<ge>s\<close>  \<open>s >0\<close>
      by auto
    then have "(\<Prod>j=1..n. f j) = (\<Prod>j=1..s-1. f j) * (\<Prod>j=s..n. f j)"
      apply (subst prod.union_disjoint[symmetric])
      by auto
    moreover have "(\<Prod>j=1..s-1. f j) > 0 "
      apply (rule linordered_semidom_class.prod_pos)
      using a unfolding f_def by auto
    then have "(\<Prod>j=1..s-1. f j) \<noteq> 0" by argo
    ultimately show ?thesis unfolding f_def by auto 
  qed
  then have " (((d (n+1))powr(2^(n+1) )) * (\<Prod>j=1..n. of_int( a j)) * ( 1/ (\<Prod>j=1..s-1. (of_int( a j) ))))
                =(((d (n+1))powr(2^(n+1) )) * (\<Prod>j=s..n. of_int( a j)))" 
  proof -
    define f where "f= (\<lambda>j. real_of_int( a j))"
    define c where "c = (d (n+1))powr(2^(n+1))"
    show ?thesis using prod
      apply (fold f_def c_def)
      by (metis mult.assoc) 
  qed
  also have
    "... \<le> ((d (n+1))powr(2^(n+1) ) * (\<Prod>i=s..n. (Max(( \<lambda> (j::nat). ( of_int( a j) powr(1 /real_of_int (2^j)) )) ` {s..n  } ))   powr(2^i)) )"
  proof (rule mult_left_mono)
    show "0 \<le> (d (n + 1)) powr 2 ^ (n + 1)"
      by auto
    show "(\<Prod>j = s..n. real_of_int (a j))
    \<le> (\<Prod>i = s..n.
           Max ((\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) `
                {s..n}) powr
           2 ^ i)"
    proof (rule prod_mono)
      fix i assume i: "i \<in> {s..n}"
      have "real_of_int (a i) = (real_of_int (a i) powr (1 / real_of_int (2 ^ i))) powr 2 ^ i"
        unfolding powr_powr by (simp add: a less_eq_real_def)
      also have  "\<dots> \<le>  (Max(( \<lambda> (j::nat). ( real_of_int( a j) powr(1 /real_of_int (2^j)))) ` {s..n}))powr(2^i)" 
      proof (rule powr_mono2)
        show "real_of_int (a i) powr (1 / real_of_int (2 ^ i))
                  \<le> Max ((\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) ` {s..n})" 
          apply (rule Max_ge)
           apply auto
          using i by blast
      qed simp_all
      finally have "real_of_int (a i) \<le> Max ((\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) ` {s..n}) powr 2 ^ i" .
      then show "0 \<le> real_of_int (a i) \<and>
         real_of_int (a i)
         \<le> Max ((\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) `
                 {s..n}) powr
            2 ^ i"
        using a i
        by (metis \<open>real_of_int (a i) = (real_of_int (a i) powr (1 / real_of_int (2 ^ i))) powr 2 ^ i\<close> 
            powr_ge_pzero)
    qed
  qed
  also have "... = ((d (n+1))powr(2^(n+1) )) * (Max(( \<lambda> (j::nat). ( of_int( a j) powr 
                      (1 /of_int (2^j)) )) ` {s..n  } )) powr (\<Sum>i=s..n. 2^i ) "
  proof-
    have  "((d (n+1))powr(2^(n+1) ))\<ge>1  "
      by (metis Transcendental.log_one  d le_powr_iff zero_le_numeral zero_le_power zero_less_one)
    moreover have "(\<Prod>i=s..n. (Max(( \<lambda> (j::nat). ( of_int( a j) powr(1 /real_of_int (2^j)) )) ` {s..n  } ) )   powr(2^i))     = (Max(( \<lambda> (j::nat). ( of_int( a j) powr(1 /of_int (2^j)) )) ` {s..n  } )) powr (\<Sum>i=s..n. 2^i )  "
    proof -
      define ff where "ff = Max (( \<lambda> (j::nat). ( of_int( a j) powr(1 /real_of_int (2^j)) )) ` {s..n  } )"
      show ?thesis apply (fold ff_def)
        using \<open>s\<le>n\<close>  powrfinitesum by auto
    qed 
    ultimately show ?thesis by auto
  qed
  also have "... \<le>   ((d (n+1))powr(2^(n+1) )) * 
                (Max(( \<lambda> (j::nat).( of_int( a j) powr(1 /of_int (2^j)) )) ` {s..n  })) powr(2^(n+1))   "

  proof -
    define ff where "ff = Max (( \<lambda> (j::nat). ( of_int( a j) powr(1 /real_of_int (2^j)) )) ` {s..n  } )"
    have " sum ((^) 2) {s..n} < (2::real) ^ (n + 1)" using factt \<open>s\<le>n\<close>  by auto
    moreover have "1 \<le> ff" 
    proof -
      define S where "S=(\<lambda>(j::nat). ( of_int( a j) powr(1 /real_of_int (2^j)) )) ` {s..n  }"
      have "finite S" unfolding S_def by auto
      moreover have "S\<noteq>{}" unfolding S_def using \<open>s\<le>n\<close>  by auto
      moreover have "\<exists>x\<in>S. x\<ge>1"
      proof-
        have " ( of_int( a s) powr(1 /real_of_int (2^s)) ) \<ge> 1  "  
          apply (rule ge_one_powr_ge_zero)
           apply auto
          by (simp add: a int_one_le_iff_zero_less)
        moreover have " ( of_int( a s) powr(1 /real_of_int (2^s)) ) \<in> S" 
          unfolding S_def
          apply (rule rev_image_eqI[where x=s])
          using \<open>s\<le>n\<close> by auto
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis 
        using Max_ge_iff[of S 1] unfolding S_def ff_def by blast
    qed
    moreover have "0 \<le> (d (n + 1)) powr 2 ^ (n + 1)" by auto
    ultimately show ?thesis
      apply(fold ff_def)
      apply (rule mult_left_mono)
       apply (rule powr_mono)
      by auto
  qed

  also have "... =  ((d (n+1)) * 
                      (Max((\<lambda>j. (of_int( a j) powr(1 /of_int (2^j)))) ` {s..n}))) powr(2^(n+1))"
  proof -
    define ss where "ss = (\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) ` {s..n}"
    have "d (n + 1) \<ge>0" using d[rule_format,of "n+1"] by argo
    moreover have "Max ss \<ge>0" 
    proof -
      have "(a s) powr (1 /  (2 ^ s)) \<ge> 0" by auto
      moreover have "(a s) powr (1 /  (2 ^ s)) \<in> ss" unfolding ss_def 
        apply (rule_tac x=s in rev_image_eqI)
        using \<open>s\<le>n\<close> by auto
      moreover have "finite ss" "ss \<noteq> {}" unfolding ss_def using \<open>s\<le>n\<close> by auto
      ultimately show ?thesis using Max_ge_iff[of ss 0] by blast
    qed
    ultimately show ?thesis 
      apply (fold ss_def)
      using powr_mult by auto
  qed
  also have "... \<le> (real_of_int (a (n + 1)) powr (1 / real_of_int (2 ^ (n + 1)))) powr 2 ^ (n + 1)"
  proof - 
    define ss where "ss = (\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) ` {s..n}"
    show ?thesis 
    proof (fold ss_def,rule powr_mono2)
      have "Max ss \<ge>0" \<comment> \<open>NOTE: we are repeating the same proof, so it may be a good idea to put 
                            this conclusion in an outer block so that it can be reused 
                            (without reproving).\<close>
      proof -
        have "(a s) powr (1 /  (2 ^ s)) \<ge> 0" by auto
        moreover have "(a s) powr (1 /  (2 ^ s)) \<in> ss" unfolding ss_def 
          apply (rule_tac x=s in rev_image_eqI)
          using \<open>s\<le>n\<close> by auto
        moreover have "finite ss" "ss \<noteq> {}" unfolding ss_def using \<open>s\<le>n\<close> by auto
        ultimately show ?thesis using Max_ge_iff[of ss 0] by blast
      qed
      moreover have "d (n + 1) \<ge>0" 
        using d[rule_format,of "n+1"] by argo
      ultimately show "0 \<le> (d (n + 1)) * Max ss" by auto
      show "(d (n + 1)) * Max ss \<le> real_of_int (a (n + 1)) powr (1 / real_of_int (2 ^ (n + 1)))"
        using asm_9[folded ss_def] .
    qed simp    
  qed
  also have "... =  (of_int (a (n+1)))" 
    by (simp add: a less_eq_real_def pos_add_strict powr_powr)
  finally show "\<exists>n\<ge>m. d (n + 1) powr 2 ^ (n + 1) * (\<Prod>j = 1..n. real_of_int (a j)) *
                (1 / (\<Prod>j = 1..s - 1. real_of_int (a j)))
                \<le> real_of_int (a (n + 1))" using \<open>n\<ge>m\<close> \<open>m\<ge>s\<close> 
    apply (rule_tac x=n in exI)
    by auto
qed

lemma lasttoshow:
  fixes d ::"nat\<Rightarrow>real " and a b ::"nat\<Rightarrow>int " and q::int and s::nat
  assumes d: "\<forall>n. d n> 1" and a:"\<forall>n. a n>0" and "s>0" and "q>0"  
    and "A > 1" and b:"\<forall>n. b n>0" and 9:
    "\<forall>m\<ge>s. \<exists>n\<ge>m. ((of_int (a (n+1))) powr(1 /of_int (2^(n+1))) \<ge>
          (d (n+1))* (Max ((\<lambda>(j::nat). (of_int (a j)) powr(1 /of_int (2^j))) ` {s..n} )))"
    and assu3: "filterlim( \<lambda> n. (d n)^(2^n)/ b n) at_top sequentially "
    and 5: "\<forall>\<^sub>F n in sequentially. (\<Sum>j. (b (n + j)) /  (a (n + j))) \<le> 2 * b n / a n"
  shows "\<exists>n. q*((\<Prod>j=1..n. real_of_int(a j))) * suminf (\<lambda>(j::nat). (b (j+n+1)/ a (j+n+1)))<1"
proof-
  define as where "as=(\<Prod>j = 1..s - 1. real_of_int (a j))"
  obtain n where "n\<ge>s" and n_def1:"real_of_int q * as * 2 
      * real_of_int (b (n + 1)) / d (n + 1) powr 2 ^ (n + 1) < 1"
    and n_def2:"d (n + 1) powr 2 ^ (n + 1) * (\<Prod>j = 1..n. real_of_int (a j)) * (1 / as) 
          \<le> real_of_int (a (n + 1))"
    and n_def3:"(\<Sum>j. (b (n+1 + j)) /  (a (n+1 + j))) \<le> 2 * b (n+1) / a (n+1)"
  proof -
    have *:"(\<lambda>n. real_of_int (b n) / d n ^ 2 ^ n) \<longlonglongrightarrow> 0"
      using tendsto_inverse_0_at_top[OF assu3] by auto
    then have "(\<lambda>n. real_of_int (b n) / d n powr 2 ^ n) \<longlonglongrightarrow> 0"
    proof -
      have "d n ^ 2 ^ n = d n powr (of_nat (2 ^ n))" for n 
        apply (subst powr_realpow)
        using d[rule_format, of n] by auto
      then show ?thesis using * by auto
    qed
    from tendsto_mult_right_zero[OF this,of "q * as * 2"] 
    have "(\<lambda>n. q * as * 2 * b n / d n powr 2 ^ n) \<longlonglongrightarrow> 0"
      by auto
    then have "\<forall>\<^sub>F n in sequentially. q * as * 2 * b n / d n powr 2 ^ n < 1"
      by (elim order_tendstoD) simp
    then have "\<forall>\<^sub>F n in sequentially. q * as * 2 * b n / d n powr 2 ^ n < 1 
                  \<and> (\<Sum>j. (b (n + j)) /  (a (n + j))) \<le> 2 * b n / a n"
      using 5 by eventually_elim auto
    then obtain N where N_def:"\<forall>n\<ge>N. q * as * 2 * b n / d n powr 2 ^ n < 1 
            \<and> (\<Sum>j. (b (n + j)) /  (a (n + j))) \<le> 2 * b n / a n"
      unfolding eventually_sequentially by auto
    obtain n where "n\<ge>s" and "n\<ge>N" and n_def:"d (n + 1) powr 2 ^ (n + 1) 
                * (\<Prod>j = 1..n. of_int (a j)) * (1 / as) \<le> real_of_int (a (n + 1))"
      using show10[OF d a \<open>s>0\<close> 9,folded as_def,rule_format,of "max s N"] by auto
    with N_def[rule_format, of "n+1"] that[of n]  show ?thesis by auto
  qed

  define pa where "pa = (\<Prod>j = 1..n. real_of_int (a j))"
  define dn where "dn = d (n + 1) powr 2 ^ (n + 1)"
  have [simp]:"dn >0" "as > 0" 
    subgoal unfolding dn_def by (metis d not_le numeral_One powr_gt_zero zero_le_numeral)
    subgoal unfolding as_def by (simp add: a prod_pos)
    done
  have [simp]:"pa>0"
    unfolding pa_def using a by (simp add: prod_pos)

  have K: "q* (\<Prod>j=1..n. real_of_int (a j)) * suminf (\<lambda> (j::nat). (b (j+n+1)/ a (j+n+1)))
              \<le>q* (\<Prod>j=1..n. real_of_int (a j)) *2* (b (n+1))/(a( n+1))"
    apply (fold pa_def)
    using mult_left_mono[OF n_def3,of "real_of_int q * pa"] 
      \<open>n\<ge>s\<close> \<open>pa>0\<close> \<open>q>0\<close> by (auto simp add:algebra_simps) 
  also have KK:"... \<le> 2*q* (\<Prod>j=1..n. real_of_int (a j)) * (b(n+1))*
      ((\<Prod>j=1..s-1. real_of_int( a j))/((d (n+1))powr(2^(n+1)) * (\<Prod>j=1..n. real_of_int ( a j))))" 
  proof -
    have " dn * pa * (1 / as) \<le> real_of_int (a (n + 1))"
      using n_def2 unfolding dn_def pa_def .
    then show ?thesis 
      apply (fold pa_def dn_def as_def)
      using \<open>pa>0\<close> \<open>q>0\<close> a[rule_format, of "Suc n"] b[rule_format, of "Suc n"]
      by (auto simp add:divide_simps algebra_simps)
  qed
  also have KKK: "... = (q* ((\<Prod>j=1..(s-1). real_of_int( a j)))*2
                                * (b (n+1)))/ ((d (n+1))powr(2^(n+1)))"
    apply (fold as_def pa_def dn_def)
    apply simp
    using \<open>0 < pa\<close> by blast
  also have KKKK: "... < 1" using n_def1 unfolding as_def by simp
  finally show ?thesis by auto
qed

lemma 
  fixes d ::"nat\<Rightarrow>real " and  a b ::"nat\<Rightarrow>int " and A::real
  assumes "A > 1" and d: "\<forall>n. d n> 1" and a: "\<forall>n. a n>0" and b:"\<forall>n. b n>0" 
    and assu1: "(( \<lambda> n. (of_int (a n)) powr(1 /of_int (2^n)))\<longlongrightarrow> A) sequentially "
    and assu3: "filterlim ( \<lambda> n. (d n)^(2^n)/ b n) at_top sequentially"
    and "convergent_prod d"
  shows issummable: "summable (\<lambda>j. b j / a j)"
    and show5: "\<forall>\<^sub>F n in sequentially. (\<Sum>j. (b (n + j)) / (a (n + j))) \<le> 2 * b n / a n"
proof-
  define c where "c = (\<lambda>j. b j / a j)"
  have c_pos:"c j>0" for j 
    using a b unfolding c_def by simp
  have c_ratio_tendsto:"(\<lambda>n. c (n+1) / c n ) \<longlonglongrightarrow> 0"
  proof -
    define nn where "nn=(\<lambda>n. (2::int)^ (Suc n))"
    define ff where "ff=(\<lambda> n. (a n / a (Suc n)) powr(1 /nn n)*(d(Suc n)))"
    have nn_pos:"nn n>0" and ff_pos:"ff n>0" for n
      subgoal unfolding nn_def by simp
      subgoal unfolding ff_def
        using d[rule_format, of "Suc n"] a[rule_format, of n] a[rule_format, of "Suc n"]
        by auto
      done
    have ff_tendsto:"ff \<longlonglongrightarrow> 1/ sqrt A" 
    proof -
      have "(of_int (a n)) powr(1 / (nn n)) = sqrt(of_int (a n) powr(1 /of_int (2^n)))" for n
        unfolding nn_def using a
        by (simp add: powr_half_sqrt [symmetric] powr_powr ac_simps)
      moreover have "(( \<lambda> n. sqrt(of_int (a n) powr(1 /of_int (2^n))))\<longlongrightarrow> sqrt A) sequentially " 
        using assu1 tendsto_real_sqrt by blast
      ultimately have "(( \<lambda> n. (of_int (a n)) powr(1 /of_int (nn n)))\<longlongrightarrow> sqrt A) sequentially " 
        by auto
      from tendsto_divide[OF this assu1[THEN LIMSEQ_ignore_initial_segment[where k=1]]] 
      have "(\<lambda>n. (a n / a (Suc n)) powr(1 /nn n)) \<longlonglongrightarrow> 1/sqrt A"
        using \<open>A>1\<close> a unfolding nn_def
        by (auto simp add:powr_divide less_imp_le inverse_eq_divide sqrt_divide_self_eq)
      moreover have "(\<lambda>n. d (Suc n))\<longlonglongrightarrow> 1" 
        apply (rule convergent_prod_imp_LIMSEQ)
        using convergent_prod_iff_shift[of d 1] \<open>convergent_prod d\<close> by auto
      ultimately show ?thesis
        unfolding ff_def by (auto intro:tendsto_eq_intros)
    qed
    have "(\<lambda>n. (ff n) powr nn n) \<longlonglongrightarrow> 0" 
    proof -
      define aa where "aa=(1+1/sqrt A) / 2"
      have "eventually (\<lambda>n. ff n<aa) sequentially"
        apply (rule order_tendstoD[OF ff_tendsto])
        unfolding aa_def using \<open>A>1\<close> by (auto simp add:field_simps)
      moreover have "(\<lambda>n. aa powr nn n) \<longlonglongrightarrow> 0" 
      proof -
        have "(\<lambda>y. aa ^ (nat \<circ> nn) y) \<longlonglongrightarrow> 0"
          apply (rule tendsto_power_zero)
          subgoal unfolding nn_def comp_def
            apply (rule filterlim_subseq)
            by (auto intro:strict_monoI)
          subgoal unfolding aa_def using \<open>A>1\<close> by auto
          done
        then show ?thesis
        proof (elim filterlim_mono_eventually)
          have "aa>0" unfolding aa_def using \<open>A>1\<close> 
            by  (auto simp add:field_simps pos_add_strict)
          then show " \<forall>\<^sub>F x in sequentially. aa ^ (nat \<circ> nn) x = aa powr real_of_int (nn x)"
            by (auto simp: powr_int order.strict_implies_order[OF nn_pos])
        qed auto
      qed
      ultimately show ?thesis
        apply (elim metric_tendsto_imp_tendsto)
        apply (auto intro!:powr_mono2 elim!:eventually_mono)
        using nn_pos ff_pos by (meson le_cases not_le)+
    qed
    then have "(\<lambda>n. (d (Suc n))^(nat (nn n)) * (a n / a (Suc n))) \<longlonglongrightarrow> 0" 
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in sequentially. ff x powr  (nn x) = d (Suc x) ^ nat (nn x) * (a x / a (Suc x))" 
        apply (rule eventuallyI)
        subgoal for x
          unfolding ff_def
          using a[rule_format,of x] a[rule_format,of "Suc x"] d[rule_format,of "Suc x"] nn_pos[of x]
          apply (auto simp add:field_simps powr_divide powr_powr powr_mult )
          by (simp add: powr_int)
        done
    qed auto 
    moreover have "(\<lambda>n. b (Suc n) / (d (Suc n))^(nat (nn n))) \<longlonglongrightarrow> 0"
      using tendsto_inverse_0_at_top[OF assu3,THEN LIMSEQ_ignore_initial_segment[where k=1]]
      unfolding nn_def by (auto simp add:field_simps nat_mult_distrib nat_power_eq)
    ultimately have "(\<lambda>n. b (Suc n) * (a n / a (Suc n))) \<longlonglongrightarrow> 0" 
      apply -
      subgoal premises asm
        using tendsto_mult[OF asm,simplified]
        apply (elim filterlim_mono_eventually)
        using d by (auto simp add:algebra_simps,metis (mono_tags, lifting) always_eventually 
            not_one_less_zero)
      done
    then have "(\<lambda>n. (b (Suc n) / b n) * (a n / a (Suc n))) \<longlonglongrightarrow> 0" 
      apply (elim Lim_transform_bound[rotated])
      apply (rule eventuallyI)
      subgoal for x using a[rule_format, of x] a[rule_format, of "Suc x"] 
          b[rule_format, of x] b[rule_format, of "Suc x"]
        by (auto simp add:field_simps)
      done
    then show ?thesis unfolding c_def by (auto simp add:algebra_simps)
  qed
  from c_ratio_tendsto
  have "(\<lambda>n. norm (b (Suc n) / a (Suc n)) / norm (b n / a n)) \<longlonglongrightarrow> 0" 
    unfolding c_def
    using a b by (force simp add:divide_simps abs_of_pos intro: Lim_transform_eventually)
  from summable_ratio_test_tendsto[OF _ _ this] a b 
  show "summable c" unfolding c_def
    apply auto 
    by (metis less_irrefl)
  have "\<forall>\<^sub>F n in sequentially. (\<Sum>j. c (n + j)) \<le> 2 * c n"
  proof -
    obtain N where N_ratio:"\<forall>n\<ge>N. c (n + 1) / c n < 1 / 2" 
    proof -
      have "eventually (\<lambda>n. c (n+1) / c n < 1/2) sequentially" 
        using c_ratio_tendsto[unfolded tendsto_iff,rule_format, of "1/2",simplified]
        apply eventually_elim
        subgoal for n using c_pos[of n] c_pos[of "Suc n"] by auto
        done
      then show ?thesis using that unfolding eventually_sequentially by auto
    qed
    have "(\<Sum>j. c (j + n)) \<le> 2 * c n" when "n\<ge>N" for n
    proof -
      have "(\<Sum>j<m. c (j + n)) \<le> 2*c n * (1 - 1 / 2^(m+1))" for m
      proof (induct m)
        case 0
        then show ?case using c_pos[of n] by simp
      next
        case (Suc m)
        have "(\<Sum>j<Suc m. c (j + n)) = c n + (\<Sum>i<m. c (Suc i + n)) "
          unfolding sum.lessThan_Suc_shift by simp
        also have "... \<le> c n + (\<Sum>i<m. c (i + n) / 2)"
        proof -
          have "c (Suc i + n) \<le> c (i + n) / 2" for i
            using N_ratio[rule_format,of "i+n"] \<open>n\<ge>N\<close> c_pos[of "i+n"]  by simp
          then show ?thesis by (auto intro:sum_mono)
        qed
        also have "... = c n + (\<Sum>i<m. c (i + n)) / 2"
          unfolding sum_divide_distrib by simp
        also have "... \<le> c n + c n * (1 - 1 / 2 ^ (m + 1))"
          using Suc by auto
        also have "... = 2 * c n * (1 - 1 / 2 ^ (Suc m + 1))"
          by (auto simp add:field_simps)
        finally show ?case .
      qed
      then have "(\<Sum>j<m. c (j + n)) \<le> 2*c n" for m
        using c_pos[of n] 
        by (smt divide_le_eq_1_pos divide_pos_pos nonzero_mult_div_cancel_left zero_less_power)
      moreover have "summable (\<lambda>j. c (j + n))" 
        using \<open>summable c\<close> by (simp add: summable_iff_shift)
      ultimately show ?thesis using suminf_le_const[of "\<lambda>j. c (j+n)" "2*c n"] by auto
    qed
    then show ?thesis unfolding eventually_sequentially by (auto simp add:algebra_simps)
  qed
  then show "\<forall>\<^sub>F n in sequentially. (\<Sum>j. (b (n + j)) /  (a (n + j))) \<le> 2 * b n / a n"
    unfolding c_def by simp
qed


theorem Hancl3:
  fixes d ::"nat\<Rightarrow>real " and  a b ::"nat\<Rightarrow>int "
  assumes "A > 1" and d:"\<forall>n. d n> 1" and a: "\<forall>n. a n>0" and b:"\<forall>n. b n>0" and "s>0"
    and assu1: "(( \<lambda> n. (of_int (a n)) powr(1 /of_int (2^n)))\<longlongrightarrow> A) sequentially "
    and assu2: "\<forall>n \<ge> s. (A/ (of_int (a n)) powr(1 /of_int (2^n)))> prodinf (\<lambda>j. d(n +j))"
    and assu3: "filterlim (\<lambda> n. (d n)^(2^n)/ b n) at_top sequentially"
    and "convergent_prod d" 
  shows "suminf(\<lambda> n. b n / a n ) \<notin> Rats"
proof(rule ccontr)
  assume asm:"\<not> (suminf(\<lambda> n. b n / a n ) \<notin> Rats)"
  have ab_sum:"summable (\<lambda>j. b j / a j)"
    using issummable[OF \<open>A>1\<close> d a b assu1 assu3 \<open>convergent_prod d\<close>] .
  obtain p q ::int where "q>0" and pq_def:"(\<lambda> n. b (n+1) / a (n+1) ) sums (p/q)"
  proof -
    from asm have "suminf(\<lambda> n. b n / a n ) \<in> Rats" by auto
    then have "suminf(\<lambda> n. b (n+1) / a (n+1)) \<in> Rats" 
      apply (subst suminf_minus_initial_segment[OF ab_sum,of 1])
      by auto   
    then obtain p' q' ::int where "q'\<noteq>0" and pq_def:"(\<lambda> n. b (n+1) / a (n+1) ) sums (p'/q')"
      unfolding Rats_eq_int_div_int
      using summable_ignore_initial_segment[OF ab_sum,of 1,THEN summable_sums]
      by force
    define p q where "p=(if q'<0 then - p' else p')" and "q=(if q'<0 then - q' else q')"
    have "p'/q'=p/q" "q>0" using \<open>q'\<noteq>0\<close> unfolding p_def q_def by auto
    then show ?thesis using that[of q p] pq_def by auto
  qed

  define ALPHA where 
    "ALPHA = (\<lambda>n. (of_int q)*((\<Prod>j=1..n. of_int(a j)))*(suminf (\<lambda> (j::nat). 
                      (b (j+n+1)/a (j+n+1)))))"
  have "ALPHA n \<ge> 1" for n 
  proof -
    have "suminf(\<lambda> n. b (n+1) / a (n+1)) > 0"
      apply (rule suminf_pos)
      subgoal using summable_ignore_initial_segment[OF ab_sum,of 1] by auto
      subgoal using a b by simp
      done
    then have "p/q > 0" using sums_unique[OF pq_def,symmetric] by auto
    then have "q\<ge>1" "p\<ge>1" using \<open>q>0\<close> by (auto simp add:divide_simps)
    moreover have "\<forall>n. 1 \<le> a n" "\<forall>n. 1 \<le> b n" using a b 
      by (auto simp add: int_one_le_iff_zero_less)
    ultimately show ?thesis unfolding ALPHA_def
      using show7[OF _ _ _ _ pq_def] by auto
  qed
  moreover have "\<exists>n. ALPHA n < 1" unfolding ALPHA_def
  proof (rule lasttoshow[OF d a \<open>s>0\<close> \<open>q>0\<close> \<open>A>1\<close> b _ assu3])
    show "\<forall>\<^sub>F n in sequentially. (\<Sum>j. real_of_int (b (n + j)) / real_of_int (a (n + j)))
                    \<le> real_of_int (2 * b n) / real_of_int (a n)"
      using show5[OF \<open>A>1\<close> d a b assu1 assu3 \<open>convergent_prod d\<close>] by simp
    show "\<forall>m\<ge>s. \<exists>n\<ge>m. d (n + 1) * Max ((\<lambda>j. real_of_int (a j) powr (1 / real_of_int (2 ^ j))) ` {s..n})
                 \<le> real_of_int (a (n + 1)) powr (1 / real_of_int (2 ^ (n + 1)))"
      apply (rule show9[OF \<open>A>1\<close> d a \<open>s>0\<close> assu1 \<open>convergent_prod d\<close>])
      using show8[OF \<open>A>1\<close> d a \<open>s>0\<close> \<open>convergent_prod d\<close> assu2] by (simp add:algebra_simps)
  qed
  ultimately show False using not_le by blast
qed

corollary Hancl3corollary:
  fixes A::real and  a b ::"nat\<Rightarrow>int "
  assumes "A > 1" and a: "\<forall>n. a n>0" and b:"\<forall>n. b n>0"
    and assu1: "((\<lambda> n. (of_int (a n)) powr(1 /of_int (2^n)))\<longlongrightarrow> A) sequentially "
    and asscor2: "\<forall>n \<ge>6. (of_int (a n)) powr(1 /of_int (2^n ))*(1+ 4*(2/3)^n) \<le> A
                    \<and> (b n \<le>2 powr((4/3)^(n-1)) )   "
  shows "suminf(\<lambda> n. b n / a n ) \<notin> Rats"
proof-
  define d::"nat\<Rightarrow>real" where "d= (\<lambda> n. 1+(2/3)^(n+1))" 

  have dgt1:"\<forall>n. 1 < d n " unfolding d_def by auto
  moreover have "convergent_prod d"
    unfolding d_def
    apply (rule abs_convergent_prod_imp_convergent_prod)
    apply (rule summable_imp_abs_convergent_prod)
    using summable_ignore_initial_segment[OF complete_algebra_summable_geometric
          [of "2/3::real",simplified],of 1] by simp
  moreover have "\<forall>n\<ge>6. (\<Prod>j. d (n + j)) 
                    < A / real_of_int (a n) powr (1 / real_of_int (2 ^ n))"
  proof rule+
    fix n::nat assume "6 \<le> n"
    have d_sum:"summable (\<lambda>j. ln (d j))" unfolding d_def
      apply (rule summable_ln_plus)
      apply (rule summable_ignore_initial_segment[OF complete_algebra_summable_geometric
          [of "2/3::real",simplified],of 1])
      by simp 

    have "(\<Sum>j. ln (d (n + j))) < ln (1+4 * (2 / 3) ^ n)"
    proof -
      define c::real where "c=(2 / 3) ^ n"
      have "0<c" "c<1/8" 
      proof -
        have "c=(2 / 3)^6 * (2 / 3)  ^ (n-6)"
          unfolding c_def using \<open>n\<ge>6\<close>
          apply (subst power_add[symmetric])
          by auto
        also have "... \<le> (2 / 3)^6" by (auto intro:power_le_one)
        also have "... < 1/8" by (auto simp add:field_simps)
        finally show "c<1/8" .
      qed (simp add:c_def)

      have "(\<Sum>j. ln (d (n + j))) \<le> (\<Sum>j. (2 / 3) ^ (n + j + 1))"
        apply (rule suminf_le)
        subgoal unfolding d_def 
          apply (intro allI ln_add_one_self_le_self2 )
          apply (rule order.strict_trans[of _ 0])
          by auto
        subgoal using summable_ignore_initial_segment[OF d_sum,of n] 
          by (auto simp add:algebra_simps)
        subgoal using summable_geometric[THEN summable_ignore_initial_segment,of "2/3" "n+1"]
          by (auto simp add:algebra_simps)
        done
      also have "... = (\<Sum>j. (2 / 3)^(n+1)*(2 / 3) ^ j)"
        by (auto simp add:algebra_simps power_add)
      also have "... = (2 / 3)^(n+1) * (\<Sum>j. (2 / 3) ^ j)"
        apply (rule suminf_mult)
        by (auto intro:summable_geometric)
      also have "... = 2 * c"
        unfolding c_def
        apply (subst suminf_geometric)
        by auto
      also have "... <  4 * c - (4 * c)\<^sup>2"
        using \<open>0<c\<close> \<open>c<1/8\<close>
        by (sos "((((A<0 * A<1) * R<1) + ((A<=0 * R<1) * (R<1/16 * [1]^2))))")
      also have "... \<le> ln (1 + 4 * c)"
        apply (rule ln_one_plus_pos_lower_bound)
        using \<open>0<c\<close> \<open>c<1/8\<close> by auto
      finally show ?thesis unfolding c_def by simp
    qed
    then have "exp (\<Sum>j. ln (d (n + j))) < 1 + 4 * (2 / 3) ^ n"
      by (metis Groups.mult_ac(2) add.right_neutral add_mono_thms_linordered_field(5) 
          divide_inverse divide_less_eq_numeral1(1) divide_pos_pos exp_gt_zero less_eq_real_def
          ln_exp ln_less_cancel_iff mult_zero_left rel_simps(27) rel_simps(76) zero_less_one
          zero_less_power)
    moreover have "exp (\<Sum>j. ln (d (n + j))) = (\<Prod>j. d (n + j))"
    proof (subst exp_suminf_prodinf_real [symmetric])
      show "\<And>k. 0 \<le> ln (d (n + k))" 
        using dgt1 by (simp add: less_imp_le)
      show "abs_convergent_prod (\<lambda>na. exp (ln (d (n + na))))"
        apply (subst exp_ln)
        subgoal for j using dgt1[rule_format,of "n+j"] by auto
        subgoal unfolding abs_convergent_prod_def real_norm_def
          apply (subst abs_of_nonneg)
          using convergent_prod_iff_shift[of d n] \<open>convergent_prod d\<close> 
          by (auto simp add: dgt1 less_imp_le algebra_simps)
        done
      show "(\<Prod>na. exp (ln (d (n + na)))) = (\<Prod>j. d (n + j))"
        apply (subst exp_ln)
        subgoal using dgt1 le_less_trans zero_le_one by blast
        subgoal by simp
        done
    qed
    ultimately have "(\<Prod>j. d (n + j))  < 1 + 4 * (2 / 3) ^ n"
      by simp
    also have "... \<le> A / (a n) powr (1 / of_int (2 ^ n))" 
    proof -
      have "a n powr (1 / real_of_int (2 ^ n)) > 0"
        using a[rule_format,of n] by auto
      then show ?thesis using asscor2[rule_format,OF \<open>6\<le>n\<close>] 
        by (auto simp add:field_simps)
    qed
    finally show "(\<Prod>j. d (n + j)) < A / real_of_int (a n) powr (1 / of_int (2 ^ n))" .
  qed
  moreover have "LIM n sequentially. d n ^ 2 ^ n / real_of_int (b n) :> at_top" 
  proof -
    have "LIM n sequentially. d n ^ 2 ^ n / 2 powr((4/3)^(n-1)) :> at_top"
    proof -
      define n1 where "n1=(\<lambda>n. (2::real)* (3/2)^(n-1))"
      define n2 where "n2=(\<lambda>n. ((4::real)/3)^(n-1))"
      have "LIM n sequentially. (((1+(8/9)/(n1 n)) powr (n1 n))/2) powr (n2 n) :> at_top" 
      proof (rule filterlim_at_top_powr_real[where g'="exp (8/9) / (2::real)"])
        define e1 where "e1=exp (8/9) / (2::real)"
        show "e1>1" unfolding e1_def by (approximation 4)
        show "(\<lambda>n. ((1+(8/9)/(n1 n)) powr (n1 n))/2) \<longlonglongrightarrow> e1"
        proof -
          have "(\<lambda>n. (1+(8/9)/(n1 n)) powr (n1 n)) \<longlonglongrightarrow> exp (8/9)"
            apply (rule filterlim_compose[OF tendsto_exp_limit_at_top])
            unfolding n1_def
            by (auto intro!: filterlim_tendsto_pos_mult_at_top 
                filterlim_realpow_sequentially_at_top
                simp:filterlim_sequentially_iff[of "\<lambda>x. (3 / 2) ^ (x - Suc 0)" _ 1])
          then show ?thesis unfolding e1_def
            by (intro tendsto_intros,auto)
        qed
        show "filterlim n2 at_top sequentially"
          unfolding n2_def
          apply (subst filterlim_sequentially_iff[of "\<lambda>n. (4 / 3) ^ (n - 1)" _ 1])
          by (auto intro:filterlim_realpow_sequentially_at_top)
      qed
      moreover have "\<forall>\<^sub>F n in sequentially. (((1+(8/9)/(n1 n)) powr (n1 n))/2) powr (n2 n)
        = d n ^ 2 ^ n / 2 powr((4/3)^(n-1))"
      proof (rule eventually_sequentiallyI[of 1])
        fix x assume "x\<ge>(1::nat)"
        have " ((1 + 8 / 9 / n1 x) powr n1 x / 2) powr n2 x 
                    = (((1 + 8 / 9 / n1 x) powr n1 x) powr n2 x) / 2 powr (4 / 3) ^ (x - 1)"
          by (simp add:n1_def n2_def powr_divide)
        also have "... = (1 + 8 / 9 / n1 x) powr (n1 x * n2 x) / 2 powr (4 / 3) ^ (x - 1)"
          by (simp add: powr_powr)
        also have "... = (1 + 8 / 9 / n1 x) powr (2 ^ x) / 2 powr (4 / 3) ^ (x - 1)"
        proof -
          have "n1 x * n2 x = 2 ^ x" 
            unfolding n1_def n2_def
            apply (subst mult.assoc)
            apply (subst power_mult_distrib[symmetric])
            using \<open>x\<ge>1\<close> by (auto simp flip:power_Suc)
          then show ?thesis by simp
        qed
        also have "... = (1 + 8 / 9 / n1 x) ^ (2 ^ x) / 2 powr (4 / 3) ^ (x - 1)"
          apply (subst (3) powr_realpow[symmetric])
           apply (simp_all add: n1_def)
          by (smt zero_le_divide_iff zero_le_power)
        also have "... = d x ^ 2 ^ x / 2 powr (4 / 3) ^ (x - 1)"
        proof -
          define x1 where "x1=x-1"
          have *:"x=x1+1" unfolding x1_def using \<open>x\<ge>1\<close> by simp
          have **: "8 / 9 / n1 x = (2 / 3) ^ (x + 1)" 
            unfolding n1_def using \<open>x\<ge>1\<close>
            apply (fold x1_def *[symmetric])
            by (auto simp add:divide_simps)
          then show ?thesis 
            unfolding d_def 
            apply (subst **)
            by auto
        qed
        finally show "((1 + 8 / 9 / n1 x) powr n1 x / 2) powr n2 x 
                        = d x ^ 2 ^ x / 2 powr (4 / 3) ^ (x - 1) " .
      qed
      ultimately show ?thesis using filterlim_cong by fast
    qed
    moreover have "\<forall>\<^sub>F n in sequentially. d n ^ 2 ^ n / 2 powr((4/3)^(n-1)) 
        \<le> d n ^ 2 ^ n / real_of_int (b n)"
      apply (rule eventually_sequentiallyI[of 6])
      apply (rule divide_left_mono)
      subgoal for x
        using asscor2[rule_format,of x] by auto
      subgoal for x
        using \<open>\<forall>n. 1 < d n\<close>[rule_format, of x] by auto
      subgoal for x
        using b by auto
      done
    ultimately show ?thesis by (auto elim: filterlim_at_top_mono)
  qed
  ultimately show ?thesis using Hancl3[OF \<open>A>1\<close> _ a b _ assu1,of d 6] by force
qed

end
