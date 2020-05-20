(* 
  Title: Lucas_Theorem.thy
  Author: Chelsea Edmonds, University of Cambridge
*)

theory Lucas_Theorem
  imports Main "HOL-Computational_Algebra.Computational_Algebra"
begin

notation fps_nth (infixl "$" 75)

section \<open>Extensions on Formal Power Series (FPS) Library\<close>

text \<open>This section presents a few extensions on the Formal Power Series (FPS) library, described in \cite{Chaieb2011} \<close>

subsection \<open>FPS Equivalence Relation \<close>

text \<open> This proof requires reasoning around the equivalence of coefficients mod some prime number. 
This section defines an equivalence relation on FPS using the pattern described by Paulson 
in \cite{paulsonDefiningFunctionsEquivalence2006}, as well as some basic lemmas for reasoning around 
how the equivalence holds after common operations are applied \<close>

definition "fpsmodrel p \<equiv> { (f, g). \<forall> n. (f $ n) mod p = (g $ n) mod p }"

lemma fpsrel_iff [simp]: "(f, g) \<in> fpsmodrel p \<longleftrightarrow> (\<forall>n. (f $ n) mod p = (g $ n) mod p)"
  by (simp add: fpsmodrel_def)

lemma fps_equiv: "equiv UNIV (fpsmodrel p)" 
proof (rule equivI)
  show "refl (fpsmodrel p)" by (simp add: refl_on_def fpsmodrel_def)
  show "sym (fpsmodrel p)" by (simp add: sym_def fpsmodrel_def)
  show "trans (fpsmodrel p)" by (intro transI) (simp add: fpsmodrel_def)
qed

text \<open> Equivalence relation over multiplication \<close>

lemma fps_mult_equiv_coeff: 
  fixes f g :: "('a :: {euclidean_ring_cancel}) fps"
  assumes "(f, g) \<in> fpsmodrel p"
  shows "(f*h)$n mod p = (g*h)$n mod p" 
proof -
  have "((f*h) $ n) mod p =(\<Sum>i=0..n. (f$i mod p * h$(n - i) mod p) mod p) mod p"
    using mod_sum_eq mod_mult_left_eq
    by (simp add: fps_mult_nth mod_sum_eq mod_mult_left_eq)
  also have "... = (\<Sum>i=0..n. (g$i mod p * h$(n - i) mod p) mod p) mod p"
    using assms by auto 
  also have "... = ((g*h) $ n) mod p"
    by (simp add: mod_mult_left_eq mod_sum_eq fps_mult_nth)
  thus ?thesis by (simp add: calculation)  
qed

lemma fps_mult_equiv: 
  fixes f g :: "('a :: {euclidean_ring_cancel}) fps"
  assumes "(f, g) \<in> fpsmodrel p"
  shows "(f*h, g*h) \<in> fpsmodrel p"
  using fpsmodrel_def fps_mult_equiv_coeff assms by blast 


text \<open> Equivalence relation over power operator \<close>
lemma fps_power_equiv: 
  fixes f g :: "('a :: {euclidean_ring_cancel}) fps"
  fixes x :: nat
  assumes "(f, g) \<in> fpsmodrel p"
  shows "(f^x, g^x) \<in> fpsmodrel p"
  using assms
proof (induct x)
  case 0
  thus ?case by (simp add: fpsmodrel_def)
next
  case (Suc x)
  then have hyp: " \<forall>n. f^x $ n mod p = g ^x $ n mod p" 
    using fpsrel_iff by blast 
  thus ?case 
  proof -
    have fact: "\<forall>n h. (g * h) $ n mod p = (f * h) $ n mod p"
      by (metis assms fps_mult_equiv_coeff)
    have "\<forall>n h. (g ^ x * h) $ n mod p = (f ^ x * h) $ n mod p"
      by (simp add: fps_mult_equiv_coeff hyp)
    then have "\<forall>n h. (h * g ^ x) $ n mod p = (h * f ^ x) $ n mod p"
      by (simp add: mult.commute)
    thus ?thesis
      using fact by force
  qed
qed

subsection \<open>Binomial Coefficients \<close>

text \<open>The @{term "fps_binomial"} definition in the formal power series uses the @{term "n gchoose k"} operator. It's 
defined as being of type @{typ "'a :: field_char_0 fps"}, however the equivalence relation requires a type @{typ 'a} 
that supports the modulo operator. 
The proof of the binomial theorem based on FPS coefficients below uses the choose operator and does
not put bounds on the type of @{term "fps_X"}.\<close> 

lemma binomial_coeffs_induct: 
  fixes n k :: nat
  shows "(1 + fps_X)^n $ k = of_nat(n choose k)"
proof (induct n arbitrary: k)
  case 0
  thus ?case
    by (metis binomial_eq_0_iff binomial_n_0 fps_nth_of_nat not_gr_zero of_nat_0 of_nat_1 power_0) 
next
  case h: (Suc n)
  fix k 
  have start: "(1 + fps_X)^(n + 1) = (1 + fps_X) * (1 + fps_X)^n" by auto
  show ?case 
    using One_nat_def Suc_eq_plus1 Suc_pred add.commute binomial_Suc_Suc binomial_n_0 
        fps_mult_fps_X_plus_1_nth h.hyps neq0_conv start by (smt of_nat_add)  
qed

subsection \<open>Freshman's Dream Lemma on FPS \<close>
text \<open> The Freshman's dream lemma modulo a prime number $p$ is a well known proof that $(1 + x^p) \equiv (1 + x)^p \mod p$\<close>

text \<open> First prove that $\binom{p^n}{k} \equiv 0 \mod p$ for $k \ge 1$ and $k < p^n$. The eventual
proof only ended up requiring this with $n = 1$\<close>

lemma pn_choose_k_modp_0:
  fixes n k::nat
  assumes "prime p"
          "k \<ge> 1 \<and> k \<le> p^n - 1"
          "n > 0"
  shows "(p^n choose k) mod p = 0"
proof - 
  have inequality: "k \<le> p^n" using assms (2) by arith
  have choose_take_1: "((p^n - 1) choose ( k - 1))= fact (p^n - 1) div (fact (k - 1) * fact (p^n - k))"
    using binomial_altdef_nat diff_le_mono inequality assms(2) by auto
  have "k * (p^n choose k) = k * ((fact (p^n)) div (fact k * fact((p^n) - k)))" 
    using assms binomial_fact'[OF inequality] by auto
  also have "... = k * fact (p^n) div (fact k * fact((p^n) - k))"
    using binomial_fact_lemma div_mult_self_is_m fact_gt_zero inequality mult.assoc mult.commute 
          nat_0_less_mult_iff by smt
  also have "... = k * fact (p^n) div (k * fact (k - 1) * fact((p^n) - k))" 
    by (metis assms(2) fact_nonzero fact_num_eq_if le0 le_antisym of_nat_id)
  also have "... = fact (p^n) div (fact (k - 1) * fact((p^n) - k))" 
    using assms by auto
  also have "... = ((p^n) * fact (p^n - 1)) div (fact (k - 1) * fact((p^n) - k))"
    by (metis assms(2) fact_nonzero fact_num_eq_if inequality le0 le_antisym of_nat_id)
  also have "... = (p^n) * (fact (p^n - 1) div (fact (k - 1) * fact((p^n) - k)))"
    by (metis assms(2) calculation choose_take_1 neq0_conv not_one_le_zero times_binomial_minus1_eq)
  finally have equality: "k * (p^n choose k) = p^n * ((p^n - 1) choose (k - 1))"
    using assms(2) times_binomial_minus1_eq by auto
  then have dvd_result: "p^n dvd (k * (p^n choose k))" by simp 
  have "\<not> (p^n dvd k)" 
    using assms (2) binomial_n_0 diff_diff_cancel nat_dvd_not_less neq0_conv by auto  
  then have "p dvd (p^n choose k)" 
    using mult.commute prime_imp_prime_elem prime_power_dvd_multD assms dvd_result by metis
  thus "?thesis" by simp 
qed

text \<open> Applying the above lemma to the coefficients of $(1 + X)^p$, it is easy to show that all 
coefficients other than the $0$th and $p$th will be $0$ \<close>

lemma fps_middle_coeffs:
  assumes "prime p"
          "n \<noteq> 0 \<and> n \<noteq> p"
  shows "((1 + fps_X :: int fps) ^p) $ n mod p = 0 mod p"
proof -
  let ?f = "(1 + fps_X :: int fps)^p"
  have "\<forall> n. n > 0 \<and> n < p \<longrightarrow> (p choose n) mod p = 0" using pn_choose_k_modp_0
    by (metis (no_types, lifting) add_le_imp_le_diff assms(1) diff_diff_cancel diff_is_0_eq' 
        discrete le_add_diff_inverse le_numeral_extra(4) power_one_right zero_le_one zero_less_one)
  then have middle_0: "\<forall> n. n > 0 \<and> n < p \<longrightarrow> (?f $ n) mod p = 0" 
    using binomial_coeffs_induct by (metis of_nat_0 zmod_int) 
  have "\<forall> n. n > p \<longrightarrow> ?f $ n mod p = 0" 
    using binomial_eq_0_iff binomial_coeffs_induct mod_0 by (metis of_nat_eq_0_iff) 
  thus ?thesis using middle_0 assms(2) nat_neq_iff by auto
qed

text \<open>It follows that $(1+ X)^p$ is equivalent to $(1 + X^p)$ under our equivalence relation, 
as required to prove the freshmans dream lemma. \<close>

lemma fps_freshmans_dream:
  assumes "prime p"
  shows "(((1 + fps_X :: int fps ) ^p), (1 + (fps_X)^(p))) \<in> fpsmodrel p"
proof -
  let ?f = "(1 + fps_X :: int fps)^p"
  let ?g = "(1 + (fps_X :: int fps)^p)"
  have all_f_coeffs: "\<forall> n. n \<noteq> 0 \<and> n \<noteq> p \<longrightarrow> ?f $ n mod p = 0 mod p" 
    using fps_middle_coeffs assms by blast 
  have "?g $ 0 = 1" using assms by auto 
  then have "?g $ 0 mod p = 1 mod p" 
    using int_ops(2) zmod_int assms by presburger 
  then have "?g $ p mod p = 1 mod p" using assms by auto 
  then have "\<forall> n . ?f $ n mod p = ?g $ n mod p" 
    using all_f_coeffs by (simp add: binomial_coeffs_induct)
  thus ?thesis using fpsrel_iff by blast
qed

section \<open>Lucas's Theorem Proof\<close>

text \<open>A formalisation of Lucas's theorem based on a generating function proof using the existing formal power series (FPS) Isabelle library\<close>

subsection \<open>Reasoning about Coefficients Helpers\<close>

text \<open>A generating function proof of Lucas's theorem relies on direct comparison between coefficients of FPS which requires a number 
of helper lemmas to prove formally. In particular it compares the coefficients of 
$(1 + X)^n \mod p$ to $(1 + X^p)^N * (1 + X) ^rn \mod p$, where $N = n / p$, and $rn = n \mod p$.
This section proves that the $k$th coefficient of $(1 + X^p)^N * (1 + X) ^rn = (N choose K) * (rn choose rk)$\<close>

text \<open>Applying the @{term "fps_compose"} operator enables reasoning about the coefficients of $(1 + X^p)^n$ 
using the existing binomial theorem proof with $X^p$ instead of $X$.\<close>

lemma fps_binomial_p_compose: 
  assumes "p \<noteq> 0" 
  shows "(1 + (fps_X:: ('a :: {idom} fps))^p)^n = ((1 + fps_X)^n) oo (fps_X^p)"
proof -
  have "(1::'a fps) + fps_X ^ p = 1 + fps_X oo fps_X ^ p"
    by (simp add: assms fps_compose_add_distrib)
  then show ?thesis
    by (simp add: assms fps_compose_power)
qed

text \<open> Next the proof determines the value of the $k$th coefficient of $(1 + X^p)^N$. \<close> 

lemma fps_X_pow_binomial_coeffs: 
  assumes "prime p"
  shows "(1 + (fps_X ::int fps)^p)^N $k = (if p dvd k then (N choose (k div p)) else 0)"
proof -
  let ?fx = "(fps_X :: int fps)"
  have "(1 + ?fx^p)^N $ k  = (((1 + ?fx)^N) oo (?fx^p)) $k"
    by (metis assms fps_binomial_p_compose not_prime_0)
  also have "... = (\<Sum>i=0..k.((1 + ?fx)^N)$i * ((?fx^p)^i$k))"
    by (simp add: fps_compose_nth) 
  finally have coeffs: "(1 + ?fx^p)^N $ k = (\<Sum>i=0..k. (N choose i) * ((?fx^(p*i))$k))"
    using binomial_coeffs_induct sum.cong by (metis (no_types, lifting) power_mult) 
  thus ?thesis 
  proof (cases "p dvd k")
    case False \<comment> \<open>$p$ does not divide $k$ implies the $k$th term has a coefficient of 0\<close> 
    have "\<forall> i. \<not>(p dvd k) \<longrightarrow> (?fx^(p*i)) $ k = 0"
      by auto 
    thus ?thesis using coeffs by (simp add: False) 
  next
    case True \<comment> \<open>$p$ divides $k$ implies the $k$th term has a non-zero coefficient\<close>
    have contained: "k div p \<in> {0.. k}" by simp
    have "\<forall> i. i \<noteq> k div p \<longrightarrow> (?fx^(p*i)) $ k = 0" using assms by auto
    then have notdivpis0: "\<forall> i \<in> ({0 .. k} - {k div p}). (?fx^(p*i)) $ k = 0" by simp
    have "(1 + ?fx^p)^N $ k = (N choose (k div p)) * (?fx^(p * (k div p))) $ k + (\<Sum>i\<in>({0..k} -{k div p}). (N choose i) * ((?fx^(p*i))$k))"
      using contained coeffs sum.remove by (metis (no_types, lifting) finite_atLeastAtMost)
    thus ?thesis using notdivpis0 True by simp 
  qed
qed

text \<open> The final helper lemma proves the $k$th coefficient is equivalent to $\binom{?N}{?K}*\binom{?rn}{?rk}$ as required.\<close>
lemma fps_div_rep_coeffs: 
  assumes "prime p"
  shows "((1 + (fps_X::int fps)^p)^(n div p) * (1 + fps_X)^(n mod p)) $ k = 
          ((n div p) choose (k div p)) * ((n mod p) choose (k mod p))"
    (is "((1 + (fps_X::int fps)^p)^?N * (1 + fps_X)^?rn) $ k = (?N choose ?K) * (?rn choose ?rk)")
proof -
  \<comment> \<open>Initial facts with results around representation and 0 valued terms\<close>
  let ?fx = "fps_X :: int fps"
  have krep: "k - ?rk = ?K*p"
    by (simp add: minus_mod_eq_mult_div)
  have rk_in_range: "?rk \<in> {0..k}" by simp
  have "\<forall> i \<ge> p. (?rn choose i) = 0" 
    using binomial_eq_0_iff 
    by (metis assms(1) leD le_less_trans linorder_cases mod_le_divisor mod_less_divisor prime_gt_0_nat)
  then have ptok0: "\<forall> i \<in> {p..k}. ((?rn choose i) * (1 + ?fx^p)^?N $ (k - i)) = 0" 
    by simp
  then have notrkis0: "\<forall>i \<in> {0.. k}. i \<noteq> ?rk \<longrightarrow> (?rn choose i) * (1 + ?fx^p)^?N $ (k - i) = 0" 
  proof (cases "k < p")
    case True \<comment> \<open>When $k < p$, it presents a side case with regards to range of reasoning\<close>
    then have k_value: "k = ?rk" by simp
    then have "\<forall> i < k. \<not> (p dvd (k - i))" 
       using True by (metis diff_diff_cancel diff_is_0_eq dvd_imp_mod_0 less_imp_diff_less less_irrefl_nat mod_less)
    then show ?thesis using fps_X_pow_binomial_coeffs assms(1) k_value by simp
  next
    case False
    then have "\<forall> i < p. i \<noteq> ?rk \<longrightarrow> \<not>(p dvd (k - i))"
      using mod_nat_eqI by auto 
    then have "\<forall> i \<in> {0..<p}. i \<noteq> ?rk \<longrightarrow> (1 + ?fx^p)^?N $ (k - i) = 0" 
      using assms fps_X_pow_binomial_coeffs by simp
    then show ?thesis using ptok0 by auto 
  qed
  \<comment> \<open>Main body of the proof, using helper facts above\<close>
  have "((1 + fps_X^p)^?N * (1 + fps_X)^?rn) $ k = (((1 + fps_X)^?rn) * (1 + fps_X^p)^?N) $ k"
    by (metis (no_types, hide_lams) distrib_left distrib_right fps_mult_fps_X_commute fps_one_mult(1) 
        fps_one_mult(2) power_commuting_commutes)
  also have "... = (\<Sum>i=0..k.(of_nat(?rn choose i)) * ((1 + (fps_X)^p)^?N $ (k - i)))" 
    by (simp add: fps_mult_nth binomial_coeffs_induct) 
  also have "... =  ((?rn choose ?rk) * (1 + ?fx^p)^?N $ (k - ?rk)) + (\<Sum>i\<in>({0..k} - {?rk}). (?rn choose i) * (1 + ?fx^p)^?N $ (k - i))" 
    using rk_in_range sum.remove by (metis (no_types, lifting) finite_atLeastAtMost)
  finally have "((1 + ?fx^p)^?N * (1 + ?fx)^?rn) $ k = ((?rn choose ?rk) * (1 + ?fx^p)^?N $ (k - ?rk))" 
    using notrkis0 by simp
  thus ?thesis using fps_X_pow_binomial_coeffs assms krep by auto 
qed

(* Lucas theorem proof *) 
subsection \<open>Lucas Theorem Proof\<close>

text \<open> The proof of Lucas's theorem combines a generating function approach, based off \cite{Fine} with induction.
For formalisation purposes, it was easier to first prove a well known corollary of the main theorem (also 
often presented as an alternative statement for Lucas's theorem), which can itself be used to backwards 
prove the the original statement by induction.
This approach was adapted from P. Cameron's lecture notes on combinatorics \cite{petercameronNotesCombinatorics2007} \<close>

subsubsection \<open> Proof of the Corollary \<close>
text \<open> This step makes use of the coefficient equivalence arguments proved in the previous sections \<close>
corollary lucas_corollary: 
  fixes n k :: nat
  assumes "prime p" 
  shows "(n choose k) mod p = (((n div p) choose (k div p)) * ((n mod p) choose (k mod p))) mod p" 
    (is "(n choose k) mod p = ((?N choose ?K) * (?rn choose ?rk)) mod p")
proof -
  let ?fx = "fps_X :: int fps"
  have n_rep: "n = ?N * p  + ?rn"
    by simp
  have k_rep: "k =?K * p + ?rk" by simp
  have rhs_coeffs: "((1 + ?fx^p)^(?N) * (1 + ?fx)^(?rn)) $ k = (?N choose ?K) * (?rn choose ?rk)" 
    using assms fps_div_rep_coeffs k_rep n_rep by blast \<comment> \<open>Application of coefficient reasoning\<close>
  have "((((1 + ?fx)^p)^(?N) * (1 + ?fx)^(?rn)), 
          ((1 + ?fx^p)^(?N) * (1 + ?fx)^(?rn))) \<in> fpsmodrel p"
    using fps_freshmans_dream assms fps_mult_equiv fps_power_equiv by blast \<comment> \<open>Application of equivalence facts and freshmans dream lemma\<close>
  then have modrel2: "((1 + ?fx)^n, ((1 + ?fx^p)^(?N) * (1 + ?fx)^(?rn))) 
                          \<in> fpsmodrel p"
    by (metis (mono_tags, hide_lams) mult_div_mod_eq power_add power_mult)
  thus ?thesis
    using fpsrel_iff binomial_coeffs_induct rhs_coeffs by (metis of_nat_eq_iff zmod_int) 
qed

subsubsection \<open> Proof of the Theorem \<close>

text \<open>The theorem statement requires a formalised way of referring to the base $p$ representation of a number. 
We use a definition that specifies the $i$th digit of the base $p$ representation. This definition is originally 
from the Hilbert's 10th Problem Formalisation project \cite{bayerDPRMTheoremIsabelle2019} which this work contributes to.\<close>
definition nth_digit_general :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nth_digit_general num i base = (num div (base ^ i)) mod base"

text \<open>Applying induction on $d$, where $d$ is the highest power required in either $n$ or $k$'s base $p$
representation, @{thm lucas_corollary} can be used to prove the original theorem.\<close>

theorem lucas_theorem:
  fixes n k d::nat
assumes "n < p ^ (Suc d)"
assumes "k < p ^ (Suc d)"
assumes "prime p"
shows "(n choose k) mod p = (\<Prod>i\<le>d. ((nth_digit_general n i p) choose (nth_digit_general k i p))) mod p"
  using assms
proof (induct d arbitrary: n k)
  case 0
  thus ?case using nth_digit_general_def assms by simp
next
  case (Suc d)
  \<comment> \<open>Representation Variables\<close>
  let ?N = "n div p"   
  let ?K = "k div p"
  let ?nr = "n mod p"
  let ?kr = "k mod p"
  \<comment> \<open>Required assumption facts\<close>
  have Mlessthan: "?N < p ^ (Suc d)" 
    using less_mult_imp_div_less power_Suc2 assms(3) prime_ge_2_nat Suc.prems(1) by metis 
  have Nlessthan: "?K < p ^ (Suc d)" 
    using less_mult_imp_div_less power_Suc2 prime_ge_2_nat Suc.prems(2) assms(3) by metis
  have shift_bounds_fact: "(\<Prod>i=(Suc 0)..(Suc (d )). ((nth_digit_general n i p) choose (nth_digit_general k i p))) = 
                            (\<Prod>i=0..(d).  (nth_digit_general n (Suc i) p) choose (nth_digit_general k (Suc i) p))"
    using prod.shift_bounds_cl_Suc_ivl by blast \<comment> \<open>Product manipulation helper fact\<close>
  have "(n choose k ) mod p = ((?N choose ?K) * (?nr choose ?kr)) mod p" 
    using lucas_corollary assms(3) by blast \<comment> \<open>Application of corollary\<close>
  also have "...= ((\<Prod>i\<le>d. ((nth_digit_general ?N i p) choose (nth_digit_general ?K i p))) * (?nr choose ?kr)) mod p"
    using Mlessthan Nlessthan Suc.hyps mod_mult_cong assms(3) by blast \<comment> \<open>Using Inductive Hypothesis\<close>
  \<comment> \<open>Product manipulation steps\<close>
  also have "... = ((\<Prod>i=0..(d). (nth_digit_general n (Suc i) p) choose (nth_digit_general k (Suc i) p)) * (?nr choose ?kr)) mod p"
    using  atMost_atLeast0 nth_digit_general_def div_mult2_eq by auto
  also have "... = ((\<Prod>i=1..(d+1). (nth_digit_general n i p) choose (nth_digit_general k i p)) * 
                            ((nth_digit_general n 0 p) choose (nth_digit_general k 0 p))) mod p" 
    using nth_digit_general_def shift_bounds_fact by simp
  finally have "(n choose k ) mod p = ((\<Prod>i=0..(d+1). (nth_digit_general n i p) choose (nth_digit_general k i p))) mod p" 
    using One_nat_def atMost_atLeast0 mult.commute prod.atLeast1_atMost_eq prod.atMost_shift
    by (smt Suc_eq_plus1 shift_bounds_fact)
  thus ?case
    using Suc_eq_plus1 atMost_atLeast0 by presburger
qed

end