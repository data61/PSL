(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-nantes.fr
    License: BSD
*)

section \<open>A theorem by Kohlberg and Neyman\<close>

theory Kohlberg_Neyman_Karlsson
  imports Fekete
begin

text \<open>In this section, we prove a theorem due to Kohlberg and Neyman: given a semicontraction
$T$ of a euclidean space, then $T^n(0)/n$ converges when $n \to \infty$. The proof we give
is due to Karlsson. It mainly builds on subadditivity ideas. The geometry of the space
is essentially not relevant except at the very end of the argument, where strict convexity
comes into play.\<close>

text \<open>We recall Fekete's lemma: if a sequence is subadditive (i.e.,
$u_{n+m}\leq u_n + u_m$), then $u_n/n$ converges to its infimum. It is proved
in a different file, but we recall the statement for self-containedness.\<close>

lemma fekete:
  fixes u::"nat \<Rightarrow> real"
  assumes "\<And>n m. u (m+n) \<le> u m + u n"
          "bdd_below {u n/n | n. n>0}"
  shows "(\<lambda>n. u n/n) \<longlonglongrightarrow> Inf {u n/n | n. n>0}"
apply (rule subadditive_converges_bounded) unfolding subadditive_def using assms by auto

text \<open>A real sequence tending to infinity has infinitely many high-scores, i.e.,
there are infinitely many times where it is larger than all its previous values.\<close>

lemma high_scores:
  fixes u::"nat \<Rightarrow> real" and i::nat
  assumes "u \<longlonglongrightarrow> \<infinity>"
  shows "\<exists>n \<ge> i. \<forall>l \<le> n. u l \<le> u n"
proof -
  define M where "M = Max {u l|l. l < i}"
  define n where "n = Inf {m. u m > M}"
  have "eventually (\<lambda>m. u m > M) sequentially"
    using assms by (simp add: filterlim_at_top_dense tendsto_PInfty_eq_at_top)
  then have "{m. u m > M} \<noteq> {}" by fastforce
  then have "n \<in> {m. u m > M}" unfolding n_def using Inf_nat_def1 by metis
  then have "u n > M" by simp
  have "n \<ge> i"
  proof (rule ccontr)
    assume " \<not> i \<le> n"
    then have *: "n < i" by simp
    have "u n \<le> M" unfolding M_def apply (rule Max_ge) using * by auto
    then show False using \<open>u n > M\<close> by auto
  qed
  moreover have "u l \<le> u n" if "l \<le> n" for l
  proof (cases "l = n")
    case True
    then show ?thesis by simp
  next
    case False
    then have "l < n" using \<open>l \<le> n\<close> by auto
    then have "l \<notin> {m. u m > M}"
      unfolding n_def by (meson bdd_below_def cInf_lower not_le zero_le)
    then show ?thesis using \<open>u n > M\<close> by auto
  qed
  ultimately show ?thesis by auto
qed

text \<open>Hahn-Banach in euclidean spaces: given a vector $u$, there exists a unit norm
vector $v$ such that $\langle u, v \rangle = \|u\|$ (and we put a minus sign as we will
use it in this form). This uses the fact that, in Isabelle/HOL, euclidean spaces
have positive dimension by definition.\<close>

lemma select_unit_norm:
  fixes u::"'a::euclidean_space"
  shows "\<exists>v. norm v = 1 \<and> v \<bullet> u = - norm u"
proof (cases "u = 0")
  case True
  then show ?thesis using norm_Basis nonempty_Basis by fastforce
next
  case False
  show ?thesis
    apply (rule exI[of _ "-u/\<^sub>R norm u"])
    using False by (auto simp add: dot_square_norm power2_eq_square)
qed

text \<open>We set up the assumption that we will use until the end of this file,
in the following locale: we fix a semicontraction $T$ of a euclidean space.
Our goal will be to show that such a semicontraction has an asymptotic translation vector.\<close>

locale Kohlberg_Neyman_Karlsson =
  fixes T::"'a::euclidean_space \<Rightarrow> 'a"
  assumes semicontract: "dist (T x) (T y) \<le> dist x y"
begin

text \<open>The iterates of $T$ are still semicontractions, by induction.\<close>

lemma semicontract_Tn:
  "dist ((T^^n) x) ((T^^n) y) \<le> dist x y"
apply (induction n, auto) using semicontract order_trans by blast

text \<open>The main quantity we will use is the distance from the origin to its image under $T^n$.
We denote it by $u_n$. The main point is that it is subadditive by semicontraction, hence
it converges to a limit $A$ given by $Inf \{u_n/n\}$, thanks to Fekete Lemma.\<close>

definition u::"nat \<Rightarrow> real"
  where "u n = dist 0 ((T^^n) 0)"

definition A::real
  where "A = Inf {u n/n | n. n>0}"

lemma Apos: "A \<ge> 0"
unfolding A_def u_def by (rule cInf_greatest, auto)

lemma Alim:"(\<lambda>n. u n/n) \<longlonglongrightarrow> A"
unfolding A_def proof (rule fekete)
  show "bdd_below {u n / real n |n. 0 < n}"
    unfolding u_def bdd_below_def by (rule exI[of _ 0], auto)

  fix m n
  have "u (m+n) = dist 0 ((T^^(m+n)) 0)"
    unfolding u_def by simp
  also have "... \<le> dist 0 ((T^^m) 0) + dist ((T^^m) 0) ((T^^(m+n)) 0)"
    by (rule dist_triangle)
  also have "... = dist 0 ((T^^m) 0) + dist ((T^^m) 0) ((T^^m) ((T^^n) 0))"
    by (auto simp add: funpow_add)
  also have "... \<le> dist 0 ((T^^m) 0) + dist 0 ((T^^n) 0)"
    using semicontract_Tn[of m] add_mono_thms_linordered_semiring(2) by blast
  also have "... = u m + u n"
    unfolding u_def by auto
  finally show "u (m+n) \<le> u m + u n" by auto
qed

text \<open>The main fact to prove the existence of an asymptotic translation vector for $T$
is the following proposition: there exists a unit norm vector $v$ such that $T^\ell(0)$ is in
the half-space at distance $A \ell$ of the origin directed by $v$.

The idea of the proof is to find such a vector $v_i$ that works (with a small error $\epsilon_i > 0$)
for times up to a time $n_i$, and then take a limit by compactness (or weak compactness, but
since we are in finite dimension, compactness works fine). Times $n_i$ are chosen to be large
high scores of the sequence $u_n - (A-\epsilon_i) n$, which tends to infinity since $u_n/n$
tends to $A$.\<close>

proposition half_space:
  "\<exists>v. norm v = 1 \<and> (\<forall>l. v \<bullet> (T ^^ l) 0 \<le> - A * l)"
proof -
  define eps::"nat \<Rightarrow> real" where "eps = (\<lambda>i. 1/of_nat (i+1))"
  have "eps i > 0" for i unfolding eps_def by auto
  have "eps \<longlonglongrightarrow> 0"
    unfolding eps_def using LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1] by simp
  have vi: "\<exists>vi. norm vi = 1 \<and> (\<forall>l \<le> i. vi \<bullet> (T ^^ l) 0 \<le> (- A + eps i) * l)" for i
  proof -
    have L: "(\<lambda>n. ereal(u n - (A - eps i) * n)) \<longlonglongrightarrow> \<infinity>"
    proof -
      have "ereal ((u n/n - A) + eps i) * ereal n = ereal(u n - (A - eps i) * n)" if "n \<ge> 1" for n
        using that by (auto simp add: divide_simps algebra_simps)
      then have *: "eventually (\<lambda>n. ereal ((u n/n - A) + eps i) * ereal n = ereal(u n - (A - eps i) * n)) sequentially"
        unfolding eventually_sequentially by auto

      have "(\<lambda>n. (ereal ((u n/n - A) + eps i)) * ereal n) \<longlonglongrightarrow> (0 + eps i) * \<infinity>"
        apply (intro tendsto_intros)
        using \<open>eps i > 0\<close> Alim by (auto simp add: LIM_zero)
      then show ?thesis using Lim_transform_eventually[OF *] \<open>eps i > 0\<close> by simp
    qed
    obtain n where n: "n \<ge> i" "\<And>l. l \<le> n \<Longrightarrow> u l - (A - eps i) * l \<le> u n - (A - eps i) * n"
      using high_scores[OF L, of i] by auto
    obtain vi where vi: "norm vi = 1" "vi \<bullet> ((T^^n) 0) = - norm ((T^^n) 0)"
      using select_unit_norm by auto
    have "vi \<bullet> (T ^^ l) 0 \<le> (- A + eps i) * l" if "l \<le> i" for l
    proof -
      have *: "n = l + (n-l)" using that \<open>n \<ge> i\<close> by auto
      have **: "real (n-l) = real n - real l" using that \<open>n \<ge> i\<close> by auto
      have "vi \<bullet> (T ^^ l) 0 = vi \<bullet> ((T ^^ l) 0 - (T^^n) 0) + vi \<bullet> ((T^^n) 0)"
        by (simp add: inner_diff_right)
      also have "... \<le> norm vi * norm (((T ^^ l) 0 - (T^^n) 0)) + vi \<bullet> ((T^^n) 0)"
        by (simp add: norm_cauchy_schwarz)
      also have "... = dist ((T^^l)(0)) ((T^^n) 0) - norm ((T^^n) 0)"
        using vi by (auto simp add: dist_norm)
      also have "... = dist ((T^^l)(0)) ((T^^l) ((T^^(n-l)) 0)) - norm ((T^^n) 0)"
        by (metis * funpow_add o_apply)
      also have "... \<le> dist 0 ((T^^(n-l)) 0) - norm ((T^^n) 0)"
        using semicontract_Tn[of l 0 "(T^^(n-l)) 0"] by auto
      also have "... = u (n-l) - u n"
        unfolding u_def by auto
      also have "... \<le> - (A - eps i) * l"
        using n(2)[of "n-l"] unfolding ** by (auto simp add: algebra_simps)
      finally show ?thesis by auto
    qed
    then show ?thesis using vi(1) by auto
  qed
  have "\<exists>V::(nat \<Rightarrow> 'a). \<forall>i. norm (V i) = 1 \<and> (\<forall>l\<le>i. V i \<bullet> (T ^^ l) 0 \<le> (- A + eps i) * l)"
    apply (rule choice) using vi by auto
  then obtain V::"nat \<Rightarrow> 'a" where V: "\<And>i. norm (V i) = 1" "\<And>l i. l \<le> i \<Longrightarrow> V i \<bullet> (T ^^ l) 0 \<le> (- A + eps i) * l"
    by auto

  have "compact (sphere (0::'a) 1)" by simp
  moreover have "V i \<in> sphere 0 1" for i using V(1) by auto
  ultimately have "\<exists>v \<in> sphere 0 1. \<exists>r. strict_mono r \<and> (V o r) \<longlonglongrightarrow> v"
    using compact_eq_seq_compact_metric seq_compact_def by metis
  then obtain v r where v: "v \<in> sphere 0 1" "strict_mono r" "(V o r) \<longlonglongrightarrow> v"
    by auto
  have "v \<bullet> (T ^^ l) 0 \<le> - A * l" for l
  proof -
    have *: "(\<lambda>i. (-A + eps (r i)) * l - V (r i) \<bullet> (T ^^ l) 0) \<longlonglongrightarrow> (-A + 0) * l - v \<bullet> (T ^^ l) 0"
      apply (intro tendsto_intros)
      using \<open>(V o r) \<longlonglongrightarrow> v\<close> \<open>eps \<longlonglongrightarrow> 0\<close> \<open>strict_mono r\<close> LIMSEQ_subseq_LIMSEQ unfolding comp_def by auto
    have "eventually (\<lambda>i. (-A + eps (r i)) * l - V (r i) \<bullet> (T ^^ l) 0 \<ge> 0) sequentially"
      unfolding eventually_sequentially apply (rule exI[of _ l])
      using V(2)[of l] seq_suble[OF \<open>strict_mono r\<close>] apply auto using le_trans by blast
    then have " (-A + 0) * l - v \<bullet> (T ^^ l) 0 \<ge> 0"
      using LIMSEQ_le_const[OF *, of 0] unfolding eventually_sequentially by auto
    then show ?thesis by auto
  qed
  then show ?thesis using \<open>v \<in> sphere 0 1\<close> by auto
qed

text \<open>We can now show the existence of an asymptotic translation vector for $T$. It is the vector
$-v$ of the previous proposition: the point $T^\ell(0)$ is in the half-space
at distance $A \ell$ of the origin directed by $v$, and has norm $\sim A \ell$, hence it has
to be essentially $-A v$ by strict convexity of the euclidean norm.\<close>

theorem KNK_thm:
  "convergent (\<lambda>n. ((T^^n) 0) /\<^sub>R n)"
proof -
  obtain v where v: "norm v = 1" "\<And>l. v \<bullet> (T ^^ l) 0 \<le> - A * l"
    using half_space by auto
  have "(\<lambda>n. norm(((T^^n) 0) /\<^sub>R n + A *\<^sub>R v)^2) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. (norm((T^^n) 0) /\<^sub>R n)^2 - A^2"])
    have "norm(((T^^n) 0) /\<^sub>R n + A *\<^sub>R v)^2 \<le> (norm((T^^n) 0) /\<^sub>R n)^2 - A^2" if "n \<ge> 1" for n
    proof -
      have "norm(((T^^n) 0) /\<^sub>R n + A *\<^sub>R v)^2 = norm(((T^^n) 0) /\<^sub>R n)^2 + A * A * (norm v)^2 + 2 * A * inverse n * (v \<bullet> (T^^n) 0)"
        unfolding power2_norm_eq_inner by (auto simp add: inner_commute algebra_simps)
      also have "... \<le> norm(((T^^n) 0) /\<^sub>R n)^2 + A * A * (norm v)^2 + 2 * A * inverse n * (-A * n)"
        using mult_left_mono[OF v(2)[of n] Apos] \<open>n \<ge> 1\<close> by (auto, auto simp add: divide_simps)
      also have "... = norm(((T^^n) 0) /\<^sub>R n)^2 - A * A"
        using \<open>n \<ge> 1\<close> v(1) by auto
      finally show ?thesis by (simp add: power2_eq_square)
    qed
    then show "eventually (\<lambda>n. norm ((T ^^ n) 0 /\<^sub>R real n + A *\<^sub>R v)^2 \<le> (norm ((T ^^ n) 0) /\<^sub>R real n)\<^sup>2 - A^2) sequentially"
      unfolding eventually_sequentially by auto
    have "(\<lambda>n. (norm ((T ^^ n) 0) /\<^sub>R real n)^2) \<longlonglongrightarrow> A\<^sup>2"
      apply (intro tendsto_intros)
      using Alim unfolding u_def by (auto simp add: divide_simps)
    then show "(\<lambda>n. (norm ((T ^^ n) 0) /\<^sub>R real n)\<^sup>2 - A\<^sup>2) \<longlonglongrightarrow> 0"
      by (simp add: LIM_zero)
  qed (auto)
  then have "(\<lambda>n. sqrt((norm(((T^^n) 0) /\<^sub>R n + A *\<^sub>R v))^2)) \<longlonglongrightarrow> sqrt 0"
    by (intro tendsto_intros)
  then have "(\<lambda>n. norm((((T^^n) 0) /\<^sub>R n) - (- A *\<^sub>R v))) \<longlonglongrightarrow> 0"
    by auto
  then have "(\<lambda>n. ((T^^n) 0) /\<^sub>R n) \<longlonglongrightarrow> - A *\<^sub>R v"
    using Lim_null tendsto_norm_zero_iff by blast
  then show "convergent (\<lambda>n. ((T^^n) 0) /\<^sub>R n)"
    unfolding convergent_def by auto
qed

end

end (*of Kolberg_Neyman_Karlsson.thy*)



