(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Asymptotic densities\<close>

theory Asymptotic_Density
  imports SG_Library_Complement
begin

text \<open>The upper asymptotic density of a subset $A$ of the integers is
$\limsup Card(A \cap [0,n)) / n \in [0,1]$. It measures how big a set of integers is,
at some times. In this paragraph, we establish the basic properties of this notion.

There is a corresponding notion of lower asymptotic density, with a liminf instead
of a limsup, measuring how big a set is at all times. The corresponding properties
are proved exactly in the same way.
\<close>

subsection \<open>Upper asymptotic densities\<close>

text \<open>As limsups are only defined for sequences taking values in a complete lattice
(here the extended reals), we define it in the extended reals and then go back to the reals.
This is a little bit artificial, but it is not a real problem as in the applications we
will never come back to this definition.\<close>

definition upper_asymptotic_density::"nat set \<Rightarrow> real"
  where "upper_asymptotic_density A = real_of_ereal(limsup (\<lambda>n. card(A \<inter> {..<n})/n))"

text \<open>First basic property: the asymptotic density is between $0$ and $1$.\<close>

lemma upper_asymptotic_density_in_01:
  "ereal(upper_asymptotic_density A) = limsup (\<lambda>n. card(A \<inter> {..<n})/n)"
  "upper_asymptotic_density A \<le> 1"
  "upper_asymptotic_density A \<ge> 0"
proof -
  {
    fix n::nat assume "n>0"
    have "card(A \<inter> {..<n}) \<le> n" by (metis card_lessThan Int_lower2 card_mono finite_lessThan)
    then have "card(A \<inter> {..<n}) / n \<le> ereal 1" using \<open>n>0\<close> by auto
  }
  then have "eventually (\<lambda>n. card(A \<inter> {..<n}) / n \<le> ereal 1) sequentially"
    by (simp add: eventually_at_top_dense)
  then have a: "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1" by (simp add: Limsup_const Limsup_bounded)

  have "card(A \<inter> {..<n}) / n \<ge> ereal 0" for n by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (simp add: le_Liminf_iff less_le_trans)
  then have b: "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (meson Liminf_le_Limsup order_trans sequentially_bot)

  have "abs(limsup (\<lambda>n. card(A \<inter> {..<n})/n)) \<noteq> \<infinity>" using a b by auto
  then show "ereal(upper_asymptotic_density A) = limsup (\<lambda>n. card(A \<inter> {..<n})/n)"
    unfolding upper_asymptotic_density_def by auto
  show "upper_asymptotic_density A \<le> 1" "upper_asymptotic_density A \<ge> 0" unfolding upper_asymptotic_density_def
    using a b by (auto simp add: real_of_ereal_le_1 real_of_ereal_pos)
qed

text \<open>The two next propositions give the usable characterization of the asymptotic density, in
terms of the eventual cardinality of $A \cap [0, n)$. Note that the inequality is strict for one
implication and large for the other.\<close>

proposition upper_asymptotic_densityD:
  fixes l::real
  assumes "upper_asymptotic_density A < l"
  shows "eventually (\<lambda>n. card(A \<inter> {..<n}) < l * n) sequentially"
proof -
  have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) < l"
    using assms upper_asymptotic_density_in_01(1) ereal_less_ereal_Ex by auto
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n < ereal l) sequentially"
    using Limsup_lessD by blast
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n < ereal l \<and> n > 0) sequentially"
    using eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n}) < l * n" if "card(A \<inter> {..<n})/n < ereal l \<and> n > 0" for n
    using that by (simp add: divide_less_eq)
  ultimately show "eventually (\<lambda>n. card(A \<inter> {..<n}) < l * n) sequentially"
    by (simp add: eventually_mono)
qed

proposition upper_asymptotic_densityI:
  fixes l::real
  assumes "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n) sequentially"
  shows "upper_asymptotic_density A \<le> l"
proof -
  have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n \<and> n > 0) sequentially"
    using assms eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n})/n \<le> ereal l" if "card(A \<inter> {..<n}) \<le> l * n \<and> n > 0" for n
    using that by (simp add: divide_le_eq)
  ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<le> ereal l) sequentially"
    by (simp add: eventually_mono)
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> ereal l"
    by (simp add: Limsup_bounded)
  then have "ereal(upper_asymptotic_density A) \<le> ereal l"
    using upper_asymptotic_density_in_01(1) by auto
  then show ?thesis by (simp del: upper_asymptotic_density_in_01)
qed

text \<open>The following trivial lemma is useful to control the asymptotic density of unions.\<close>

lemma lem_ge_sum:
  fixes l x y::real
  assumes "l>x+y"
  shows "\<exists>lx ly. l = lx + ly \<and> lx > x \<and> ly > y"
proof -
  define lx ly where "lx = x + (l-(x+y))/2" and "ly = y + (l-(x+y))/2"
  have "l = lx + ly \<and> lx > x \<and> ly > y" unfolding lx_def ly_def using assms by auto
  then show ?thesis by auto
qed

text \<open>The asymptotic density of a union is bounded by the sum of the asymptotic densities.\<close>

lemma upper_asymptotic_density_union:
  "upper_asymptotic_density (A \<union> B) \<le> upper_asymptotic_density A + upper_asymptotic_density B"
proof -
  have "upper_asymptotic_density (A \<union> B) \<le> l" if H: "l > upper_asymptotic_density A + upper_asymptotic_density B" for l
  proof -
    obtain lA lB where l: "l = lA+lB" and lA: "lA > upper_asymptotic_density A" and lB: "lB > upper_asymptotic_density B"
      using lem_ge_sum H by blast
    {
      fix n assume H: "card (A \<inter> {..<n}) < lA * n \<and> card (B \<inter> {..<n}) < lB * n"
      have "card((A\<union>B) \<inter> {..<n}) \<le> card(A \<inter> {..<n}) + card(B \<inter> {..<n})"
        by (simp add: card_Un_le inf_sup_distrib2)
      also have "... \<le> l * n" using l H by (simp add: ring_class.ring_distribs(2))
      finally have "card ((A\<union>B) \<inter> {..<n}) \<le> l * n" by simp
    }
    moreover have "eventually (\<lambda>n. card (A \<inter> {..<n}) < lA * n \<and> card (B \<inter> {..<n}) < lB * n) sequentially"
      using upper_asymptotic_densityD[OF lA] upper_asymptotic_densityD[OF lB] eventually_conj by blast
    ultimately have "eventually (\<lambda>n. card((A\<union>B) \<inter> {..<n}) \<le> l * n) sequentially"
      by (simp add: eventually_mono)
    then show "upper_asymptotic_density (A \<union> B) \<le> l" using upper_asymptotic_densityI by auto
  qed
  then show ?thesis by (meson dense not_le)
qed

text \<open>It follows that the asymptotic density is an increasing function for inclusion.\<close>

lemma upper_asymptotic_density_subset:
  assumes "A \<subseteq> B"
  shows "upper_asymptotic_density A \<le> upper_asymptotic_density B"
proof -
  have "upper_asymptotic_density A \<le> l" if l: "l > upper_asymptotic_density B" for l
  proof -
    have "card(A \<inter> {..<n}) \<le> card(B \<inter> {..<n})" for n
      using assms by (metis Int_lower2 Int_mono card_mono finite_lessThan finite_subset inf.left_idem)
    then have "card(A \<inter> {..<n}) \<le> l * n" if "card(B \<inter> {..<n}) < l * n" for n
      using that by (meson lessThan_def less_imp_le of_nat_le_iff order_trans)
    moreover have "eventually (\<lambda>n. card(B \<inter> {..<n}) < l * n) sequentially"
      using upper_asymptotic_densityD l by simp
    ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<le> l * n) sequentially"
      by (simp add: eventually_mono)
    then show ?thesis using upper_asymptotic_densityI by auto
  qed
  then show ?thesis by (meson dense not_le)
qed

text \<open>If a set has a density, then it is also its asymptotic density.\<close>

lemma upper_asymptotic_density_lim:
  assumes "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> l"
  shows "upper_asymptotic_density A = l"
proof -
  have "(\<lambda>n. ereal(card(A \<inter> {..<n})/n)) \<longlonglongrightarrow> l" using assms by auto
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) = l"
    using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  then show ?thesis unfolding upper_asymptotic_density_def by auto
qed

text \<open>If two sets are equal up to something small, i.e. a set with zero upper density,
then they have the same upper density.\<close>

lemma upper_asymptotic_density_0_diff:
  assumes "A \<subseteq> B" "upper_asymptotic_density (B-A) = 0"
  shows "upper_asymptotic_density A = upper_asymptotic_density B"
proof -
  have "upper_asymptotic_density B \<le> upper_asymptotic_density A + upper_asymptotic_density (B-A)"
    using upper_asymptotic_density_union[of A "B-A"] by (simp add: assms(1) sup.absorb2)
  then have "upper_asymptotic_density B \<le> upper_asymptotic_density A"
    using assms(2) by simp
  then show ?thesis using upper_asymptotic_density_subset[OF assms(1)] by simp
qed

lemma upper_asymptotic_density_0_Delta:
  assumes "upper_asymptotic_density (A \<Delta> B) = 0"
  shows "upper_asymptotic_density A = upper_asymptotic_density B"
proof -
  have "A- (A\<inter>B) \<subseteq> A \<Delta> B" "B- (A\<inter>B) \<subseteq> A \<Delta> B"
    using assms(1) by (auto simp add: Diff_Int Un_infinite)
  then have "upper_asymptotic_density (A - (A\<inter>B)) = 0"
            "upper_asymptotic_density (B - (A\<inter>B)) = 0"
    using upper_asymptotic_density_subset assms(1) upper_asymptotic_density_in_01(3)
    by (metis inf.absorb_iff2 inf.orderE)+
  then have "upper_asymptotic_density (A\<inter>B) = upper_asymptotic_density A"
            "upper_asymptotic_density (A\<inter>B) = upper_asymptotic_density B"
    using upper_asymptotic_density_0_diff by auto
  then show ?thesis by simp
qed

text \<open>Finite sets have vanishing upper asymptotic density.\<close>

lemma upper_asymptotic_density_finite:
  assumes "finite A"
  shows "upper_asymptotic_density A = 0"
proof -
  have "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[where ?f = "\<lambda>n. 0" and ?h = "\<lambda>(n::nat). card A / n"])
    have "card(A \<inter> {..<n})/n \<le> card A / n" if "n>0" for n
      using that \<open>finite A\<close> by (simp add: card_mono divide_right_mono)
    then show "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<le> card A / n) sequentially"
      by (simp add: eventually_at_top_dense)
    have "(\<lambda>n. real (card A)* (1 / real n)) \<longlonglongrightarrow> real(card A) * 0"
      by (intro tendsto_intros)
    then show "(\<lambda>n. real (card A) / real n) \<longlonglongrightarrow> 0" by auto
  qed (auto)
  then show "upper_asymptotic_density A = 0" using upper_asymptotic_density_lim by auto
qed

text \<open>In particular, bounded intervals have zero upper density.\<close>

lemma upper_asymptotic_density_bdd_interval [simp]:
  "upper_asymptotic_density {} = 0"
  "upper_asymptotic_density {..N} = 0"
  "upper_asymptotic_density {..<N} = 0"
  "upper_asymptotic_density {n..N} = 0"
  "upper_asymptotic_density {n..<N} = 0"
  "upper_asymptotic_density {n<..N} = 0"
  "upper_asymptotic_density {n<..<N} = 0"
by (auto intro!: upper_asymptotic_density_finite)

text \<open>The density of a finite union is bounded by the sum of the densities.\<close>

lemma upper_asymptotic_density_finite_Union:
  assumes "finite I"
  shows "upper_asymptotic_density (\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. upper_asymptotic_density (A i))"
using assms apply (induction I rule: finite_induct)
using order_trans[OF upper_asymptotic_density_union] by auto

text \<open>It is sometimes useful to compute the asymptotic density by shifting a little bit the set:
this only makes a finite difference that vanishes when divided by $n$.\<close>

lemma upper_asymptotic_density_shift:
  fixes k::nat and l::int
  shows "ereal(upper_asymptotic_density A) = limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n)"
proof -
  define C where "C = k+2*nat(abs(l))+1"
  have *: "(\<lambda>n. C*(1/n)) \<longlonglongrightarrow> real C * 0"
    by (intro tendsto_intros)
  have l0: "limsup (\<lambda>n. C/n) = 0"
    apply (rule lim_imp_Limsup, simp) using * by (simp add: zero_ereal_def)

  have "card(A \<inter> {k..nat(n+l)}) / n \<le> card (A \<inter> {..<n})/n + C/n" for n
  proof -
    have "card(A \<inter> {k..nat(n+l)}) \<le> card (A \<inter> {..<n} \<union> {n..n + nat(abs(l))})"
      by (rule card_mono, auto)
    also have "... \<le> card (A \<inter> {..<n}) + card {n..n + nat(abs(l))}"
      by (rule card_Un_le)
    also have "... \<le> card (A \<inter> {..<n}) + real C"
      unfolding C_def by auto
    finally have "card(A \<inter> {k..nat(n+l)}) / n \<le> (card (A \<inter> {..<n}) + real C) /n"
      by (simp add: divide_right_mono)
    also have "... = card (A \<inter> {..<n})/n + C/n"
      using add_divide_distrib by auto
    finally show ?thesis
      by auto
  qed
  then have "limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n + ereal(C/n))"
    by (simp add: Limsup_mono)
  also have "... \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n) + limsup (\<lambda>n. C/n)"
    by (rule ereal_limsup_add_mono)
  finally have a: "limsup (\<lambda>n. card(A \<inter> {k..nat(n+l)}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {..<n})/n)"
    using l0 by simp

  have "card (A \<inter> {..<n}) / n \<le> card (A \<inter> {k..nat(n+l)})/n + C/n" for n
  proof -
    have "card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}) \<le> card {..<k} + card {n-nat(abs(l))..n + nat(abs(l))}"
      by (rule card_Un_le)
    also have "... \<le> k + 2*nat(abs(l)) + 1" by auto
    finally have *: "card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}) \<le> C" unfolding C_def by blast

    have "card(A \<inter> {..<n}) \<le> card (A \<inter> {k..nat(n+l)} \<union> ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))}))"
      by (rule card_mono, auto)
    also have "... \<le> card (A \<inter> {k..nat(n+l)}) + card ({..<k} \<union> {n-nat(abs(l))..n + nat(abs(l))})"
      by (rule card_Un_le)
    also have "... \<le> card (A \<inter> {k..nat(n+l)}) + C"
      using * by auto
    finally have "card (A \<inter> {..<n}) / n \<le> (card (A \<inter> {k..nat(n+l)}) + real C)/n"
      by (simp add: divide_right_mono)
    also have "... = card (A \<inter> {k..nat(n+l)})/n + C/n"
      using add_divide_distrib by auto
    finally show ?thesis
      by auto
  qed
  then have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n + ereal(C/n))"
    by (simp add: Limsup_mono)
  also have "... \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n) + limsup (\<lambda>n. C/n)"
    by (rule ereal_limsup_add_mono)
  finally have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) \<le> limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n)"
    using l0 by simp
  then have "limsup (\<lambda>n. card(A \<inter> {..<n}) / n) = limsup (\<lambda>n. card (A \<inter> {k..nat(n+l)})/n)"
    using a by auto
  then show ?thesis using upper_asymptotic_density_in_01(1) by auto
qed

text \<open>Upper asymptotic density is measurable.\<close>

lemma upper_asymptotic_density_meas [measurable]:
  assumes [measurable]: "\<And>(n::nat). Measurable.pred M (P n)"
  shows "(\<lambda>x. upper_asymptotic_density {n. P n x}) \<in> borel_measurable M"
unfolding upper_asymptotic_density_def by auto

text \<open>A finite union of sets with zero upper density still has zero upper density.\<close>

lemma upper_asymptotic_density_zero_union:
  assumes "upper_asymptotic_density A = 0" "upper_asymptotic_density B = 0"
  shows "upper_asymptotic_density (A \<union> B) = 0"
using upper_asymptotic_density_in_01(3)[of "A \<union> B"] upper_asymptotic_density_union[of A B] unfolding assms by auto

lemma upper_asymptotic_density_zero_finite_Union:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> upper_asymptotic_density (A i) = 0"
  shows "upper_asymptotic_density (\<Union>i\<in>I. A i) = 0"
using assms by (induction rule: finite_induct, auto intro!: upper_asymptotic_density_zero_union)

text \<open>The union of sets with small asymptotic densities can have a large density: think
of $A_n = [0,n]$, it has density $0$, but the union of the $A_n$ has density $1$. However, if one
only wants a set which contains each $A_n$ eventually, then one can obtain a ``union'' that has
essentially the same density as each $A_n$. This is often used as a replacement for the diagonal
argument in density arguments: if for each $n$ one can find a set $A_n$ with good properties and
a controlled density, then their ``union'' will have the same properties (eventually) and a
controlled density.\<close>

proposition upper_asymptotic_density_incseq_Union:
  assumes "\<And>(n::nat). upper_asymptotic_density (A n) \<le> l" "incseq A"
  shows "\<exists>B. upper_asymptotic_density B \<le> l \<and> (\<forall>n. \<exists>N. A n \<inter> {N..} \<subseteq> B)"
proof -
  have A: "\<exists>N. \<forall>j \<ge> N. card (A k \<inter> {..<j}) < (l + (1/2)^k) * j" for k
  proof -
    have *: "upper_asymptotic_density (A k) < l + (1/2)^k" using assms(1)[of k]
      by (metis add.right_neutral add_mono_thms_linordered_field(4) less_divide_eq_numeral1(1) mult_zero_left zero_less_one zero_less_power)
    show ?thesis
      using upper_asymptotic_densityD[OF *] unfolding eventually_sequentially by auto
  qed
  have "\<exists>N. \<forall>k. (\<forall>j \<ge> N k. card (A k \<inter> {..<j}) \<le> (l+(1/2)^k) * j) \<and> N (Suc k) > N k"
  proof (rule dependent_nat_choice)
    fix x k::nat
    obtain N where N: "\<forall>j\<ge>N. real (card (A (Suc k) \<inter> {..<j})) \<le> (l + (1 / 2) ^ Suc k) * real j"
      using A[of "Suc k"] less_imp_le by auto
    show "\<exists>y. (\<forall>j\<ge>y. real (card (A(Suc k) \<inter> {..<j})) \<le> (l + (1 / 2) ^ Suc k) * real j) \<and> x < y"
      apply (rule exI[of _ "max x N + 1"]) using N by auto
  next
    show "\<exists>x. \<forall>j\<ge>x. real (card ((A 0) \<inter> {..<j})) \<le> (l + (1 / 2) ^ 0) * real j"
      using A[of 0] less_imp_le by auto
  qed
  text \<open>Here is the choice of the good waiting function $N$\<close>
  then obtain N where N: "\<And>k j. j \<ge> N k \<Longrightarrow> card (A k \<inter> {..<j}) \<le> (l + (1/2)^k) * j" "\<And>k. N (Suc k) > N k"
    by blast
  then have "strict_mono N" by (simp add: strict_monoI_Suc)
  have Nmono: "N k < N l" if "k < l" for k l
    using N(2) by (simp add: lift_Suc_mono_less that)

  text \<open>We can now define the global bad set $B$.\<close>
  define B where "B = (\<Union>k. A k \<inter> {N k..})"
  text \<open>We will now show that it also has density at most $l$.\<close>
  have Bcard: "card (B \<inter> {..<n}) \<le> (l+(1/2)^k) * n" if "N k \<le> n" "n < N (Suc k)" for n k
  proof -
    have "{N j..<n} = {}" if "j \<in> {k<..}" for j
      using \<open>n < N (Suc k)\<close> that by (auto, meson \<open>strict_mono N\<close> less_trans not_less_eq strict_mono_less)
    then have *: "(\<Union>j\<in>{k<..}. A j \<inter> {N j..<n}) = {}" by force

    have "B \<inter> {..<n} = (\<Union>j. A j \<inter> {N j..<n})"
      unfolding B_def by auto
    also have "... = (\<Union>j \<in> {..k}. A j \<inter> {N j..<n}) \<union> (\<Union>j\<in>{k<..}. A j \<inter> {N j..<n})"
      unfolding UN_Un [symmetric] by (rule arg_cong [of _ _ Union]) auto
    also have "... = (\<Union>j \<in> {..k}. A j \<inter> {N j..<n})"
      unfolding * by simp
    also have "... \<subseteq> (\<Union>j \<in> {..k}. A k \<inter> {..<n})"
      using \<open>incseq A\<close> unfolding incseq_def by (auto intro!: UN_mono)
    also have "... = A k \<inter> {..<n}"
      by simp
    finally have "card (B \<inter> {..<n}) \<le> card (A k \<inter> {..<n})"
      by (rule card_mono[rotated], auto)
    then show ?thesis
      using N(1)[OF \<open>n \<ge> N k\<close>] by simp
  qed
  have "eventually (\<lambda>n. card (B \<inter> {..<n}) \<le> a * n) sequentially" if "l < a" for a::real
  proof -
    have "eventually (\<lambda>k. (l+(1/2)^k) < a) sequentially"
      apply (rule order_tendstoD[of _ "l+0"], intro tendsto_intros) using that by auto
    then obtain k where "l + (1/2)^k < a"
      unfolding eventually_sequentially by auto
    have "card (B \<inter> {..<n}) \<le> a * n" if "n \<ge> N k + 1"for n
    proof -
      have "n \<ge> N k" "n \<ge> 1" using that by auto
      have "{p. n \<ge> N p} \<subseteq> {..n}"
        using \<open>strict_mono N\<close> dual_order.trans seq_suble by blast
      then have *: "finite {p. n \<ge> N p}" "{p. n \<ge> N p} \<noteq> {}"
        using \<open>n \<ge> N k\<close> finite_subset by auto
      define m where "m = Max {p. n \<ge> N p}"
      have "k \<le> m"
        unfolding m_def using Max_ge[OF *(1), of k] that by auto
      have "N m \<le> n"
        unfolding m_def using Max_in[OF *] by auto
      have "Suc m \<notin> {p. n \<ge> N p}"
        unfolding m_def using * Max_ge Suc_n_not_le_n by blast
      then have "n < N (Suc m)" by simp
      have "card (B \<inter> {..<n}) \<le> (l+(1/2)^m) * n"
        using Bcard[OF \<open>N m \<le> n\<close> \<open>n < N (Suc m)\<close>] by simp
      also have "... \<le> (l + (1/2)^k) * n"
        apply (rule mult_right_mono) using \<open>k \<le> m\<close> by (auto simp add: power_decreasing)
      also have "... \<le> a * n"
        using \<open>l + (1/2)^k < a\<close> \<open>n \<ge> 1\<close> by auto
      finally show ?thesis by auto
    qed
    then show ?thesis unfolding eventually_sequentially by auto
  qed
  then have "upper_asymptotic_density B \<le> a" if "a > l" for a
    using upper_asymptotic_densityI that by auto
  then have "upper_asymptotic_density B \<le> l"
    by (meson dense not_le)
  moreover have "\<exists>N. A n \<inter> {N..} \<subseteq> B" for n
    apply (rule exI[of _ "N n"]) unfolding B_def by auto
  ultimately show ?thesis by auto
qed

text \<open>When the sequence of sets is not increasing, one can only obtain a set whose density
is bounded by the sum of the densities.\<close>

proposition upper_asymptotic_density_Union:
  assumes "summable (\<lambda>n. upper_asymptotic_density (A n))"
  shows "\<exists>B. upper_asymptotic_density B \<le> (\<Sum>n. upper_asymptotic_density (A n)) \<and> (\<forall>n. \<exists>N. A n \<inter> {N..} \<subseteq> B)"
proof -
  define C where "C = (\<lambda>n. (\<Union>i\<le>n. A i))"
  have C1: "incseq C"
    unfolding C_def incseq_def by fastforce
  have C2: "upper_asymptotic_density (C k) \<le> (\<Sum>n. upper_asymptotic_density (A n))" for k
  proof -
    have "upper_asymptotic_density (C k) \<le> (\<Sum>i\<le>k. upper_asymptotic_density (A i))"
      unfolding C_def by (rule upper_asymptotic_density_finite_Union, auto)
    also have "... \<le> (\<Sum>i. upper_asymptotic_density (A i))"
      apply (rule sum_le_suminf[OF assms]) using upper_asymptotic_density_in_01 by auto
    finally show ?thesis by simp
  qed
  obtain B where B: "upper_asymptotic_density B \<le> (\<Sum>n. upper_asymptotic_density (A n))"
                    "\<And>n. \<exists>N. C n \<inter> {N..} \<subseteq> B"
    using upper_asymptotic_density_incseq_Union[OF C2 C1] by blast
  have "\<exists>N. A n \<inter> {N..} \<subseteq> B" for n
    using B(2)[of n] unfolding C_def by auto
  then show ?thesis using B(1) by blast
qed

text \<open>A particular case of the previous proposition, often useful, is when all sets have density
zero.\<close>

proposition upper_asymptotic_density_zero_Union:
  assumes "\<And>n::nat. upper_asymptotic_density (A n) = 0"
  shows "\<exists>B. upper_asymptotic_density B = 0 \<and> (\<forall>n. \<exists>N. A n \<inter> {N..} \<subseteq> B)"
proof -
  have "\<exists>B. upper_asymptotic_density B \<le> (\<Sum>n. upper_asymptotic_density (A n)) \<and> (\<forall>n. \<exists>N. A n \<inter> {N..} \<subseteq> B)"
    apply (rule upper_asymptotic_density_Union) unfolding assms by auto
  then obtain B where "upper_asymptotic_density B \<le> 0" "\<And>n. \<exists>N. A n \<inter> {N..} \<subseteq> B"
    unfolding assms by auto
  then show ?thesis
    using upper_asymptotic_density_in_01(3)[of B] by auto
qed

subsection \<open>Lower asymptotic densities\<close>

text \<open>The lower asymptotic density of a set of natural numbers is defined just as its
upper asymptotic density but using a liminf instead of a limsup. Its properties are proved
exactly in the same way.\<close>

definition lower_asymptotic_density::"nat set \<Rightarrow> real"
  where "lower_asymptotic_density A = real_of_ereal(liminf (\<lambda>n. card(A \<inter> {..<n})/n))"

lemma lower_asymptotic_density_in_01:
  "ereal(lower_asymptotic_density A) = liminf (\<lambda>n. card(A \<inter> {..<n})/n)"
  "lower_asymptotic_density A \<le> 1"
  "lower_asymptotic_density A \<ge> 0"
proof -
  {
    fix n::nat assume "n>0"
    have "card(A \<inter> {..<n}) \<le> n" by (metis card_lessThan Int_lower2 card_mono finite_lessThan)
    then have "card(A \<inter> {..<n}) / n \<le> ereal 1" using \<open>n>0\<close> by auto
  }
  then have "eventually (\<lambda>n. card(A \<inter> {..<n}) / n \<le> ereal 1) sequentially"
    by (simp add: eventually_at_top_dense)
  then have "limsup (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1" by (simp add: Limsup_const Limsup_bounded)
  then have a: "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<le> 1"
    by (meson Liminf_le_Limsup less_le_trans not_le sequentially_bot)

  have "card(A \<inter> {..<n}) / n \<ge> ereal 0" for n by auto
  then have b: "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> 0" by (simp add: le_Liminf_iff less_le_trans)

  have "abs(liminf (\<lambda>n. card(A \<inter> {..<n})/n)) \<noteq> \<infinity>" using a b by auto
  then show "ereal(lower_asymptotic_density A) = liminf (\<lambda>n. card(A \<inter> {..<n})/n)"
    unfolding lower_asymptotic_density_def by auto
  show "lower_asymptotic_density A \<le> 1" "lower_asymptotic_density A \<ge> 0" unfolding lower_asymptotic_density_def
    using a b by (auto simp add: real_of_ereal_le_1 real_of_ereal_pos)
qed

text \<open>The lower asymptotic density is bounded by the upper one. When they coincide,
$Card(A \cap [0,n))/n$ converges to this common value.\<close>

lemma lower_asymptotic_density_le_upper:
  "lower_asymptotic_density A \<le> upper_asymptotic_density A"
using lower_asymptotic_density_in_01(1) upper_asymptotic_density_in_01(1)
by (metis (mono_tags, lifting) Liminf_le_Limsup ereal_less_eq(3) sequentially_bot)

lemma lower_asymptotic_density_eq_upper:
  assumes "lower_asymptotic_density A = l" "upper_asymptotic_density A = l"
  shows "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> l"
apply (rule limsup_le_liminf_real)
using upper_asymptotic_density_in_01(1)[of A] lower_asymptotic_density_in_01(1)[of A] assms by auto

text \<open>In particular, when a set has a zero upper density, or a lower density one, then this
implies the corresponding convergence of $Card(A \cap [0,n))/n$.\<close>

lemma upper_asymptotic_density_zero_lim:
  assumes "upper_asymptotic_density A = 0"
  shows "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> 0"
apply (rule lower_asymptotic_density_eq_upper)
using assms lower_asymptotic_density_le_upper[of A] lower_asymptotic_density_in_01(3)[of A] by auto

lemma lower_asymptotic_density_one_lim:
  assumes "lower_asymptotic_density A = 1"
  shows "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> 1"
apply (rule lower_asymptotic_density_eq_upper)
using assms lower_asymptotic_density_le_upper[of A] upper_asymptotic_density_in_01(2)[of A] by auto

text \<open>The lower asymptotic density of a set is $1$ minus the upper asymptotic density of its complement.
Hence, most statements about one of them follow from statements about the other one,
although we will rather give direct proofs as they are not more complicated.\<close>

lemma lower_upper_asymptotic_density_complement:
  "lower_asymptotic_density A = 1 - upper_asymptotic_density (UNIV - A)"
proof -
  {
    fix n assume "n>(0::nat)"
    have "{..<n} \<inter> UNIV - (UNIV - ({..<n} - (UNIV - A))) = {..<n} \<inter> A"
      by blast
    moreover have "{..<n} \<inter> UNIV \<inter> (UNIV - ({..<n} - (UNIV - A))) = (UNIV - A) \<inter> {..<n}"
      by blast
    ultimately have "card (A \<inter> {..<n}) = n - card((UNIV-A) \<inter> {..<n})"
      by (metis (no_types) Int_commute card_Diff_subset_Int card_lessThan finite_Int finite_lessThan inf_top_right)
    then have "card (A \<inter> {..<n})/n = (real n - card((UNIV-A) \<inter> {..<n})) / n"
      by (metis Int_lower2 card_lessThan card_mono finite_lessThan of_nat_diff)
    then have "card (A \<inter> {..<n})/n = ereal 1 - card((UNIV-A) \<inter> {..<n})/n"
      using \<open>n>0\<close> by (simp add: diff_divide_distrib)
  }
  then have "eventually (\<lambda>n. card (A \<inter> {..<n})/n = ereal 1 - card((UNIV-A) \<inter> {..<n})/n) sequentially"
    by (simp add: eventually_at_top_dense)
  then have "liminf (\<lambda>n. card (A \<inter> {..<n})/n) = liminf (\<lambda>n. ereal 1 - card((UNIV-A) \<inter> {..<n})/n)"
    by (rule Liminf_eq)
  also have "... = ereal 1 - limsup (\<lambda>n. card((UNIV-A) \<inter> {..<n})/n)"
    by (rule liminf_ereal_cminus, simp)
  finally show ?thesis unfolding lower_asymptotic_density_def
    by (metis ereal_minus(1) real_of_ereal.simps(1) upper_asymptotic_density_in_01(1))
qed

proposition lower_asymptotic_densityD:
  fixes l::real
  assumes "lower_asymptotic_density A > l"
  shows "eventually (\<lambda>n. card(A \<inter> {..<n}) > l * n) sequentially"
proof -
  have "ereal(lower_asymptotic_density A) > l" using assms by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) > l"
    using lower_asymptotic_density_in_01(1) by auto
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n > ereal l) sequentially"
    using less_LiminfD by blast
  then have "eventually (\<lambda>n. card(A \<inter> {..<n})/n > ereal l \<and> n > 0) sequentially"
    using eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n}) > l * n" if "card(A \<inter> {..<n})/n > ereal l \<and> n > 0" for n
    using that divide_le_eq ereal_less_eq(3) less_imp_of_nat_less not_less of_nat_eq_0_iff by fastforce
  ultimately show "eventually (\<lambda>n. card(A \<inter> {..<n}) > l * n) sequentially"
    by (simp add: eventually_mono)
qed

proposition lower_asymptotic_densityI:
  fixes l::real
  assumes "eventually (\<lambda>n. card(A \<inter> {..<n}) \<ge> l * n) sequentially"
  shows "lower_asymptotic_density A \<ge> l"
proof -
  have "eventually (\<lambda>n. card(A \<inter> {..<n}) \<ge> l * n \<and> n > 0) sequentially"
    using assms eventually_gt_at_top eventually_conj by blast
  moreover have "card(A \<inter> {..<n})/n \<ge> ereal l" if "card(A \<inter> {..<n}) \<ge> l * n \<and> n > 0" for n
    using that by (meson ereal_less_eq(3) not_less of_nat_0_less_iff pos_divide_less_eq)
  ultimately have "eventually (\<lambda>n. card(A \<inter> {..<n})/n \<ge> ereal l) sequentially"
    by (simp add: eventually_mono)
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) \<ge> ereal l"
    by (simp add: Liminf_bounded)
  then have "ereal(lower_asymptotic_density A) \<ge> ereal l"
    using lower_asymptotic_density_in_01(1) by auto
  then show ?thesis by auto
qed

text \<open>One can control the asymptotic density of an intersection in terms of the asymptotic density
of each component\<close>

lemma lower_asymptotic_density_intersection:
  "lower_asymptotic_density A + lower_asymptotic_density B \<le> lower_asymptotic_density (A \<inter> B) + 1"
using upper_asymptotic_density_union[of "UNIV - A" "UNIV - B"]
unfolding lower_upper_asymptotic_density_complement by (auto simp add: algebra_simps Diff_Int)

lemma lower_asymptotic_density_subset:
  assumes "A \<subseteq> B"
  shows "lower_asymptotic_density A \<le> lower_asymptotic_density B"
using upper_asymptotic_density_subset[of "UNIV-B" "UNIV-A"] assms
unfolding lower_upper_asymptotic_density_complement by auto

lemma lower_asymptotic_density_lim:
  assumes "(\<lambda>n. card(A \<inter> {..<n})/n) \<longlonglongrightarrow> l"
  shows "lower_asymptotic_density A = l"
proof -
  have "(\<lambda>n. ereal(card(A \<inter> {..<n})/n)) \<longlonglongrightarrow> l" using assms by auto
  then have "liminf (\<lambda>n. card(A \<inter> {..<n})/n) = l"
    using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
  then show ?thesis unfolding lower_asymptotic_density_def by auto
qed

lemma lower_asymptotic_density_finite:
  assumes "finite A"
  shows "lower_asymptotic_density A = 0"
using lower_asymptotic_density_in_01(3) upper_asymptotic_density_finite[OF assms] lower_asymptotic_density_le_upper
by (metis antisym_conv)

text \<open>In particular, bounded intervals have zero lower density.\<close>

lemma lower_asymptotic_density_bdd_interval [simp]:
  "lower_asymptotic_density {} = 0"
  "lower_asymptotic_density {..N} = 0"
  "lower_asymptotic_density {..<N} = 0"
  "lower_asymptotic_density {n..N} = 0"
  "lower_asymptotic_density {n..<N} = 0"
  "lower_asymptotic_density {n<..N} = 0"
  "lower_asymptotic_density {n<..<N} = 0"
by (auto intro!: lower_asymptotic_density_finite)

text \<open>Conversely, unbounded intervals have density $1$.\<close>

lemma lower_asymptotic_density_infinite_interval [simp]:
  "lower_asymptotic_density {N..} = 1"
  "lower_asymptotic_density {N<..} = 1"
  "lower_asymptotic_density UNIV = 1"
proof -
  have "UNIV - {N..} = {..<N}" by auto
  then show "lower_asymptotic_density {N..} = 1"
    by (auto simp add: lower_upper_asymptotic_density_complement)
  have "UNIV - {N<..} = {..N}" by auto
  then show "lower_asymptotic_density {N<..} = 1"
    by (auto simp add: lower_upper_asymptotic_density_complement)
  show "lower_asymptotic_density UNIV = 1"
    by (auto simp add: lower_upper_asymptotic_density_complement)
qed

lemma upper_asymptotic_density_infinite_interval [simp]:
  "upper_asymptotic_density {N..} = 1"
  "upper_asymptotic_density {N<..} = 1"
  "upper_asymptotic_density UNIV = 1"
by (metis antisym upper_asymptotic_density_in_01(2) lower_asymptotic_density_infinite_interval lower_asymptotic_density_le_upper)+

text \<open>The intersection of sets with lower density one still has lower density one.\<close>

lemma lower_asymptotic_density_one_intersection:
  assumes "lower_asymptotic_density A = 1" "lower_asymptotic_density B = 1"
  shows "lower_asymptotic_density (A \<inter> B) = 1"
using lower_asymptotic_density_in_01(2)[of "A \<inter> B"] lower_asymptotic_density_intersection[of A B] unfolding assms by auto

lemma lower_asymptotic_density_one_finite_Intersection:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> lower_asymptotic_density (A i) = 1"
  shows "lower_asymptotic_density (\<Inter>i\<in>I. A i) = 1"
using assms by (induction rule: finite_induct, auto intro!: lower_asymptotic_density_one_intersection)

text \<open>As for the upper asymptotic density, there is a modification of the intersection, akin
to the diagonal argument in this context, for which the ``intersection'' of sets with large
lower density still has large lower density.\<close>

proposition lower_asymptotic_density_decseq_Inter:
  assumes "\<And>(n::nat). lower_asymptotic_density (A n) \<ge> l" "decseq A"
  shows "\<exists>B. lower_asymptotic_density B \<ge> l \<and> (\<forall>n. \<exists>N. B \<inter> {N..} \<subseteq> A n)"
proof -
  define C where "C = (\<lambda>n. UNIV - A n)"
  have *: "upper_asymptotic_density (C n) \<le> 1 - l" for n
    using assms(1)[of n] unfolding C_def lower_upper_asymptotic_density_complement[of "A n"] by auto
  have **: "incseq C"
    using assms(2) unfolding C_def incseq_def decseq_def by auto
  obtain D where D: "upper_asymptotic_density D \<le> 1 - l" "\<And>n. \<exists>N. C n \<inter> {N..} \<subseteq> D"
    using upper_asymptotic_density_incseq_Union[OF * **] by blast
  define B where "B = UNIV - D"
  have "lower_asymptotic_density B \<ge> l"
    using D(1) lower_upper_asymptotic_density_complement[of B] unfolding B_def by auto
  moreover have "\<exists>N. B \<inter> {N..} \<subseteq> A n" for n
    using D(2)[of n] unfolding B_def C_def by auto
  ultimately show ?thesis by auto
qed

text \<open>In the same way, the modified intersection of sets of density $1$ still has density one,
and is eventually contained in each of them.\<close>

proposition lower_asymptotic_density_one_Inter:
  assumes "\<And>n::nat. lower_asymptotic_density (A n) = 1"
  shows "\<exists>B. lower_asymptotic_density B = 1 \<and> (\<forall>n. \<exists>N. B \<inter> {N..} \<subseteq> A n)"
proof -
  define C where "C = (\<lambda>n. UNIV - A n)"
  have *: "upper_asymptotic_density (C n) = 0" for n
    using assms(1)[of n] unfolding C_def lower_upper_asymptotic_density_complement[of "A n"] by auto
  obtain D where D: "upper_asymptotic_density D = 0" "\<And>n. \<exists>N. C n \<inter> {N..} \<subseteq> D"
    using upper_asymptotic_density_zero_Union[OF *] by force
  define B where "B = UNIV - D"
  have "lower_asymptotic_density B = 1"
    using D(1) lower_upper_asymptotic_density_complement[of B] unfolding B_def by auto
  moreover have "\<exists>N. B \<inter> {N..} \<subseteq> A n" for n
    using D(2)[of n] unfolding B_def C_def by auto
  ultimately show ?thesis by auto
qed

text \<open>Sets with density $1$ play an important role in relation to Cesaro convergence of nonnegative
bounded sequences: such a sequence converges to $0$ in Cesaro average if and only if it converges
to $0$ along a set of density $1$.

The proof is not hard. Since the Cesaro average tends to $0$, then given $\epsilon>0$ the
proportion of times where $u_n < \epsilon$ tends to $1$, i.e., the set $A_\epsilon$ of such good
times has density $1$. A modified intersection (as constructed in
Proposition~\verb+lower_asymptotic_density_one_Inter+) of these times has density $1$, and
$u_n$ tends to $0$ along this set.
\<close>

theorem cesaro_imp_density_one:
  assumes "\<And>n. u n \<ge> (0::real)" "(\<lambda>n. (\<Sum>i<n. u i)/n) \<longlonglongrightarrow> 0"
  shows "\<exists>A. lower_asymptotic_density A = 1 \<and> (\<lambda>n. u n * indicator A n) \<longlonglongrightarrow> 0"
proof -
  define B where "B = (\<lambda>e. {n. u n \<ge> e})"
  text \<open>$B e$ is the set of bad times where $u_n \geq e$. It has density $0$ thanks to
  the assumption of Cesaro convergence to $0$.\<close>
  have A: "upper_asymptotic_density (B e) = 0" if "e > 0" for e
  proof -
    have *: "card (B e \<inter> {..<n}) / n \<le> (1/e) * ((\<Sum>i\<in>{..<n}. u i)/n)" if "n \<ge> 1" for n
    proof -
      have "e * card (B e \<inter> {..<n}) = (\<Sum>i\<in>B e \<inter> {..<n}. e)" by auto
      also have "... \<le> (\<Sum>i\<in>B e \<inter> {..<n}. u i)"
        apply (rule sum_mono) unfolding B_def by auto
      also have "... \<le> (\<Sum>i\<in>{..<n}. u i)"
        apply (rule sum_mono2) using assms by auto
      finally show ?thesis
        using \<open>e > 0\<close> \<open>n \<ge> 1\<close> by (auto simp add: divide_simps algebra_simps)
    qed
    have "(\<lambda>n. card (B e \<inter> {..<n}) / n) \<longlonglongrightarrow> 0"
    proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. (1/e) * ((\<Sum>i\<in>{..<n}. u i)/n)"])
      have "(\<lambda>n. (1/e) * ((\<Sum>i\<in>{..<n}. u i)/n)) \<longlonglongrightarrow> (1/e) * 0"
        by (intro tendsto_intros assms)
      then show "(\<lambda>n. (1/e) * ((\<Sum>i\<in>{..<n}. u i)/n)) \<longlonglongrightarrow> 0" by simp
      show "\<forall>\<^sub>F n in sequentially. real (card (B e \<inter> {..<n})) / real n \<le> 1 / e * (sum u {..<n} / real n)"
        using * unfolding eventually_sequentially by auto
    qed (auto)
    then show ?thesis
      by (rule upper_asymptotic_density_lim)
  qed
  define C where "C = (\<lambda>n::nat. UNIV - B (((1::real)/2)^n))"
  have "lower_asymptotic_density (C n) = 1" for n
    unfolding C_def lower_upper_asymptotic_density_complement by (auto intro!: A)
  then obtain A where A: "lower_asymptotic_density A = 1" "\<And>n. \<exists>N. A \<inter> {N..} \<subseteq> C n"
    using lower_asymptotic_density_one_Inter by blast
  have E: "eventually (\<lambda>n. u n * indicator A n < e) sequentially" if "e > 0" for e
  proof -
    have "eventually (\<lambda>n. ((1::real)/2)^n < e) sequentially"
      by (rule order_tendstoD[OF _ \<open>e > 0\<close>], intro tendsto_intros, auto)
    then obtain n where n: "((1::real)/2)^n < e"
      unfolding eventually_sequentially by auto
    obtain N where N: "A \<inter> {N..} \<subseteq> C n"
      using A(2) by blast
    have "u k * indicator A k < e" if "k \<ge> N" for k
    proof (cases "k \<in> A")
      case True
      then have "k \<in> C n" using N that by auto
      then have "u k < ((1::real)/2)^n"
        unfolding C_def B_def by auto
      then have "u k < e"
        using n by auto
      then show ?thesis
        unfolding indicator_def using True by auto
    next
      case False
      then show ?thesis
        unfolding indicator_def using \<open>e > 0\<close> by auto
    qed
    then show ?thesis
      unfolding eventually_sequentially by auto
  qed
  have "(\<lambda>n. u n * indicator A n) \<longlonglongrightarrow> 0"
    apply (rule order_tendstoI[OF _ E])
    unfolding indicator_def using \<open>\<And>n. u n \<ge> 0\<close> by (simp add: less_le_trans)
  then show ?thesis
    using \<open>lower_asymptotic_density A = 1\<close> by auto
qed

text \<open>The proof of the reverse implication is more direct: in the Cesaro sum, just bound the
elements in $A$ by a small $\epsilon$, and the other ones by a uniform bound, to get a bound
which is $o(n)$.\<close>

theorem density_one_imp_cesaro:
  assumes "\<And>n. u n \<ge> (0::real)" "\<And>n. u n \<le> C"
          "lower_asymptotic_density A = 1"
          "(\<lambda>n. u n * indicator A n) \<longlonglongrightarrow> 0"
  shows "(\<lambda>n. (\<Sum>i<n. u i)/n) \<longlonglongrightarrow> 0"
proof (rule order_tendstoI)
  fix e::real assume "e < 0"
  have "(\<Sum>i<n. u i)/n \<ge> 0" for n
    using assms(1) by (simp add: sum_nonneg divide_simps)
  then have "(\<Sum>i<n. u i)/n > e" for n
    using \<open>e < 0\<close> less_le_trans by auto
  then show "eventually (\<lambda>n. (\<Sum>i<n. u i)/n > e) sequentially"
    unfolding eventually_sequentially by auto
next
  fix e::real assume "e > 0"
  have "C \<ge> 0" using \<open>u 0 \<ge> 0\<close> \<open>u 0 \<le> C\<close> by auto
  have "eventually (\<lambda>n. u n * indicator A n < e/4) sequentially"
    using order_tendstoD(2)[OF assms(4), of "e/4"] \<open>e>0\<close> by auto
  then obtain N where N: "\<And>k. k \<ge> N \<Longrightarrow> u k * indicator A k < e/4"
    unfolding eventually_sequentially by auto
  define B where "B = UNIV - A"
  have *: "upper_asymptotic_density B = 0"
    using assms unfolding B_def lower_upper_asymptotic_density_complement by auto
  have "eventually (\<lambda>n. card(B \<inter> {..<n}) < (e/(4 * (C+1))) * n) sequentially"
    apply (rule upper_asymptotic_densityD) using \<open>e > 0\<close> \<open>C \<ge> 0\<close> * by auto
  then obtain M where M: "\<And>n. n \<ge> M \<Longrightarrow> card(B \<inter> {..<n}) < (e/(4 * (C+1))) * n"
      unfolding eventually_sequentially by auto

  obtain P::nat where P: "P \<ge> 4 * N * C/e"
    using real_arch_simple by auto
  define Q where "Q = N + M + 1 + P"

  have "(\<Sum>i<n. u i)/n < e" if "n \<ge> Q" for n
  proof -
    have n: "n \<ge> N" "n \<ge> M" "n \<ge> P" "n \<ge> 1"
      using \<open>n \<ge> Q\<close> unfolding Q_def by auto
    then have n2: "n \<ge> 4 * N * C/e" using P by auto
    have "(\<Sum>i<n. u i) \<le> (\<Sum>i\<in>{..<N} \<union> ({N..<n} \<inter> A) \<union> ({N..<n} - A). u i)"
      by (rule sum_mono2, auto simp add: assms)
    also have "... = (\<Sum>i\<in>{..<N}. u i) + (\<Sum>i\<in>{N..<n} \<inter> A. u i) + (\<Sum>i\<in>{N..<n} - A. u i)"
      by (subst sum.union_disjoint, auto)+
    also have "... = (\<Sum>i\<in>{..<N}. u i) + (\<Sum>i\<in>{N..<n} \<inter> A. u i * indicator A i) + (\<Sum>i\<in>{N..<n} - A. u i)"
      unfolding indicator_def by auto
    also have "... \<le> (\<Sum>i\<in>{..<N}. u i) + (\<Sum>i\<in>{N..<n}. u i * indicator A i) + (\<Sum>i\<in> B \<inter> {..<n}. u i)"
      apply (intro add_mono sum_mono2) unfolding B_def using assms by auto
    also have "... \<le> (\<Sum>i\<in>{..<N}. C) + (\<Sum>i\<in>{N..<n}. e/4) + (\<Sum>i\<in>B \<inter> {..<n}. C)"
      apply (intro add_mono sum_mono) using assms less_imp_le[OF N] by auto
    also have "... = N * C + (n-N) * e/4 + card(B \<inter> {..<n}) * C"
      by auto
    also have "... \<le> n * e/4 + n * e/4 + (e/(4 * (C+1))) * n * C"
      apply (intro add_mono)
      using n2 \<open>e > 0\<close> mult_right_mono[OF less_imp_le[OF M[OF \<open>n \<ge> M\<close>]] \<open>C \<ge> 0\<close>] by (auto simp add: divide_simps)
    also have "... \<le> n * e * 3/4"
      using \<open>C \<ge> 0\<close> \<open>e > 0\<close> by (simp add: divide_simps algebra_simps)
    also have "... < n * e"
      using \<open>n \<ge> 1\<close> \<open>e > 0\<close> by auto
    finally show ?thesis
      using \<open>n \<ge> 1\<close> by (simp add: divide_simps algebra_simps)
  qed
  then show "eventually (\<lambda>n. (\<Sum>i<n. u i)/n < e) sequentially"
    unfolding eventually_sequentially by auto
qed

end (*of Asymptotic_Density.thy*)
