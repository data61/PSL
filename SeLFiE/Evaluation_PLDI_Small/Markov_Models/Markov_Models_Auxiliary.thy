(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Auxiliary Theory\<close>

text \<open>Parts of it should be moved to the Isabelle repository\<close>

theory Markov_Models_Auxiliary
imports
  "HOL-Probability.Probability"
  "HOL-Library.Rewrite"
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
  Coinductive.Coinductive_Stream
  Coinductive.Coinductive_Nat
begin

lemma lfp_upperbound: "(\<And>y. x \<le> f y) \<Longrightarrow> x \<le> lfp f"
  unfolding lfp_def by (intro Inf_greatest) (auto intro: order_trans)

(* ?? *)
lemma lfp_arg: "(\<lambda>t. lfp (F t)) = lfp (\<lambda>x t. F t (x t))"
  apply (auto simp: lfp_def le_fun_def fun_eq_iff intro!: Inf_eqI Inf_greatest)
  subgoal for x y
    by (rule INF_lower2[of "top(x := y)"]) auto
  done

lemma lfp_pair: "lfp (\<lambda>f (a, b). F (\<lambda>a b. f (a, b)) a b) (a, b) = lfp F a b"
  unfolding lfp_def
  by (auto intro!: INF_eq simp: le_fun_def)
     (auto intro!: exI[of _ "\<lambda>(a, b). x a b" for x])

lemma all_Suc_split: "(\<forall>i. P i) \<longleftrightarrow> (P 0 \<and> (\<forall>i. P (Suc i)))"
  using nat_induct by auto

definition "with P f d = (if \<exists>x. P x then f (SOME x. P x) else d)"

lemma withI[case_names default exists]:
  "((\<And>x. \<not> P x) \<Longrightarrow> Q d) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q (f x)) \<Longrightarrow> Q (with P f d)"
  unfolding with_def by (auto intro: someI2)

context order
begin

definition
  "maximal f S = {x\<in>S. \<forall>y\<in>S. f y \<le> f x}"

lemma maximalI: "x \<in> S \<Longrightarrow> (\<And>y. y \<in> S \<Longrightarrow> f y \<le> f x) \<Longrightarrow> x \<in> maximal f S"
  by (simp add: maximal_def)

lemma maximalI_trans: "x \<in> maximal f S \<Longrightarrow> f x \<le> f y \<Longrightarrow> y \<in> S \<Longrightarrow> y \<in> maximal f S"
  unfolding maximal_def by (blast intro: antisym order_trans)

lemma maximalD1: "x \<in> maximal f S \<Longrightarrow> x \<in> S"
  by (simp add: maximal_def)

lemma maximalD2: "x \<in> maximal f S \<Longrightarrow> y \<in> S \<Longrightarrow> f y \<le> f x"
  by (simp add: maximal_def)

lemma maximal_inject: "x \<in> maximal f S \<Longrightarrow> y \<in> maximal f S \<Longrightarrow> f x = f y"
  unfolding maximal_def by (blast intro: antisym)

lemma maximal_empty[simp]: "maximal f {} = {}"
  by (simp add: maximal_def)

lemma maximal_singleton[simp]: "maximal f {x} = {x}"
  by (auto simp add: maximal_def)

lemma maximal_in_S: "maximal f S \<subseteq> S"
  by (auto simp: maximal_def)

end

context linorder
begin

lemma maximal_ne:
  assumes "finite S" "S \<noteq> {}"
  shows "maximal f S \<noteq> {}"
  using assms
proof (induct rule: finite_ne_induct)
  case (insert s S)
  show ?case
  proof cases
    assume "\<forall>x\<in>S. f x \<le> f s"
    with insert have "s \<in> maximal f (insert s S)"
      by (auto intro!: maximalI)
    then show ?thesis
      by auto
  next
    assume "\<not> (\<forall>x\<in>S. f x \<le> f s)"
    then have "maximal f (insert s S) = maximal f S"
      by (auto simp: maximal_def)
    with insert show ?thesis
      by auto
  qed
qed simp

end

lemma mono_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. set_pmf (K s)) \<subseteq> S \<union> N"
  assumes int_l1[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes int_l2[simp]: "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes to_N: "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes l1: "\<And>s. s \<in> S \<Longrightarrow> (\<integral>t. l1 t \<partial>K s) + c s \<le> l1 s"
  assumes l2: "\<And>s. s \<in> S \<Longrightarrow> l2 s \<le> (\<integral>t. l2 t \<partial>K s) + c s"
  assumes eq: "\<And>s. s \<in> N \<Longrightarrow> l2 s \<le> l1 s"
  assumes finitary: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s \<le> l1 s"
proof -
  define M where "M = {s\<in>S\<union>N. \<forall>t\<in>S\<union>N. \<Delta> t \<le> \<Delta> s}"

  have [simp]: "\<And>s. s\<in>S \<Longrightarrow> integrable (K s) \<Delta>"
    by (simp add: \<Delta>_def[abs_def])

  have M_unqiue: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> M \<Longrightarrow> \<Delta> s = \<Delta> t"
    by (auto intro!: antisym simp: M_def)
  have M1: "\<And>s. s \<in> M \<Longrightarrow> s \<in> S \<union> N"
    by (auto simp: M_def)
  have M2: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> \<Delta> t \<le> \<Delta> s"
    by (auto simp: M_def)
  have M3: "\<And>s t. s \<in> M \<Longrightarrow> t \<in> S \<union> N \<Longrightarrow> t \<notin> M \<Longrightarrow> \<Delta> t < \<Delta> s"
    by (auto simp: M_def less_le)

  have N: "\<forall>s\<in>N. \<Delta> s \<le> 0"
    using eq by (simp add: \<Delta>_def)

  { fix s assume s: "s \<in> M" "M \<inter> N = {}"
    then have "s \<in> S - N"
      by (auto dest: M1)
    with to_N[of s] obtain t where "(s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*" and "t \<in> N"
      by (auto simp: M_def)
    from this(1) \<open>s \<in> M\<close> have "\<Delta> s \<le> 0"
    proof (induction rule: converse_rtrancl_induct)
      case (step s s')
      then have s: "s \<in> M" "s \<in> S" "s \<notin> N" and s': "s' \<in> S \<union> N" "s' \<in> K s"
        using S \<open>M \<inter> N = {}\<close> by (auto dest: M1)
      have "s' \<in> M"
      proof (rule ccontr)
        assume "s' \<notin> M"
        with \<open>s \<in> S\<close> s' \<open>s \<in> M\<close>
        have "0 < pmf (K s) s'" "\<Delta> s' < \<Delta> s"
          by (auto intro: M2 M3 pmf_positive)

        have "\<Delta> s \<le> ((\<integral>t. l2 t \<partial>K s) + c s) - ((\<integral>t. l1 t \<partial>K s) + c s)"
          unfolding \<Delta>_def using \<open>s \<in> S\<close> \<open>s \<notin> N\<close> by (intro diff_mono l1 l2) auto
        then have "\<Delta> s \<le> (\<integral>s'. \<Delta> s' \<partial>K s)"
          using \<open>s \<in> S\<close> by (simp add: \<Delta>_def)
        also have "\<dots> < (\<integral>s'. \<Delta> s \<partial>K s)"
          using \<open>s' \<in> K s\<close> \<open>\<Delta> s' < \<Delta> s\<close> \<open>s\<in>S\<close> S \<open>s\<in>M\<close>
          by (intro measure_pmf.integral_less_AE[where A="{s'}"])
             (auto simp: emeasure_measure_pmf_finite AE_measure_pmf_iff set_pmf_iff[symmetric]
                   intro!: M2)
        finally show False
          using measure_pmf.prob_space[of "K s"] by simp
      qed
      with step.IH \<open>t\<in>N\<close> N have "\<Delta> s' \<le> 0" "s' \<in> M"
        by auto
      with \<open>s\<in>S\<close> show "\<Delta> s \<le> 0"
        by (force simp: M_def)
    qed (insert N \<open>t\<in>N\<close>, auto) }

  show ?thesis
  proof cases
    assume "M \<inter> N = {}"
    have "Max (\<Delta>`(S\<union>N)) \<in> \<Delta>`(S\<union>N)"
      using \<open>s \<in> S\<close> by (intro Max_in finitary) auto
    then obtain t where "t \<in> S \<union> N" "\<Delta> t = Max (\<Delta>`(S\<union>N))"
      unfolding image_iff by metis
    then have "t \<in> M"
      by (auto simp: M_def finitary intro!: Max_ge)
    have "\<Delta> s \<le> \<Delta> t"
      using \<open>t\<in>M\<close> \<open>s\<in>S\<close> by (auto dest: M2)
    also have "\<Delta> t \<le> 0"
      using \<open>t\<in>M\<close> \<open>M \<inter> N = {}\<close> by fact
    finally show ?thesis
      by (simp add: \<Delta>_def)
  next
    assume "M \<inter> N \<noteq> {}"
    then obtain t where "t \<in> M" "t \<in> N" by auto
    with N \<open>s\<in>S\<close> have "\<Delta> s \<le> 0"
      by (intro order_trans[of "\<Delta> s" "\<Delta> t" 0]) (auto simp: M_def)
    then show ?thesis
      by (simp add: \<Delta>_def)
  qed
qed

lemma unique_les:
  fixes s S N and l1 l2 :: "'a \<Rightarrow> real" and K :: "'a \<Rightarrow> 'a pmf"
  defines "\<Delta> x \<equiv> l2 x - l1 x"
  assumes s: "s \<in> S" and S: "(\<Union>s\<in>S. set_pmf (K s)) \<subseteq> S \<union> N"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l1"
  assumes "\<And>s. s \<in> S \<Longrightarrow> integrable (K s) l2"
  assumes "\<And>s. s \<in> S \<Longrightarrow> \<exists>t\<in>N. (s, t) \<in> (SIGMA s:UNIV. K s)\<^sup>*"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l1 s = (\<integral>t. l1 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> S \<Longrightarrow> l2 s = (\<integral>t. l2 t \<partial>K s) + c s"
  assumes "\<And>s. s \<in> N \<Longrightarrow> l2 s = l1 s"
  assumes 1: "finite (\<Delta> ` (S\<union>N))"
  shows "l2 s = l1 s"
proof -
  have "finite ((\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    using 1 by (auto simp: \<Delta>_def[abs_def])
  moreover then have "finite (uminus ` (\<lambda>x. l2 x - l1 x) ` (S\<union>N))"
    by auto
  ultimately show ?thesis
    using assms
    by (intro antisym mono_les[of s S K N l2 l1 c] mono_les[of s S K N l1 l2 c])
       (auto simp: image_comp comp_def)
qed

lemma inf_continuous_suntil_disj[order_continuous_intros]:
  assumes Q: "inf_continuous Q"
  assumes disj: "\<And>x \<omega>. \<not> (P \<omega> \<and> Q x \<omega>)"
  shows "inf_continuous (\<lambda>x. P suntil Q x)"
  unfolding inf_continuous_def
proof (safe intro!: ext)
  fix M \<omega> i assume "(P suntil Q (\<Sqinter>i. M i)) \<omega>" "decseq M" then show "(P suntil Q (M i)) \<omega>"
    unfolding inf_continuousD[OF Q \<open>decseq M\<close>] by induction (auto intro: suntil.intros)
next
  fix M \<omega> assume *: "(\<Sqinter>i. P suntil Q (M i)) \<omega>" "decseq M"
  then have "(P suntil Q (M 0)) \<omega>"
    by auto
  from this * show "(P suntil Q (\<Sqinter>i. M i)) \<omega>"
    unfolding inf_continuousD[OF Q \<open>decseq M\<close>]
  proof induction
    case (base \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  next
    case (step \<omega>) with disj[of \<omega> "M _"] show ?case by (auto intro: suntil.intros elim: suntil.cases)
  qed
qed

lemma inf_continuous_nxt[order_continuous_intros]: "inf_continuous P \<Longrightarrow> inf_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: inf_continuous_def image_comp)

lemma sup_continuous_nxt[order_continuous_intros]: "sup_continuous P \<Longrightarrow> sup_continuous (\<lambda>x. nxt (P x) \<omega>)"
  by (auto simp: sup_continuous_def image_comp)

lemma mcont_ennreal_of_enat: "mcont Sup (\<le>) Sup (\<le>) ennreal_of_enat"
  by (auto intro!: mcontI monotoneI contI ennreal_of_enat_Sup)

lemma mcont2mcont_ennreal_of_enat[cont_intro]:
  "mcont lub ord Sup (\<le>) f \<Longrightarrow> mcont lub ord Sup (\<le>) (\<lambda>x. ennreal_of_enat (f x))"
  by (auto intro: ccpo.mcont2mcont[OF complete_lattice_ccpo'] mcont_ennreal_of_enat)

declare stream.exhaust[cases type: stream]

lemma scount_eq_emeasure: "scount P \<omega> = emeasure (count_space UNIV) {i. P (sdrop i \<omega>)}"
proof cases
  assume "alw (ev P) \<omega>"
  moreover then have "infinite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: scount_infinite_iff[symmetric])
next
  assume "\<not> alw (ev P) \<omega>"
  moreover then have "finite {i. P (sdrop i \<omega>)}"
    using infinite_iff_alw_ev[of P \<omega>] by simp
  ultimately show ?thesis
    by (simp add: not_alw_iff not_ev_iff scount_eq_card)
qed

lemma measurable_scount[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "scount P \<in> measurable (stream_space M) (count_space UNIV)"
  unfolding scount_eq[abs_def] by measurable

lemma measurable_sfirst2:
  assumes [measurable]: "Measurable.pred (N \<Otimes>\<^sub>M stream_space M) (\<lambda>(x, \<omega>). P x \<omega>)"
  shows "(\<lambda>(x, \<omega>). sfirst (P x) \<omega>) \<in> measurable (N \<Otimes>\<^sub>M  stream_space M) (count_space UNIV)"
  apply (coinduction rule: measurable_enat_coinduct)
  apply simp
  apply (rule exI[of _ "\<lambda>x. 0"])
  apply (rule exI[of _ "\<lambda>(x, \<omega>). (x, stl \<omega>)"])
  apply (rule exI[of _ "\<lambda>(x, \<omega>). P x \<omega>"])
  apply (subst sfirst.simps[abs_def])
  apply (simp add: fun_eq_iff)
  done

lemma measurable_sfirst2'[measurable (raw)]:
  assumes [measurable (raw)]: "f \<in> N \<rightarrow>\<^sub>M stream_space M" "Measurable.pred (N \<Otimes>\<^sub>M stream_space M) (\<lambda>x. P (fst x) (snd x))"
  shows "(\<lambda>x. sfirst (P x) (f x)) \<in> measurable N (count_space UNIV)"
  using measurable_sfirst2[measurable] by measurable

lemma measurable_sfirst[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "sfirst P \<in> measurable (stream_space M) (count_space UNIV)"
  by measurable

lemma measurable_epred[measurable]: "epred \<in> count_space UNIV \<rightarrow>\<^sub>M count_space UNIV"
  by (rule measurable_count_space)

lemma nn_integral_stretch:
  "f \<in> borel \<rightarrow>\<^sub>M borel \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (\<integral>\<^sup>+x. f (c * x) \<partial>lborel) = (1 / \<bar>c\<bar>::real) * (\<integral>\<^sup>+x. f x \<partial>lborel)"
  using nn_integral_real_affine[of f c 0] by (simp add: mult.assoc[symmetric] ennreal_mult[symmetric])

lemma prod_sum_distrib:
  fixes f g :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::comm_semiring_1"
  assumes "finite I" shows "(\<And>i. i \<in> I \<Longrightarrow> finite (J i)) \<Longrightarrow> (\<Prod>i\<in>I. \<Sum>j\<in>J i. f i j) = (\<Sum>m\<in>Pi\<^sub>E I J. \<Prod>i\<in>I. f i (m i))"
  using \<open>finite I\<close>
proof induction
  case (insert i I) then show ?case
    by (auto simp: PiE_insert_eq finite_PiE sum.reindex inj_combinator sum.swap[of _ "Pi\<^sub>E I J"]
                   sum_cartesian_product' sum_distrib_left sum_distrib_right
             intro!: sum.cong prod.cong arg_cong[where f="(*) x" for x])
qed simp

lemma prod_add_distrib:
  fixes f g :: "'a \<Rightarrow> 'b::comm_semiring_1"
  assumes "finite I" shows "(\<Prod>i\<in>I. f i + g i) = (\<Sum>J\<in>Pow I. (\<Prod>i\<in>J. f i) * (\<Prod>i\<in>I - J. g i))"
proof -
  have "(\<Prod>i\<in>I. f i + g i) = (\<Prod>i\<in>I. \<Sum>b\<in>{True, False}. if b then f i else g i)"
    by simp
  also have "\<dots> = (\<Sum>m\<in>I \<rightarrow>\<^sub>E {True, False}. \<Prod>i\<in>I. if m i then f i else g i)"
    using \<open>finite I\<close> by (rule prod_sum_distrib) simp
  also have "\<dots> = (\<Sum>J\<in>Pow I. (\<Prod>i\<in>J. f i) * (\<Prod>i\<in>I - J. g i))"
    by (rule sum.reindex_bij_witness[where i="\<lambda>J. \<lambda>i\<in>I. i\<in>J" and j="\<lambda>m. {i\<in>I. m i}"])
       (auto simp: fun_eq_iff prod.If_cases \<open>finite I\<close> intro!: arg_cong2[where f="(*)"] prod.cong)
  finally show ?thesis .
qed

subclass (in linordered_nonzero_semiring) ordered_semiring_0
  proof qed

lemma (in linordered_nonzero_semiring) prod_nonneg: "(\<forall>a\<in>A. 0 \<le> f a) \<Longrightarrow> 0 \<le> prod f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in linordered_nonzero_semiring) prod_mono:
  "\<forall>i\<in>A. 0 \<le> f i \<and> f i \<le> g i \<Longrightarrow> prod f A \<le> prod g A"
  by (induct A rule: infinite_finite_induct) (auto intro!: prod_nonneg mult_mono)

lemma (in linordered_nonzero_semiring) prod_mono2:
  assumes "finite J" "I \<subseteq> J" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> g i \<and> g i \<le> f i" "(\<And>i. i \<in> J - I \<Longrightarrow> 1 \<le> f i)"
  shows "prod g I \<le> prod f J"
proof -
  have "prod g I = (\<Prod>i\<in>J. if i \<in> I then g i else 1)"
    using \<open>finite J\<close> \<open>I \<subseteq> J\<close> by (simp add: prod.If_cases Int_absorb1)
  also have "\<dots> \<le> prod f J"
    using assms by (intro prod_mono) auto
  finally show ?thesis .
qed

lemma (in linordered_nonzero_semiring) prod_mono3:
  assumes "finite J" "I \<subseteq> J" "\<And>i. i \<in> J \<Longrightarrow> 0 \<le> g i" "\<And>i. i \<in> I \<Longrightarrow> g i \<le> f i" "(\<And>i. i \<in> J - I \<Longrightarrow> g i \<le> 1)"
  shows "prod g J \<le> prod f I"
proof -
  have "prod g J \<le> (\<Prod>i\<in>J. if i \<in> I then f i else 1)"
    using assms by (intro prod_mono) auto
  also have "\<dots> = prod f I"
    using \<open>finite J\<close> \<open>I \<subseteq> J\<close> by (simp add: prod.If_cases Int_absorb1)
  finally show ?thesis .
qed

lemma (in linordered_nonzero_semiring) one_le_prod: "(\<And>i. i \<in> I \<Longrightarrow> 1 \<le> f i) \<Longrightarrow> 1 \<le> prod f I"
proof (induction I rule: infinite_finite_induct)
  case (insert i I) then show ?case
    using mult_mono[of 1 "f i" 1 "prod f I"]
    by (auto intro: order_trans[OF zero_le_one])
qed auto

lemma sum_plus_one_le_prod_plus_one:
  fixes p :: "'a \<Rightarrow> 'b::linordered_nonzero_semiring"
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> p i"
  shows "(\<Sum>i\<in>I. p i) + 1 \<le> (\<Prod>i\<in>I. p i + 1)"
proof cases
  assume [simp]: "finite I"
  with assms have [simp]: "J \<subseteq> I \<Longrightarrow> 0 \<le> prod p J" for J
    by (intro prod_nonneg) auto
  have "1 + (\<Sum>i\<in>I. p i) = (\<Sum>J\<in>insert {} ((\<lambda>x. {x})`I). (\<Prod>i\<in>J. p i) * (\<Prod>i\<in>I - J. 1))"
    by (subst sum.insert) (auto simp: sum.reindex)
  also have "\<dots> \<le> (\<Sum>J\<in>Pow I. (\<Prod>i\<in>J. p i) * (\<Prod>i\<in>I - J. 1))"
    using assms by (intro sum_mono2) auto
  finally show ?thesis
    by (subst prod_add_distrib) (auto simp: add.commute)
qed simp

lemma summable_iff_convergent_prod:
  fixes p :: "nat \<Rightarrow> real" assumes p: "\<And>i. 0 \<le> p i"
  shows "summable p \<longleftrightarrow> convergent (\<lambda>n. \<Prod>i<n. p i + 1)"
  unfolding summable_iff_convergent
proof
  assume "convergent (\<lambda>n. \<Prod>i<n. p i + 1)"
  then obtain x where x: "(\<lambda>n. \<Prod>i<n. p i + 1) \<longlonglongrightarrow> x"
    by (auto simp: convergent_def)
  then have "1 \<le> x"
    by (rule tendsto_lowerbound) (auto intro!: always_eventually one_le_prod p)

  have "convergent (\<lambda>n. 1 + (\<Sum>i<n. p i))"
  proof (intro Bseq_mono_convergent BseqI allI)
    show "0 < x" using \<open>1 \<le> x\<close> by auto
  next
    fix n
    have "norm ((\<Sum>i<n. p i) + 1) \<le> (\<Prod>i<n. p i + 1)"
      using p by (simp add: sum_nonneg sum_plus_one_le_prod_plus_one p)
    also have "\<dots> \<le> x"
      using assms
      by (intro tendsto_lowerbound[OF x])
          (auto simp: eventually_sequentially intro!: exI[of _ n] prod_mono2)
    finally show "norm (1 + sum p {..<n}) \<le> x"
      by (simp add: add.commute)
  qed (insert p, auto intro!: sum_mono2)
  then show "convergent (\<lambda>n. \<Sum>i<n. p i)"
    unfolding convergent_add_const_iff .
next
  assume "convergent (\<lambda>n. \<Sum>i<n. p i)"
  then obtain x where x: "(\<lambda>n. exp (\<Sum>i<n. p i)) \<longlonglongrightarrow> exp x"
    by (force simp: convergent_def intro!: tendsto_exp)
  show "convergent (\<lambda>n. \<Prod>i<n. p i + 1)"
  proof (intro Bseq_mono_convergent BseqI allI)
    show "0 < exp x" by simp
  next
    fix n
    have "norm (\<Prod>i<n. p i + 1) \<le> exp (\<Sum>i<n. p i)"
      using p exp_ge_add_one_self[of "p _"] by (auto simp add: prod_nonneg exp_sum add.commute intro!: prod_mono)
    also have "\<dots> \<le> exp x"
      using p
      by (intro tendsto_lowerbound[OF x]) (auto simp: eventually_sequentially intro!: sum_mono2 )
    finally show "norm (\<Prod>i<n. p i + 1) \<le> exp x" .
  qed (insert p, auto intro!: prod_mono2)
qed

primrec eexp :: "ereal \<Rightarrow> ennreal"
  where
    "eexp MInfty = 0"
  | "eexp (ereal r) = ennreal (exp r)"
  | "eexp PInfty = top"

lemma
  shows eexp_minus_infty[simp]: "eexp (-\<infinity>) = 0"
    and eexp_infty[simp]: "eexp \<infinity> = top"
  using eexp.simps by simp_all

lemma eexp_0[simp]: "eexp 0 = 1"
  by (simp add: zero_ereal_def)

lemma eexp_inj[simp]: "eexp x = eexp y \<longleftrightarrow> x = y"
  by (cases x; cases y; simp)

lemma eexp_mono[simp]: "eexp x \<le> eexp y \<longleftrightarrow> x \<le> y"
  by (cases x; cases y; simp add: top_unique)

lemma eexp_strict_mono[simp]: "eexp x < eexp y \<longleftrightarrow> x < y"
  by (simp add: less_le)

lemma exp_eq_0_iff[simp]: "eexp x = 0 \<longleftrightarrow> x = -\<infinity>"
  using eexp_inj[of x "-\<infinity>"] unfolding eexp_minus_infty .

lemma eexp_surj: "range eexp = UNIV"
proof -
  have part: "UNIV = {0} \<union> {0 <..< top} \<union> {top::ennreal}"
    by (auto simp: less_top)
  show ?thesis
    unfolding part
    by (force simp: image_iff less_top less_top_ennreal intro!: eexp.simps[symmetric] eexp.simps dest: exp_total)
qed

lemma continuous_on_eexp': "continuous_on UNIV eexp"
  by (rule continuous_onI_mono) (auto simp: eexp_surj)

lemma continuous_on_eexp[continuous_intros]: "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. eexp (f x))"
  by (rule continuous_on_compose2[OF continuous_on_eexp']) auto

lemma tendsto_eexp[tendsto_intros]: "(f \<longlongrightarrow> x) F \<Longrightarrow> ((\<lambda>x. eexp (f x)) \<longlongrightarrow> eexp x) F"
  by (rule continuous_on_tendsto_compose[OF continuous_on_eexp']) auto

lemma measurable_eexp[measurable]: "eexp \<in> borel \<rightarrow>\<^sub>M borel"
  using continuous_on_eexp' by (rule borel_measurable_continuous_onI)

lemma eexp_add: "\<not> ((x = \<infinity> \<and> y = -\<infinity>) \<or> (x = -\<infinity> \<and> y = \<infinity>)) \<Longrightarrow> eexp (x + y) = eexp x * eexp y"
  by (cases x; cases y; simp add: exp_add ennreal_mult ennreal_top_mult ennreal_mult_top)

lemma sum_Pinfty:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "sum f I = \<infinity> \<longleftrightarrow> (finite I \<and> (\<exists>i\<in>I. f i = \<infinity>))"
  by (induction I rule: infinite_finite_induct) auto

lemma sum_Minfty:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "sum f I = -\<infinity> \<longleftrightarrow> (finite I \<and> \<not> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<exists>i\<in>I. f i = -\<infinity>))"
  by (induction I rule: infinite_finite_induct)
     (auto simp: sum_Pinfty)

lemma eexp_sum: "\<not> (\<exists>i\<in>I. \<exists>j\<in>I. f i = -\<infinity> \<and> f j = \<infinity>) \<Longrightarrow> eexp (\<Sum>i\<in>I. f i) = (\<Prod>i\<in>I. eexp (f i))"
proof (induction I rule: infinite_finite_induct)
  case (insert i I)
  have "eexp (sum f (insert i I)) = eexp (f i) * eexp (sum f I)"
    using insert.prems insert.hyps by (auto simp: sum_Pinfty sum_Minfty intro!: eexp_add)
  then show ?case
    using insert by auto
qed simp_all

lemma eexp_suminf:
  assumes wf_f: "\<not> {-\<infinity>, \<infinity>} \<subseteq> range f" and f: "summable f"
  shows "(\<lambda>n. \<Prod>i<n. eexp (f i)) \<longlonglongrightarrow> eexp (\<Sum>i. f i)"
proof -
  have "(\<lambda>n. eexp (\<Sum>i<n. f i)) \<longlonglongrightarrow> eexp (\<Sum>i. f i)"
    by (intro tendsto_eexp summable_LIMSEQ f)
  also have "(\<lambda>n. eexp (\<Sum>i<n. f i)) = (\<lambda>n. \<Prod>i<n. eexp (f i))"
    using wf_f by (auto simp: fun_eq_iff image_iff eq_commute intro!: eexp_sum)
  finally show ?thesis .
qed

lemma continuous_onI_antimono:
  fixes f :: "'a::linorder_topology \<Rightarrow> 'b::{dense_order,linorder_topology}"
  assumes "open (f`A)"
    and mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> y \<Longrightarrow> f y \<le> f x"
  shows "continuous_on A f"
proof (rule continuous_on_generate_topology[OF open_generated_order], safe)
  have monoD: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f y < f x \<Longrightarrow> x < y"
    by (auto simp: not_le[symmetric] mono)
  have "\<exists>x. x \<in> A \<and> f x < b \<and> x < a" if a: "a \<in> A" and fa: "f a < b" for a b
  proof -
    obtain y where "f a < y" "{f a ..< y} \<subseteq> f`A"
      using open_right[OF \<open>open (f`A)\<close>, of "f a" b] a fa
      by auto
    obtain z where z: "f a < z" "z < min b y"
      using dense[of "f a" "min b y"] \<open>f a < y\<close> \<open>f a < b\<close> by auto
    then obtain c where "z = f c" "c \<in> A"
      using \<open>{f a ..< y} \<subseteq> f`A\<close>[THEN subsetD, of z] by (auto simp: less_imp_le)
    with a z show ?thesis
      by (auto intro!: exI[of _ c] simp: monoD)
  qed
  then show "\<exists>C. open C \<and> C \<inter> A = f -` {..<b} \<inter> A" for b
    by (intro exI[of _ "(\<Union>x\<in>{x\<in>A. f x < b}. {x <..})"])
       (auto intro: le_less_trans[OF mono] less_imp_le)

  have "\<exists>x. x \<in> A \<and> b < f x \<and> x > a" if a: "a \<in> A" and fa: "b < f a" for a b
  proof -
    note a fa
    moreover
    obtain y where "y < f a" "{y <.. f a} \<subseteq> f`A"
      using open_left[OF \<open>open (f`A)\<close>, of "f a" b]  a fa
      by auto
    then obtain z where z: "max b y < z" "z < f a"
      using dense[of "max b y" "f a"] \<open>y < f a\<close> \<open>b < f a\<close> by auto
    then obtain c where "z = f c" "c \<in> A"
      using \<open>{y <.. f a} \<subseteq> f`A\<close>[THEN subsetD, of z] by (auto simp: less_imp_le)
    with a z show ?thesis
      by (auto intro!: exI[of _ c] simp: monoD)
  qed
  then show "\<exists>C. open C \<and> C \<inter> A = f -` {b <..} \<inter> A" for b
    by (intro exI[of _ "(\<Union>x\<in>{x\<in>A. b < f x}. {..< x})"])
       (auto intro: less_le_trans[OF _ mono] less_imp_le)
qed

lemma minus_add_eq_ereal: "\<not> ((a = \<infinity> \<and> b = -\<infinity>) \<or> (a = -\<infinity> \<and> b = \<infinity>)) \<Longrightarrow> - (a + b::ereal) = -a - b"
  by (cases a; cases b; simp)

lemma setsum_negf_ereal: "\<not> {-\<infinity>, \<infinity>} \<subseteq> f`I \<Longrightarrow> (\<Sum>i\<in>I. - f i) = - (\<Sum>i\<in>I. f i::ereal)"
  by (induction I rule: infinite_finite_induct)
     (auto simp: minus_add_eq_ereal sum_Minfty sum_Pinfty,
      (subst minus_add_eq_ereal; auto simp: sum_Pinfty sum_Minfty image_iff minus_ereal_def)+)

lemma convergent_minus_iff_ereal: "convergent (\<lambda>x. - f x::ereal) \<longleftrightarrow> convergent f"
  unfolding convergent_def  by (metis ereal_uminus_uminus ereal_Lim_uminus)

lemma summable_minus_ereal: "\<not> {-\<infinity>, \<infinity>} \<subseteq> range f \<Longrightarrow> summable (\<lambda>n. f n) \<Longrightarrow> summable (\<lambda>n. - f n::ereal)"
  unfolding summable_iff_convergent
  by (subst setsum_negf_ereal) (auto simp: convergent_minus_iff_ereal)

lemma (in product_prob_space) product_nn_integral_component:
  assumes "f \<in> borel_measurable (M i)""i \<in> I"
  shows "integral\<^sup>N (Pi\<^sub>M I M) (\<lambda>x. f (x i)) = integral\<^sup>N (M i) f"
proof -
  from assms show ?thesis
    apply (subst PiM_component[symmetric, OF \<open>i \<in> I\<close>])
    apply (subst nn_integral_distr[OF measurable_component_singleton])
    apply simp_all
    done
qed

lemma ennreal_inverse_le[simp]: "inverse x \<le> inverse y \<longleftrightarrow> y \<le> (x::ennreal)"
  by (cases "0 < x"; cases x; cases "0 < y"; cases y; auto simp: top_unique inverse_ennreal)

lemma inverse_inverse_ennreal[simp]: "inverse (inverse x::ennreal) = x"
  by (cases "0 < x"; cases x; auto simp: inverse_ennreal)

lemma range_inverse_ennreal: "range inverse = (UNIV::ennreal set)"
proof -
  have "\<exists>x. y = inverse x" for y :: ennreal
    by (intro exI[of _ "inverse y"]) simp
  then show ?thesis
    unfolding surj_def by auto
qed

lemma continuous_on_inverse_ennreal': "continuous_on (UNIV :: ennreal set) inverse"
  by (rule continuous_onI_antimono) (auto simp: range_inverse_ennreal)

lemma sums_minus_ereal: "\<not> {- \<infinity>, \<infinity>} \<subseteq> f ` UNIV \<Longrightarrow> (\<lambda>n. - f n::ereal) sums x \<Longrightarrow> f sums - x"
  unfolding sums_def
  apply (subst ereal_Lim_uminus)
  apply (subst (asm) setsum_negf_ereal)
  apply auto
  done

lemma suminf_minus_ereal: "\<not> {- \<infinity>, \<infinity>} \<subseteq> f ` UNIV \<Longrightarrow> summable f \<Longrightarrow> (\<Sum>n. - f n :: ereal) = - suminf f"
  apply (rule sums_unique[symmetric])
  apply (rule sums_minus_ereal)
  apply (auto simp: ereal_uminus_eq_reorder)
  done

end
