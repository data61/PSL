(*  Title:      Infinite_Coin_Toss_Space.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Infinite coin toss space\<close>

text \<open>This section contains the formalization of the infinite coin toss space, i.e., the probability
space constructed on infinite sequences of independent coin tosses.\<close>

theory Infinite_Coin_Toss_Space imports Filtration Generated_Subalgebra Disc_Cond_Expect

begin

subsection \<open>Preliminary results\<close>

lemma decompose_init_prod:
  fixes n::nat
  shows "(\<Prod> i\<in> {0..n}. f i) = f 0 * (\<Prod> i\<in> {1..n}. f i)"
proof (cases "Suc 0 \<le> n")
  case True
  thus ?thesis
    by (metis One_nat_def Suc_le_D True prod.atLeast0_atMost_Suc_shift prod.atLeast_Suc_atMost_Suc_shift)
next
  case False
  thus ?thesis
    by (metis One_nat_def atLeastLessThanSuc_atLeastAtMost prod.atLeast0_lessThan_Suc_shift
        prod.atLeast_Suc_lessThan_Suc_shift)
qed


lemma Inter_nonempty_distrib:
  assumes "A \<noteq> {}"
  shows "\<Inter>A \<inter> B = (\<Inter> C\<in> A. (C\<inter> B))"
proof
  show "(\<Inter>C\<in>A. C \<inter> B) \<subseteq> \<Inter>A \<inter> B"
  proof
    fix x
    assume mem: "x \<in> (\<Inter>C\<in>A. C \<inter> B)"
    from \<open>A \<noteq> {}\<close> obtain C where "C\<in> A" by blast
    hence "x\<in> C\<inter> B" using mem by blast
    hence in1: "x\<in> B" by auto
    have "\<And>C. C\<in> A \<Longrightarrow> x \<in> C\<inter>B" using mem by blast
    hence "\<And>C. C\<in> A \<Longrightarrow> x\<in> C" by auto
    hence in2: "x\<in> \<Inter>A" by auto
    thus "x\<in> \<Inter>A \<inter> B" using in1 in2 by simp
  qed
qed auto



lemma enn2real_sum: shows "finite A \<Longrightarrow> (\<And>a. a\<in> A\<Longrightarrow> f a < top) \<Longrightarrow>enn2real (sum f A) = (\<Sum> a\<in> A. enn2real (f a))"
proof (induct rule:finite_induct)
  case empty
  thus ?case by simp
next
  case (insert a A)
  have "enn2real (sum f (insert a A)) = enn2real (f a + (sum f A))"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... = enn2real (f a) + enn2real (sum f A)"
    by (simp add: enn2real_plus insert.hyps(1) insert.prems)
  also have "... = enn2real (f a) + (\<Sum> a\<in> A. enn2real (f a))"
    by (simp add: insert.hyps(3) insert.prems)
  also have "... = (\<Sum> a\<in> (insert a A). enn2real (f a))"
    by (metis calculation insert.hyps(1) insert.hyps(2) sum.insert)
  finally show ?case .
qed

lemma ennreal_sum: shows "finite A \<Longrightarrow> (\<And>a. 0 \<le> f a) \<Longrightarrow> (\<Sum>a\<in> A. ennreal (f a)) = ennreal (\<Sum>a\<in> A. f a)"
proof (induct rule:finite_induct)
  case empty
  thus ?case by simp
next
  case (insert a A)
  have "(\<Sum>a\<in> (insert a A). ennreal (f a)) = ennreal (f a) + (\<Sum>a\<in> A. ennreal (f a))"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... = ennreal (f a) + ennreal (\<Sum>a\<in> A. f a)"
    by (simp add: insert.prems)
  also have "... = ennreal (f a + (\<Sum>a\<in> A. f a))"
    by (simp add: insert.prems sum_nonneg)
  also have "... = ennreal (\<Sum>a\<in> (insert a A). (f a))"
    using insert.hyps(1) insert.hyps(2) by auto
  finally show ?case .
qed


lemma stake_snth:
  assumes "stake n w = stake n x"
  shows "Suc i \<le> n \<Longrightarrow> snth w i = snth x i"
by (metis Suc_le_eq assms stake_nth)

lemma stake_snth_charact:
  assumes "stake n w = stake n x"
  shows "\<forall>i < n. snth w i = snth x i"
proof (intro allI impI)
  fix i
  assume "i < n"
  thus "snth w i = snth x i" using Suc_leI assms stake_snth by blast
qed

lemma stake_snth':
  shows "(\<And>i. Suc i \<le> n \<Longrightarrow> snth w i = snth x i) \<Longrightarrow>stake n w = stake n x"
proof (induct n arbitrary:w x)
case 0
  then show ?case by auto
next
case (Suc n)
  hence mh: "\<And>i. Suc i \<le> Suc n \<Longrightarrow> w !! i = x !! i" by auto
  hence seq:"snth w n = snth x n"  by auto
  have "stake n w = stake n x" using mh Suc by (meson Suc_leD Suc_le_mono)
  thus "stake (Suc n) w = stake (Suc n) x" by (metis seq stake_Suc)
qed

lemma  stake_inter_snth:
  fixes x
  assumes "Suc 0 \<le> n"
  shows "{w\<in> space M. (stake n w = stake n x)} = (\<Inter> i \<in> {0.. n-1}. {w\<in> space M. (snth w i = snth x i)})"
proof
  let ?S =  "{w\<in> space M. (stake n w = stake n x)}"
  show "?S \<subseteq> (\<Inter>i\<in>{0..n-1}. {w \<in> space M. w !! i = x !! i})" using stake_snth assms by fastforce
  show "(\<Inter>i\<in>{0..n-1}. {w \<in> space M. w !! i = x !! i}) \<subseteq> ?S"
  proof
    fix w
    assume inter: "w \<in> (\<Inter>i\<in>{0..n-1}. {w \<in> space M. w !! i = x !! i})"
    have "\<forall> i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> snth w i = snth x i"
    proof (intro allI impI)
      fix i
      assume "0 \<le> i \<and> i \<le> n-1"
      thus "snth w i = snth x i" using inter by auto
    qed
    hence "stake n w = stake n x"
      by (metis One_nat_def Suc_le_D diff_Suc_Suc diff_is_0_eq diff_zero le0 stake_snth')
    thus "w\<in> ?S" using inter by auto
  qed
qed

lemma streams_stake_set:
  shows "pw \<in> streams A \<Longrightarrow> set (stake n pw) \<subseteq> A"
proof (induct n arbitrary: pw)
  case (Suc n) note hyp = this
  have "set (stake (Suc 0) pw) \<subseteq> A"
  proof -
    have "shd pw \<in> A" using hyp  streams_shd[of pw A] by simp
    have "stake (Suc 0) pw = [shd pw]" by auto
    hence "set (stake (Suc 0) pw) = {shd pw}" by auto
    thus ?thesis using \<open>shd pw \<in> A\<close> by auto
  qed
  thus ?case by (simp add: Suc.hyps Suc.prems streams_stl)
qed simp


lemma stake_finite_universe_induct:
  assumes "finite A"
  and "A \<noteq> {}"
  shows "(stake (Suc n) `(streams A)) = {s#w| s w. s\<in> A \<and> w\<in> (stake n `(streams A))}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix l::"'a list"
    assume "l\<in> ?L"
    hence "\<exists>pw. pw \<in> streams A \<and> l = stake (Suc n) pw" by auto
    from this obtain pw where "pw \<in> streams A" and  "l = stake (Suc n) pw" by blast
    hence "l = shd pw # stake n (stl pw)" unfolding stake_def by auto
    thus "l\<in> ?R" by (simp add: \<open>pw \<in> streams A\<close> streams_shd streams_stl)
  qed
  show "?R \<subseteq> ?L"
  proof
    fix l::"'a list"
    assume "l\<in> ?R"
    hence "\<exists> s w. s\<in> A \<and> w\<in> (stake n `(streams A)) \<and> l = s# w" by auto
    from this obtain s and w where "s\<in> A" and "w\<in> (stake n `(streams A))" and "l = s# w" by blast
      note swprop = this
    have "\<exists>pw. pw \<in> streams A \<and> w = stake n pw" using swprop by auto
    from this obtain pw where "pw\<in> streams A" and "w = stake n pw" by blast note pwprop = this
    have "l \<in> lists A"
    proof -
      have "s\<in> A" using swprop by simp
      have "set w \<subseteq> A" using pwprop streams_stake_set by simp
      have "set l = set w \<union> {s}" using swprop by auto
      thus ?thesis using \<open>s\<in> A\<close> \<open>set w \<subseteq> A\<close> by auto
    qed
    have "\<exists>x. x \<in> A" using assms by auto
    from this obtain x where "x\<in> A" by blast
    let ?sx = "sconst x"
    let ?st = "shift l ?sx"
    have "l = stake (Suc n) ?st" by (simp add: pwprop(2) stake_shift swprop(3))
    have "sset ?sx = {x}" by simp
    hence "sset ?sx \<subseteq> A" using \<open>x\<in> A\<close> by simp
    hence "?sx \<in> streams A" using sset_streams[of "sconst x"] by simp
    hence "?st \<in> streams A" using \<open>l \<in> lists A\<close> shift_streams[of l A "sconst x"] by simp
    thus "l\<in> ?L" using \<open>l = stake (Suc n) ?st\<close> by blast
  qed
qed


lemma stake_finite_universe_finite:
  assumes "finite A"
  and "A \<noteq> {}"
  shows "finite (stake n `(streams A))"
proof (induction n)
  let ?L = "(stake 0 `(streams A))"
  have "streams A \<noteq> {}"
  proof
    assume "streams A = {}"
    have "\<exists>x. x \<in> A" using assms by auto
    from this obtain x where "x\<in> A" by blast
    let ?sx = "sconst x"
    have "sset ?sx = {x}" by simp
    hence "sset ?sx \<subseteq> A" using \<open>x\<in> A\<close> by simp
    hence "?sx \<in> streams A" using sset_streams[of "sconst x"] by simp
    thus False using \<open>streams A = {}\<close> by simp
  qed
  have "stake 0 = (\<lambda>s. [])" unfolding stake_def by simp
  hence "?L = {[]}" using \<open>streams A \<noteq> {}\<close> by auto
  show "finite (stake 0 `(streams A))" by (simp add: \<open>?L = {[]}\<close> image_constant_conv)
next
  fix n assume "finite (stake n `(streams A))" note hyp = this
  have "(stake (Suc n) `(streams A)) = {s#w| s w. s\<in> A \<and> w\<in> (stake n `(streams A))}" (is "?L = ?R")
  using assms stake_finite_universe_induct[of A n] by simp
  have "finite ?R"  by (simp add: assms(1) finite_image_set2 hyp)
  thus "finite ?L" using \<open>?L = ?R\<close>by simp
qed


lemma  diff_streams_only_if:
  assumes "w \<noteq> x"
  shows "\<exists>n. snth w n \<noteq> snth x n"
proof -
  have f1: "smap (\<lambda>n. x !! (n - Suc 0)) (fromN (Suc 0)) \<noteq> w"
    by (metis assms stream_smap_fromN)
  obtain nn :: "'a stream \<Rightarrow> nat stream \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat" where
    "\<forall>x0 x1 x2. (\<exists>v3. x2 (x1 !! v3) \<noteq> x0 !! v3) = (x2 (x1 !! nn x0 x1 x2) \<noteq> x0 !! nn x0 x1 x2)"
    by moura
  then have "x !! (fromN (Suc 0) !! nn w (fromN (Suc 0)) (\<lambda>n. x !! (n - Suc 0)) - Suc 0) \<noteq> w !! nn w (fromN (Suc 0)) (\<lambda>n. x !! (n - Suc 0))"
    using f1 by (meson smap_alt)
  then show ?thesis
    by (metis (no_types) snth_smap stream_smap_fromN)
qed

lemma diff_streams_if:
  assumes "\<exists>n. snth w n \<noteq> snth x n"
  shows "w\<noteq> x"
  using assms by auto

lemma sigma_set_union_count:
  assumes "\<forall> y\<in> A. B y \<in> sigma_sets X Y"
and "countable A"
  shows "(\<Union> y\<in> A. B y) \<in> sigma_sets X Y"
  by (metis (mono_tags, lifting) assms countable_image imageE sigma_sets_UNION)

lemma sigma_set_inter_init:
  assumes "\<And>i. i\<le>(n::nat) \<Longrightarrow> A i \<in> sigma_sets sp B"
and "B \<subseteq> Pow sp"
shows "(\<Inter> i\<in> {m. m\<le> n}. A i) \<in> sigma_sets sp B"
  by (metis (full_types) assms(1) assms(2) bot.extremum empty_iff mem_Collect_eq sigma_sets_INTER)



lemma  adapt_sigma_sets:
assumes "\<And>i. i \<le> n\<Longrightarrow> (X i) \<in> measurable M N"
shows "sigma_algebra (space M) (sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}))"
proof (rule sigma_algebra_sigma_sets)
  show "(\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}) \<subseteq> Pow (space M)"
  proof (rule UN_subset_iff[THEN iffD2], intro ballI)
    fix i
    assume "i \<in> {m. m\<le> n}"
    show "{X i -` A \<inter> space M |A. A \<in> sets N} \<subseteq> Pow (space M)" by auto
  qed
qed

subsection \<open>Bernoulli streams\<close>

text \<open>Bernoulli streams represent the formal definition of the infinite coin toss space. The parameter
\<open>p\<close> represents the probability of obtaining a head after a coin toss.\<close>

definition bernoulli_stream::"real \<Rightarrow> (bool stream) measure" where
  "bernoulli_stream p = stream_space (measure_pmf (bernoulli_pmf p))"


lemma bernoulli_stream_space:
  assumes "N = bernoulli_stream p"
  shows "space N = streams UNIV::bool"
using assms unfolding bernoulli_stream_def stream_space_def
by (simp add: assms bernoulli_stream_def space_stream_space)

lemma bernoulli_stream_preimage:
  assumes "N = bernoulli_stream p"
  shows "f -` A \<inter> (space N) = f-`A"
using assms by (simp add: bernoulli_stream_space)

lemma  bernoulli_stream_component_probability:
  assumes "N = bernoulli_stream p" and "0 \<le> p" and "p \<le> 1"
  shows "\<forall> n. emeasure N {w\<in> space N. (snth w n)} = p"
proof
  have "prob_space N" using assms by (simp add: bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
  fix n::nat
  let ?S = "{w\<in> space N. (snth w n)}"
  have s: "?S \<in> sets N"
  proof -
    have "(\<lambda>w. snth w n) \<in> measurable N (measure_pmf (bernoulli_pmf p))" using assms by (simp add: bernoulli_stream_def)
    moreover have "{True} \<in> sets (measure_pmf (bernoulli_pmf p))" by simp
    ultimately show ?thesis by simp
  qed
  let ?PM = "(\<lambda>i::nat. (measure_pmf (bernoulli_pmf p)))"
  have isps: "product_prob_space ?PM" by unfold_locales
  let ?Z = "{X::nat\<Rightarrow>bool. X n = True}"
  let ?wPM = "Pi\<^sub>M UNIV ?PM"
  have "space ?wPM = UNIV" using space_PiM by fastforce
  hence "(to_stream -` ?S \<inter> (space ?wPM)) = to_stream -` ?S" by simp
  also have "... = ?Z" using assms by (simp add:bernoulli_stream_space to_stream_def)
  also have "... = prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))"
  proof
    {
      fix X
      assume "X \<in> prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))"
      hence "restrict X {n} \<in> (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))" using prod_emb_iff[of X] by simp
      hence "X n = True"
        unfolding PiE_iff by auto
      hence "X \<in> ?Z" by simp
    }
    thus "prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True})) \<subseteq> ?Z" by auto
    {
      fix X
      assume "X \<in> ?Z"
      hence "X n = True" by simp
      hence "restrict X {n} \<in> (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))"
        unfolding PiE_iff by auto
      moreover have "X \<in> extensional UNIV" by simp
      moreover have "\<forall>i \<in> UNIV. X i \<in> space (?PM i)" by auto
      ultimately have "X \<in> prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))" using prod_emb_iff[of X] by simp
    }
    thus "?Z \<subseteq> prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))" by auto
  qed
  finally have inteq: "(to_stream -` ?S \<inter> (space ?wPM)) = prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True}))" .
  have "emeasure N ?S = emeasure ?wPM (to_stream -` ?S \<inter> (space ?wPM))"
    using assms emeasure_distr[of "to_stream" ?wPM "(vimage_algebra (streams (space (measure_pmf (bernoulli_pmf p)))) (!!)
           (Pi\<^sub>M UNIV (\<lambda>i. measure_pmf (bernoulli_pmf p))))" ?S] measurable_to_stream[of "(measure_pmf (bernoulli_pmf p))"] s
    unfolding bernoulli_stream_def stream_space_def  by auto
  also have "... = emeasure ?wPM (prod_emb UNIV ?PM {n} (Pi\<^sub>E {n} (\<lambda>x::nat. {True})))" using inteq by simp
  also have "... =
    (\<Prod>i\<in>{n}. emeasure (?PM i) ((\<lambda>x::nat. {True}) i))" using isps
    by (auto simp add: product_prob_space.emeasure_PiM_emb simp del: ext_funcset_to_sing_iff)
  also have "... = emeasure (?PM n) {True}" by simp
  also have "... = p" using assms by (simp add: emeasure_pmf_single)
  finally show "emeasure N ?S = p" .
qed


lemma  bernoulli_stream_component_probability_compl:
  assumes "N = bernoulli_stream p" and "0 \<le> p" and "p \<le> 1"
  shows "\<forall> n. emeasure N {w\<in> space N. \<not>(snth w n)} = 1- p"
proof
  fix n
  let ?A = "{w \<in> space N. \<not> w !! n}"
  let ?B = "{w \<in> space N. w !! n}"
  have "?A \<union> ?B = space N" by auto
  have "?A\<inter>?B = {}" by auto
  hence eqA: "?A = (?A\<union> ?B) - ?B" using Diff_cancel by blast
  moreover have "?A \<in> sets N"
  proof -
    have "(\<lambda>w. snth w n) \<in> measurable N (measure_pmf (bernoulli_pmf p))" using assms by (simp add: bernoulli_stream_def)
    moreover have "{True} \<in> sets (measure_pmf (bernoulli_pmf p))" by simp
    ultimately show ?thesis by simp
  qed
  moreover have "?B \<in> sets N"
  proof -
    have "(\<lambda>w. snth w n) \<in> measurable N (measure_pmf (bernoulli_pmf p))" using assms by (simp add: bernoulli_stream_def)
    moreover have "{True} \<in> sets (measure_pmf (bernoulli_pmf p))" by simp
    ultimately show ?thesis by simp
  qed
  ultimately have "emeasure N ((?A\<union> ?B) - ?B) = emeasure N (?A\<union> ?B) - emeasure N ?B"
  proof -
    have f1: "\<And>S m. (S::bool stream set) \<notin> sets m \<or> emeasure m S = \<top> \<or> emeasure m (space m) - emeasure m S = emeasure m (space m - S)"
      by (metis emeasure_compl infinity_ennreal_def)
    have "emeasure N {s \<in> space N. s !! n} \<noteq> \<top>"
      using assms(1) assms(2) assms(3) ennreal_neq_top bernoulli_stream_component_probability by presburger
    then have "emeasure N (space N) - emeasure N {s \<in> space N. s !! n} = emeasure N (space N - {s \<in> space N. s !! n})"
      using f1 \<open>{w \<in> space N. w !! n} \<in> sets N\<close> by blast
    then show ?thesis
      using \<open>{w \<in> space N. \<not> w !! n} \<union> {w \<in> space N. w !! n} = space N\<close> by presburger
  qed
  hence "emeasure N ?A = emeasure N (?A\<union> ?B) - emeasure N ?B" using eqA by simp
  also have "... = 1 - emeasure N ?B"
    by (metis (no_types, lifting) \<open>?A \<union> ?B = space N\<close> assms(1) bernoulli_stream_def
      prob_space.emeasure_space_1 prob_space.prob_space_stream_space prob_space_measure_pmf)
  also have "... = 1 - p" using bernoulli_stream_component_probability[of N p] assms
    by (metis (mono_tags) ennreal_1 ennreal_minus_if)
  finally show "emeasure N ?A = 1 - p" .
qed

lemma bernoulli_stream_sets:
  assumes "0 < q"
  and "q < 1"
  and "0 < p"
  and "p < 1"
shows "sets (bernoulli_stream p) = sets (bernoulli_stream q)" unfolding bernoulli_stream_def
by (rule sets_stream_space_cong, simp)


locale infinite_coin_toss_space =
  fixes p::real and M::"bool stream measure"
  assumes p_gt_0: "0 \<le> p"
  and p_lt_1: "p \<le> 1"
  and bernoulli: "M = bernoulli_stream p"



sublocale infinite_coin_toss_space \<subseteq> prob_space
by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)

subsection \<open>Natural filtration on the infinite coin toss space\<close>

text \<open>The natural filtration on the infinite coin toss space is the discrete filtration @{term F}
such that @{term "F n"} represents the restricted measure space in which the outcome of the first
@{term n} coin tosses is known.\<close>

subsubsection \<open>The projection function\<close>

text \<open>Intuitively, the restricted measure space in which the outcome of the first @{term n} coin tosses is known
can be defined by any measurable function that maps all infinite sequences that agree on the first
@{term n} coin tosses to the same element.\<close>

definition (in infinite_coin_toss_space) pseudo_proj_True:: "nat \<Rightarrow> bool stream \<Rightarrow> bool stream" where
  "pseudo_proj_True n  = (\<lambda>w. shift (stake n w) (sconst True))"

definition (in infinite_coin_toss_space) pseudo_proj_False:: "nat \<Rightarrow> bool stream \<Rightarrow> bool stream" where
  "pseudo_proj_False n  = (\<lambda>w. shift (append (stake n w) [False]) (sconst True))"



lemma (in infinite_coin_toss_space) pseudo_proj_False_neq_True:
  shows "pseudo_proj_False n w \<noteq> pseudo_proj_True n w"
proof (rule diff_streams_if, intro exI)
  have "snth (pseudo_proj_False n w) n = False" unfolding pseudo_proj_False_def by simp
  moreover have "snth (pseudo_proj_True n w) n = True" unfolding pseudo_proj_True_def by simp
  ultimately show "snth (pseudo_proj_False n w) n \<noteq> snth (pseudo_proj_True n w) n" by simp
qed


lemma (in infinite_coin_toss_space) pseudo_proj_False_measurable:
  shows "pseudo_proj_False n \<in> measurable (bernoulli_stream p) (bernoulli_stream p)"
proof -
  let ?N = "bernoulli_stream p"
  have "id \<in> measurable ?N ?N" by simp
  moreover have "(\<lambda>w. (sconst True)) \<in> measurable ?N ?N"  using bernoulli_stream_space  by simp
  ultimately show ?thesis using measurable_shift  p_gt_0 p_lt_1
    unfolding bernoulli_stream_def pseudo_proj_False_def by simp
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_stake:
  shows "stake n (pseudo_proj_True n w) = stake n w" by (simp add: pseudo_proj_True_def stake_shift)

lemma (in infinite_coin_toss_space) pseudo_proj_False_stake:
  shows "stake n (pseudo_proj_False n w) = stake n w" by (simp add: pseudo_proj_False_def stake_shift)

lemma (in infinite_coin_toss_space) pseudo_proj_True_stake_image:
  assumes "(stake n w) = stake n x"
  shows "pseudo_proj_True n w = pseudo_proj_True n x" by (simp add: assms pseudo_proj_True_def)

lemma (in infinite_coin_toss_space) pseudo_proj_True_prefix:
  assumes "n \<le> m"
  and "pseudo_proj_True m x = pseudo_proj_True m y"
  shows "pseudo_proj_True n x = pseudo_proj_True n y"
by (metis assms diff_is_0_eq id_stake_snth_sdrop length_stake pseudo_proj_True_def stake.simps(1) stake_shift)

lemma (in infinite_coin_toss_space) pseudo_proj_True_measurable:
  shows "pseudo_proj_True n \<in> measurable (bernoulli_stream p) (bernoulli_stream p)"
proof -
  let ?N = "bernoulli_stream p"
  have "id \<in> measurable ?N ?N" by simp
  moreover have "(\<lambda>w. (sconst True)) \<in> measurable ?N ?N"  using bernoulli_stream_space  by simp
  ultimately show ?thesis using measurable_shift p_gt_0 p_lt_1
    unfolding bernoulli_stream_def pseudo_proj_True_def by simp
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_finite_image:
  shows "finite (range (pseudo_proj_True n))"
proof -
  let ?U = "UNIV::bool set"
  have "?U = {True, False}" by auto
  hence "finite ?U"  by simp
  moreover have "?U \<noteq> {}" by auto
  ultimately have fi: "finite (stake n `streams ?U)" using stake_finite_universe_finite[of ?U] by simp
  let ?sh= "(\<lambda>l. shift l (sconst True))"
  have "finite {?sh l|l. l\<in>(stake n `streams ?U)}" using fi by simp
  moreover have "{?sh l|l. l\<in>(stake n `streams ?U)} = range (pseudo_proj_True n)" unfolding pseudo_proj_True_def by auto
  ultimately show ?thesis by simp
qed

lemma (in infinite_coin_toss_space) pseudo_proj_False_finite_image:
  shows "finite (range (pseudo_proj_False n))"
proof -
  let ?U = "UNIV::bool set"
  have "?U = {True, False}" by auto
  hence "finite ?U"  by simp
  moreover have "?U \<noteq> {}" by auto
  ultimately have fi: "finite (stake n `streams ?U)" using stake_finite_universe_finite[of ?U] by simp
  let ?sh= "(\<lambda>l. shift (l @ [False]) (sconst True))"
  have "finite {?sh l|l. l\<in>(stake n `streams ?U)}" using fi by simp
  moreover have "{?sh l|l. l\<in>(stake n `streams ?U)} = range (pseudo_proj_False n)" unfolding pseudo_proj_False_def by auto
  ultimately show ?thesis by simp
qed


lemma (in infinite_coin_toss_space) pseudo_proj_True_proj:
  shows "pseudo_proj_True n (pseudo_proj_True n w) = pseudo_proj_True n w"
by (metis pseudo_proj_True_def pseudo_proj_True_stake)

lemma (in infinite_coin_toss_space) pseudo_proj_True_Suc_False_proj:
  shows "pseudo_proj_True (Suc n) (pseudo_proj_False n w) = pseudo_proj_False n w"
by (metis append_Nil2 cancel_comm_monoid_add_class.diff_cancel length_append_singleton length_stake order_refl pseudo_proj_False_def pseudo_proj_True_def stake.simps(1) stake_shift take_all)



lemma (in infinite_coin_toss_space) pseudo_proj_True_Suc_proj:
  shows "pseudo_proj_True (Suc n) (pseudo_proj_True n w) = pseudo_proj_True n w"
by (metis id_apply id_stake_snth_sdrop pseudo_proj_True_def pseudo_proj_True_stake shift_left_inj siterate.code stake_sdrop stream.sel(2))

lemma (in infinite_coin_toss_space) pseudo_proj_True_proj_Suc:
  shows "pseudo_proj_True n (pseudo_proj_True (Suc n) w) = pseudo_proj_True n w"
by (meson Suc_n_not_le_n nat_le_linear pseudo_proj_True_prefix pseudo_proj_True_stake pseudo_proj_True_stake_image)

lemma (in infinite_coin_toss_space) pseudo_proj_True_shift:
  shows "length l = n \<Longrightarrow> pseudo_proj_True n (shift l (sconst True)) = shift l (sconst True)"
by (simp add: pseudo_proj_True_def stake_shift)


lemma (in infinite_coin_toss_space) pseudo_proj_True_suc_img:
  shows "pseudo_proj_True (Suc n) w \<in> {pseudo_proj_True n w, pseudo_proj_False n w}"
by (metis (full_types) cycle_decomp insertCI list.distinct(1) pseudo_proj_True_def pseudo_proj_False_def sconst_cycle shift_append stake_Suc)



lemma (in infinite_coin_toss_space) measurable_snth_count_space:
  shows "(\<lambda>w. snth w n) \<in> measurable (bernoulli_stream p) (count_space (UNIV::bool set))"
by (simp add: bernoulli_stream_def)



lemma (in infinite_coin_toss_space) pseudo_proj_True_same_img:
  assumes "pseudo_proj_True n w = pseudo_proj_True n x"
  shows "stake n w = stake n x" by (metis assms pseudo_proj_True_stake)


lemma (in infinite_coin_toss_space) pseudo_proj_True_snth:
  assumes "pseudo_proj_True n x  = pseudo_proj_True n w"
  shows "\<And>i. Suc i \<le> n \<Longrightarrow>  snth x i = snth w i"
proof -
  fix i
  have "stake n w= stake n x" using assms by (metis pseudo_proj_True_stake)
  assume "Suc i \<le> n"
  thus "snth x i = snth w i" using \<open>stake n w = stake n x\<close> stake_snth by auto
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_snth':
  assumes "(\<And>i. Suc i \<le> n \<Longrightarrow>  snth w i = snth x i)"
  shows "pseudo_proj_True n w  = pseudo_proj_True n x"
proof -
  have "stake n w = stake n x" using stake_snth'[of n w x] using assms by simp
  moreover have "stake n w = stake n x \<Longrightarrow> pseudo_proj_True n w = pseudo_proj_True n x" using pseudo_proj_True_stake_image[of n w x] by simp
  ultimately show ?thesis by auto
qed


lemma (in infinite_coin_toss_space) pseudo_proj_True_preimage:
  assumes "w = pseudo_proj_True n w"
  shows "(pseudo_proj_True n) -` {w} = (\<Inter>i\<in> {m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
proof
  show "(pseudo_proj_True n) -` {w} \<subseteq> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
  proof
    fix x
    assume "x \<in> (pseudo_proj_True n) -`{w}"
    hence "pseudo_proj_True n x = pseudo_proj_True n w" using assms by auto
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> x  \<in> (\<lambda>x. snth x i) -`{snth w i}"
      by (metis (mono_tags) Suc_le_eq mem_Collect_eq
      pseudo_proj_True_stake stake_nth vimage_singleton_eq)
    thus "x \<in> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})" by auto
  qed
  show "(\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i}) \<subseteq> (pseudo_proj_True n) -` {w}"
  proof
    fix x
    assume "x\<in> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> x  \<in> (\<lambda>x. snth x i) -`{snth w i}" by simp
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> snth x i = snth w i" by simp
    hence "\<And>i. Suc i \<le> n \<Longrightarrow> snth x i = snth w i" by auto
    hence "pseudo_proj_True n x = pseudo_proj_True n w" using pseudo_proj_True_snth'[of n x w] by simp
    also have "... = w" using assms by simp
    finally have "pseudo_proj_True n x = w" .
    thus "x \<in> (pseudo_proj_True n) -`{w}"  by auto
  qed
qed


lemma (in infinite_coin_toss_space) pseudo_proj_False_preimage:
  assumes "w = pseudo_proj_False n w"
  shows "(pseudo_proj_False n) -` {w} = (\<Inter>i\<in> {m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
proof
  show "(pseudo_proj_False n) -` {w} \<subseteq> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
  proof
    fix x
    assume "x \<in> (pseudo_proj_False n) -`{w}"
    hence "pseudo_proj_False n x = pseudo_proj_False n w" using assms by auto
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> x  \<in> (\<lambda>x. snth x i) -`{snth w i}"
      by (metis (mono_tags) Suc_le_eq mem_Collect_eq
      pseudo_proj_False_stake stake_nth vimage_singleton_eq)
    thus "x \<in> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})" by auto
  qed
  show "(\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i}) \<subseteq> (pseudo_proj_False n) -` {w}"
  proof
    fix x
    assume "x\<in> (\<Inter>i\<in>{m. Suc m \<le> n}. (\<lambda>w. snth w i) -` {snth w i})"
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> x  \<in> (\<lambda>x. snth x i) -`{snth w i}" by simp
    hence "\<And>i. i \<in>{m. Suc m \<le> n} \<Longrightarrow> snth x i = snth w i" by simp
    hence "\<And>i. Suc i \<le> n \<Longrightarrow> snth x i = snth w i" by auto
    hence "pseudo_proj_False n x = pseudo_proj_False n w"
      by (metis (full_types) pseudo_proj_False_def stake_snth')
    also have "... = w" using assms by simp
    finally have "pseudo_proj_False n x = w" .
    thus "x \<in> (pseudo_proj_False n) -`{w}"  by auto
  qed
qed



lemma (in infinite_coin_toss_space) pseudo_proj_True_preimage_stake:
  assumes "w = pseudo_proj_True n w"
  shows "(pseudo_proj_True n) -` {w} = {x. stake n x = stake n w}"
proof
  show "{x. stake n x = stake n w} \<subseteq> (pseudo_proj_True n) -` {w}"
  proof
    fix x
    assume "x \<in> {x. stake n x = stake n w}"
    hence "stake n x = stake n w" by auto
    hence "pseudo_proj_True n x = w" using assms pseudo_proj_True_def by auto
    thus "x \<in> (pseudo_proj_True n) -` {w}" by auto
  qed
  show "(pseudo_proj_True n) -` {w} \<subseteq> {x. stake n x = stake n w}"
  proof
    fix x
    assume "x\<in> pseudo_proj_True n -`{w}"
    hence "pseudo_proj_True n x = pseudo_proj_True n w" using assms by auto
    hence "stake n x = stake n w" by (metis pseudo_proj_True_stake)
    thus "x\<in> {x. stake n x = stake n w}" by simp
  qed
qed

lemma (in infinite_coin_toss_space) pseudo_proj_False_preimage_stake:
  assumes "w = pseudo_proj_False n w"
  shows "(pseudo_proj_False n) -` {w} = {x. stake n x = stake n w}"
proof
  show "{x. stake n x = stake n w} \<subseteq> (pseudo_proj_False n) -` {w}"
  proof
    fix x
    assume "x \<in> {x. stake n x = stake n w}"
    hence "stake n x = stake n w" by auto
    hence "pseudo_proj_False n x = w" using assms pseudo_proj_False_def by auto
    thus "x \<in> (pseudo_proj_False n) -` {w}" by auto
  qed
  show "(pseudo_proj_False n) -` {w} \<subseteq> {x. stake n x = stake n w}"
  proof
    fix x
    assume "x\<in> pseudo_proj_False n -`{w}"
    hence "pseudo_proj_False n x = pseudo_proj_False n w" using assms by auto
    hence "stake n x = stake n w" by (metis pseudo_proj_False_stake)
    thus "x\<in> {x. stake n x = stake n w}" by simp
  qed
qed


lemma (in infinite_coin_toss_space) pseudo_proj_True_preimage_stake_space:
  assumes "w = pseudo_proj_True n w"
  shows "(pseudo_proj_True n) -` {w} \<inter> space M = {x\<in> space M. stake n x = stake n w}"
proof -
  have "(pseudo_proj_True n) -` {w} = {x. stake n x = stake n w}" using assms
    by (simp add:pseudo_proj_True_preimage_stake)
  hence "(pseudo_proj_True n) -` {w}\<inter> space M = {x. stake n x = stake n w}\<inter> space M"
    by simp
  also have "... = {x\<in> space M. stake n x = stake n w}" by auto
  finally show ?thesis .
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_singleton:
  assumes "w = pseudo_proj_True n w"
  shows "(pseudo_proj_True n) -`{w} \<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
proof (cases "{m. (Suc m) \<le> n} = {}")
case False
  have "\<And>i. (\<lambda>x. snth x i) \<in> measurable (bernoulli_stream p) (count_space UNIV)" by (simp add: measurable_snth_count_space)
  have fi: "\<And>i. Suc i \<le> n \<Longrightarrow> (\<lambda>w. snth w i) -` {snth w i} \<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
  proof -
    fix i
    assume "Suc i \<le> n"
    have "(\<lambda>x. snth x i) \<in> measurable (bernoulli_stream p) (count_space UNIV)" by (simp add: measurable_snth_count_space)
    moreover have "{snth w i} \<in> sets (count_space UNIV)" by auto
    ultimately show "(\<lambda>x. snth x i) -` {snth w i}\<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
      unfolding measurable_def by (simp add: measurable_snth_count_space)
  qed
  have "(\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i}\<inter> (space (bernoulli_stream p))) \<in> sets (bernoulli_stream p)"
  proof ((rule sigma_algebra.countable_INT''), auto)
    show "sigma_algebra (space (bernoulli_stream p)) (sets (bernoulli_stream p))"
      using measure_space measure_space_def by auto
    show "UNIV \<in> sets (bernoulli_stream p)" by (metis bernoulli_stream_space sets.top streams_UNIV)
    show "\<And>i. Suc i \<le> n \<Longrightarrow> (\<lambda>w. w !! i) -` {w !! i} \<inter> space (bernoulli_stream p) \<in> sets (bernoulli_stream p)" using fi by simp
  qed
  moreover have "(\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i}\<inter> (space (bernoulli_stream p))) =
    (\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i})\<inter> (space (bernoulli_stream p))"
    using False Inter_nonempty_distrib by auto
  ultimately show ?thesis using assms pseudo_proj_True_preimage[of w n] by simp
next
case True
  hence "n = 0" using less_eq_Suc_le by auto
  hence "pseudo_proj_True n = (\<lambda>w. sconst True)" by (simp add: pseudo_proj_True_def)
  hence "w = sconst True" using assms by simp
  hence "(pseudo_proj_True n) -`{w} \<inter> (space (bernoulli_stream p)) = (space (bernoulli_stream p))" by (simp add: \<open>pseudo_proj_True n = (\<lambda>w. sconst True)\<close>)
  thus "(pseudo_proj_True n) -`{w} \<inter> (space (bernoulli_stream p))\<in> sets (bernoulli_stream p)" by simp
qed


lemma (in infinite_coin_toss_space) pseudo_proj_False_singleton:
  assumes "w = pseudo_proj_False n w"
  shows "(pseudo_proj_False n) -`{w} \<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
proof (cases "{m. (Suc m) \<le> n} = {}")
case False
  have "\<And>i. (\<lambda>x. snth x i) \<in> measurable (bernoulli_stream p) (count_space UNIV)" by (simp add: measurable_snth_count_space)
  have fi: "\<And>i. Suc i \<le> n \<Longrightarrow> (\<lambda>w. snth w i) -` {snth w i} \<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
  proof -
    fix i
    assume "Suc i \<le> n"
    have "(\<lambda>x. snth x i) \<in> measurable (bernoulli_stream p) (count_space UNIV)" by (simp add: measurable_snth_count_space)
    moreover have "{snth w i} \<in> sets (count_space UNIV)" by auto
    ultimately show "(\<lambda>x. snth x i) -` {snth w i}\<inter> (space (bernoulli_stream p)) \<in> sets (bernoulli_stream p)"
      unfolding measurable_def by (simp add: measurable_snth_count_space)
  qed
  have "(\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i}\<inter> (space (bernoulli_stream p))) \<in> sets (bernoulli_stream p)"
  proof ((rule sigma_algebra.countable_INT''), auto)
    show "sigma_algebra (space (bernoulli_stream p)) (sets (bernoulli_stream p))"
      using measure_space measure_space_def by auto
    show "UNIV \<in> sets (bernoulli_stream p)" by (metis bernoulli_stream_space sets.top streams_UNIV)
    show "\<And>i. Suc i \<le> n \<Longrightarrow> (\<lambda>w. w !! i) -` {w !! i} \<inter> space (bernoulli_stream p) \<in> sets (bernoulli_stream p)" using fi by simp
  qed
  moreover have "(\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i}\<inter> (space (bernoulli_stream p))) =
    (\<Inter>i\<in> {m. (Suc m) \<le> n}. (\<lambda>w. snth w i) -` {snth w i})\<inter> (space (bernoulli_stream p))"
    using False Inter_nonempty_distrib by auto
  ultimately show ?thesis using assms pseudo_proj_False_preimage[of w n] by simp
next
case True
  hence "n = 0" using less_eq_Suc_le by auto
  hence "pseudo_proj_False n = (\<lambda>w. False ## sconst True)" by (simp add: pseudo_proj_False_def)
  hence "w = False ## sconst True" using assms by simp
  hence "(pseudo_proj_False n) -`{w} \<inter> (space (bernoulli_stream p)) = (space (bernoulli_stream p))"
    by (simp add: \<open>pseudo_proj_False n = (\<lambda>w. False##sconst True)\<close>)
  thus "(pseudo_proj_False n) -`{w} \<inter> (space (bernoulli_stream p))\<in> sets (bernoulli_stream p)" by simp
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_inverse_induct:
  assumes "w \<in> range (pseudo_proj_True n)"
  shows "(pseudo_proj_True n) -` {w} =
    (pseudo_proj_True (Suc n)) -` {w} \<union> (pseudo_proj_True (Suc n)) -`{pseudo_proj_False n w}"
proof
  let ?y = "pseudo_proj_False n w"
  show "(pseudo_proj_True n) -` {w} \<subseteq> (pseudo_proj_True (Suc n)) -` {w} \<union> (pseudo_proj_True (Suc n)) -`{?y}"
  proof
    fix z
    assume "z\<in> pseudo_proj_True n -`{w}"
    thus "z\<in> pseudo_proj_True (Suc n) -`{w} \<union> pseudo_proj_True (Suc n) -`{?y}"
      using pseudo_proj_False_def pseudo_proj_True_def pseudo_proj_True_stake
      pseudo_proj_True_suc_img by fastforce
  qed
  {
    fix z
    assume "z \<in> pseudo_proj_True (Suc n) -` {w}"
    hence "pseudo_proj_True (Suc n) z = w" by simp
    hence "pseudo_proj_True n z = pseudo_proj_True n w" by (metis  pseudo_proj_True_proj_Suc)
    also have "... = w" using assms pseudo_proj_True_def pseudo_proj_True_stake by auto
    finally have "pseudo_proj_True n z = w" .
  }
  hence fst: "pseudo_proj_True (Suc n) -` {w} \<subseteq> (pseudo_proj_True n) -` {w}" by blast
  {
    fix z
    assume "z \<in> pseudo_proj_True (Suc n) -` {?y}"
    hence "pseudo_proj_True n z = pseudo_proj_True n w"
      by (metis append1_eq_conv append_Nil2 cancel_comm_monoid_add_class.diff_cancel
        length_append_singleton length_stake order_refl pseudo_proj_False_def
        pseudo_proj_True_stake pseudo_proj_True_stake_image stake_Suc stake_invert_Nil stake_shift
        take_all vimage_singleton_eq)

    also have "... = w" using assms pseudo_proj_True_def pseudo_proj_True_stake by auto
    finally have "pseudo_proj_True n z = w" .
  }
  hence scd: "pseudo_proj_True (Suc n) -` {?y} \<subseteq> (pseudo_proj_True n) -` {w}" by blast
  show "(pseudo_proj_True (Suc n)) -` {w} \<union> (pseudo_proj_True (Suc n)) -`{?y} \<subseteq> (pseudo_proj_True n) -` {w}"
    using fst scd by auto
qed




subsubsection \<open>Natural filtration locale\<close>

text \<open>This part is mainly devoted to the proof that the projection function defined above indeed
permits to obtain a filtration on the infinite coin toss space, and that this filtration is initially trivial.\<close>

definition (in infinite_coin_toss_space) nat_filtration::"nat \<Rightarrow> bool stream measure" where
  "nat_filtration n = fct_gen_subalgebra M M (pseudo_proj_True n)"




locale infinite_cts_filtration = infinite_coin_toss_space +
  fixes F
  assumes natural_filtration: "F = nat_filtration"


lemma (in infinite_coin_toss_space) nat_filtration_space:
  shows "space (nat_filtration n) = UNIV"
by (metis bernoulli bernoulli_stream_space fct_gen_subalgebra_space nat_filtration_def streams_UNIV)

lemma (in infinite_coin_toss_space) nat_filtration_sets:
  shows "sets (nat_filtration n) =
    sigma_sets (space (bernoulli_stream p))
            {pseudo_proj_True n -` B \<inter> space M |B. B \<in> sets (bernoulli_stream p)}"
proof -
  have "sigma_sets (space M) {pseudo_proj_True n -` S \<inter> space M |S. S \<in> sets (bernoulli_stream p)} =
    sets (fct_gen_subalgebra M M (pseudo_proj_True n))"
    using bernoulli fct_gen_subalgebra_sets pseudo_proj_True_measurable by blast
  then show ?thesis
    using bernoulli nat_filtration_def by force
qed


lemma (in infinite_coin_toss_space) nat_filtration_singleton:
  assumes "pseudo_proj_True n w = w"
  shows "pseudo_proj_True n -`{w} \<in> sets (nat_filtration n)"
proof -
  let ?pw = "pseudo_proj_True n -`{w}"
  have memset:"?pw \<in> sets M" using bernoulli assms bernoulli_stream_preimage[of _ _ "pseudo_proj_True n"]
      pseudo_proj_True_singleton[of w n] by simp
  have "pseudo_proj_True n -`?pw \<in> sets (nat_filtration n)"
  proof -
    have "pseudo_proj_True n -`?pw \<inter> (space M) \<in> sets (nat_filtration n)" using memset
      by (metis fct_gen_subalgebra_sets_mem nat_filtration_def)
    moreover have "pseudo_proj_True n -`?pw \<inter> (space M) = pseudo_proj_True n -`?pw" using
      bernoulli_stream_preimage[of _ _ "pseudo_proj_True n"] bernoulli by simp
    ultimately show "pseudo_proj_True n -`?pw \<in> sets (nat_filtration n)"  by auto
  qed
  moreover have "pseudo_proj_True n -`?pw = ?pw" using pseudo_proj_True_proj by auto
  ultimately show ?thesis by simp
qed



lemma (in infinite_coin_toss_space) nat_filtration_pseudo_proj_True_measurable:
  shows "pseudo_proj_True n \<in> measurable (nat_filtration n) M" unfolding nat_filtration_def
using bernoulli fct_gen_subalgebra_fct_measurable[of "pseudo_proj_True n" M M]  pseudo_proj_True_measurable[of n]
  bernoulli_stream_space by auto



lemma (in infinite_coin_toss_space) nat_filtration_comp_measurable:
  assumes "f \<in> measurable M N"
  and "f \<circ> pseudo_proj_True n = f"
  shows "f \<in> measurable (nat_filtration n) N"
by (metis assms measurable_comp nat_filtration_pseudo_proj_True_measurable)

definition (in infinite_coin_toss_space) set_discriminating where
"set_discriminating n f N \<equiv> (\<forall>w. f w \<noteq> f (pseudo_proj_True n w) \<longrightarrow>
  (\<exists>A\<in>sets N. (f w \<in> A) = (f (pseudo_proj_True n w) \<notin> A)))"

lemma (in infinite_coin_toss_space) set_discriminating_if:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "set_discriminating n f borel" unfolding set_discriminating_def
proof (intro allI impI)
  {
    fix w
    assume "f w \<noteq> (f \<circ> (pseudo_proj_True n)) w"
    hence "\<exists>U. open U \<and> ( f w \<in> U = ((f \<circ> (pseudo_proj_True n)) w \<notin> U))" using separation_t0 by auto
    from this obtain A where "open A" and "f w\<in> A = ((f \<circ> (pseudo_proj_True n)) w \<notin> A)" by blast note Ah = this
    have "A\<in> sets borel" using Ah by simp
    hence "\<exists>A\<in>sets borel. (f w \<in> A) = ((f \<circ> (pseudo_proj_True n)) w \<notin> A)" using Ah by blast
  }
  thus "\<And>w. f w \<noteq> f (pseudo_proj_True n w) \<Longrightarrow> \<exists>A\<in>sets borel. (f w \<in> A) = (f (pseudo_proj_True n w) \<notin> A)"  by simp
qed

lemma (in infinite_coin_toss_space) nat_filtration_not_borel_info:
  assumes "f\<in> measurable (nat_filtration n) N"
  and "set_discriminating n f N"
  shows "f\<circ> pseudo_proj_True n = f"
proof (rule ccontr)
  assume "f\<circ> pseudo_proj_True n \<noteq> f"
  hence "\<exists> w. (f\<circ> (pseudo_proj_True n)) w \<noteq> f w" by auto
  from this obtain w where "(f\<circ> (pseudo_proj_True n)) w \<noteq> f w" by blast note wh = this
  let ?x = "pseudo_proj_True n w"
  have "pseudo_proj_True n ?x = pseudo_proj_True n w" by (simp add: pseudo_proj_True_proj)
  have "f w \<noteq> f (pseudo_proj_True n w)" using wh by simp
  hence "\<exists>A \<in> sets N. ( f w \<in> A = (f ?x \<notin> A))" using assms  unfolding set_discriminating_def by simp
  from this obtain A where "A \<in> sets N" and "f w\<in> A = (f ?x \<notin> A)" by blast note Ah = this
  have "f-` A\<inter> (space (nat_filtration n)) \<in> sets (nat_filtration n)"
    using Ah assms borel_open measurable_sets by blast
  hence fn:"f-` A \<in> sets (nat_filtration n)" using nat_filtration_space by simp
  have "?x\<in> f-`A = (w \<in> f -`A)" using \<open>pseudo_proj_True n ?x = pseudo_proj_True n w\<close> assms
    fct_gen_subalgebra_info[of "pseudo_proj_True n" M] bernoulli_stream_space
    by (metis Pi_I UNIV_I bernoulli fn nat_filtration_def streams_UNIV)
  also have "... = (f w \<in> A)" by simp
  also have "... = (f ?x \<notin> A)" using Ah by simp
  also have "... = (?x \<notin> f -`A)" by simp
  finally have "?x\<in> f-`A = (?x \<notin> f -`A)" .
  thus False by simp
qed




lemma (in infinite_coin_toss_space) nat_filtration_info:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "f\<circ> pseudo_proj_True n = f"
proof (rule nat_filtration_not_borel_info)
  show "f\<in> borel_measurable (nat_filtration n)" using assms by simp
  show "set_discriminating n f borel" using assms by (simp add: set_discriminating_if)
qed





lemma (in infinite_coin_toss_space) nat_filtration_not_borel_info':
  assumes "f\<in> measurable (nat_filtration n) N"
  and "set_discriminating n f N"
  shows "f\<circ> pseudo_proj_False n = f"
proof
  fix x
  have "(f \<circ> pseudo_proj_False n) x = f (pseudo_proj_False n x)" by simp
  also have "... = f (pseudo_proj_True n (pseudo_proj_False n x))" using assms nat_filtration_not_borel_info
    by (metis comp_apply)
  also have "... = f (pseudo_proj_True n x)"
  proof -
    have "pseudo_proj_True n (pseudo_proj_False n x) = pseudo_proj_True n x"
      by (simp add: pseudo_proj_False_stake pseudo_proj_True_def)
    thus ?thesis by simp
  qed
  also have "... = f x" using assms nat_filtration_not_borel_info by (metis comp_apply)
  finally show "(f \<circ> pseudo_proj_False n) x = f x" .
qed

lemma (in infinite_coin_toss_space) nat_filtration_info':
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "f\<circ> pseudo_proj_False n = f"
proof
  fix x
  have "(f \<circ> pseudo_proj_False n) x = f (pseudo_proj_False n x)" by simp
  also have "... = f (pseudo_proj_True n (pseudo_proj_False n x))" using assms nat_filtration_info
    by (metis comp_apply)
  also have "... = f (pseudo_proj_True n x)"
  proof -
    have "pseudo_proj_True n (pseudo_proj_False n x) = pseudo_proj_True n x"
      by (simp add: pseudo_proj_False_stake pseudo_proj_True_def)
    thus ?thesis by simp
  qed
  also have "... = f x" using assms nat_filtration_info by (metis comp_apply)
  finally show "(f \<circ> pseudo_proj_False n) x = f x" .
qed



lemma (in infinite_coin_toss_space) nat_filtration_borel_measurable_characterization:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable M"
  shows "f\<in> borel_measurable (nat_filtration n) \<longleftrightarrow> f\<circ> pseudo_proj_True n = f"
using assms nat_filtration_comp_measurable nat_filtration_info by blast




lemma (in infinite_coin_toss_space) nat_filtration_borel_measurable_init:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (nat_filtration 0)"
  shows "f = (\<lambda>w. f (sconst True))"
proof
  fix w
  have "f w = f ((pseudo_proj_True 0) w)" using assms nat_filtration_info[of f 0] by (metis comp_apply)
  also have "... = f (sconst True)" by (simp add: pseudo_proj_True_def)
  finally show "f w = f (sconst True)" .
qed




lemma (in infinite_coin_toss_space) nat_filtration_Suc_sets:
  shows "sets (nat_filtration n) \<subseteq> sets (nat_filtration (Suc n))"
proof -
  {
    fix x
    assume "x\<in> {pseudo_proj_True n -` B \<inter> space M |B. B \<in> sets M}"
    hence "\<exists>B. B \<in> sets M \<and> x = pseudo_proj_True n -` B \<inter> space M" by auto
    from this obtain B where "B \<in> sets M" and "x = pseudo_proj_True n -` B \<inter> space M"
      by blast note xhyps = this
      let ?Bim = "B\<inter> (range (pseudo_proj_True n))"
      let ?preT = "(\<lambda>n w. (pseudo_proj_True n) -` {w})"
      have "finite ?Bim" using pseudo_proj_True_finite_image by simp
      have "pseudo_proj_True n -`B \<inter> (space M) = pseudo_proj_True n -`B"
        using bernoulli bernoulli_stream_preimage[of _ _ "pseudo_proj_True n"] by simp
      also have "... = pseudo_proj_True n -`?Bim" by auto
      also have "... = (\<Union> w \<in> ?Bim.?preT n w)" by auto
      also have "... = (\<Union> w \<in> ?Bim. (?preT (Suc n) w \<union> ?preT (Suc n) (pseudo_proj_False n w)))"
        by (simp add:pseudo_proj_True_inverse_induct)
      also have "... = (\<Union> w \<in> ?Bim. ?preT (Suc n) w) \<union> (\<Union> w \<in> ?Bim. ?preT (Suc n) (pseudo_proj_False n w))" by auto
      finally have tmpeq: "pseudo_proj_True n -`B \<inter> (space M) =
        (\<Union> w \<in> ?Bim. ?preT (Suc n) w) \<union> (\<Union> w \<in> ?Bim. ?preT (Suc n) (pseudo_proj_False n w))" .
      have "(\<Union> w \<in> ?Bim. ?preT (Suc n) w) \<in> sets (nat_filtration (Suc n))"
        using \<open>finite ?Bim\<close> nat_filtration_singleton pseudo_proj_True_Suc_proj by auto
      moreover have "(\<Union> w \<in> ?Bim. ?preT (Suc n) (pseudo_proj_False n w)) \<in> sets (nat_filtration (Suc n))" using \<open>finite ?Bim\<close>
        by (simp add: nat_filtration_singleton pseudo_proj_True_Suc_False_proj sets.finite_UN)
      ultimately have "x \<in> sets (nat_filtration (Suc n))"
        using tmpeq xhyps by simp
  } note xmem = this
  have "sets (nat_filtration n) = sigma_sets (space M) {pseudo_proj_True n -` B \<inter> space M |B. B \<in> sets M}"
    using bernoulli nat_filtration_sets by blast
  also have "... \<subseteq> (nat_filtration (Suc n))"
  proof (rule sigma_algebra.sigma_sets_subset)
    show "{pseudo_proj_True n -` B \<inter> space M |B. B \<in> sets M}
      \<subseteq> sets (nat_filtration (Suc n))" using xmem by auto
    show "sigma_algebra (space M) (sets (nat_filtration (Suc n)))"
      by (metis bernoulli bernoulli_stream_space nat_filtration_space sets.sigma_algebra_axioms streams_UNIV)
  qed
  finally show ?thesis .
qed

lemma (in infinite_coin_toss_space) nat_filtration_subalgebra:
  shows "subalgebra M (nat_filtration n)" using bernoulli fct_gen_subalgebra_is_subalgebra nat_filtration_def
      pseudo_proj_True_measurable by metis

lemma (in infinite_coin_toss_space) nat_discrete_filtration:
  shows "filtration M nat_filtration"
  unfolding filtration_def
proof((intro conjI), (intro allI)+)
  {
    fix n
    let ?F = "nat_filtration n"
    show "subalgebra M ?F"
      using bernoulli fct_gen_subalgebra_is_subalgebra nat_filtration_def
      pseudo_proj_True_measurable by metis
  } note allrm = this
  show "\<forall>n m. n \<le> m \<longrightarrow> subalgebra (nat_filtration m) (nat_filtration n)"
  proof (intro allI impI)
    let ?F = nat_filtration
    fix n::nat
    fix m
    show "n \<le> m \<Longrightarrow> subalgebra (nat_filtration m) (nat_filtration n)"
    proof (induct m)
      case (Suc m)
      have "subalgebra (?F (Suc m)) (?F m)" unfolding subalgebra_def
      proof (intro conjI)
        show speq: "space (?F m) = space (?F (Suc m))" by (simp add: nat_filtration_space)
        show "sets (?F m) \<subseteq> sets (?F (Suc m))" using nat_filtration_Suc_sets by simp
      qed

      thus "n \<le> Suc m \<Longrightarrow> subalgebra (?F (Suc m)) (?F n)" using Suc
        using Suc.hyps le_Suc_eq subalgebra_def by fastforce
      next
      case 0
        thus ?case by (simp add: subalgebra_def)
    qed
  qed
qed

lemma (in infinite_coin_toss_space) nat_info_filtration:
  shows "init_triv_filt M nat_filtration" unfolding init_triv_filt_def
proof
  show "filtration M nat_filtration" by (simp add:nat_discrete_filtration)
  have img: "\<forall> w\<in> space M. pseudo_proj_True 0 w = sconst True" unfolding pseudo_proj_True_def by simp
  show "sets (nat_filtration bot) = {{}, space M}"
  proof
    show "{{}, space M} \<subseteq> sets (nat_filtration bot)"
      by (metis empty_subsetI insert_subset nat_filtration_subalgebra sets.empty_sets sets.top subalgebra_def)
    show "sets (nat_filtration bot) \<subseteq> {{}, space M}"
    proof -
      have "\<forall>B \<in> sets (bernoulli_stream p). pseudo_proj_True 0 -` B \<inter> space M \<in> {{}, space M}"
      proof
        fix B
        assume "B \<in> sets (bernoulli_stream p)"
        show "pseudo_proj_True 0 -` B \<inter> space M \<in> {{}, space M}"
        proof (cases "sconst True \<in> B")
          case True
          hence "pseudo_proj_True 0 -` B \<inter> space M = space M" using img by auto
          thus ?thesis by auto
        next
          case False
          hence "pseudo_proj_True 0 -` B \<inter> space M = {}" using img by auto
          thus ?thesis by auto
        qed
      qed
      hence "{pseudo_proj_True 0 -` B \<inter> space M |B. B \<in> sets (bernoulli_stream p)} \<subseteq> {{}, space M}" by auto
      hence "sigma_sets (space (bernoulli_stream p))
            {pseudo_proj_True 0 -` B \<inter> space M |B. B \<in> sets (bernoulli_stream p)} \<subseteq> {{}, space M}"
        using sigma_algebra.sigma_sets_subset[of "space (bernoulli_stream p)" "{{}, space M}"]
        by (simp add: bernoulli sigma_algebra_trivial)
      thus ?thesis by (simp add:nat_filtration_sets bot_nat_def)
    qed
  qed
qed



sublocale infinite_cts_filtration \<subseteq> triv_init_disc_filtr_prob_space
proof (unfold_locales, intro conjI)
  show "disc_filtr M F" unfolding disc_filtr_def
    using filtrationE2 nat_discrete_filtration nat_filtration_subalgebra natural_filtration by auto
  show "sets (F bot) = {{}, space M}" using nat_info_filtration natural_filtration
    unfolding init_triv_filt_def by simp
qed





lemma (in infinite_coin_toss_space) nat_filtration_vimage_finite:
  fixes f::"bool stream \<Rightarrow> 'b::{t2_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "finite (f`(space M))" using pseudo_proj_True_finite_image nat_filtration_info[of f n]
    by (metis assms bernoulli bernoulli_stream_space finite_imageI fun.set_map streams_UNIV)

lemma (in infinite_coin_toss_space) nat_filtration_borel_measurable_simple:
  fixes f::"bool stream \<Rightarrow> 'b::{t2_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "simple_function M f"
proof -
  have f1: "\<forall>m ma. (m::bool stream measure) \<rightarrow>\<^sub>M (ma::'b measure) = {f \<in> space m \<rightarrow> space ma. \<forall>B. B \<in> sets ma \<longrightarrow> f -` B \<inter> space m \<in> sets m}"
    by (metis measurable_def)
  then have "f \<in> space (nat_filtration n) \<rightarrow> space borel \<and> (\<forall>B. B \<in> sets borel \<longrightarrow> f -` B \<inter> space (nat_filtration n) \<in> sets (nat_filtration n))"
    using assms by blast
  then have "f \<in> space M \<rightarrow> space borel \<and> (\<forall>B. B \<in> sets borel \<longrightarrow> f -` B \<inter> space M \<in> events)"
    by (metis (no_types) contra_subsetD nat_filtration_subalgebra subalgebra_def)
  then have "random_variable borel f"
    using f1 by blast
  then show ?thesis
    using assms nat_filtration_vimage_finite simple_function_borel_measurable by blast
qed


lemma (in infinite_coin_toss_space) nat_filtration_singleton_range_set:
  fixes f::"bool stream \<Rightarrow> 'b::{t2_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "\<exists> A\<in> sets borel. range f \<inter> A = {f x}"
proof -
  let ?Ax = "range f - {f x}"
  have "range f = f`space M" using bernoulli bernoulli_stream_space by simp
  hence "finite ?Ax" using assms nat_filtration_vimage_finite by auto
  hence "\<exists>U. open U \<and> f x\<in> U \<and> U\<inter> ?Ax = {}" by (simp add:open_except_set)
  then obtain U where "open U" and "f x\<in> U" and "U\<inter> ?Ax = {}" by auto
  have "U \<in> sets borel" using \<open>open U\<close> by simp
  have "range f \<inter> U = {f x}" using \<open>f x \<in> U\<close> \<open>U\<inter> ?Ax = {}\<close> by blast
  thus "\<exists>A\<in> sets borel. range f \<inter> A = {f x}" using \<open>U\<in> sets borel\<close> by auto
qed

lemma (in infinite_coin_toss_space) nat_filtration_borel_measurable_singleton:
  fixes f::"bool stream \<Rightarrow> 'b::{t2_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "f -`{f x} \<in> sets (nat_filtration n)"
proof -
  let ?Ax = "f`space M - {f x}"
  have "finite ?Ax"
    using assms nat_filtration_vimage_finite by blast
  hence "\<exists>U. open U \<and> f x\<in> U \<and> U\<inter> ?Ax = {}" by (simp add:open_except_set)
  then obtain U where "open U" and "f x\<in> U" and "U\<inter> ?Ax = {}" by auto
  have "f x \<in> f ` space M" using bernoulli_stream_space bernoulli by simp
  hence "f`space M \<inter> U = {f x}" using \<open>f x\<in> U\<close> \<open>U\<inter> ?Ax = {}\<close> by blast
  hence "\<exists>A. open A\<and> f`space M \<inter> A = {f x}" using \<open>open U\<close> by auto
  from this obtain A where "open A" and inter: "f`space M \<inter> A = {f x}" by auto
  have "A \<in> sets borel" using \<open>open A\<close> by simp
  hence "f -`A \<inter> space M \<in> sets (nat_filtration n)" using assms nat_filtration_space
    by (simp add: bernoulli bernoulli_stream_space in_borel_measurable_borel)
  hence "f -`A \<inter> space M \<in> events" using nat_filtration_subalgebra
    by (meson subalgebra_def subset_eq)
  have "f -`{f x}\<inter> space M  = f -`A\<inter> space M"
  proof
    have "f x\<in> A" using inter by auto
    thus "f -` {f x}\<inter> space M \<subseteq> f -` A\<inter> space M" by auto
    show "f -` A\<inter> space M \<subseteq> f -` {f x}\<inter> space M"
    proof
      fix y
      assume "y\<in> f-` A\<inter> space M"
      hence  "f y \<in> A\<inter> f`space M" by simp
      hence "f y = f x" using inter by auto
      thus "y\<in> f -` {f x}\<inter> space M" using \<open>y\<in> f-` A\<inter> space M\<close> by auto
    qed
  qed
  moreover have "f -`A \<inter> space M \<in> (nat_filtration n)" using assms \<open>A\<in> sets borel\<close>
    using \<open>f -` A \<inter> space M \<in> sets (nat_filtration n)\<close> by blast
  ultimately show ?thesis using bernoulli_stream_space bernoulli by simp
qed

lemma (in infinite_cts_filtration) borel_adapt_nat_filtration_info:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
  and "m \<le> n"
shows "X m (pseudo_proj_True n w) = X m w"
proof -
  have "X m \<in> borel_measurable (F n)" using assms natural_filtration
    using  increasing_measurable_info
    by (metis adapt_stoch_proc_def)
  thus ?thesis using nat_filtration_info natural_filtration
    by (metis comp_apply)
qed

lemma (in infinite_coin_toss_space) nat_filtration_borel_measurable_integrable:
  assumes "f\<in> borel_measurable (nat_filtration n)"
  shows "integrable M f"
proof -
  have "simple_function M f" using assms by (simp add: nat_filtration_borel_measurable_simple)
  moreover have "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" by simp
  ultimately have "Bochner_Integration.simple_bochner_integrable M f"
    using Bochner_Integration.simple_bochner_integrable.simps by blast
  hence "has_bochner_integral M f (Bochner_Integration.simple_bochner_integral M f)"
    using has_bochner_integral_simple_bochner_integrable by auto
  thus ?thesis using integrable.simps by auto
qed




definition (in infinite_coin_toss_space) spick:: "bool stream \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool stream" where
  "spick w n v = shift (stake n w) (v## sconst True)"


lemma (in infinite_coin_toss_space) spickI:
  shows "stake n (spick w n v) = stake n w \<and> snth (spick w n v) n = v"
by (simp add: spick_def stake_shift)

lemma (in infinite_coin_toss_space) spick_eq_pseudo_proj_True:
  shows "spick w n True = pseudo_proj_True n w" unfolding spick_def pseudo_proj_True_def
  by (metis (full_types) id_apply siterate.code)

lemma (in infinite_coin_toss_space) spick_eq_pseudo_proj_False:
  shows "spick w n False = pseudo_proj_False n w" unfolding spick_def pseudo_proj_False_def by simp


lemma (in infinite_coin_toss_space) spick_pseudo_proj:
  shows "spick (pseudo_proj_True (Suc n) w) n v = spick w n v"
      by (metis pseudo_proj_True_proj_Suc pseudo_proj_True_stake spick_def)

lemma (in infinite_coin_toss_space) spick_pseudo_proj_gen:
  shows "m < n \<Longrightarrow> spick (pseudo_proj_True n w) m v = spick w m v"
by (metis Suc_leI pseudo_proj_True_proj pseudo_proj_True_prefix spick_pseudo_proj)


lemma (in infinite_coin_toss_space) spick_nat_filtration_measurable:
  shows "(\<lambda>w. spick w n v) \<in> measurable (nat_filtration n) M"
proof (rule nat_filtration_comp_measurable)
  show "(\<lambda>w. spick w n v) \<in> measurable M M"
  proof -
    let ?N = "bernoulli_stream p"
    have "id \<in> measurable ?N ?N" by simp
    moreover have "(\<lambda>w. v## (sconst True)) \<in> measurable ?N ?N"  using bernoulli_stream_space  by simp
    ultimately show ?thesis using measurable_shift bernoulli p_gt_0 p_lt_1
      unfolding bernoulli_stream_def spick_def by simp
  qed
  {
    fix w
    have "spick (pseudo_proj_True n w) n v = spick w n v"
      by (simp add: pseudo_proj_True_stake spick_def)
  }
  thus "(\<lambda>w. spick w n v) \<circ> pseudo_proj_True n = (\<lambda>w. spick w n v)" by auto
qed


definition (in infinite_coin_toss_space) proj_rep_set:
  "proj_rep_set n = range (pseudo_proj_True n)"

lemma (in infinite_coin_toss_space) proj_rep_set_finite:
  shows "finite (proj_rep_set n)" using pseudo_proj_True_finite_image
  by (simp add: proj_rep_set)


lemma (in infinite_coin_toss_space) set_filt_contain:
  assumes "A\<in> sets (nat_filtration n)"
and "w\<in> A"
shows "pseudo_proj_True n -` {pseudo_proj_True n w} \<subseteq> A"
proof
  define indA where "indA = ((indicator A)::bool stream\<Rightarrow>real)"
  have "indA \<in> borel_measurable (nat_filtration n)" unfolding indA_def
    by (simp add: assms(1) borel_measurable_indicator)
  fix x
  assume "x \<in> pseudo_proj_True n -` {pseudo_proj_True n w}"
  have "indA x = indA (pseudo_proj_True n x)"
    using nat_filtration_info[symmetric, of "indicator A" n] \<open>indA \<in> borel_measurable (nat_filtration n)\<close>
    unfolding indA_def by (metis comp_apply)
  also have "... = indA (pseudo_proj_True n w)" using \<open>x \<in> pseudo_proj_True n -` {pseudo_proj_True n w}\<close>
    by simp
  also have "... = indA w" using nat_filtration_info[of "indicator A" n]
    \<open>indA \<in> borel_measurable (nat_filtration n)\<close> unfolding indA_def by (metis comp_apply)
  also have "... = 1" using assms unfolding indA_def by simp
  finally have "indA x = 1" .
  thus "x\<in> A" unfolding indA_def by (simp add: indicator_eq_1_iff)
qed




lemma (in infinite_cts_filtration) measurable_range_rep:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f \<in> borel_measurable (nat_filtration n)"
  shows "range f = (\<Union> r\<in>(proj_rep_set n). {f(r)})"
proof -
  have "f = f \<circ> (pseudo_proj_True n)" using assms nat_filtration_info[of f n] by simp
  hence "range f = f `(proj_rep_set n)" by (metis fun.set_map proj_rep_set)
  also have "... = (\<Union>r\<in>proj_rep_set n. {f r})" by blast
  finally show "range f = (\<Union>r\<in>proj_rep_set n. {f r})" .
qed

lemma (in infinite_coin_toss_space) borel_measurable_stake:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (nat_filtration n)"
  and "stake n w = stake n y"
shows "f w = f y"
proof -
  have "pseudo_proj_True n w = pseudo_proj_True n y" unfolding pseudo_proj_True_def using assms by simp
  thus ?thesis using assms nat_filtration_info by (metis comp_apply)
qed





subsubsection \<open>Probability component\<close>

text \<open>The probability component permits to compute measures of subspaces in a straightforward way.\<close>

definition  prob_component where
  "prob_component (p::real) w n = (if (snth w n) then p else 1-p)"

lemma  prob_component_neq_zero:
  assumes "0 < p"
and "p < 1"
  shows "prob_component p w n \<noteq> 0" using assms prob_component_def by auto

lemma  prob_component_measure:
  fixes x::"bool stream"
assumes "0 \<le> p"
and "p \<le> 1"
  shows "emeasure (measure_pmf (bernoulli_pmf p)) {snth x i} = prob_component p x i"  unfolding prob_component_def using emeasure_pmf_single
    pmf_bernoulli_False pmf_bernoulli_True
  by (simp add: emeasure_pmf_single assms)



lemma  stake_preimage_measurable:
  fixes x::"bool stream"
  assumes "Suc 0 \<le> n" and "M = bernoulli_stream p"
  shows "{w\<in> space M. (stake n w = stake n x)} \<in> sets M"
proof -
  let ?S =  "{w\<in> space M. (stake n w = stake n x)}"
  have "?S = (\<Inter> i \<in> {0.. n-1}. {w\<in> space M. (snth w i = snth x i)})" using stake_inter_snth assms by simp
  moreover have "(\<Inter> i \<in> {0.. n-1}. {w\<in> space M. (snth w i = snth x i)}) \<in> sets M"
  proof -
    have "\<forall> i \<le> n-1. {w\<in> space M. (snth w i = snth x i)} \<in> sets M"
    proof (intro allI impI)
      fix i
      assume "i \<le> n-1"
      thus "{w \<in> space M. w !! i = x !! i} \<in> sets M"
      proof -
        have "(\<lambda>w. snth w i) \<in> measurable M (measure_pmf (bernoulli_pmf p))" using assms by (simp add: assms bernoulli_stream_def)
        thus ?thesis by simp
      qed
    qed
    thus ?thesis by auto
  qed
  ultimately show ?thesis by simp
qed

lemma snth_as_fct:
  fixes b
  assumes "M = bernoulli_stream p"
  shows "to_stream -` {w\<in> space M. snth w i = b} = {X::nat\<Rightarrow>bool. X i = b}"
proof -
  let ?S = "{w\<in> space M. snth w i = b}"
  let ?PM = "(\<lambda>i::nat. (measure_pmf (bernoulli_pmf p)))"
  have isps: "product_prob_space ?PM" by unfold_locales
  let ?Z = "{X::nat\<Rightarrow>bool. X i = b}"
  show "to_stream -`?S = ?Z" by (simp add: assms bernoulli_stream_space to_stream_def)
qed

lemma  stake_as_fct:
  assumes "Suc 0 \<le> n" and "M= bernoulli_stream p"
  shows "to_stream -`{w\<in> space M. (stake n w = stake n x)} = {X::nat\<Rightarrow>bool. \<forall>i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> X i = snth x i}"
proof -
  let ?S = "{w\<in> space M. (stake n w = stake n x)}"
  let ?Z = "{X::nat\<Rightarrow>bool. \<forall>i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> X i = snth x i}"
  have "to_stream -` ?S = to_stream -` (\<Inter> i \<in> {0.. n-1}. {w\<in> space M. (snth w i = snth x i)})"
    using \<open>Suc 0 \<le> n\<close> stake_inter_snth by blast
  also have "... = (\<Inter> i \<in> {0.. n-1}. to_stream -`{w\<in> space M. (snth w i = snth x i)})" by auto
  also have "... = (\<Inter> i \<in> {0.. n-1}. {X::nat\<Rightarrow>bool. X i = snth x i})" using snth_as_fct assms by simp
  also have "... = ?Z" by auto
  finally show ?thesis .
qed

lemma  bernoulli_stream_npref_prob:
  fixes x
  assumes "M = bernoulli_stream p"
  shows "emeasure M {w\<in> space M. (stake 0 w = stake 0 x)} = 1"
proof -
  define S where "S = {w\<in> space M. (stake 0 w = stake 0 x)}"
  have "S = space M" unfolding S_def by simp
  thus ?thesis
    by (simp add: assms bernoulli_stream_def prob_space.emeasure_space_1
        prob_space.prob_space_stream_space prob_space_measure_pmf)
qed



lemma bernoulli_stream_pref_prob:
  fixes x
  assumes "M =bernoulli_stream p"
and "0 \<le> p" and "p \<le> 1"
  shows "n\<ge> Suc 0\<Longrightarrow> emeasure M {w\<in> space M. (stake n w = stake n x)} = (\<Prod>i\<in>{0..n-1}. prob_component p x i)"
proof -
  have "prob_space M"
    by (simp add: assms bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
  fix n::nat
  assume "n\<ge> Suc 0"
  define S where "S = {w\<in> space M. (stake n w = stake n x)}"
  have s: "S \<in> sets M" unfolding S_def by (simp add: assms stake_preimage_measurable \<open>Suc 0 \<le> n\<close>)
  define PM where  "PM = (\<lambda>i::nat. (measure_pmf (bernoulli_pmf p)))"
  have isps: "product_prob_space PM" unfolding PM_def by unfold_locales
  define Z where "Z = {X::nat\<Rightarrow>bool. \<forall>i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> X i = snth x i}"
  let ?wPM = "Pi\<^sub>M UNIV PM"
  define imgSbs where "imgSbs = prod_emb UNIV PM {0..n-1} (Pi\<^sub>E {0..n-1} (\<lambda>i::nat. {snth x i}))"
  have "space ?wPM = UNIV" using space_PiM unfolding PM_def by fastforce
  hence "(to_stream -` S \<inter> (space ?wPM)) = to_stream -` S" by simp
  also have "... =  Z" using stake_as_fct \<open>Suc 0 \<le> n\<close> assms unfolding Z_def S_def by simp
  also have "... = imgSbs"
  proof
    {
      fix X
      assume "X \<in> imgSbs"
      hence "restrict X {0..n-1} \<in> (Pi\<^sub>E {0..n-1} (\<lambda>i::nat. {snth x i}))" using prod_emb_iff[of X] unfolding imgSbs_def by simp
      hence "\<forall>i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> X i = snth x i" by auto
      hence "X \<in> Z" unfolding Z_def by simp
    }
    thus "imgSbs \<subseteq> Z" by blast
    {
      fix X
      assume "X \<in> Z"
      hence "\<forall>i. 0 \<le> i \<and> i \<le> n-1 \<longrightarrow> X i = snth x i" unfolding Z_def by simp
      hence "restrict X {0..n-1} \<in> (Pi\<^sub>E {0..n-1} (\<lambda>i::nat. {snth x i}))" by simp
      moreover have "X \<in> extensional UNIV" by simp
      moreover have "\<forall>i \<in> UNIV. X i \<in> space (PM i)" unfolding PM_def by auto
      ultimately have "X \<in> imgSbs"
        using prod_emb_iff[of X] unfolding imgSbs_def by simp
    }
    thus "Z \<subseteq> imgSbs" by auto
  qed
  finally have inteq: "(to_stream -` S \<inter> (space ?wPM)) = imgSbs" .

  have "emeasure M S = emeasure ?wPM (to_stream -` S \<inter> (space ?wPM))"
    using  emeasure_distr[of "to_stream" ?wPM "M" S] measurable_to_stream[of "(measure_pmf (bernoulli_pmf p))"] s assms
    unfolding bernoulli_stream_def stream_space_def PM_def
    by (simp add: emeasure_distr)
  also have "... = emeasure ?wPM imgSbs" using inteq by simp
  also have "... = (\<Prod>i\<in>{0..n-1}. emeasure (PM i) ((\<lambda>m::nat. {snth x m}) i))"
    using isps  unfolding imgSbs_def PM_def by (auto simp add:product_prob_space.emeasure_PiM_emb)
  also have "... = (\<Prod>i\<in>{0..n-1}. prob_component p x i)" using prob_component_measure  unfolding PM_def
  proof -
    have f1: "\<forall>N f. (\<exists>n. (n::nat) \<in> N \<and> \<not> 0 \<le> f n) \<or> (\<Prod>n\<in>N. ennreal (f n)) = ennreal (prod f N)"
      by (metis (no_types) prod_ennreal)
    obtain nn :: "(nat \<Rightarrow> real) \<Rightarrow> nat set \<Rightarrow> nat" where
          f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<not> 0 \<le> x0 v2) = (nn x0 x1 \<in> x1 \<and> \<not> 0 \<le> x0 (nn x0 x1))"
      by moura
    have f3: "\<forall>s n. if s !! n then prob_component p s n = p else p + prob_component p s n = 1"
      by (simp add: prob_component_def)
    { assume "prob_component p x (nn (prob_component p x) {0..n - 1}) \<noteq> p"
      then have "p + prob_component p x (nn (prob_component p x) {0..n - 1}) = 1"
        using f3 by metis
      then have "nn (prob_component p x) {0..n - 1} \<notin> {0..n - 1} \<or> 0 \<le> prob_component p x (nn (prob_component p x) {0..n - 1})"
        using assms by linarith }
    then have "nn (prob_component p x) {0..n - 1} \<notin> {0..n - 1} \<or> 0 \<le> prob_component p x (nn (prob_component  p x) {0..n - 1})"
      using assms by linarith
    then have "(\<Prod>n = 0..n - 1. ennreal (prob_component p x n)) = ennreal (prod (prob_component p x) {0..n - 1})"
      using f2 f1 by meson
    moreover have "(\<Prod>n = 0..n - 1. ennreal (prob_component p x n)) =
      (\<Prod>n = 0..n - 1. emeasure (measure_pmf (bernoulli_pmf p)) {x !! n})"  using prob_component_measure[of p x]
       assms by simp
    ultimately show "(\<Prod>n = 0..n - 1. emeasure (measure_pmf (bernoulli_pmf p)) {x !! n}) = ennreal (prod (prob_component p x) {0..n - 1})"
      using prob_component_measure[of p x]   by simp
  qed
  finally show "emeasure M S = (\<Prod>i\<in>{0..n-1}. prob_component p x i)" .
qed


lemma  bernoulli_stream_pref_prob':
  fixes x
  assumes "M = bernoulli_stream p"
and "p \<le> 1" and "0 \<le> p"
  shows "emeasure M {w\<in> space M. (stake n w = stake n x)} = (\<Prod>i\<in>{0..<n}. prob_component p x i)"
proof (cases "Suc 0 \<le> n")
  case True
  hence "emeasure M {w\<in> space M. (stake n w = stake n x)} = (\<Prod>i\<in>{0..n -1}. prob_component p x i)" using assms
    by (simp add: bernoulli_stream_pref_prob)
  moreover have "(\<Prod>i\<in>{0..n -1}. prob_component p x i) = (\<Prod>i\<in>{0..<n}. prob_component p x i)"
  proof (rule prod.cong)
    show "{0..n - 1} = {0..<n}" using True by auto
    show "\<And>xa. xa \<in> {0..<n} \<Longrightarrow> prob_component p x xa = prob_component p x xa" by simp
  qed
  ultimately show ?thesis by simp
next
  case False
  hence "n = 0" using False by simp
  have "{w\<in> space M. (stake n w = stake n x)} = space M"
  proof
    show "{w \<in> space M. stake n w = stake n x} \<subseteq> space M"
    proof
      fix w
      assume "w\<in> {w \<in> space M. stake n w = stake n x}"
      thus "w \<in> space M" by auto
    qed
    show "space M \<subseteq> {w \<in> space M. stake n w = stake n x}"
    proof
      fix w
      assume "w\<in> space M"
      have "stake 0 w = stake 0 x" by simp
      hence "stake n w = stake n x" using \<open>n = 0\<close> by simp
      thus "w\<in> {w \<in> space M. stake n w = stake n x}" using \<open>w\<in> space M\<close> by auto
    qed
  qed
  hence "emeasure M {w \<in> space M. stake n w = stake n x} = emeasure M (space M)" by simp
  also have "... = 1" using assms
    by (simp add: bernoulli_stream_def prob_space.emeasure_space_1
        prob_space.prob_space_stream_space prob_space_measure_pmf)
  also have "... = (\<Prod>i\<in>{0..<n}. prob_component p x i)" using \<open>n = 0\<close> by simp
  finally show ?thesis .
qed

lemma  bernoulli_stream_stake_prob:
  fixes x
  assumes "M = bernoulli_stream p"
and "p \<le> 1" and "0 \<le> p"
shows "measure M {w\<in> space M. (stake n w = stake n x)} = (\<Prod>i\<in>{0..<n}. prob_component p x i)"
proof -
  have "measure M {w\<in> space M. (stake n w = stake n x)} = emeasure M {w\<in> space M. (stake n w = stake n x)}"
    by (metis (no_types, lifting) assms(1) bernoulli_stream_def emeasure_eq_ennreal_measure emeasure_space
        ennreal_one_neq_top neq_top_trans prob_space.emeasure_space_1 prob_space.prob_space_stream_space
        prob_space_measure_pmf)
  also have "... = (\<Prod>i\<in>{0..<n}. prob_component p x i)" using bernoulli_stream_pref_prob' assms by simp
  finally show ?thesis by (simp add: assms(2) assms(3) prob_component_def prod_nonneg)
qed

lemma (in infinite_coin_toss_space) bernoulli_stream_pseudo_prob:
  fixes x
  assumes "M = bernoulli_stream p"
and "p \<le> 1" and "0 \<le> p"
and "w\<in> range (pseudo_proj_True n)"
shows "measure M (pseudo_proj_True n -`{w} \<inter> space M) = (\<Prod>i\<in>{0..<n}. prob_component p w i)"
proof -
  have "(pseudo_proj_True n -`{w}) \<inter> space M = {x\<in> space M. (stake n w = stake n x)}"
    using assms(4) infinite_coin_toss_space.pseudo_proj_True_def infinite_coin_toss_space_axioms
      pseudo_proj_True_preimage_stake pseudo_proj_True_stake by force
  thus ?thesis using bernoulli_stream_stake_prob assms
  proof -
    have "pseudo_proj_True n w = w"
      using \<open>w \<in> range (pseudo_proj_True n)\<close> pseudo_proj_True_proj by blast
    then show ?thesis
      using bernoulli bernoulli_stream_stake_prob p_gt_0 p_lt_1 pseudo_proj_True_preimage_stake_space by presburger
  qed
qed


lemma bernoulli_stream_element_prob_rec:
  fixes x
  assumes "M = bernoulli_stream p"
and "0 \<le> p" and "p \<le> 1"
  shows "\<And> n. emeasure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)} =
    (emeasure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)"
proof -
  fix n
  define S where "S = {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)}"
  define precS where "precS = {w\<in> space M. (stake n w = stake n x)}"
  show "emeasure M S = emeasure M precS * prob_component p x n"
  proof (cases " n\<le> 0")
    case True
    hence "n=0" by simp
    hence "emeasure M S = (\<Prod>i\<in>{0..n}. prob_component p x i)" unfolding S_def
      using bernoulli_stream_pref_prob assms diff_Suc_1 le_refl by presburger
    also have "... = prob_component p x 0" using True by simp
    also have "... = emeasure M precS * prob_component p x n" using bernoulli_stream_npref_prob assms
      by (simp add: \<open>n=0\<close> precS_def)
    finally show "emeasure M S = emeasure M precS * prob_component p x n" .
  next
    case False
    hence "n \<ge> Suc 0" by simp
    hence "emeasure M S = (\<Prod>i\<in>{0..n}. prob_component p x i)" unfolding S_def
      using bernoulli_stream_pref_prob diff_Suc_1 le_refl assms by fastforce
    also have "... = (\<Prod>i\<in>{0..n-1}. prob_component p x i) * prob_component p x n" using \<open>n \<ge> Suc 0\<close>
      by (metis One_nat_def Suc_le_lessD Suc_pred prod.atLeast0_atMost_Suc)
    also have "... = emeasure M precS * prob_component p x n" using bernoulli_stream_pref_prob
      unfolding precS_def
      using \<open>Suc 0 \<le> n\<close> ennreal_mult'' assms prob_component_def by auto
    finally show "emeasure M S = emeasure M precS * prob_component p x n" .
  qed
qed

lemma  bernoulli_stream_element_prob_rec':
  fixes x
  assumes "M = bernoulli_stream p"
and "0 \<le> p" and "p \<le> 1"
  shows "\<And> n. measure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)} =
    (measure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)"
proof -
  fix n
  have "ennreal (measure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)}) =
    emeasure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)}"
    by (metis (no_types, lifting) assms(1) bernoulli_stream_def emeasure_eq_ennreal_measure
        emeasure_space ennreal_top_neq_one neq_top_trans prob_space.emeasure_space_1
        prob_space.prob_space_stream_space prob_space_measure_pmf)
  also have "... = (emeasure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)"
    using bernoulli_stream_element_prob_rec assms by simp
  also have "... = (measure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)"
  proof -
    have "prob_space M"
      using assms(1) bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf by auto
    then show ?thesis
      by (simp add: ennreal_mult'' finite_measure.emeasure_eq_measure mult.commute prob_space_def)
  qed
  finally have "ennreal (measure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)}) =
    (measure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)" .
  thus "measure M {w\<in> space M. (stake (Suc n) w = stake (Suc n) x)} =
    (measure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)"
    using assms prob_component_def by auto
qed

lemma (in infinite_coin_toss_space) bernoulli_stream_pseudo_prob_rec':
  fixes x
  assumes "pseudo_proj_True n x = x"
  shows "measure M (pseudo_proj_True (Suc n) -`{x}) =
    (measure M (pseudo_proj_True n-`{x}) * prob_component p x n)"
proof -
  have "pseudo_proj_True (Suc n) -`{x} = {w. (stake (Suc n) w = stake (Suc n) x)}" using pseudo_proj_True_preimage_stake
    assms by (metis pseudo_proj_True_Suc_proj)
  moreover have "pseudo_proj_True n -`{x} = {w. (stake n w = stake n x)}" using pseudo_proj_True_preimage_stake
    assms by simp
  ultimately show ?thesis using assms bernoulli_stream_element_prob_rec'
    by (simp add: bernoulli bernoulli_stream_space p_gt_0 p_lt_1)
qed


lemma (in infinite_coin_toss_space) bernoulli_stream_pref_prob_pos:
  fixes x
  assumes "0 < p"
and "p < 1"
  shows "emeasure M {w\<in> space M. (stake n w = stake n x)} > 0"
proof (induct n)
  case 0
  hence "emeasure M {w\<in> space M. (stake 0 w = stake 0 x)} = 1" using bernoulli_stream_npref_prob[of M p x]
    bernoulli by simp
  thus ?case by simp
next
  case (Suc n)
  have "emeasure M {w \<in> space M. stake (Suc n) w = stake (Suc n) x} =
    (emeasure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)" using bernoulli_stream_element_prob_rec
    bernoulli p_gt_0 p_lt_1 by simp
  thus ?case using Suc using assms p_gt_0 p_lt_1 prob_component_def
    by (simp add: ennreal_zero_less_mult_iff)
qed

lemma (in infinite_coin_toss_space) bernoulli_stream_pref_prob_neq_zero:
  fixes x
assumes "0 < p"
and "p < 1"
  shows "emeasure M {w\<in> space M. (stake n w = stake n x)} \<noteq> 0"
proof (induct n)
  case 0
  hence "emeasure M {w\<in> space M. (stake 0 w = stake 0 x)} = 1" using bernoulli_stream_npref_prob[of M p x]
    bernoulli by simp
  thus ?case by simp
next
  case (Suc n)
  have "emeasure M {w \<in> space M. stake (Suc n) w = stake (Suc n) x} =
    (emeasure M {w\<in> space M. (stake n w = stake n x)} * prob_component p x n)" using bernoulli_stream_element_prob_rec
    bernoulli assms by simp
  thus ?case using Suc using assms p_gt_0 p_lt_1 prob_component_def by auto
qed



lemma (in infinite_coin_toss_space) pseudo_proj_element_prob_pref:
  assumes "w\<in> range (pseudo_proj_True n)"
  shows "emeasure M {y\<in> space M. \<exists>x \<in> (pseudo_proj_True n -`{w}). y = c ## x} =
    prob_component p (c##w) 0 * emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)"
proof -
  have "pseudo_proj_True n w = w" using assms pseudo_proj_True_def pseudo_proj_True_stake by auto
  have "pseudo_proj_True (Suc n) (c##w) = c##w" using assms
          pseudo_proj_True_def pseudo_proj_True_stake by auto
  have "{y\<in> space M. \<exists>x \<in> (pseudo_proj_True n -`{w}). y = c ## x} = pseudo_proj_True (Suc n) -`{c##w} \<inter> space M"
  proof
    show "{y\<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. y = c ## x} \<subseteq> pseudo_proj_True (Suc n) -` {c ## w} \<inter> space M"
    proof
      fix y
      assume "y\<in> {y\<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. y = c ## x}"
      hence "y\<in> space M" and "\<exists>x \<in> pseudo_proj_True n -` {w}. y = c ## x" by auto
      from this obtain x where "x\<in> pseudo_proj_True n -` {w}" and "y = c## x" by auto
      have "pseudo_proj_True (Suc n) y = c##w" using \<open>x\<in> pseudo_proj_True n -` {w}\<close> \<open>y = c## x\<close>
        unfolding pseudo_proj_True_def by simp
      thus "y \<in> pseudo_proj_True (Suc n) -` {c ## w} \<inter> space M" using \<open>y\<in> space M\<close> by auto
    qed
    show "pseudo_proj_True (Suc n) -` {c ## w} \<inter> space M \<subseteq> {y\<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. y = c ## x}"
    proof
      fix y
      assume "y \<in> pseudo_proj_True (Suc n) -` {c ## w} \<inter> space M"
      hence "pseudo_proj_True (Suc n) y = c##w" and "y\<in> space M" by auto
      have "pseudo_proj_True n (stl y) = pseudo_proj_True n w"
      proof (rule pseudo_proj_True_snth')
        have "pseudo_proj_True (Suc n) (c##w) = c##w" using \<open>pseudo_proj_True (Suc n) (c##w) = c##w\<close> .
        also have "... = pseudo_proj_True (Suc n) y" using \<open>pseudo_proj_True (Suc n) y = c##w\<close> by simp
        finally have "pseudo_proj_True (Suc n) (c##w) = pseudo_proj_True (Suc n) y" .
        hence "\<And>i. Suc i \<le> Suc n \<Longrightarrow> (c##w)!! i = y!! i" by (simp add: pseudo_proj_True_snth)
        thus "\<And>i. Suc i \<le> n \<Longrightarrow> stl y !! i = w !! i" by fastforce
      qed
      also have "... = w" using assms pseudo_proj_True_def pseudo_proj_True_stake by auto
      finally have "pseudo_proj_True n (stl y) = w" .
      hence "stl y \<in> (pseudo_proj_True n) -` {w}" by simp
      moreover have "y = c##(stl y)"
      proof -
        have "stake (Suc n) y = stake (Suc n) (pseudo_proj_True (Suc n) y)" unfolding pseudo_proj_True_def
          using pseudo_proj_True_def pseudo_proj_True_stake by auto
        hence "shd y = shd (pseudo_proj_True (Suc n) y)" by simp
        also have "... = shd (c##w)" using \<open>pseudo_proj_True (Suc n) y = c##w\<close> by simp
        also have "... = c" by simp
        finally have "shd y = c" .
        thus ?thesis by (simp add: stream_eq_Stream_iff)
      qed
      ultimately show "y\<in> {y\<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. y = c ## x}" using \<open>y\<in> space M\<close> by auto
    qed
  qed
  hence "emeasure M {y\<in> space M. \<exists>x \<in> (pseudo_proj_True n -`{w}). y = c ## x} =
    emeasure M (pseudo_proj_True (Suc n) -`{c##w}\<inter> space M)" by simp
  also have "... = emeasure M {y\<in> space M. stake (Suc n) y = stake (Suc n) (c##w)}"
    using \<open>pseudo_proj_True (Suc n) (c##w) = c##w\<close> by (simp add:pseudo_proj_True_preimage_stake_space)
  also have "... = (\<Prod>i\<in>{0..n}. prob_component p (c##w) i)"
    using bernoulli_stream_pref_prob[of M p "Suc n" "c##w"] bernoulli p_lt_1 p_gt_0 diff_Suc_1 le_refl by simp
  also have "... = prob_component p (c##w) 0 * (\<Prod>i\<in>{1..n}. prob_component p (c##w) i)"
    by (simp add: decompose_init_prod)
  also have "... = prob_component p (c##w) 0 * (\<Prod>i\<in>{1..< Suc n}. prob_component p (c##w) i)"
  proof -
    have "(\<Prod>i\<in>{1..n}. prob_component p (c##w) i) = (\<Prod>i\<in>{1..< Suc n}. prob_component p (c##w) i)"
    proof (rule prod.cong)
      show "{1..n} = {1..<Suc n}" by auto
      show "\<And>x. x \<in> {1..<Suc n} \<Longrightarrow> prob_component p (c ## w) x = prob_component p (c ## w) x" by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = prob_component p (c##w) 0 * (\<Prod>i\<in>{0..< n}. prob_component p w i)"
  proof -
    have "(\<Prod>i\<in>{1..< Suc n}. prob_component p (c##w) i) = (\<Prod>i\<in>{0..< n}. prob_component p w i)"
    proof (rule prod.reindex_cong)
      show "inj_on (\<lambda>n. Suc n) {0..<n}" by simp
      show "{1..< Suc n} = Suc ` {0..< n}"  by auto
      show "\<And>x. x \<in> {0..< n} \<Longrightarrow> prob_component p (c ## w) (Suc x) = prob_component p w x"
        by (simp add: prob_component_def)
    qed
    thus ?thesis by simp
  qed
  also have "... = prob_component p (c##w) 0 * emeasure M {y \<in> space M. stake n y = stake n w}"
    using bernoulli_stream_pref_prob'[symmetric, of M p w n] ennreal_mult' p_gt_0 p_lt_1 bernoulli
    prob_component_def by auto
  also have "... = prob_component p (c##w) 0 * emeasure M (pseudo_proj_True n -` {w} \<inter> space M)"
    using pseudo_proj_True_preimage_stake_space \<open>pseudo_proj_True n w = w\<close>
    by (simp add: pseudo_proj_True_preimage_stake_space)
  finally show ?thesis .
qed

subsubsection \<open>Filtration equivalence for the natural filtration\<close>

lemma (in infinite_coin_toss_space) nat_filtration_null_set:
  assumes "A\<in> sets (nat_filtration n)"
and "0 < p"
and "p  < 1"
and "emeasure M A = 0"
shows "A = {}"
proof (rule ccontr)
  assume "A\<noteq> {}"
  hence "\<exists>w. w\<in> A" by auto
  from this obtain w where "w \<in> A" by auto
  hence inc: "pseudo_proj_True n -` {pseudo_proj_True n w} \<subseteq> A" using assms by (simp add: set_filt_contain)
  have "0 < emeasure M {x\<in> space M. (stake n x = stake n (pseudo_proj_True n w))}" using assms by (simp add: bernoulli_stream_pref_prob_pos)
  also have "... = emeasure M (pseudo_proj_True n -` {pseudo_proj_True n w})" using pseudo_proj_True_preimage_stake
    pseudo_proj_True_proj bernoulli bernoulli_stream_space by simp
  also have "... \<le> emeasure M A"
  proof (rule emeasure_mono, (simp add: inc))
    show "A \<in> events" using assms nat_discrete_filtration unfolding filtration_def subalgebra_def by auto
  qed
  finally have "0 < emeasure M A" .
  thus False using assms by simp
qed

lemma (in infinite_coin_toss_space) nat_filtration_AE_zero:
  fixes f::"bool stream \<Rightarrow> real"
  assumes "AE w in M. f w = 0"
and "f\<in> borel_measurable (nat_filtration n)"
and "0 < p"
and "p < 1"
  shows "\<forall>w. f w = 0"
proof -
  from \<open>AE w in M. f w = 0\<close> obtain N' where Nprops: "{w\<in> space M. \<not>f w = 0} \<subseteq> N'" "N'\<in> sets M" "emeasure M N' = 0"
    by (force elim:AE_E)
  have "{w\<in> space M. f w < 0} \<in> sets (nat_filtration n)"
    by (metis (no_types) assms(2) bernoulli bernoulli_stream_space borel_measurable_iff_less nat_filtration_space streams_UNIV)
  moreover have "{w\<in> space M. f w > 0} \<in> sets (nat_filtration n)"
    by (metis (no_types) assms(2) bernoulli bernoulli_stream_space borel_measurable_iff_greater nat_filtration_space streams_UNIV)
  moreover have "{w\<in> space M. \<not>f w = 0} = {w\<in> space M. f w < 0} \<union> {w\<in> space M. f w > 0}" by auto
  ultimately have "{w\<in> space M. \<not>f w = 0} \<in> sets (nat_filtration n)" by auto
  hence "emeasure M {w\<in> space M. \<not>f w = 0} = 0" using Nprops by (metis (no_types, lifting) emeasure_eq_0)
  hence "{w\<in> space M. \<not>f w = 0} = {}" using \<open>{w\<in> space M. \<not>f w = 0} \<in> sets (nat_filtration n)\<close>
      nat_filtration_null_set[of "{w \<in> space M. f w \<noteq> 0}" n] assms by simp
  hence "{w. f w\<noteq> 0} = {}" by (simp add:bernoulli_stream_space bernoulli)
  thus ?thesis by auto
qed


lemma (in infinite_coin_toss_space) nat_filtration_AE_eq:
  fixes f::"bool stream \<Rightarrow> real"
  assumes "AE w in M. f w = g w"
and "0 < p"
and "p < 1"
and "f\<in> borel_measurable (nat_filtration n)"
and "g\<in> borel_measurable (nat_filtration n)"
  shows "f w = g w"
proof -
  define diff where "diff = (\<lambda>w. f w - g w)"
  have "AE w in M. diff w = 0"
  proof (rule AE_mp)
    show "AE w in M. f w = g w" using assms by simp
    show "AE w in M. f w = g w \<longrightarrow> diff w = 0"
      by (rule AE_I2, intro impI, (simp add: diff_def))
  qed
  have "\<forall>w. diff w = 0"
  proof (rule nat_filtration_AE_zero)
    show "AE w in M. diff w = 0" using \<open>AE w in M. diff w = 0\<close> .
    show "diff \<in> borel_measurable (nat_filtration n)" using assms unfolding diff_def by simp
    show "0 < p" and "p < 1" using assms by auto
  qed
  thus "f w = g w" unfolding diff_def by auto
qed



lemma (in infinite_coin_toss_space) bernoulli_stream_equiv:
  assumes "N = bernoulli_stream q"
and "0 < p"
and "p < 1"
and "0 < q"
and "q < 1"
shows "filt_equiv nat_filtration M N" unfolding filt_equiv_def
proof (intro conjI)
  have "sets (stream_space (measure_pmf (bernoulli_pmf p))) = sets (stream_space (measure_pmf (bernoulli_pmf q)))"
    by (rule sets_stream_space_cong, simp)
  thus "events = sets N" using assms bernoulli unfolding bernoulli_stream_def by simp
  show "filtration M nat_filtration" by (simp add:nat_discrete_filtration)
  show "\<forall>t A. A \<in> sets (nat_filtration t) \<longrightarrow> (emeasure M A = 0) = (emeasure N A = 0)"
  proof (intro allI impI)
    fix n
    fix A
    assume "A\<in> sets (nat_filtration n)"
    show "(emeasure M A = 0) = (emeasure N A = 0)"
    proof
    {
      assume "emeasure M A = 0"
      hence "A = {}" using \<open>A\<in> sets (nat_filtration n)\<close> using assms by (simp add:nat_filtration_null_set)
      thus "emeasure N A = 0" by simp
    }
    {
      assume "emeasure N A = 0"
      hence "A = {}" using \<open>A\<in> sets (nat_filtration n)\<close> infinite_coin_toss_space.nat_filtration_null_set[of q N A n]
        assms
        using \<open>events = sets N\<close> bernoulli bernoulli_stream_space infinite_coin_toss_space.nat_filtration_sets
          infinite_coin_toss_space_def nat_filtration_sets by force
      thus "emeasure M A = 0" by simp
    }
    qed
  qed
qed

lemma (in infinite_coin_toss_space) bernoulli_nat_filtration:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
and "0 < p"
and "p < 1"
shows "infinite_cts_filtration q N nat_filtration"
proof (unfold_locales)
  have "0 < q" using assms by simp
  thus "0 \<le> q" by simp
  have "q < 1" using assms by simp
  thus "q \<le> 1" by simp
  show "N = bernoulli_stream q" using assms by simp
  show "nat_filtration = infinite_coin_toss_space.nat_filtration N"
  proof -
    have "filt_equiv nat_filtration M N" using \<open>q < 1\<close> \<open>0 < q\<close>
      by (simp add: assms bernoulli_stream_equiv)
    hence "sets M = sets N" unfolding filt_equiv_def by simp
    hence "space M = space N" using sets_eq_imp_space_eq by auto
    have "\<forall>m. nat_filtration m = infinite_coin_toss_space.nat_filtration N m"
    proof
      fix m
      have "infinite_coin_toss_space.nat_filtration N m = fct_gen_subalgebra N N (pseudo_proj_True m)"
        using \<open>0 \<le> q\<close> \<open>N = bernoulli_stream q\<close> \<open>q \<le> 1\<close> infinite_coin_toss_space.intro
        infinite_coin_toss_space.nat_filtration_def by blast
      thus "nat_filtration m = infinite_coin_toss_space.nat_filtration N m"
        unfolding nat_filtration_def
        using fct_gen_subalgebra_cong[of M N M N "pseudo_proj_True m"] \<open>sets M = sets N\<close> \<open>space M = space N\<close>
        by simp
    qed
    thus ?thesis by auto
  qed
qed


subsubsection \<open>More results on the projection function\<close>

lemma (in infinite_coin_toss_space) pseudo_proj_True_Suc_prefix:
  shows "pseudo_proj_True (Suc n) w = (w!!0)## pseudo_proj_True n (stl w)"
proof -
  have "pseudo_proj_True (Suc n) w = shift (stake (Suc n) w) (sconst True)" unfolding pseudo_proj_True_def by simp
  also have "... = shift (w!!0 # (stake n (stl w))) (sconst True)" by simp
  also have "... = w!!0 ## shift (stake n (stl w)) (sconst True)" by simp
  also have "... = w!!0 ## pseudo_proj_True n (stl w)" unfolding pseudo_proj_True_def by simp
  finally show ?thesis .
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_img:
  assumes "pseudo_proj_True n w = w"
  shows "w\<in> range (pseudo_proj_True n)"
  by (metis assms rangeI)

lemma (in infinite_coin_toss_space) sconst_if:
  assumes "\<And>n. snth w n = True"
  shows "w = sconst True"
proof -
  obtain nn :: "(bool \<Rightarrow> bool) \<Rightarrow> bool stream \<Rightarrow> bool stream \<Rightarrow> nat" where
    "\<And>p s n sa sb na pa sc pb sd se. (\<not> p (s !! n::bool) \<or> smap p s \<noteq> sa \<or> sa !! n) \<and> (\<not> sb !! na \<or> smap pa sc \<noteq> sb \<or> pa (sc !! na::bool)) \<and> (\<not> pb (sd !! nn pb sd se) \<or> \<not> se !! nn pb sd se \<or> smap pb sd = se)"
    using smap_alt by moura
  then show ?thesis
    by (metis (no_types) assms eq_id_iff id_funpow snth_siterate)
qed

lemma (in infinite_coin_toss_space) pseudo_proj_True_suc_img_pref:
  shows "range (pseudo_proj_True (Suc n)) = {y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w} \<union>
    {y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}"
proof
  show "range (pseudo_proj_True (Suc n))
    \<subseteq> {y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w} \<union> {y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}"
  proof
    fix x
    assume "x \<in> range (pseudo_proj_True (Suc n))"
    hence "x = pseudo_proj_True (Suc n) x" using pseudo_proj_True_proj by auto
    define xp where "xp = stl x"
    have "xp = stl (shift (stake (Suc n) x) (sconst True))" using \<open>x = pseudo_proj_True (Suc n) x\<close>
      unfolding xp_def pseudo_proj_True_def by simp
    also have "... = shift ((stake n (stl x))) (sconst True)" by simp
    finally have "xp = shift ((stake n (stl x))) (sconst True)" .
    hence "xp \<in> range (pseudo_proj_True n)" using  pseudo_proj_True_def by auto
    show "x\<in> {y. \<exists>w \<in> range (pseudo_proj_True n) . y = True ## w} \<union> {y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}"
    proof (cases "snth x 0")
      case True
      have "x = True ## xp" unfolding xp_def using True by (simp add: stream_eq_Stream_iff)
      hence "x \<in> {y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}" using \<open>xp \<in> range (pseudo_proj_True n)\<close> by auto
      thus ?thesis by auto
    next
      case False
      have "x = False ## xp" unfolding xp_def using False by (simp add: stream_eq_Stream_iff)
      hence "x \<in> {y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}" using \<open>xp \<in> range (pseudo_proj_True n)\<close> by auto
      thus ?thesis by auto
    qed
  qed
  have "{y. \<exists>w \<in> range (pseudo_proj_True n) . y = True ## w} \<subseteq> range (pseudo_proj_True (Suc n))"
  proof
    fix y
    assume "y \<in> {y. \<exists>w \<in> range (pseudo_proj_True n) . y = True ## w}"
    hence "\<exists>w. w \<in> range (pseudo_proj_True n) \<and> y = True ## w" by auto
    from this obtain w where "w\<in> range (pseudo_proj_True n)" and "y = True ## w" by auto
    have "w = pseudo_proj_True n w" using pseudo_proj_True_proj \<open>w\<in> range (pseudo_proj_True n)\<close> by auto
    hence "y = True ## (shift (stake n w) (sconst True))" using \<open>y = True ## w\<close> unfolding pseudo_proj_True_def by simp
    also have "... = shift (stake (Suc n) (True ## w)) (sconst True)" by simp
    also have "... = pseudo_proj_True (Suc n) (True ## w)" unfolding pseudo_proj_True_def by simp
    finally have "y = pseudo_proj_True (Suc n) (True##w)" .
    thus "y \<in> range (pseudo_proj_True (Suc n))" by simp
  qed
  moreover have "{y. \<exists>w \<in> range (pseudo_proj_True n) . y = False ## w} \<subseteq> range (pseudo_proj_True (Suc n))"
  proof
    fix y
    assume "y \<in> {y. \<exists>w \<in> range (pseudo_proj_True n) . y = False ## w}"
    hence "\<exists>w. w \<in> range (pseudo_proj_True n) \<and> y = False ## w" by auto
    from this obtain w where "w\<in> range (pseudo_proj_True n)" and "y = False ## w" by auto
    have "w = pseudo_proj_True n w" using pseudo_proj_True_proj \<open>w\<in> range (pseudo_proj_True n)\<close> by auto
    hence "y = False ## (shift (stake n w) (sconst True))" using \<open>y = False ## w\<close> unfolding pseudo_proj_True_def by simp
    also have "... = shift (stake (Suc n) (False ## w)) (sconst True)" by simp
    also have "... = pseudo_proj_True (Suc n) (False ## w)" unfolding pseudo_proj_True_def by simp
    finally have "y = pseudo_proj_True (Suc n) (False##w)" .
    thus "y \<in> range (pseudo_proj_True (Suc n))" by simp
  qed
  ultimately show "{y. \<exists>w \<in> range (pseudo_proj_True n) . y = True ## w} \<union>
   {y. \<exists>w \<in> range (pseudo_proj_True n) . y = False ## w} \<subseteq> range (pseudo_proj_True (Suc n))" by simp
qed

lemma (in infinite_coin_toss_space) reindex_pseudo_proj:
  shows "(\<Sum>w\<in>range (pseudo_proj_True n). f (c ## w)) =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = c ## w}.f y)"
proof (rule sum.reindex_cong[symmetric],auto)
  define ccons where "ccons = (\<lambda>w. c## w)"
  show "inj_on ccons (range (pseudo_proj_True n))"
  proof
    fix x y
    assume "x\<in> range (pseudo_proj_True n)" and "y\<in> range (pseudo_proj_True n)" and "ccons x = ccons y"
    hence "c##x = c##y" unfolding ccons_def by simp
    thus "x = y" by simp
  qed
qed


lemma (in infinite_coin_toss_space) pseudo_proj_True_imp_False:
  assumes "pseudo_proj_True n w = pseudo_proj_True n x"
  shows "pseudo_proj_False n w = pseudo_proj_False n x"
  by (metis assms pseudo_proj_False_def pseudo_proj_True_stake)


lemma (in infinite_coin_toss_space) pseudo_proj_Suc_prefix:
  assumes "pseudo_proj_True n w = pseudo_proj_True n x"
  shows "pseudo_proj_True (Suc n) w \<in> {pseudo_proj_True n x, pseudo_proj_False n x}"
proof -
  have "pseudo_proj_False n w = pseudo_proj_False n x" using assms pseudo_proj_True_imp_False[of n w x] by simp
  hence "{pseudo_proj_True n w, pseudo_proj_False n w} = {pseudo_proj_True n x, pseudo_proj_False n x}" using assms by simp
  thus ?thesis using pseudo_proj_True_suc_img[of n w] by simp
qed


lemma (in infinite_coin_toss_space) pseudo_proj_Suc_preimage:
  shows "range (pseudo_proj_True (Suc n)) \<inter> (pseudo_proj_True n) -` {pseudo_proj_True n x} =
    {pseudo_proj_True n x, pseudo_proj_False n x}"
proof
  show "range (pseudo_proj_True (Suc n)) \<inter> pseudo_proj_True n -` {pseudo_proj_True n x}
    \<subseteq> {pseudo_proj_True n x, pseudo_proj_False n x}"
  proof
    fix w
    assume "w\<in> range (pseudo_proj_True (Suc n)) \<inter> pseudo_proj_True n -` {pseudo_proj_True n x}"
    hence "w\<in> range (pseudo_proj_True (Suc n))" and "w\<in> pseudo_proj_True n -` {pseudo_proj_True n x}" by auto
    hence "pseudo_proj_True n w = pseudo_proj_True n x" by simp
    have "w = pseudo_proj_True (Suc n) w" using \<open>w\<in> range (pseudo_proj_True (Suc n))\<close>
      using pseudo_proj_True_proj by auto
    also have "... \<in> {pseudo_proj_True n x, pseudo_proj_False n x}" using \<open>pseudo_proj_True n w = pseudo_proj_True n x\<close>
      pseudo_proj_Suc_prefix by simp
    finally show "w \<in> {pseudo_proj_True n x, pseudo_proj_False n x}" .
  qed
  show "{pseudo_proj_True n x, pseudo_proj_False n x}
    \<subseteq> range (pseudo_proj_True (Suc n)) \<inter> pseudo_proj_True n -` {pseudo_proj_True n x}"
  proof -
    have "pseudo_proj_True n x \<in> range (pseudo_proj_True (Suc n)) \<inter> pseudo_proj_True n -` {pseudo_proj_True n x}"
      by (simp add: pseudo_proj_True_Suc_proj pseudo_proj_True_img pseudo_proj_True_proj)
    moreover have "pseudo_proj_False n x \<in> range (pseudo_proj_True (Suc n)) \<inter> pseudo_proj_True n -` {pseudo_proj_True n x}"
      by (metis (no_types, lifting) Int_iff UnI2 infinite_coin_toss_space.pseudo_proj_False_def infinite_coin_toss_space_axioms
          pseudo_proj_True_Suc_False_proj pseudo_proj_True_inverse_induct pseudo_proj_True_stake rangeI singletonI vimage_eq)
    ultimately show ?thesis by auto
  qed
qed


lemma (in infinite_cts_filtration) f_borel_Suc_preimage:
  assumes "f\<in> measurable (F n) N"
  and "set_discriminating n f N"
  shows "range (pseudo_proj_True (Suc n)) \<inter> f -` {f x} =
  (pseudo_proj_True n) ` (f -` {f x}) \<union> (pseudo_proj_False n) ` (f -` {f x})"
proof -
  have "range (pseudo_proj_True (Suc n)) \<inter> f -` {f x} =
    (\<Union> w\<in> {y. f y = f x}.{pseudo_proj_True n w, pseudo_proj_False n w})"
  proof
    show "range (pseudo_proj_True (Suc n)) \<inter> f -` {f x} \<subseteq> (\<Union>w\<in>{y. f y = f x}. {pseudo_proj_True n w, pseudo_proj_False n w})"
    proof
      fix w
      assume "w\<in> range (pseudo_proj_True (Suc n)) \<inter> f -` {f x}"
      hence "w\<in> range (pseudo_proj_True (Suc n))" and "w\<in> f -` {f x}" by auto
      hence "f w = f x" by simp
      hence "w\<in> {y. f y = f x}" by simp
      have "w = pseudo_proj_True (Suc n) w" using \<open>w\<in> range (pseudo_proj_True (Suc n))\<close>
        using pseudo_proj_True_proj by auto
      also have "... \<in> {pseudo_proj_True n w, pseudo_proj_False n w}"
        using pseudo_proj_Suc_prefix by auto
      also have "... \<subseteq> (\<Union>w\<in>{y. f y = f x}. {pseudo_proj_True n w, pseudo_proj_False n w})" using \<open>w\<in> {y. f y = f x}\<close>
        by auto
      finally show "w \<in> (\<Union>w\<in>{y. f y = f x}. {pseudo_proj_True n w, pseudo_proj_False n w})" .
    qed
    show "(\<Union>w\<in>{y. f y = f x}. {pseudo_proj_True n w, pseudo_proj_False n w})
      \<subseteq> range (pseudo_proj_True (Suc n)) \<inter> f -` {f x}"
    proof
      fix w
      assume "w \<in> (\<Union>w\<in>{y. f y = f x}. {pseudo_proj_True n w, pseudo_proj_False n w})"
      hence "\<exists>y. f y = f x \<and> w\<in> {pseudo_proj_True n y, pseudo_proj_False n y}" by auto
      from this obtain y where "f y = f x" and "w\<in> {pseudo_proj_True n y, pseudo_proj_False n y}" by auto
      hence "w = pseudo_proj_True n y \<or> w = pseudo_proj_False n y" by auto
      show "w \<in> range (pseudo_proj_True (Suc n)) \<inter> f -` {f x}"
      proof (cases "w = pseudo_proj_True n y")
        case True
        hence "f w = f y" using assms nat_filtration_not_borel_info natural_filtration
          by (metis comp_apply)
        thus ?thesis using \<open>f y = f x\<close>
          by (simp add: True pseudo_proj_True_Suc_proj pseudo_proj_True_img)
      next
        case False
        hence "f w = f y" using assms nat_filtration_not_borel_info natural_filtration
          by (metis Int_iff \<open>w \<in> {pseudo_proj_True n y, pseudo_proj_False n y}\<close>
              comp_apply pseudo_proj_Suc_preimage singletonD vimage_eq)
      thus ?thesis using \<open>f y = f x\<close>
        using \<open>w \<in> {pseudo_proj_True n y, pseudo_proj_False n y}\<close> pseudo_proj_Suc_preimage by auto
      qed
    qed
  qed
  also have "... =
    (\<Union> w\<in> {y. f y = f x}.{pseudo_proj_True n w}) \<union> (\<Union> w\<in> {y. f y = f x}.{pseudo_proj_False n w})" by auto
  also have "... = (pseudo_proj_True n) ` {y. f y = f x} \<union> (pseudo_proj_False n) `{y. f y = f x}" by auto
  also have "... = (pseudo_proj_True n) ` (f -` {f x}) \<union> (pseudo_proj_False n) ` (f -` {f x})" by auto
  finally show ?thesis .
qed



lemma (in infinite_cts_filtration) pseudo_proj_preimage:
  assumes "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  shows "pseudo_proj_True n -` (g -` {g z}) = pseudo_proj_True n -` (pseudo_proj_True n `(g -` {g z}))"
proof
  show "pseudo_proj_True n -` g -` {g z} \<subseteq> pseudo_proj_True n -` pseudo_proj_True n ` g -` {g z}"
  proof
    fix w
    assume "w\<in> pseudo_proj_True n -` g -` {g z}"
    have "pseudo_proj_True n w = pseudo_proj_True n (pseudo_proj_True n w)"
      by (simp add: pseudo_proj_True_proj)
    also have "... \<in> pseudo_proj_True n `(g -` {g z})" using \<open>w\<in> pseudo_proj_True n -` g -` {g z}\<close>
      by simp
    finally have "pseudo_proj_True n w \<in> pseudo_proj_True n `(g -` {g z})" .
    thus "w\<in> pseudo_proj_True n -` (pseudo_proj_True n `(g -` {g z}))" by simp
  qed
  show "pseudo_proj_True n -` pseudo_proj_True n ` g -` {g z} \<subseteq> pseudo_proj_True n -` g -` {g z}"
  proof
    fix w
    assume "w \<in> pseudo_proj_True n -` pseudo_proj_True n ` g -` {g z}"
    hence "\<exists>y. pseudo_proj_True n w = pseudo_proj_True n y \<and> g y = g z" by auto
    from this obtain y where "pseudo_proj_True n w = pseudo_proj_True n y" and "g y = g z" by auto
    have "g (pseudo_proj_True n w) = g (pseudo_proj_True n y)" using \<open>pseudo_proj_True n w = pseudo_proj_True n y\<close>
      by simp
    also have "... = g y" using assms nat_filtration_not_borel_info natural_filtration by (metis comp_apply)
    also have "... = g z" using \<open>g y = g z\<close> .
    finally have "g (pseudo_proj_True n w) = g z" .
    thus "w\<in> pseudo_proj_True n -` g -` {g z}" by simp
  qed
qed


lemma (in infinite_cts_filtration) borel_pseudo_proj_preimage:
  fixes g::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "g\<in> borel_measurable (F n)"
  shows "pseudo_proj_True n -` (g -` {g z}) = pseudo_proj_True n -` (pseudo_proj_True n `(g -` {g z}))"
  using pseudo_proj_preimage[of g n borel z] set_discriminating_if[of g n] natural_filtration assms by simp

lemma (in infinite_cts_filtration) pseudo_proj_False_preimage:
  assumes "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  shows "pseudo_proj_False n -` (g -` {g z}) = pseudo_proj_False n -` (pseudo_proj_False n `(g -` {g z}))"
proof
  show "pseudo_proj_False n -` g -` {g z} \<subseteq> pseudo_proj_False n -` pseudo_proj_False n ` g -` {g z}"
  proof
    fix w
    assume "w\<in> pseudo_proj_False n -` g -` {g z}"
    have "pseudo_proj_False n w = pseudo_proj_False n (pseudo_proj_False n w)"
      using pseudo_proj_False_def pseudo_proj_False_stake by auto
    also have "... \<in> pseudo_proj_False n `(g -` {g z})" using \<open>w\<in> pseudo_proj_False n -` g -` {g z}\<close>
      by simp
    finally have "pseudo_proj_False n w \<in> pseudo_proj_False n `(g -` {g z})" .
    thus "w\<in> pseudo_proj_False n -` (pseudo_proj_False n `(g -` {g z}))" by simp
  qed
  show "pseudo_proj_False n -` pseudo_proj_False n ` g -` {g z} \<subseteq> pseudo_proj_False n -` g -` {g z}"
  proof
    fix w
    assume "w \<in> pseudo_proj_False n -` pseudo_proj_False n ` g -` {g z}"
    hence "\<exists>y. pseudo_proj_False n w = pseudo_proj_False n y \<and> g y = g z" by auto
    from this obtain y where "pseudo_proj_False n w = pseudo_proj_False n y" and "g y = g z" by auto
    have "g (pseudo_proj_False n w) = g (pseudo_proj_False n y)" using \<open>pseudo_proj_False n w = pseudo_proj_False n y\<close>
      by simp
    also have "... = g y" using assms nat_filtration_not_borel_info' natural_filtration by (metis comp_apply)
    also have "... = g z" using \<open>g y = g z\<close> .
    finally have "g (pseudo_proj_False n w) = g z" .
    thus "w\<in> pseudo_proj_False n -` g -` {g z}" by simp
  qed
qed

lemma (in infinite_cts_filtration) borel_pseudo_proj_False_preimage:
  fixes g::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "g\<in> borel_measurable (F n)"
  shows "pseudo_proj_False n -` (g -` {g z}) = pseudo_proj_False n -` (pseudo_proj_False n `(g -` {g z}))"
using pseudo_proj_False_preimage[of g n borel z] set_discriminating_if[of g n] natural_filtration assms by simp


lemma (in infinite_cts_filtration) pseudo_proj_preimage':
  assumes "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  shows "pseudo_proj_True n -` (g -` {g z}) = g -` {g z}"
proof
  show "pseudo_proj_True n -` g -` {g z} \<subseteq> g -` {g z}"
  proof
    fix w
    assume "w\<in> pseudo_proj_True n -` g -` {g z}"
    have "g w = g (pseudo_proj_True n w)" using assms nat_filtration_not_borel_info natural_filtration
      by (metis comp_apply)
    also have "... = g z" using \<open>w\<in> pseudo_proj_True n -` g -` {g z}\<close> by simp
    finally have "g w = g z".
    thus "w\<in> g -`{g z}" by simp
  qed
  show "g -` {g z} \<subseteq> pseudo_proj_True n -` g -` {g z}"
  proof
    fix w
    assume "w \<in> g -` {g z}"
    have "g (pseudo_proj_True n w) = g w" using assms nat_filtration_not_borel_info natural_filtration
      by (metis comp_apply)
    also have "... = g z" using \<open>w\<in> g -`{g z}\<close> by simp
    finally have "g (pseudo_proj_True n w) = g z" .
    thus "w\<in> pseudo_proj_True n -` g -` {g z}" by simp
  qed
qed

lemma (in infinite_cts_filtration) borel_pseudo_proj_preimage':
  fixes g::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "g\<in> borel_measurable (F n)"
  shows "pseudo_proj_True n -` (g -` {g z}) = g -` {g z}"
  using assms natural_filtration by (simp add: set_discriminating_if pseudo_proj_preimage')


lemma (in infinite_cts_filtration) pseudo_proj_False_preimage':
  assumes "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  shows "pseudo_proj_False n -` (g -` {g z}) = g -` {g z}"
proof
  show "pseudo_proj_False n -` g -` {g z} \<subseteq> g -` {g z}"
  proof
    fix w
    assume "w\<in> pseudo_proj_False n -` g -` {g z}"
    have "g w = g (pseudo_proj_False n w)" using assms nat_filtration_not_borel_info' natural_filtration
      by (metis comp_apply)
    also have "... = g z" using \<open>w\<in> pseudo_proj_False n -` g -` {g z}\<close> by simp
    finally have "g w = g z".
    thus "w\<in> g -`{g z}" by simp
  qed
  show "g -` {g z} \<subseteq> pseudo_proj_False n -` g -` {g z}"
  proof
    fix w
    assume "w \<in> g -` {g z}"
    have "g (pseudo_proj_False n w) = g w" using assms nat_filtration_not_borel_info' natural_filtration
      by (metis comp_apply)
    also have "... = g z" using \<open>w\<in> g -`{g z}\<close> by simp
    finally have "g (pseudo_proj_False n w) = g z" .
    thus "w\<in> pseudo_proj_False n -` g -` {g z}" by simp
  qed
qed


lemma (in infinite_cts_filtration) borel_pseudo_proj_False_preimage':
  fixes g::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "g\<in> borel_measurable (F n)"
  shows "pseudo_proj_False n -` (g -` {g z}) = g -` {g z}"
using assms natural_filtration by (simp add: set_discriminating_if pseudo_proj_False_preimage')

subsubsection \<open>Integrals and conditional expectations on the natural filtration\<close>

lemma (in infinite_cts_filtration) cst_integral:
  fixes f::"bool stream\<Rightarrow>real"
  assumes "f \<in> borel_measurable (F 0)"
  and "f (sconst True) = c"
shows "has_bochner_integral M f c"
proof -
  have "space M = space (F 0)"  using filtration by (simp add: filtration_def subalgebra_def)
  have "f\<in> borel_measurable M"
    using assms(1) nat_filtration_borel_measurable_integrable natural_filtration by blast
  have "\<exists>d. \<forall>x\<in> space (F 0). f x = d"
  proof (rule triv_measurable_cst)
    show "space (F 0) = space M" using \<open>space M = space (F 0)\<close> ..
    show "sets (F 0) = {{}, space M}" using info_disc_filtr
      by (simp add: init_triv_filt_def bot_nat_def)
    show "f \<in> borel_measurable (F 0)" using assms by simp
    show "space M \<noteq> {}" by (simp add:not_empty)
  qed
  from this obtain d where "\<forall>x\<in> space (F 0). f x = d" by auto
  hence "\<forall> x\<in> space M. f x = d" using \<open>space M = space (F 0)\<close> by simp
  hence "f (sconst True) = d" using bernoulli_stream_space bernoulli  by simp
  hence "c = d" using assms by simp
  hence "\<forall>x\<in> space M. f x = c" using \<open>\<forall> x\<in> space M. f x = d\<close> \<open>c = d\<close> by simp
  have "f\<in> borel_measurable M"
    using assms(1) nat_filtration_borel_measurable_integrable natural_filtration by blast
  have "integral\<^sup>N M f = integral\<^sup>N M (\<lambda>w. c)"
  proof (rule nn_integral_cong)
    fix x
    assume "x\<in> space M"
    thus "ennreal (f x) = ennreal c" using \<open>\<forall> x\<in> space M. f x = d\<close> \<open>c = d\<close> by auto
  qed
  also have "... = integral\<^sup>N M (\<lambda>w. c * (indicator (space M)) w)"
    by (simp add: nn_integral_cong)
  also have "... = ennreal c * emeasure M (space M)" using nn_integral_cmult_indicator[of "space M" M c]
    by (simp add: nn_integral_cong)
  also have "... = ennreal c" by (simp add: emeasure_space_1)
  finally have "integral\<^sup>N M f = ennreal c" .
  hence "integral\<^sup>N M (\<lambda>x. - f x) = ennreal (-c)"
    by (simp add: \<open>\<forall>x\<in>space M. f x = d\<close> \<open>c = d\<close> emeasure_space_1 nn_integral_cong)
  show "has_bochner_integral M f c"
  proof (cases "0 \<le> c")
    case True
    hence "AE x in M. 0 \<le> f x" using \<open>\<forall>x\<in> space M. f x = c\<close> by simp
    thus ?thesis using \<open>random_variable borel f\<close> True
      \<open>integral\<^sup>N M f = ennreal c\<close> by (simp add: has_bochner_integral_nn_integral)
  next
    case False
    let ?mf = "\<lambda>w. - f w"
    have "AE x in M. 0 \<le> ?mf x" using \<open>\<forall>x\<in> space M. f x = c\<close> False by simp
    hence "has_bochner_integral M ?mf (-c)" using \<open>random_variable borel f\<close> False
      \<open>integral\<^sup>N M (\<lambda>x. - f x) = ennreal (-c)\<close> by (simp add: has_bochner_integral_nn_integral)
    thus ?thesis using has_bochner_integral_minus by fastforce
  qed
qed

lemma (in infinite_cts_filtration) cst_nn_integral:
  fixes f::"bool stream\<Rightarrow>real"
  assumes "f \<in> borel_measurable (F 0)"
  and "\<And>w. 0 \<le> f w"
  and "f (sconst True) = c"
shows "integral\<^sup>N M f = ennreal c" using assms cst_integral
  by (simp add: assms(1) has_bochner_integral_iff nn_integral_eq_integral)

lemma (in infinite_cts_filtration) suc_measurable:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f\<in> borel_measurable (F (Suc n))"
  shows "(\<lambda>w. f (c ## w)) \<in> borel_measurable (F n)"
proof -
  have "(\<lambda>w. f (c ## w)) \<in> borel_measurable (nat_filtration n)"
  proof (rule nat_filtration_comp_measurable)
    have "f\<in> borel_measurable M" using assms
      using measurable_from_subalg nat_filtration_subalgebra natural_filtration by blast
    hence "f\<in> borel_measurable (stream_space (measure_pmf (bernoulli_pmf p)))" using bernoulli unfolding bernoulli_stream_def by simp
    have "(\<lambda>w. c ## w) \<in> (stream_space (measure_pmf (bernoulli_pmf p))  \<rightarrow>\<^sub>M stream_space (measure_pmf (bernoulli_pmf p)))"
    proof (rule measurable_Stream)
      show "(\<lambda>x. c) \<in> stream_space (measure_pmf (bernoulli_pmf p)) \<rightarrow>\<^sub>M measure_pmf (bernoulli_pmf p)" by simp
      show "(\<lambda>x. x) \<in> stream_space (measure_pmf (bernoulli_pmf p)) \<rightarrow>\<^sub>M stream_space (measure_pmf (bernoulli_pmf p))" by simp
    qed
    hence "(\<lambda>w. f (c ## w)) \<in> (stream_space (measure_pmf (bernoulli_pmf p))  \<rightarrow>\<^sub>M borel)" using \<open>f\<in> borel_measurable (stream_space (measure_pmf (bernoulli_pmf p)))\<close>
        measurable_comp[of "(\<lambda>w. c ## w)" "stream_space (measure_pmf (bernoulli_pmf p))" "stream_space (measure_pmf (bernoulli_pmf p))" f borel]
      by simp
    thus "random_variable borel (\<lambda>w. f (c ## w))" using  bernoulli unfolding bernoulli_stream_def by simp
    have "\<forall>w. f (c ## (pseudo_proj_True n w)) = f (c##w)"
    proof
      fix w
      have "c## (pseudo_proj_True n w) = pseudo_proj_True (Suc n) (c##w)" unfolding pseudo_proj_True_def by simp
      hence "f (c ## (pseudo_proj_True n w)) = f (pseudo_proj_True (Suc n) (c##w))" by simp
      also have "... = f (c##w)" using assms nat_filtration_info[of f "Suc n"] natural_filtration
        by (metis comp_apply)
      finally show "f (c ## (pseudo_proj_True n w)) = f (c##w)" .
    qed
    thus "(\<lambda>w. f (c ## w)) \<circ> pseudo_proj_True n = (\<lambda>w. f (c ## w))" by auto
  qed
  thus "(\<lambda>w. f (c ## w)) \<in> borel_measurable (F n)" using natural_filtration by simp
qed




lemma (in infinite_cts_filtration) F_n_nn_integral_pos:
  fixes f::"bool stream\<Rightarrow>real"
  shows "\<And>f. (\<forall>x. 0 \<le> f x) \<Longrightarrow> f \<in> borel_measurable (F n) \<Longrightarrow> integral\<^sup>N M f =
    (\<Sum> w\<in> range (pseudo_proj_True n). (emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *  ennreal (f w))"
proof (induct n)
  case 0
  have "range (pseudo_proj_True 0) = {sconst True}"
  proof
    have "\<And>w. pseudo_proj_True 0 w = sconst True"
    proof -
      fix w
      show "pseudo_proj_True 0 w = sconst True" unfolding pseudo_proj_True_def by simp
    qed
    thus "range (pseudo_proj_True 0) \<subseteq> {sconst True}" by auto
    show "{sconst True} \<subseteq> range (pseudo_proj_True 0)"
      using \<open>range (pseudo_proj_True 0) \<subseteq> {sconst True}\<close> subset_singletonD by fastforce
  qed
  hence "(emeasure M ((pseudo_proj_True 0) -`{sconst True} \<inter> space M)) = ennreal 1"
    by (metis Int_absorb1 UNIV_I emeasure_eq_measure image_eqI prob_space subsetI vimage_eq)
  have "(\<Sum> w\<in> range (pseudo_proj_True 0). f w) = (\<Sum> w\<in> {sconst True}. f w)" using \<open>range (pseudo_proj_True 0) = {sconst True}\<close>
    sum.cong[of "range (pseudo_proj_True n)" "{sconst True}" f f] by simp
  also have "... = f (sconst True)" by simp
  finally have "(\<Sum> w\<in> range (pseudo_proj_True 0). f w) = f (sconst True)" .
  hence "(\<Sum> w\<in> range (pseudo_proj_True 0). (emeasure M ((pseudo_proj_True 0) -`{w} \<inter> space M)) * f w) = f (sconst True)"
    using \<open>(emeasure M ((pseudo_proj_True 0) -`{sconst True} \<inter> space M)) = ennreal 1\<close>
    by (simp add: \<open>range (pseudo_proj_True 0) = {sconst True}\<close>)
  thus "integral\<^sup>N M f = (\<Sum> w\<in> range (pseudo_proj_True 0). (emeasure M ((pseudo_proj_True 0) -`{w} \<inter> space M)) * f w)"
    using 0  by (simp add:cst_nn_integral)
next
  case (Suc n)
  define BP where "BP = measure_pmf (bernoulli_pmf p)"
  have "integral\<^sup>N M f = integral\<^sup>N (stream_space BP) f" using bernoulli
    unfolding bernoulli_stream_def BP_def by simp
  also have "... = \<integral>\<^sup>+ x. \<integral>\<^sup>+ X. f (x ## X) \<partial>stream_space BP \<partial>BP"
  proof (rule prob_space.nn_integral_stream_space)
    show "prob_space BP" unfolding BP_def by (simp add: bernoulli bernoulli_stream_def
      prob_space.prob_space_stream_space prob_space_measure_pmf)
    have "f\<in> borel_measurable (stream_space BP)" using bernoulli Suc unfolding bernoulli_stream_def BP_def
      using measurable_from_subalg nat_filtration_subalgebra natural_filtration by blast
    thus "(\<lambda>X. ennreal (f X)) \<in> borel_measurable (stream_space BP)" by simp
  qed
  also have "... = (\<lambda>x. (\<integral>\<^sup>+ X. f (x ## X) \<partial>stream_space BP)) True * ennreal p +
    (\<lambda>x. (\<integral>\<^sup>+ X. f (x ## X) \<partial>stream_space BP)) False * ennreal (1 -p)"
    using  p_gt_0 p_lt_1 unfolding BP_def by simp
  also have "... = (\<integral>\<^sup>+ X. f (True ## X) \<partial>stream_space BP) * p +
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (False ## w))) * (1-p)"
  proof -
    define ff where "ff = (\<lambda>w. f (False ## w))"
    have "\<And>x. 0 \<le> ff x" using Suc unfolding ff_def by simp
    moreover have "ff\<in> borel_measurable (F n)" using Suc unfolding ff_def by (simp add:suc_measurable)
    ultimately have "(\<integral>\<^sup>+ x. ennreal (ff x) \<partial>M) =
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (ff w))"
      using Suc by simp
    thus ?thesis unfolding ff_def by (simp add: BP_def bernoulli bernoulli_stream_def)
  qed
  also have "... = (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (True ## w))) * p +
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (False ## w))) * (1-p)"
  proof -
    define ft where "ft = (\<lambda>w. f (True ## w))"
    have "\<And>x. 0 \<le> ft x" using Suc unfolding ft_def by simp
    moreover have "ft\<in> borel_measurable (F n)" using Suc unfolding ft_def by (simp add:suc_measurable)
    ultimately have "(\<integral>\<^sup>+ x. ennreal (ft x) \<partial>M) =
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (ft w))"
      using Suc by simp
    thus ?thesis unfolding ft_def by (simp add: BP_def bernoulli bernoulli_stream_def)
  qed
  also have "... = (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p *  (f (True ## w))) +
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M)  *  (f (False ## w)))* (1-p)"
  proof -
    have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (True ## w))) * p =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (True ## w)) * p)"
      by (rule sum_distrib_right)
    also have "... = (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p * (f (True ## w)))"
    proof (rule sum.cong, simp)
      fix w
      assume "w\<in> range (pseudo_proj_True n)"
      show "emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (f (True ## w)) * ennreal p =
         emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal p * ennreal (f (True ## w))"
      proof -
        have "ennreal (f (True ## w)) * ennreal p = ennreal p * ennreal (f (True ## w))" by (simp add:mult.commute)
        hence "\<And>x. x * ennreal (f (True ## w)) * ennreal p = x * ennreal p * ennreal (f (True ## w))"
          by (simp add: semiring_normalization_rules(16))
        thus ?thesis by simp
      qed
    qed
    finally have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (True ## w))) * p =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p * (f (True ## w)))" .
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p *  (f (True ## w))) +
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) *  (f (False ## w)))"
  proof -
    have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (False ## w))) * (1-p) =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (False ## w)) * (1-p))"
      by (rule sum_distrib_right)
    also have "... = (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) * (f (False ## w)))"
    proof (rule sum.cong, simp)
      fix w
      assume "w\<in> range (pseudo_proj_True n)"
      show "emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (f (False ## w)) * ennreal (1-p) =
         emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (1-p) * ennreal (f (False ## w))"
      proof -
        have "ennreal (f (False ## w)) * ennreal (1-p) = ennreal (1-p) * ennreal (f (False ## w))" by (simp add:mult.commute)
        hence "\<And>x. x * ennreal (f (False ## w)) * ennreal (1-p) = x * ennreal (1-p) * ennreal (f (False ## w))"
          by (simp add: semiring_normalization_rules(16))
        thus ?thesis by simp
      qed
    qed
    finally have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) *  (f (False ## w))) * (1-p) =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) * (f (False ## w)))" .
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p *  (f (y))) +
    (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) *  (f (False ## w)))"
  proof -
    have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p *  (f (True ## w))) =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {stl (True##w)} \<inter> space M) * p *  (f (True ## w)))" by simp
    also have "... =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p *  (f (y)))"
      by (rule reindex_pseudo_proj)
    finally have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * p *  (f (True ## w))) =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p *  (f (y)))" .
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p *  (f (y))) +
    (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) *  (f (y)))"
  proof -
    have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) *  (f (False ## w))) =
      (\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {stl (False##w)} \<inter> space M) * (1-p) *  (f (False ## w)))" by simp
    also have "... =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) *  (f (y)))"
      by (rule reindex_pseudo_proj)
    finally have "(\<Sum>w\<in>range (pseudo_proj_True n). emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * (1-p) *  (f (False ## w))) =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) *  (f (y)))" .
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) *  (f (y))) +
    (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) *  (f (y)))"
  proof -
    have "\<forall>y \<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p =
      prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)"
    proof
      fix y
      assume "y \<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}"
      hence "\<exists>w \<in> range (pseudo_proj_True n). y = True ## w" by simp
      from this obtain w where "w\<in> range (pseudo_proj_True n)" and "y = True ## w" by auto
      have "emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p = p *emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)"
        by (simp add:mult.commute)
      also have "... = prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)" using \<open>y = True ## w\<close>
        unfolding prob_component_def by simp
      finally show "emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * p =
        prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)" .
    qed
    thus ?thesis by auto
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) *  (f (y))) +
    (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) *  (f (y)))"
  proof -
    have "\<forall>y \<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) =
      prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)"
    proof
      fix y
      assume "y \<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}"
      hence "\<exists>w \<in> range (pseudo_proj_True n). y = False ## w" by simp
      from this obtain w where "w\<in> range (pseudo_proj_True n)" and "y = False ## w" by auto
      have "emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) = (1-p) *emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)"
        by (simp add:mult.commute)
      also have "... = prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)" using \<open>y = False ## w\<close>
        unfolding prob_component_def by simp
      finally show "emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (1-p) =
        prob_component p y 0 * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M)" .
    qed
    thus ?thesis by auto
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = True ## x} *  (f y)) +
    (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) *  (f (y)))"
  proof -
    have "(\<Sum>y | \<exists>w\<in>range (pseudo_proj_True n). y = True ## w.
       ennreal (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (f y)) =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = True ## x} * (f y))"
    proof (rule sum.cong, simp)
      fix xx
      assume "xx \<in> {y. \<exists>w\<in>range (pseudo_proj_True n). y = True ## w}"
      hence "\<exists>w\<in>range (pseudo_proj_True n). xx = True ## w" by simp
      from this obtain ww where "ww\<in>range (pseudo_proj_True n)" and "xx = True## ww" by auto
      have "ennreal (prob_component p (True##ww) 0) * emeasure M (pseudo_proj_True n -` {ww} \<inter> space M) =
         emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {ww}. z = True ## x}" using \<open>ww\<in>range (pseudo_proj_True n)\<close>
        by (rule pseudo_proj_element_prob_pref[symmetric])
      thus "ennreal (prob_component p xx 0) * emeasure M (pseudo_proj_True n -` {stl xx} \<inter> space M) * (f xx) =
         emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl xx}. z = True ## x} * (f xx)" using \<open>xx = True##ww\<close>  by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = True ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = True ## x} *  (f y)) +
    (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = False ## x} *  (f y))"
  proof -
    have "(\<Sum>y | \<exists>w\<in>range (pseudo_proj_True n). y = False ## w.
       ennreal (prob_component p y 0) * emeasure M (pseudo_proj_True n -` {stl y} \<inter> space M) * (f y)) =
      (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = False ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = False ## x} * (f y))"
    proof (rule sum.cong, simp)
      fix xx
      assume "xx \<in> {y. \<exists>w\<in>range (pseudo_proj_True n). y = False ## w}"
      hence "\<exists>w\<in>range (pseudo_proj_True n). xx = False ## w" by simp
      from this obtain ww where "ww\<in>range (pseudo_proj_True n)" and "xx = False## ww" by auto
      have "ennreal (prob_component p (False##ww) 0) * emeasure M (pseudo_proj_True n -` {ww} \<inter> space M) =
         emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {ww}. z = False ## x}" using \<open>ww\<in>range (pseudo_proj_True n)\<close>
        by (rule pseudo_proj_element_prob_pref[symmetric])
      thus "ennreal (prob_component p xx 0) * emeasure M (pseudo_proj_True n -` {stl xx} \<inter> space M) * (f xx) =
         emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl xx}. z = False ## x} * (f xx)" using \<open>xx = False##ww\<close>  by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = True ## x} *  (f (True##w))) +
    (\<Sum>w \<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = False ## x} *  (f (False##w)))"
  proof -
    have "\<And>c. (\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = c ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = c ## x} *  (f y)) =
      (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = c ## x} *  (f (c##w)))"
    proof -
      fix c
      have "(\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = c ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = c ## x} *  (f y)) =
      (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl (c##w)}. z = c ## x} *  (f (c##w)))"
        by (rule reindex_pseudo_proj[symmetric])
      also have "... = (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = c ## x} *  (f (c##w)))"
        by simp
      finally show "(\<Sum>y\<in>{y. \<exists>w \<in> range (pseudo_proj_True n). y = c ## w}. emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl y}. z = c ## x} *  (f y)) =
        (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = c ## x} *  (f (c##w)))" .
    qed
    thus ?thesis by auto
  qed
  also have "... = (\<Sum>w\<in> {w. w\<in> range (pseudo_proj_True (Suc n)) \<and> w!!0 = True}. emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> (space M)) *  (f w)) +
    (\<Sum>w\<in> {w. w\<in> range (pseudo_proj_True (Suc n)) \<and> w!!0 = False}. emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> (space M)) *  (f w))"
  proof -
    have "\<And>c. (\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = c ## x} *  (f (c##w))) =
      (\<Sum>w\<in> {w. w\<in> range (pseudo_proj_True (Suc n)) \<and> w!!0 = c}. emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> (space M)) *  (f w))"
    proof -
      fix c
      show "(\<Sum>w\<in> range (pseudo_proj_True n). emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {w}. z = c ## x} *  (f (c##w))) =
        (\<Sum>w\<in> {w. w\<in> range (pseudo_proj_True (Suc n)) \<and> w!!0 = c}. emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> (space M)) *  (f w))"
      proof (rule sum.reindex_cong)
        show "inj_on stl {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
        proof
          fix x y
          assume "x \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
            and "y \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
            and "stl x = stl y"
          have "x!!0 = c" using \<open>x \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}\<close> by simp
          moreover have "y!!0 = c" using \<open>y \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}\<close> by simp
          ultimately show "x = y" using \<open>stl x=  stl y\<close>
            by (smt snth.simps(1) stream_eq_Stream_iff)
            (*by (metis (full_types, hide_lams)  pmf_bernoulli_True snth.simps(1) stream_eq_Stream_iff) *)
        qed
        show "range (pseudo_proj_True n) = stl ` {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
        proof
          show "range (pseudo_proj_True n) \<subseteq> stl ` {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
          proof
            fix x
            assume "x\<in> range (pseudo_proj_True n)"
            hence "pseudo_proj_True n x = x" using pseudo_proj_True_proj by auto
            have "pseudo_proj_True (Suc n) (c##x) = c##x"
            proof -
              have "pseudo_proj_True (Suc n) (c##x) = c ## pseudo_proj_True n x" using pseudo_proj_True_Suc_prefix[of n "c##x"]
                by simp
              also have "... = c## x" using \<open>pseudo_proj_True n x = x\<close> by simp
              finally show ?thesis .
            qed
            hence "c##x\<in> range (pseudo_proj_True (Suc n))" by (simp add: pseudo_proj_True_img)
            thus "x\<in> stl`{w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
            proof -
              have "\<exists>s. (s \<in> range (pseudo_proj_True (Suc n)) \<and> s !! 0 = c) \<and> stl s = x"
                by (metis (no_types) \<open>c ## x \<in> range (pseudo_proj_True (Suc n))\<close> snth.simps(1) stream.sel(1) stream.sel(2))
              then show ?thesis
                by force
            qed
          qed
          show "stl ` {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c} \<subseteq> range (pseudo_proj_True n)"
          proof
            fix x
            assume "x\<in> stl ` {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
            hence "\<exists> w\<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}. x = stl w" by auto
            from this obtain w where "w \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}" and "x = stl w" by auto
            have "w\<in> range (pseudo_proj_True (Suc n))" and "w!!0 = c" using \<open>w \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}\<close>
              by auto
            have "c##x = w" using \<open>x = stl w\<close> \<open>w!!0 = c\<close> by force
            also have "... = pseudo_proj_True (Suc n) w" using \<open>w\<in> range (pseudo_proj_True (Suc n))\<close>
              using pseudo_proj_True_proj by auto
            also have "... = c ## pseudo_proj_True n x" using \<open>x = stl w\<close> \<open>w!!0 = c\<close> by (simp add:pseudo_proj_True_Suc_prefix)
            finally have "c##x = c## pseudo_proj_True n x" .
            hence "x = pseudo_proj_True n x" by simp
            thus "x\<in> range (pseudo_proj_True n)" by auto
          qed
        qed
        show "\<And>x. x \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c} \<Longrightarrow>
         emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl x}. z = c ## x} * ennreal (f (c ## stl x)) =
         emeasure M (pseudo_proj_True (Suc n) -` {x} \<inter> space M) * ennreal (f x)"
        proof -
          fix w
          assume "w \<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = c}"
          hence "w \<in> range (pseudo_proj_True (Suc n))" and "w !! 0 = c" by auto
          have "{z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x} = (pseudo_proj_True (Suc n) -` {w} \<inter> space M)"
          proof
            show "{z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x} \<subseteq> pseudo_proj_True (Suc n) -` {w} \<inter> space M"
            proof
              fix z
              assume "z \<in> {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x}"
              hence "\<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x" and "z\<in> space M" by auto
              from \<open>\<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x\<close> obtain x where "x\<in>pseudo_proj_True n -` {stl w}"
                and "z = c##x" by auto
              have "pseudo_proj_True (Suc n) z = c ## pseudo_proj_True n x" using \<open>z = c##x\<close>
                by (simp add:pseudo_proj_True_Suc_prefix)
              also have "... = c## stl w" using \<open>x\<in>pseudo_proj_True n -` {stl w}\<close> by simp
              also have "... = w" using \<open>w !! 0 = c\<close> by force
              finally have "pseudo_proj_True (Suc n) z = w" .
              thus "z\<in> pseudo_proj_True (Suc n) -` {w} \<inter> space M" using \<open>z\<in> space M\<close> by auto
            qed
            show "pseudo_proj_True (Suc n) -` {w} \<inter> space M \<subseteq> {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x}"
            proof
              fix z
              assume "z\<in> pseudo_proj_True (Suc n) -` {w} \<inter> space M"
              hence "z\<in> space M" and "pseudo_proj_True (Suc n) z = w" by auto
              hence "stl w = stl (pseudo_proj_True (Suc n) z)" by simp
              also have "... = pseudo_proj_True n (stl z)" by (simp add: pseudo_proj_True_Suc_prefix)
              finally have "stl w = pseudo_proj_True n (stl z)" .
              hence "stl z \<in> pseudo_proj_True n -` {stl w}" by simp
              have "z!!0 ## pseudo_proj_True n (stl z) = w" using pseudo_proj_True_Suc_prefix
                \<open>pseudo_proj_True (Suc n) z = w\<close> by simp
              also have "... = c## (stl w)" using \<open>w!!0 = c\<close> by force
              finally have "z!!0 ## pseudo_proj_True n (stl z) = c## (stl w)" .
              hence "z!!0 = c" by simp
              hence "z =c## (stl z)" by force
              thus "z\<in> {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x}" using \<open>z\<in> space M\<close>
                \<open>stl z \<in> pseudo_proj_True n -` {stl w}\<close> by auto
            qed
          qed
          hence "emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x} * ennreal (f (c ## stl w)) =
            emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f (c ## stl w))" by simp
          also have "... = emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f w)" using \<open>w!!0 = c\<close> by force
          finally show "emeasure M {z \<in> space M. \<exists>x\<in>pseudo_proj_True n -` {stl w}. z = c ## x} * ennreal (f (c ## stl w)) =
            emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f w)" .
        qed
      qed
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>w\<in> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True} \<union>
    {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False}.
    emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f w))"
  proof (rule sum.union_disjoint[symmetric])
    show "finite {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True}" by (simp add: pseudo_proj_True_finite_image)
    show "finite {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False}" by (simp add: pseudo_proj_True_finite_image)
    show "{w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True} \<inter> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False} = {}"
      by auto
  qed
  also have "... = (\<Sum>w\<in> range (pseudo_proj_True (Suc n)).emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f w))"
  proof (rule sum.cong)
    show "{w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True} \<union> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False} =
    range (pseudo_proj_True (Suc n))"
    proof
      show "{w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True} \<union> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False}
        \<subseteq> range (pseudo_proj_True (Suc n))" by auto
      show "range (pseudo_proj_True (Suc n))
        \<subseteq> {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = True} \<union>
        {w \<in> range (pseudo_proj_True (Suc n)). w !! 0 = False}"
        by (simp add: subsetI)
    qed
  qed simp
  finally show "integral\<^sup>N M f =
    (\<Sum>w\<in> range (pseudo_proj_True (Suc n)). emeasure M (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * ennreal (f w))" .
qed


lemma (in infinite_cts_filtration) F_n_integral_pos:
  fixes f::"bool stream\<Rightarrow>real"
  assumes "f\<in> borel_measurable (F n)"
  and "\<forall>w. 0 \<le> f w"
  shows "has_bochner_integral M f
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w))"
proof -
  have "integral\<^sup>N M f = (\<Sum> w\<in> range (pseudo_proj_True n). (emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w))"
    using assms by (simp add: F_n_nn_integral_pos)
  have "integral\<^sup>L M f = enn2real (integral\<^sup>N M f)"
  proof (rule integral_eq_nn_integral)
    show "AE x in M. 0\<le> f x" using assms by simp
    show "random_variable borel f" using assms
      using measurable_from_subalg nat_filtration_subalgebra natural_filtration by blast
  qed
  also have "... = enn2real (\<Sum> w\<in> range (pseudo_proj_True n). (emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w))"
    using assms by (simp add: F_n_nn_integral_pos)
  also have "... = (\<Sum> w\<in> range (pseudo_proj_True n). enn2real ((emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w)))"
  proof (rule enn2real_sum)
    show "finite (range (pseudo_proj_True n))" by (simp add: pseudo_proj_True_finite_image)
    show "\<And>w. w \<in> range (pseudo_proj_True n) \<Longrightarrow> emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (f w) < \<top>"
    proof -
      fix w
      assume "w\<in> range (pseudo_proj_True n)"
      show "emeasure M (pseudo_proj_True n -` {w} \<inter> space M) * ennreal (f w) < \<top>"
        by (simp add: emeasure_eq_measure ennreal_mult_less_top)
    qed
  qed
  also have "... = (\<Sum> w\<in> range (pseudo_proj_True n).  ((measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w)))"
    by (simp add: Sigma_Algebra.measure_def assms(2) enn2real_mult)
  finally have "integral\<^sup>L M f =(\<Sum> w\<in> range (pseudo_proj_True n).  ((measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w)))" .
  moreover have "integrable M f"
  proof (rule integrableI_nn_integral_finite)
    show "random_variable borel f" using assms
      using measurable_from_subalg nat_filtration_subalgebra natural_filtration by blast
    show "AE x in M. 0 \<le> f x" using assms by simp
    have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>M) = (\<Sum> w\<in> range (pseudo_proj_True n). (emeasure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (f w))"
      using assms by (simp add: F_n_nn_integral_pos)
    also have "... = (\<Sum> w\<in> range (pseudo_proj_True n). ennreal (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) *   (f w)))"
    proof (rule sum.cong, simp)
      fix x
      assume "x\<in> range (pseudo_proj_True n)"
      thus "emeasure M (pseudo_proj_True n -` {x} \<inter> space M) * ennreal (f x) =
         ennreal (prob (pseudo_proj_True n -` {x} \<inter> space M) * f x)"
        using assms(2) emeasure_eq_measure ennreal_mult'' by auto
    qed
    also have "... = ennreal (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) *   (f w)))"
    proof (rule ennreal_sum)
      show "finite (range (pseudo_proj_True n))" by (simp add: pseudo_proj_True_finite_image)
      show "\<And>w. 0 \<le> prob (pseudo_proj_True n -` {w} \<inter> space M) * f w"
        using assms(2) measure_nonneg zero_le_mult_iff by blast
    qed
    finally show "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>M) =
      ennreal (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) *   (f w)))" .
  qed
  ultimately show ?thesis using has_bochner_integral_iff by blast
qed


lemma (in infinite_cts_filtration) F_n_integral:
  fixes f::"bool stream\<Rightarrow>real"
  assumes "f\<in> borel_measurable (F n)"
  shows "has_bochner_integral M f
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) * (f w))"
proof -
  define fpos where "fpos = (\<lambda>w. max 0 (f w))"
  define fneg where "fneg = (\<lambda>w. max 0 (-f w))"
  have "\<forall>w. 0 \<le> fpos w" unfolding fpos_def by simp
  have "\<forall>w. 0 \<le> fneg w" unfolding fneg_def by simp
  have "fpos \<in> borel_measurable (F n)" using assms unfolding fpos_def by simp
  have "fneg \<in> borel_measurable (F n)" using assms unfolding fneg_def by simp
  have "has_bochner_integral M fpos
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fpos w))"
    using \<open>fpos\<in> borel_measurable (F n)\<close> \<open>\<forall>w. 0 \<le> fpos w\<close> by (simp add: F_n_integral_pos)
  moreover have "has_bochner_integral M fneg
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fneg w))"
    using \<open>fneg\<in> borel_measurable (F n)\<close> \<open>\<forall>w. 0 \<le> fneg w\<close> by (simp add: F_n_integral_pos)
  ultimately have posd: "has_bochner_integral M (\<lambda>w. fpos w - fneg w)
    ((\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fpos w)) -
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fneg w)))"
    by (simp add:has_bochner_integral_diff)
  have "((\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fpos w)) -
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fneg w))) =
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) * fpos w -
      (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) * fneg w))"
    by (rule sum_subtractf[symmetric])
  also have "... =
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) * (fpos w - fneg w)))"
  proof (rule sum.cong, simp)
    fix x
    assume "x\<in> range (pseudo_proj_True n)"
    show "prob (pseudo_proj_True n -` {x} \<inter> space M) * fpos x - prob (pseudo_proj_True n -` {x} \<inter> space M) * fneg x =
         prob (pseudo_proj_True n -` {x} \<inter> space M) * (fpos x - fneg x)"
      by (rule right_diff_distrib[symmetric])
  qed
  also have "... =
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) * f w))"
  proof (rule sum.cong, simp)
    fix x
    assume "x\<in> range (pseudo_proj_True n)"
    show "prob (pseudo_proj_True n -` {x} \<inter> space M) * (fpos x - fneg x) = prob (pseudo_proj_True n -` {x} \<inter> space M) * f x"
      unfolding fpos_def fneg_def by auto
  qed
  finally have "((\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fpos w)) -
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) *   (fneg w))) =
    (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) * f w))" .
  hence "has_bochner_integral M (\<lambda>w. fpos w - fneg w) (\<Sum> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M) * f w))"
    using posd by simp
  moreover have "\<And>w. fpos w - fneg w = f w" unfolding fpos_def fneg_def by auto
  ultimately show ?thesis using has_bochner_integral_diff by simp
qed

lemma (in infinite_cts_filtration) F_n_integral_prob_comp:
fixes f::"bool stream\<Rightarrow>real"
  assumes "f\<in> borel_measurable (F n)"
  shows "has_bochner_integral M f
    (\<Sum> w\<in> range (pseudo_proj_True n). (prod (prob_component p w) {0..<n}) * (f w))"
proof -
  have "\<forall> w\<in> range (pseudo_proj_True n). (measure M ((pseudo_proj_True n) -`{w} \<inter> space M)) * f w =
    (prod (prob_component p w) {0..<n}) * (f w)"
  proof
    fix w
    assume "w\<in> range (pseudo_proj_True n)"
    thus "prob (pseudo_proj_True n -` {w} \<inter> space M) * f w = prod (prob_component p w) {0..<n} * f w"
      using bernoulli_stream_pseudo_prob bernoulli p_lt_1 p_gt_0 by simp
  qed
  thus ?thesis using F_n_integral assms by (metis (no_types, lifting) sum.cong)
qed

lemma (in infinite_cts_filtration) expect_prob_comp:
fixes f::"bool stream\<Rightarrow>real"
  assumes "f\<in> borel_measurable (F n)"
  shows "expectation f =
    (\<Sum> w\<in> range (pseudo_proj_True n). (prod (prob_component p w) {0..<n}) * (f w))"
  using assms F_n_integral_prob_comp has_bochner_integral_iff by blast

lemma sum_union_disjoint':
  assumes "finite A"
    and "finite B"
    and "A \<inter> B = {}"
    and "A \<union> B = C"
  shows "sum g C = sum g A + sum g B"
  using sum.union_disjoint[OF assms(1-3)] and assms(4) by auto

lemma (in infinite_cts_filtration) borel_Suc_expectation:
  fixes f::"bool stream\<Rightarrow> real"
  assumes "f\<in> borel_measurable (F (Suc n))"
  and "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  and "g -` {g z} \<in> sets (F n)"
  and "\<forall>y z. (g y = g z \<and> snth y n = snth z n) \<longrightarrow> f y = f z"
  shows "expectation (\<lambda>x. f x * indicator (g -` {g z}) x) =
    prob (g -` {g z}) * (p * f (pseudo_proj_True n z) +
     (1 -p) * f (pseudo_proj_False n z))"
proof -
  define expind where "expind = (\<lambda>x. f x * indicator (g -` {g z}) x)"
  have "expind\<in> borel_measurable (F (Suc n))" unfolding expind_def
  proof (rule borel_measurable_times, (simp add:assms(1,2)))
    show "indicator (g -` {g z}) \<in> borel_measurable (F (Suc n))"
    proof (rule borel_measurable_indicator)
      have "g -` {g z} \<in> sets (nat_filtration n)"
        using assms nat_filtration_borel_measurable_singleton natural_filtration by simp
      hence "g -` {g z} \<in> sets (F n)" using natural_filtration by simp
      thus "g -` {g z} \<in> sets (F (Suc n))"
        using nat_filtration_Suc_sets natural_filtration by blast
    qed
  qed
  hence "expectation expind =
    (\<Sum> w\<in> range (pseudo_proj_True (Suc n)). (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * (expind w))"
    by (simp add:F_n_integral has_bochner_integral_integral_eq)
  also have "... = (\<Sum> w\<in> range (pseudo_proj_True (Suc n)) \<inter> g -` {g z}.
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * (expind w)) +
    (\<Sum> w\<in> range (pseudo_proj_True (Suc n)) - g -` {g z}.
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * (expind w))"
    by (simp add: Int_Diff_Un Int_Diff_disjoint assms sum_union_disjoint' pseudo_proj_True_finite_image)
  also have "... = (\<Sum> w\<in> range (pseudo_proj_True (Suc n)) \<inter> g -` {g z}.
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * (expind w))"
  proof -
    have "\<forall>w\<in> range (pseudo_proj_True (Suc n)) - g -` {g z}. expind w = 0"
    proof
      fix w
      assume "w\<in> range (pseudo_proj_True (Suc n)) - g -` {g z}"
      thus "expind w = 0" unfolding expind_def by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum> w\<in> range (pseudo_proj_True (Suc n)) \<inter> g -` {g z}.
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * f w)"
  proof -
    have "\<forall>w\<in> range (pseudo_proj_True (Suc n)) \<inter> g -` {g z}. expind w = f w"
    proof
      fix w
      assume "w\<in> range (pseudo_proj_True (Suc n)) \<inter> g -` {g z}"
      hence "w\<in> g -`{g z}" by simp
      thus "expind w = f w" unfolding expind_def by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum> w\<in> (pseudo_proj_True n) ` (g -` {g z}) \<union> (pseudo_proj_False n) ` (g -` {g z}).
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * f w)" using f_borel_Suc_preimage[of g] assms(1,2, 3) by auto
  also have "... = (\<Sum> w\<in> (pseudo_proj_True n) ` (g -` {g z}).
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * f w) +
    (\<Sum>w\<in> (pseudo_proj_False n) ` (g -` {g z}).
    (measure M ((pseudo_proj_True (Suc n)) -`{w} \<inter> space M)) * f w)"
  proof (rule sum_union_disjoint')
    show "finite (pseudo_proj_True n ` g -` {g z})"
    proof -
      have "finite (range (pseudo_proj_True n))" by (simp add: pseudo_proj_True_finite_image)
      moreover have "pseudo_proj_True n ` g -` {g z} \<subseteq> range (pseudo_proj_True n)"
        by (simp add: image_mono)
      ultimately show ?thesis by (simp add:finite_subset)
    qed
    show "finite (pseudo_proj_False n ` g -` {g z})"
    proof -
      have "finite (range (pseudo_proj_False n))"
        by (metis image_subsetI infinite_super proj_rep_set proj_rep_set_finite pseudo_proj_True_Suc_False_proj rangeI)
      moreover have "pseudo_proj_False n ` g -` {g z} \<subseteq> range (pseudo_proj_False n)"
        by (simp add: image_mono)
      ultimately show ?thesis by (simp add:finite_subset)
    qed
    show "pseudo_proj_True n ` g -` {g z} \<inter> pseudo_proj_False n ` g -` {g z} = {}"
    proof (rule ccontr)
      assume "pseudo_proj_True n ` g -` {g z} \<inter> pseudo_proj_False n ` g -` {g z} \<noteq> {}"
      hence "\<exists>y. y\<in> pseudo_proj_True n ` g -` {g z} \<inter> pseudo_proj_False n ` g -` {g z}" by auto
      from this obtain y where "y\<in> pseudo_proj_True n ` g -` {g z}" and "y\<in> pseudo_proj_False n ` g -` {g z}" by auto
      have "\<exists>yt. yt\<in> g -`{g z} \<and> y = pseudo_proj_True n yt" using \<open>y\<in> pseudo_proj_True n ` g -` {g z}\<close> by auto
      from this obtain yt where "y = pseudo_proj_True n yt" by auto
      have "\<exists>yf. yf\<in> g -`{g z} \<and> y = pseudo_proj_False n yf" using \<open>y\<in> pseudo_proj_False n ` g -` {g z}\<close> by auto
      from this obtain yf where "y = pseudo_proj_False n yf" by auto
      have "snth y n = True" using \<open>y = pseudo_proj_True n yt\<close> unfolding pseudo_proj_True_def by simp
      moreover have "snth y n = False" using \<open>y = pseudo_proj_False n yf\<close> unfolding pseudo_proj_False_def by simp
      ultimately show False by simp
    qed
  qed simp
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * f (pseudo_proj_True n z)) +
  (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * f w)"
  proof -
    define zt where "zt = pseudo_proj_True n z"
    have eqw: "\<And>w. w\<in>pseudo_proj_True n ` g -` {g z} \<Longrightarrow> (g w = g zt \<and> snth w n = snth zt n)"
    proof
      fix w
      assume "w\<in> pseudo_proj_True n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_True n y \<and> g y = g z" by auto
      from this obtain yt where "w = pseudo_proj_True n yt" and "g yt = g z" by auto
      have "g w= g yt" using \<open>w = pseudo_proj_True n yt\<close> nat_filtration_not_borel_info[of g] natural_filtration
        assms by (metis comp_apply)
      also have "... = g zt"  using assms using nat_filtration_not_borel_info[of g] natural_filtration \<open>g yt = g z\<close>
        unfolding zt_def by (metis comp_apply)
      finally show "g w = g zt" .
      show "w !! n = zt !! n" using \<open>w = pseudo_proj_True n yt\<close> unfolding zt_def pseudo_proj_True_def by simp
    qed
    hence "\<And>w. w\<in>pseudo_proj_True n ` g -` {g z} \<Longrightarrow> f w = f zt"
    proof
      fix w
      assume "w \<in> pseudo_proj_True n ` g -` {g z}"
      hence "g w = g zt \<and> snth w n = snth zt n" using eqw [of w] by simp
      thus "f w = f zt" using assms(5) by blast
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * f (pseudo_proj_True n z)) +
  (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M) * f (pseudo_proj_False n z))"
  proof -
    define zf where "zf = pseudo_proj_False n z"
    have eqw: "\<And>w. w\<in>pseudo_proj_False n ` g -` {g z} \<Longrightarrow> (g w = g zf \<and> snth w n = snth zf n)"
    proof
      fix w
      assume "w\<in> pseudo_proj_False n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_False n y \<and> g y = g z" by auto
      from this obtain yf where "w = pseudo_proj_False n yf" and "g yf = g z" by auto
      have "g w= g yf" using \<open>w = pseudo_proj_False n yf\<close> nat_filtration_not_borel_info'[of g] natural_filtration
        assms by (metis comp_apply)
      also have "... = g zf"  using assms using nat_filtration_not_borel_info'[of g] natural_filtration \<open>g yf = g z\<close>
        unfolding zf_def by (metis comp_apply)
      finally show "g w = g zf" .
      show "w !! n = zf !! n" using \<open>w = pseudo_proj_False n yf\<close> unfolding zf_def pseudo_proj_False_def by simp
    qed
    hence "\<And>w. w\<in>pseudo_proj_False n ` g -` {g z} \<Longrightarrow> f w = f zf"
    proof
      fix w
      assume "w\<in> pseudo_proj_False n ` g -` {g z}"
      hence "g w = g zf \<and> snth w n = snth zf n" using eqw [of w] by simp
      thus "f w = f zf" using assms by blast
    qed
    thus ?thesis by simp
  qed
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M)) * f (pseudo_proj_True n z) +
    (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M)) * f (pseudo_proj_False n z)"
    by (simp add: sum_distrib_right)
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob ({x. stake n x = stake n w}) * p) * f (pseudo_proj_True n z) +
    (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M)) * f (pseudo_proj_False n z)"
  proof -
    have "\<And>w. w\<in>pseudo_proj_True n ` g -` {g z} \<Longrightarrow> (prob (pseudo_proj_True (Suc n) -` {w}) =
      (prob ({x. stake n x = stake n w})) * p)"
    proof -
      fix w
      assume "w\<in>pseudo_proj_True n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_True n y \<and> g y = g z" by auto
      from this obtain yt where "w = pseudo_proj_True n yt" and "g yt = g z" by auto
      hence "snth w n" unfolding pseudo_proj_True_def by simp
      have "pseudo_proj_True (Suc n) w = w" using \<open>w = pseudo_proj_True n yt\<close>
        by (simp add: pseudo_proj_True_Suc_proj)
      hence "pseudo_proj_True (Suc n) -` {w} = {x. stake (Suc n) x = stake (Suc n) w}" using pseudo_proj_True_preimage_stake
        by simp
      hence "prob (pseudo_proj_True (Suc n) -` {w}) = prob {x. stake n x = stake n w} * prob_component p w n"
        using bernoulli_stream_element_prob_rec' bernoulli bernoulli_stream_space p_lt_1 p_gt_0 by simp
      also have "... = prob {x. stake n x = stake n w} * p" using \<open>snth w n\<close> unfolding prob_component_def by simp
      finally show "prob (pseudo_proj_True (Suc n) -` {w}) = prob {x. stake n x = stake n w} * p" .
    qed
    thus ?thesis using bernoulli bernoulli_stream_space by simp
  qed
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob ({x. stake n x = stake n w}) * p) * f (pseudo_proj_True n z) +
    (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob {x. stake n x = stake n w} * (1 -p)) * f (pseudo_proj_False n z)"
  proof -
    have "\<And>w. w\<in>pseudo_proj_False n ` g -` {g z} \<Longrightarrow> (prob (pseudo_proj_True (Suc n) -` {w} \<inter> space M) =
      (prob {x. stake n x = stake n w}) * (1-p))"
    proof -
      fix w
      assume "w\<in>pseudo_proj_False n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_False n y \<and> g y = g z" by auto
      from this obtain yt where "w = pseudo_proj_False n yt" and "g yt = g z" by auto
      hence "\<not>snth w n" unfolding pseudo_proj_False_def by simp
      have "pseudo_proj_True (Suc n) w = w" using \<open>w = pseudo_proj_False n yt\<close>
        by (simp add: pseudo_proj_True_Suc_False_proj)
      hence "pseudo_proj_True (Suc n) -`{w} = {x. stake (Suc n) x = stake (Suc n) w}" using pseudo_proj_True_preimage_stake
        by simp
      hence "prob (pseudo_proj_True (Suc n) -`{w}) = prob {x. stake n x = stake n w} * prob_component p w n"
        using bernoulli_stream_element_prob_rec' bernoulli bernoulli_stream_space p_lt_1 p_gt_0 by simp
      also have "... = prob {x. stake n x = stake n w} * (1-p)" using \<open>\<not>snth w n\<close> unfolding prob_component_def by simp
      finally show "prob (pseudo_proj_True (Suc n) -`{w} \<inter> space M) = prob {x. stake n x = stake n w} * (1-p)"  using bernoulli
        bernoulli_stream_space by simp
    qed
    thus ?thesis  by simp
  qed
  also have "... = (\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob ({x. stake n x = stake n w})) * p * f (pseudo_proj_True n z) +
    (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob {x. stake n x = stake n w}) * (1 -p) * f (pseudo_proj_False n z)"
    by (simp add:sum_distrib_right)
  also have "... = prob (g -` {g z}) * p * f (pseudo_proj_True n z) +
    (\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob {x. stake n x = stake n w}) * (1 -p) * f (pseudo_proj_False n z)"
  proof -
    have projset: "\<And>w. w\<in>pseudo_proj_True n ` g -` {g z} \<Longrightarrow> {x. stake n x = stake n w} \<in> sets M"
    proof -
      fix w
      assume "w\<in> pseudo_proj_True n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_True n y" by auto
      from this obtain y where "w = pseudo_proj_True n y" by auto
      hence "w = pseudo_proj_True n w" by (simp add: pseudo_proj_True_proj)
      hence "pseudo_proj_True n -`{w} = {x. stake n x = stake n w}"  using pseudo_proj_True_preimage_stake by simp
      moreover have "pseudo_proj_True n -`{w} \<in> sets M"
        using \<open>w = pseudo_proj_True n w\<close> bernoulli bernoulli_stream_space pseudo_proj_True_singleton by auto
      ultimately show "{x. stake n x = stake n w} \<in> sets M" by simp
    qed
    have "(\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob ({x. stake n x = stake n w})) =
      prob (\<Union>w\<in>pseudo_proj_True n ` g -` {g z}. {x. stake n x = stake n w})"
    proof (rule finite_measure_finite_Union[symmetric])
      show "finite (pseudo_proj_True n ` g -` {g z})"
        by (meson finite_subset image_mono pseudo_proj_True_finite_image subset_UNIV)
      show "(\<lambda>i. {x. stake n x = stake n i}) ` pseudo_proj_True n ` g -` {g z} \<subseteq> events" using projset by auto
      show "disjoint_family_on (\<lambda>i. {x. stake n x = stake n i}) (pseudo_proj_True n ` g -` {g z})"
        unfolding disjoint_family_on_def
      proof (intro ballI impI)
        fix u v
        assume "u \<in>  pseudo_proj_True n ` g -` {g z}" and "v\<in> pseudo_proj_True n ` g -` {g z}" and "u \<noteq> v" note uvprops = this
        show "{x. stake n x = stake n u} \<inter> {x. stake n x = stake n v} = {}"
        proof (rule ccontr)
          assume "{x. stake n x = stake n u} \<inter> {x. stake n x = stake n v} \<noteq> {}"
          hence "\<exists> uu. uu\<in> {x. stake n x = stake n u} \<inter> {x. stake n x = stake n v}" by auto
          from this obtain uu where "uu\<in> {x. stake n x = stake n u} \<inter> {x. stake n x = stake n v}" by auto
          hence "stake n uu = stake n u" and "stake n uu = stake n v" by auto
          moreover have "stake n u \<noteq> stake n v" by (metis uvprops imageE pseudo_proj_True_proj pseudo_proj_True_stake_image)
          ultimately show False by simp
        qed
      qed
    qed
    also have "... = prob (\<Union>w\<in>pseudo_proj_True n ` g -` {g z}. pseudo_proj_True n -`{w})"
    proof -
      have "\<And>w. w\<in>pseudo_proj_True n ` g -` {g z} \<Longrightarrow> {x. stake n x = stake n w} =  pseudo_proj_True n -`{w}"
        using pseudo_proj_True_preimage_stake pseudo_proj_True_proj by force
      hence "(\<Union>w\<in>pseudo_proj_True n ` g -` {g z}. {x. stake n x = stake n w}) =
        (\<Union>w\<in>pseudo_proj_True n ` g -` {g z}. pseudo_proj_True n -`{w})" by auto
      thus ?thesis by simp
    qed
    also have "... = prob (pseudo_proj_True n -`(pseudo_proj_True n ` g -` {g z}))" by (metis vimage_eq_UN)
    also have "... = prob (g -` {g z})" using pseudo_proj_preimage[symmetric, of g n N z]
      pseudo_proj_preimage'[of g n] assms by simp
    finally have "(\<Sum>w\<in>pseudo_proj_True n ` g -` {g z}. prob ({x. stake n x = stake n w})) = prob (g -` {g z})" .
    thus ?thesis by simp
  qed
  also have "... = prob (g -` {g z}) * p * f (pseudo_proj_True n z) +
    prob (g -`{g z}) * (1 -p) * f (pseudo_proj_False n z)"
  proof -
    have projset: "\<And>w. w\<in>pseudo_proj_False n ` g -` {g z} \<Longrightarrow> {x. stake n x = stake n w} \<in> sets M"
    proof -
      fix w
      assume "w\<in> pseudo_proj_False n ` g -` {g z}"
      hence "\<exists>y. w = pseudo_proj_False n y" by auto
      from this obtain y where "w = pseudo_proj_False n y" by auto
      hence "w = pseudo_proj_False n w" using pseudo_proj_False_def pseudo_proj_False_stake by auto
      hence "pseudo_proj_False n -`{w} = {x. stake n x = stake n w}"  using pseudo_proj_False_preimage_stake by simp
      moreover have "pseudo_proj_False n -`{w} \<in> sets M"
        using \<open>w = pseudo_proj_False n w\<close> bernoulli bernoulli_stream_space pseudo_proj_False_singleton by auto
      ultimately show "{x. stake n x = stake n w} \<in> sets M" by simp
    qed
    have "(\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob ({x. stake n x = stake n w})) =
      prob (\<Union>w\<in>pseudo_proj_False n ` g -` {g z}. {x. stake n x = stake n w})"
    proof (rule finite_measure_finite_Union[symmetric])
      show "finite (pseudo_proj_False n ` g -` {g z})"
        by (meson finite_subset image_mono pseudo_proj_False_finite_image subset_UNIV)
      show "(\<lambda>i. {x. stake n x = stake n i}) ` pseudo_proj_False n ` g -` {g z} \<subseteq> events" using projset by auto
      show "disjoint_family_on (\<lambda>i. {x. stake n x = stake n i}) (pseudo_proj_False n ` g -` {g z})"
        unfolding disjoint_family_on_def
      proof (intro ballI impI)
        fix u v
        assume "u \<in>  pseudo_proj_False n ` g -` {g z}" and "v\<in> pseudo_proj_False n ` g -` {g z}" and "u \<noteq> v" note uvprops = this
        show "{x. stake n x = stake n u} \<inter> {x. stake n x = stake n v} = {}"
        proof (rule ccontr)
          assume "{x. stake n x = stake n u} \<inter> {x. stake n x = stake n v} \<noteq> {}"
          hence "\<exists> uu. uu\<in> {x. stake n x = stake n u} \<inter> {x. stake n x = stake n v}" by auto
          from this obtain uu where "uu\<in> {x. stake n x = stake n u} \<inter> {x. stake n x = stake n v}" by auto
          hence "stake n uu = stake n u" and "stake n uu = stake n v" by auto
          moreover have "stake n u \<noteq> stake n v"
            using pseudo_proj_False_def pseudo_proj_False_stake uvprops by auto
          ultimately show False by simp
        qed
      qed
    qed
    also have "... = prob (\<Union>w\<in>pseudo_proj_False n ` g -` {g z}. pseudo_proj_False n -`{w})"
    proof -
      have "\<And>w. w\<in>pseudo_proj_False n ` g -` {g z} \<Longrightarrow> {x. stake n x = stake n w} =  pseudo_proj_False n -`{w}"
        using pseudo_proj_False_preimage_stake pseudo_proj_False_def pseudo_proj_False_stake by force
      hence "(\<Union>w\<in>pseudo_proj_False n ` g -` {g z}. {x. stake n x = stake n w}) =
        (\<Union>w\<in>pseudo_proj_False n ` g -` {g z}. pseudo_proj_False n -`{w})" by auto
      thus ?thesis by simp
    qed
    also have "... = prob (pseudo_proj_False n -`(pseudo_proj_False n ` g -` {g z}))" by (metis vimage_eq_UN)
    also have "... = prob (g -` {g z})" using pseudo_proj_False_preimage[symmetric, of g n N z]
      pseudo_proj_False_preimage'[of g n] assms by simp
    finally have "(\<Sum>w\<in>pseudo_proj_False n ` g -` {g z}. prob ({x. stake n x = stake n w})) = prob (g -` {g z})" .
    thus ?thesis by simp
  qed
  also have "... = prob (g -` {g z}) * (p * f (pseudo_proj_True n z) +
     (1 -p) * f (pseudo_proj_False n z))"
    using distrib_left[symmetric, of "prob (g -` {g z})" "p * f (pseudo_proj_True n z)" "(1 - p) * f (pseudo_proj_False n z)"]
    by simp
  finally show "expectation (\<lambda>x. f x * indicator (g -` {g z}) x) =
    prob (g -` {g z}) * (p * f (pseudo_proj_True n z) +
     (1 -p) * f (pseudo_proj_False n z))" unfolding expind_def .
qed


lemma (in infinite_cts_filtration) borel_Suc_expectation_pseudo_proj:
  fixes f::"bool stream\<Rightarrow> real"
  assumes "f\<in> borel_measurable (F (Suc n))"
  shows "expectation (\<lambda>x. f x * indicator (pseudo_proj_True n -` {pseudo_proj_True n z}) x) =
    prob (pseudo_proj_True n -` {pseudo_proj_True n z}) *
    (p * (f (pseudo_proj_True n z)) + (1-p) * (f (pseudo_proj_False n z)))"
proof (rule borel_Suc_expectation)
  show "f \<in> borel_measurable (F (Suc n))" using assms by simp
  show "pseudo_proj_True n \<in> F n \<rightarrow>\<^sub>M M"
    by (simp add: nat_filtration_pseudo_proj_True_measurable natural_filtration)
  show "pseudo_proj_True n -` {pseudo_proj_True n z} \<in> sets (F n)"
    by (simp add: nat_filtration_singleton natural_filtration pseudo_proj_True_proj)
  show "\<forall>y z. (pseudo_proj_True n y = pseudo_proj_True n z \<and> snth y n = snth z n) \<longrightarrow> f y = f z"
  proof (intro allI impI conjI)
    fix y z
    assume "pseudo_proj_True n y = pseudo_proj_True n z \<and> y !! n = z !! n"
    hence "pseudo_proj_True n y = pseudo_proj_True n z" and "snth y n = snth z n" by auto
    hence "pseudo_proj_True (Suc n) y = pseudo_proj_True (Suc n) z" unfolding pseudo_proj_True_def
      by (metis (full_types) \<open>pseudo_proj_True n y = pseudo_proj_True n z\<close> pseudo_proj_True_same_img stake_Suc)
    thus "f y = f z" using nat_filtration_info assms natural_filtration by (metis comp_apply)
  qed
  show "set_discriminating n (pseudo_proj_True n) M" unfolding set_discriminating_def using pseudo_proj_True_proj by simp
qed



lemma (in infinite_cts_filtration) f_borel_Suc_expl_cond_expect:
  assumes "f\<in> borel_measurable (F (Suc n))"
  and "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  and "g -` {g w} \<in> sets (F n)"
  and "\<forall>y z. (g y = g z \<and> snth y n = snth z n) \<longrightarrow> f y = f z"
and "0 < p"
and "p < 1"
  shows "expl_cond_expect M g f w = p * f (pseudo_proj_True n w) + (1 - p) * f (pseudo_proj_False n w)"
proof -
  have nz:"prob (g -`{g w}) \<noteq> 0"
  proof -
    have "pseudo_proj_True n -`{pseudo_proj_True n w}  \<subseteq> g -` {g w}"
    proof -
      have "\<forall>f n m s. f \<notin> F n \<rightarrow>\<^sub>M m \<or> \<not> set_discriminating n f m \<or> pseudo_proj_True n -` f -` {f s::'a} = f -` {f s}"
        by (meson pseudo_proj_preimage')
      then show ?thesis using assms by blast
    qed
    moreover have "prob (pseudo_proj_True n -`{pseudo_proj_True n w}) > 0" using bernoulli_stream_pref_prob_pos
      pseudo_proj_True_preimage_stake bernoulli bernoulli_stream_space emeasure_eq_measure pseudo_proj_True_proj assms by auto
    moreover have "pseudo_proj_True n -`{pseudo_proj_True n w} \<in> sets M"
      using bernoulli bernoulli_stream_space pseudo_proj_True_proj pseudo_proj_True_singleton by auto
    moreover have "g -`{g w} \<in> events" using assms natural_filtration nat_filtration_subalgebra
      unfolding subalgebra_def by blast
    ultimately show ?thesis using  measure_increasing  increasingD
    proof -
      have "g -` {g w} \<notin> events \<or> pseudo_proj_True n -` {pseudo_proj_True n w} \<notin> events \<or> prob (pseudo_proj_True n -` {pseudo_proj_True n w}) \<le> prob (g -` {g w})"
        using \<open>pseudo_proj_True n -` {pseudo_proj_True n w} \<subseteq> g -` {g w}\<close> increasingD measure_increasing by blast
      then show ?thesis
        using \<open>0 < prob (pseudo_proj_True n -` {pseudo_proj_True n w})\<close> \<open>g -` {g w} \<in> events\<close> \<open>pseudo_proj_True n -` {pseudo_proj_True n w} \<in> events\<close> by linarith
    qed
  qed
  hence "expl_cond_expect M g f w =
    expectation (\<lambda>x. f x * indicator (g -` {g w} \<inter> space M) x) /
      prob (g -` {g w} \<inter> space M)" unfolding expl_cond_expect_def img_dce_def
    by simp
  also have "... = expectation (\<lambda>x. f x * indicator (g -` {g w}) x) / prob (g -` {g w})"
    using bernoulli by (simp add:bernoulli_stream_space)
  also have "... = prob (g -` {g w}) * (p * f (pseudo_proj_True n w) +
     (1 -p) * f (pseudo_proj_False n w)) / prob (g -` {g w})"
  proof -
    have "expectation (\<lambda>x. f x * indicator (g -` {g w}) x) = prob (g -` {g w}) * (p * f (pseudo_proj_True n w) +
     (1 -p) * f (pseudo_proj_False n w))"
    proof (rule borel_Suc_expectation)
      show "f \<in> borel_measurable (F (Suc n))" using assms by simp
      show "g \<in> F n \<rightarrow>\<^sub>M N" using assms by simp
      show "set_discriminating n g N" using assms by simp
      show "g -` {g w} \<in> sets (F n)" using assms by simp
      show "\<forall>y z. g y = g z \<and> y !! n = z !! n \<longrightarrow> f y = f z" using assms(5) by blast
    qed
    thus ?thesis by simp
  qed
  also have "... = p * f (pseudo_proj_True n w) + (1 -p) * f (pseudo_proj_False n w)" using nz by simp
  finally show ?thesis .
qed


lemma (in infinite_cts_filtration) f_borel_Suc_real_cond_exp:
  assumes "f\<in> borel_measurable (F (Suc n))"
  and "g\<in> measurable (F n) N"
  and "set_discriminating n g N"
  and "\<forall>w. g -` {g w} \<in> sets (F n)"
  and "\<forall>r\<in>range g \<inter> space N. \<exists>A\<in>sets N. range g \<inter> A = {r}"
  and "\<forall>y z. (g y = g z \<and> snth y n = snth z n) \<longrightarrow> f y = f z"
  and "0 < p"
and "p < 1"
  shows "AE w in M. real_cond_exp M (fct_gen_subalgebra M N g) f w = p * f (pseudo_proj_True n w) + (1 - p) * f (pseudo_proj_False n w)"
proof -
  have "AE w in M. real_cond_exp M (fct_gen_subalgebra M N g) f w = expl_cond_expect M g f w"
  proof (rule charact_cond_exp')
    show "disc_fct g"
    proof -
      have "g = g \<circ> (pseudo_proj_True n)" using nat_filtration_not_borel_info[of g n] assms natural_filtration by simp
      have "disc_fct (pseudo_proj_True n)"  unfolding disc_fct_def using pseudo_proj_True_finite_image
        by (simp add: countable_finite)
      hence "disc_fct (g \<circ> (pseudo_proj_True n))" unfolding disc_fct_def
        by (metis countable_image image_comp)
      thus ?thesis using \<open>g = g \<circ> (pseudo_proj_True n)\<close> by simp
    qed
    show "integrable M f" using assms nat_filtration_borel_measurable_integrable natural_filtration by simp
    show "random_variable N g" using assms filtration_measurable natural_filtration nat_filtration_subalgebra
      using nat_discrete_filtration by blast
    show "\<forall>r\<in>range g \<inter> space N. \<exists>A\<in>sets N. range g \<inter> A = {r}" using assms by simp
  qed
  moreover have "\<And>w. expl_cond_expect M g f w = p * f (pseudo_proj_True n w) + (1 - p) * f (pseudo_proj_False n w)"
    using assms f_borel_Suc_expl_cond_expect by blast
  ultimately show ?thesis by simp
qed

lemma (in infinite_cts_filtration) f_borel_Suc_real_cond_exp_proj:
  assumes "f\<in> borel_measurable (F (Suc n))"
and "0 < p"
and "p < 1"
shows "AE w in M. real_cond_exp M (fct_gen_subalgebra M M (pseudo_proj_True n)) f w =
  p * f (pseudo_proj_True n w) + (1 - p) * f (pseudo_proj_False n w)"
proof (rule f_borel_Suc_real_cond_exp)
  show "f \<in> borel_measurable (F (Suc n))" using assms by simp
  show "pseudo_proj_True n \<in> F n \<rightarrow>\<^sub>M M"
    by (simp add: nat_filtration_pseudo_proj_True_measurable natural_filtration)
  show "\<forall>w. pseudo_proj_True n -` {pseudo_proj_True n w} \<in> sets (F n)"
  proof
    fix w
    show "pseudo_proj_True n -` {pseudo_proj_True n w} \<in> sets (F n) "
      by (simp add: nat_filtration_singleton natural_filtration pseudo_proj_True_proj)
  qed
  show "\<forall>r\<in>range (pseudo_proj_True n) \<inter> space M. \<exists>A\<in>events. range (pseudo_proj_True n) \<inter> A = {r}"
  proof (intro ballI)
    fix r
    assume "r \<in> range (pseudo_proj_True n) \<inter> space M"
    hence "r\<in> range (pseudo_proj_True n)" and "r\<in> space M" by auto
    hence "pseudo_proj_True n r = r" using pseudo_proj_True_proj by auto
    hence "(pseudo_proj_True n) -`{r} \<inter> space M \<in> sets M" using pseudo_proj_True_singleton bernoulli by simp
    moreover have "range (pseudo_proj_True n) \<inter> ((pseudo_proj_True n) -`{r} \<inter> space M) = {r}"
    proof
      have "r\<in> range (pseudo_proj_True n) \<inter> (pseudo_proj_True n -` {r} \<inter> space M)"
        using \<open>pseudo_proj_True n r = r\<close> \<open>r \<in> range (pseudo_proj_True n)\<close> \<open>r \<in> space M\<close> by blast
      thus "{r} \<subseteq> range (pseudo_proj_True n) \<inter> (pseudo_proj_True n -` {r} \<inter> space M)" by auto
      show "range (pseudo_proj_True n) \<inter> (pseudo_proj_True n -` {r} \<inter> space M) \<subseteq> {r}"
      proof
        fix x
        assume "x \<in> range (pseudo_proj_True n) \<inter> (pseudo_proj_True n -` {r} \<inter> space M)"
        hence "x\<in> range (pseudo_proj_True n)" and "x\<in> (pseudo_proj_True n -` {r})" by auto
        have "x = pseudo_proj_True n x" using \<open>x\<in> range (pseudo_proj_True n)\<close> pseudo_proj_True_proj by auto
        also have "... = r" using \<open>x\<in> (pseudo_proj_True n -` {r})\<close> by simp
        finally have "x = r" .
        thus "x\<in> {r}" by simp
      qed
    qed
    ultimately show "\<exists>A\<in>events. range (pseudo_proj_True n) \<inter> A = {r}" by auto
  qed
  show "\<forall>y z. pseudo_proj_True n y = pseudo_proj_True n z \<and> y !! n = z !! n \<longrightarrow> f y = f z"
  proof (intro allI impI conjI)
    fix y z
    assume "pseudo_proj_True n y = pseudo_proj_True n z \<and> y !! n = z !! n"
    hence "pseudo_proj_True n y = pseudo_proj_True n z" and "snth y n = snth z n" by auto
    hence "pseudo_proj_True (Suc n) y = pseudo_proj_True (Suc n) z" unfolding pseudo_proj_True_def
      by (metis (full_types) \<open>pseudo_proj_True n y = pseudo_proj_True n z\<close> pseudo_proj_True_same_img stake_Suc)
    thus "f y = f z" using nat_filtration_info assms natural_filtration by (metis comp_apply)
  qed
  show "set_discriminating n (pseudo_proj_True n) M" unfolding set_discriminating_def using pseudo_proj_True_proj by simp
  show "0 < p" and "p < 1" using assms by auto
qed


subsection  \<open>Images of stochastic processes by prefixes of streams\<close>

text \<open>We define a function that, given a stream of coin tosses and a stochastic process, returns a stream of the values
of the stochastic process up to a given time. This function will be used to characterize the smallest filtration that,
at any time n, makes each random variable of a given stochastic process measurable up to time n.\<close>

subsubsection \<open>Definitions\<close>



primrec smap_stoch_proc where
  "smap_stoch_proc 0 f k w = []"
| "smap_stoch_proc (Suc n) f k w = (f k w) # (smap_stoch_proc n f (Suc k) w)"


lemma smap_stoch_proc_length:
  shows "length (smap_stoch_proc n f k w) = n"
  by (induction n arbitrary:k) auto


lemma smap_stoch_proc_nth:
  shows "Suc p \<le> Suc n \<Longrightarrow> nth (smap_stoch_proc (Suc n) f k w) p = f (k+p) w"
proof (induction n arbitrary:p k)
  case 0
  hence "p = 0" by simp
  hence "(smap_stoch_proc (Suc 0) f k w) ! p = ((f k w) # (smap_stoch_proc 0 f (Suc k) w))!0" by simp
  also have "... = f (k+p) w" using \<open>p=0\<close> by simp
  finally show ?case .
next
  case (Suc n)
  show ?case
  proof (cases "\<exists>m. p = Suc m")
    case True
    from this obtain m where "p = Suc m" by auto
    hence "smap_stoch_proc (Suc (Suc n)) f k w ! p = (smap_stoch_proc (Suc n) f (Suc k) w) ! m" by simp
    also have "... = f ((Suc k) + m) w" using Suc(1)[of m] Suc.prems \<open>p = Suc m\<close> by blast
    also have "... = f (k + (Suc m)) w" by simp
    finally show "smap_stoch_proc (Suc (Suc n)) f k w ! p = f (k + p) w" using \<open>p = Suc m\<close> by simp
  next
    case False
    hence "p = 0" using less_Suc_eq_0_disj by blast
    thus "smap_stoch_proc (Suc (Suc n)) f k w ! p =  f (k+p) w" by simp
  qed
qed


definition proj_stoch_proc where
"proj_stoch_proc f n = (\<lambda>w. shift (smap_stoch_proc n f 0 w) (sconst (f n w)))"


lemma proj_stoch_proc_component:
  shows "k < n \<Longrightarrow> (snth (proj_stoch_proc f n w) k) = f k w"
    and "n \<le> k \<Longrightarrow> (snth (proj_stoch_proc f n w) k) = f n w"
proof -
  show "k < n \<Longrightarrow> proj_stoch_proc f n w !! k = f k w"
  proof -
    assume "k < n"
    hence "\<exists>m. n = Suc m" using less_imp_Suc_add by blast
    from this obtain m where "n = Suc m" by auto
    have "proj_stoch_proc f n w !! k = (smap_stoch_proc n f 0 w) ! k" unfolding proj_stoch_proc_def
      using \<open>k<n\<close> by (simp add: smap_stoch_proc_length)
    also have "... = f k w" using \<open>n = Suc m\<close> \<open>k < n\<close> smap_stoch_proc_nth
      by (metis Suc_leI add.left_neutral)
    finally show ?thesis .
  qed
  show "n \<le> k \<Longrightarrow> (snth (proj_stoch_proc f n w) k) = f n w"
  proof -
    assume "n \<le> k"
    hence "proj_stoch_proc f n w !! k = (sconst (f n w)) !! (k - n)"
      by (simp add: proj_stoch_proc_def smap_stoch_proc_length)
    also have "... = f n w" by simp
    finally show ?thesis .
  qed
qed

lemma proj_stoch_proc_component':
  assumes "k \<le> n"
  shows "f k x = snth (proj_stoch_proc f n x) k"
  proof (cases "k < n")
    case True
    thus ?thesis using proj_stoch_proc_component[of k n f x] assms by simp
  next
    case False
    hence "k = n" using assms by simp
    thus ?thesis using proj_stoch_proc_component[of k n f x] assms by simp
  qed

lemma proj_stoch_proc_eq_snth:
  assumes "proj_stoch_proc f n x = proj_stoch_proc f n y"
and "k \<le> n"
shows "f k x = f k y"
proof -
  have "f k x = snth (proj_stoch_proc f n x) k"  using assms proj_stoch_proc_component'[of k n f] by simp
  also have "... = snth (proj_stoch_proc f n y) k" using assms by simp
  also have "... = f k y" using assms proj_stoch_proc_component'[of k n f] by simp
  finally show ?thesis .
qed

lemma proj_stoch_measurable_if_adapted:
  assumes "filtration M F"
  and "adapt_stoch_proc F f N"
  shows "proj_stoch_proc f n \<in> measurable M (stream_space N)"
proof (rule measurable_stream_space2)
  fix m
  show "(\<lambda>x. proj_stoch_proc f n x !! m) \<in> M \<rightarrow>\<^sub>M N"
  proof (cases "m < n")
    case True
    hence "\<forall>x. proj_stoch_proc f n x !! m = f m x" by (simp add: proj_stoch_proc_component)
    hence "(\<lambda>x. proj_stoch_proc f n x !! m) = f m" by simp
    thus ?thesis using assms unfolding adapt_stoch_proc_def filtration_def
      by (metis measurable_from_subalg)
  next
    case False
    hence "\<forall>x. proj_stoch_proc f n x !! m = f n x" by (simp add: proj_stoch_proc_component)
    hence "(\<lambda>x. proj_stoch_proc f n x !! m) = f n" by simp
    thus ?thesis using assms unfolding adapt_stoch_proc_def filtration_def
      by (metis measurable_from_subalg)
  qed
qed

lemma proj_stoch_adapted_if_adapted:
  assumes "filtration M F"
  and "adapt_stoch_proc F f N"
  shows "proj_stoch_proc f n \<in> measurable (F n) (stream_space N)"
proof (rule measurable_stream_space2)
  fix m
  show "(\<lambda>x. proj_stoch_proc f n x !! m) \<in> measurable (F n) N"
  proof (cases "m < n")
    case True
    hence "\<forall>x. proj_stoch_proc f n x !! m = f m x" by (simp add: proj_stoch_proc_component)
    hence "(\<lambda>x. proj_stoch_proc f n x !! m) = f m" by simp
    thus ?thesis using assms unfolding adapt_stoch_proc_def filtration_def
      by (metis True measurable_from_subalg not_less order.asym)
  next
    case False
    hence "\<forall>x. proj_stoch_proc f n x !! m = f n x" by (simp add: proj_stoch_proc_component)
    hence "(\<lambda>x. proj_stoch_proc f n x !! m) = f n" by simp
    thus ?thesis using assms unfolding adapt_stoch_proc_def by metis
  qed
qed

lemma proj_stoch_adapted_if_adapted':
  assumes "filtration M F"
  and "adapt_stoch_proc F f N"
shows "adapt_stoch_proc F (proj_stoch_proc f) (stream_space N)" unfolding adapt_stoch_proc_def
proof
  fix n
  show "proj_stoch_proc f n \<in> F n \<rightarrow>\<^sub>M stream_space N" using assms by (simp add: proj_stoch_adapted_if_adapted)
qed


lemma (in infinite_cts_filtration) proj_stoch_proj_invariant:
fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
shows "proj_stoch_proc X n w = proj_stoch_proc X n (pseudo_proj_True n w)"
proof -
  have "\<And>m. snth (proj_stoch_proc X n w) m = snth (proj_stoch_proc X n (pseudo_proj_True n w)) m"
  proof -
    fix m
    show "snth (proj_stoch_proc X n w) m = snth (proj_stoch_proc X n (pseudo_proj_True n w)) m"
    proof (cases "m < n")
      case True
      hence "snth (proj_stoch_proc X n w) m = X m w" by (simp add: proj_stoch_proc_component)
      also have "... = X m (pseudo_proj_True n w)"
      proof (rule borel_adapt_nat_filtration_info[symmetric], (simp add:assms))
        show "m \<le> n" using True by linarith
      qed
      also have "... = snth (proj_stoch_proc X n (pseudo_proj_True n w)) m" using True
        by (simp add: proj_stoch_proc_component)
      finally show ?thesis .
    next
      case False
      hence "snth (proj_stoch_proc X n w) m = X n w" by (simp add: proj_stoch_proc_component)
      also have "... = X n (pseudo_proj_True n w)"
        by (rule borel_adapt_nat_filtration_info[symmetric]) (auto simp add:assms)
      also have "... = snth (proj_stoch_proc X n (pseudo_proj_True n w)) m" using False
        by (simp add: proj_stoch_proc_component)
      finally show ?thesis .
    qed
  qed
  thus "proj_stoch_proc X n w = proj_stoch_proc X n (pseudo_proj_True n w)"
    using diff_streams_only_if by auto
qed

lemma (in infinite_cts_filtration) proj_stoch_set_finite_range:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
  shows "finite (range (proj_stoch_proc X n))"
proof -
  have "finite (range (pseudo_proj_True n))" using pseudo_proj_True_finite_image by simp
  moreover have "proj_stoch_proc X n = (proj_stoch_proc X n) \<circ> (pseudo_proj_True n)"
  proof
    fix x
    show "proj_stoch_proc X n x = (proj_stoch_proc X n \<circ> pseudo_proj_True n) x"
      using assms proj_stoch_proj_invariant by (metis comp_apply)
  qed
  ultimately show ?thesis
    by (metis finite_imageI fun.set_map)
qed

lemma (in infinite_cts_filtration) proj_stoch_set_discriminating:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
  shows "set_discriminating n (proj_stoch_proc X n) N"
proof -
  have "\<forall>w. proj_stoch_proc X n w = proj_stoch_proc X n (pseudo_proj_True n w)"
    using assms proj_stoch_proj_invariant  by auto
  thus ?thesis unfolding set_discriminating_def by simp
qed

lemma (in infinite_cts_filtration) proj_stoch_preimage:
  assumes "borel_adapt_stoch_proc F X"
  shows "(proj_stoch_proc X n) -` {proj_stoch_proc X n w} = (\<Inter>i\<in> {m. m \<le> n}. (X i) -` {X i w})"
proof
  define psX where "psX = proj_stoch_proc X n"
  show "proj_stoch_proc X n -` {proj_stoch_proc X n w} \<subseteq> (\<Inter>i\<in>{m. m \<le> n}. X i -` {X i w})"
  proof
    fix x
    assume "x \<in> proj_stoch_proc X n -` {proj_stoch_proc X n w}"
    hence "psX x = psX w" unfolding psX_def using assms by simp
    hence "\<And>i. i \<in>{m. m \<le> n} \<Longrightarrow> x  \<in> (X i) -`{X i w}"
    proof -
      fix i
      assume "i\<in> {m. m\<le>n}"
      hence "i \<le> n" by auto
      have "X i x = snth (psX x) i" unfolding psX_def
        by (metis Suc_le_eq Suc_le_mono \<open>i \<le> n\<close> le_Suc_eq nat.simps(1) proj_stoch_proc_component(1)
            proj_stoch_proc_component(2))
      also have "... = snth (psX w) i" using \<open>psX x = psX w\<close> by simp
      also have "... = X i w" unfolding psX_def
        by (metis Suc_le_eq Suc_le_mono \<open>i \<le> n\<close> le_Suc_eq nat.simps(1) proj_stoch_proc_component(1)
            proj_stoch_proc_component(2))
      finally have "X i x = X i w" .
      thus "x  \<in> (X i) -`{X i w}" by simp
    qed
    thus "x \<in> (\<Inter>i\<in>{m. m \<le> n}. (X i) -` {X i w})" by auto
  qed
  show "(\<Inter>i\<in>{m. m \<le> n}. (X i) -` {X i w}) \<subseteq> (proj_stoch_proc X n) -` {proj_stoch_proc X n w}"
  proof
    fix x
    assume "x\<in> (\<Inter>i\<in>{m. m \<le> n}. (X i) -` {X i w})"
    hence "\<And>i. i \<in>{m. m \<le> n} \<Longrightarrow> x  \<in> (X i) -`{X i w}" by simp
    hence "\<And>i. i \<in>{m. m \<le> n} \<Longrightarrow> X i x = X i w" by simp
    hence "\<And>i. i \<le> n \<Longrightarrow> X i x = X i w" by auto
    hence "psX x = psX w" unfolding psX_def
      by (metis (mono_tags, hide_lams) diff_streams_only_if linear not_le order_refl
          proj_stoch_proc_component(1) proj_stoch_proc_component(2))
    thus "x \<in> (proj_stoch_proc X n) -` {proj_stoch_proc X n w}" unfolding psX_def by auto
  qed
qed


lemma (in infinite_cts_filtration) proj_stoch_singleton_set:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  shows "(proj_stoch_proc X n) -` {proj_stoch_proc X n w} \<in> sets (F n)"
proof -
  have "\<And>i. i \<le> n \<Longrightarrow> (X i) \<in> measurable (F n) borel"
    by (meson adapt_stoch_proc_def assms increasing_measurable_info)
  have "(\<Inter>i\<in> {m. m \<le> n}. (X i) -` {X i w}) \<in> sets (F n)"
  proof ((rule sigma_algebra.countable_INT''), auto)
    show "sigma_algebra (space (F n)) (sets (F n))"
      using measure_space measure_space_def by auto
    show "UNIV \<in> sets (F n)"
      using \<open>sigma_algebra (space (F n)) (sets (F n))\<close> nat_filtration_space natural_filtration
        sigma_algebra.sigma_sets_eq sigma_sets_top by fastforce
    have "\<And>i. i \<le> n \<Longrightarrow> (X i) -` {X i w} \<in> sets (nat_filtration n)"
    proof (rule nat_filtration_borel_measurable_singleton)
      fix i
      assume "i \<le> n"
      show "X i \<in> borel_measurable (nat_filtration n)" using assms natural_filtration unfolding adapt_stoch_proc_def
        using \<open>i \<le> n\<close> increasing_measurable_info by blast
    qed
    thus "\<And>i. i \<le> n \<Longrightarrow> (X i) -` {X i w} \<in> sets (F n)" using natural_filtration by simp
  qed
  thus ?thesis using assms  by (simp add: proj_stoch_preimage)
qed


lemma (in infinite_cts_filtration) finite_range_stream_space:
  fixes f::"'a \<Rightarrow> 'b::t1_space"
  assumes "finite (range f)"
  shows "(\<lambda>w. snth w i) -` (open_exclude_set (f x) (range f)) \<in> sets (stream_space borel)"
proof -
  define opex where "opex = open_exclude_set (f x) (range f)"
  have "open opex" and "opex \<inter> (range f) = {f x}" using assms unfolding opex_def by
    (auto simp add:open_exclude_finite)
  hence "opex\<in> sets borel" by simp
  hence vim: "(\<lambda>w. snth w i) -` opex \<in> sets (vimage_algebra (streams (space borel)) (\<lambda>w. snth w i) borel)"
    by (metis in_vimage_algebra inf_top.right_neutral space_borel streams_UNIV)
  have "(\<lambda>w. snth w i) -` opex \<in> sets (\<Squnion>i. vimage_algebra (streams (space borel)) (\<lambda>w. snth w i) borel)"
  proof (rule in_sets_SUP, simp)
    show "\<And>i. i \<in> UNIV \<Longrightarrow> space (vimage_algebra (streams (space borel)) (\<lambda>w. w !! i) borel) =
      UNIV" by simp
    show "(\<lambda>w. w !! i) -` opex \<in> sets (vimage_algebra (streams (space borel)) (\<lambda>w. w !! i) borel)"
      using vim by simp
  qed
  thus ?thesis using sets_stream_space_eq unfolding opex_def by blast
qed

lemma (in infinite_cts_filtration) proj_stoch_range_singleton:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  and "r\<in> range (proj_stoch_proc X n)"
shows "\<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc X n) \<inter> A = {r}"
proof -
  have "\<exists>x. r = proj_stoch_proc X n x" using assms by auto
  from this obtain x where "r = proj_stoch_proc X n x" by auto
  have "\<And>i. i \<le> n \<Longrightarrow> (X i) \<in> measurable (F n) borel"
    by (meson adapt_stoch_proc_def assms increasing_measurable_info)
  hence fin: "\<And>i. i \<le> n \<Longrightarrow> finite (range (X i))"
    by (metis bernoulli bernoulli_stream_space nat_filtration_vimage_finite natural_filtration streams_UNIV)
  show ?thesis
  proof
    define cand where "cand = (\<Inter>i \<in> {m. m\<le> n}. (\<lambda>w. snth w i) -` (open_exclude_set (X i x) (range (X i))))"
    show "cand \<in> sets (stream_space borel)" unfolding cand_def
    proof ((rule sigma_algebra.countable_INT''), auto)
      show "UNIV \<in> sets (stream_space borel)" by (metis space_borel streams_UNIV streams_stream_space)
      show "sigma_algebra (space (stream_space borel)) (sets (stream_space borel))"
        by (simp add: sets.sigma_algebra_axioms)
      show "\<And>i. i \<le> n \<Longrightarrow> (\<lambda>w. w !! i) -` open_exclude_set (X i x) (range (X i)) \<in> sets (stream_space borel)"
      proof -
        fix i
        assume "i \<le> n"
        thus "(\<lambda>w. w !! i) -` open_exclude_set (X i x) (range (X i)) \<in> sets (stream_space borel)"
          using fin by (simp add:finite_range_stream_space)
      qed
    qed
    have "range (proj_stoch_proc X n) \<inter> cand = {proj_stoch_proc X n x}"
    proof
      have "proj_stoch_proc X n x \<in> range (proj_stoch_proc X n) \<inter> cand"
      proof
        show "proj_stoch_proc X n x \<in> range (proj_stoch_proc X n)" by simp
        show "proj_stoch_proc X n x \<in> cand" unfolding cand_def
        proof
          fix i
          assume "i\<in> {m. m\<le> n}"
          hence "i \<le> n" by simp
          hence "snth (proj_stoch_proc X n x) i = X i x"
            by (metis le_antisym not_less proj_stoch_proc_component)
          also have "... \<in> open_exclude_set (X i x) (range (X i))" using assms open_exclude_finite(2)
            by (metis IntE \<open>i \<le> n\<close> fin insert_iff rangeI)
          finally have "snth (proj_stoch_proc X n x) i \<in> open_exclude_set (X i x) (range (X i))" .
          thus "proj_stoch_proc X n x \<in> (\<lambda>w. w !! i) -` open_exclude_set (X i x) (range (X i))" by simp
        qed
      qed
      thus "{proj_stoch_proc X n x} \<subseteq> range (proj_stoch_proc X n) \<inter> cand" by simp
      show "range (proj_stoch_proc X n) \<inter> cand \<subseteq> {proj_stoch_proc X n x}"
      proof
        fix z
        assume "z\<in> range (proj_stoch_proc X n) \<inter> cand"
        hence "\<exists>y. z = proj_stoch_proc X n y" by auto
        from this obtain y where "z = proj_stoch_proc X n y" by auto
        hence "proj_stoch_proc X n y \<in> cand" using \<open>z\<in> range (proj_stoch_proc X n) \<inter> cand\<close> by simp
        have "\<forall>i. i\<le>n \<longrightarrow> X i y = X i x"
        proof (intro allI impI)
          fix i
          assume "i \<le> n"
          hence "X i y = snth (proj_stoch_proc X n y) i"
            by (metis le_antisym not_less proj_stoch_proc_component)
          also have "... \<in> open_exclude_set (X i x) (range (X i))"
            using \<open>proj_stoch_proc X n y \<in> cand\<close> \<open>i \<le> n\<close> unfolding cand_def by simp
          finally have "X i y \<in> open_exclude_set (X i x) (range (X i))" .
          thus "X i y = X i x" using assms using assms open_exclude_finite(2)
            by (metis Int_iff \<open>i \<le> n\<close> empty_iff fin insert_iff rangeI)
        qed
        hence "\<forall>i. snth (proj_stoch_proc X n y) i = snth (proj_stoch_proc X n x) i"
          using proj_stoch_proc_component by (metis nat_le_linear not_less)
        hence "proj_stoch_proc X n y = proj_stoch_proc X n x"
          using diff_streams_only_if by auto
        thus "z\<in> {proj_stoch_proc X n x}" using \<open>z = proj_stoch_proc X n y\<close> by auto
      qed
    qed
    thus "range (proj_stoch_proc X n) \<inter> cand = {r}" using \<open>r = proj_stoch_proc X n x\<close> by simp
  qed
qed

definition (in infinite_cts_filtration) stream_space_single where
"stream_space_single X r = (if (\<exists>U. U\<in> sets (stream_space borel) \<and> U\<inter> (range X) = {r})
  then SOME U. U\<in> sets (stream_space borel) \<and> U \<inter> (range X) = {r} else {})"

lemma (in infinite_cts_filtration) stream_space_singleI:
  assumes "\<exists>U. U\<in> sets (stream_space borel) \<and> U\<inter> (range X) = {r}"
  shows "stream_space_single X r \<in> sets (stream_space borel) \<and> stream_space_single X r \<inter> (range X) = {r}"
proof -
  let ?V = "SOME U. U\<in> sets (stream_space borel) \<and> U\<inter> (range X) = {r}"
  have vprop: "?V\<in> sets (stream_space borel) \<and> ?V \<inter> (range X) = {r}" using someI_ex[of "\<lambda>U. U\<in> sets (stream_space borel) \<and> U\<inter> (range X) = {r}"]
    assms by blast
  show ?thesis by (simp add:stream_space_single_def vprop assms)
qed

lemma (in infinite_cts_filtration)
fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  and "r\<in> range (proj_stoch_proc X n)"
shows stream_space_single_set: "stream_space_single (proj_stoch_proc X n) r \<in> sets (stream_space borel)"
and stream_space_single_preimage: "stream_space_single (proj_stoch_proc X n) r \<inter> range (proj_stoch_proc X n) = {r}"
proof -
  have "\<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc X n) \<inter> A = {r}"
    by (simp add: assms proj_stoch_range_singleton)
  hence "\<exists>U. U \<in> sets (stream_space borel) \<and> U \<inter> range (proj_stoch_proc X n) = {r}" by auto
  hence a: "stream_space_single (proj_stoch_proc X n) r \<in> sets (stream_space borel) \<and>
    stream_space_single (proj_stoch_proc X n) r \<inter> (range (proj_stoch_proc X n)) = {r}"
    using stream_space_singleI[of "proj_stoch_proc X n"] by simp
  thus "stream_space_single (proj_stoch_proc X n) r \<in> sets (stream_space borel)" by simp
  show "stream_space_single (proj_stoch_proc X n) r \<inter> range (proj_stoch_proc X n) = {r}" using a by simp
qed

subsubsection \<open>Induced filtration, relationship with filtration generated by underlying stochastic process\<close>

definition comp_proj_i where
"comp_proj_i X n i y = {z\<in> range (proj_stoch_proc X n). snth z i = y}"

lemma (in infinite_cts_filtration) comp_proj_i_finite:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
  shows "finite (comp_proj_i X n i y)"
proof -
  have "finite (range (proj_stoch_proc X n))"
    using proj_stoch_set_finite_range[of X] assms by simp
  thus ?thesis unfolding comp_proj_i_def by simp
qed

lemma stoch_proc_comp_proj_i_preimage:
  assumes "i \<le> n"
  shows "(X i) -` {X i x} = (\<Union>z\<in> comp_proj_i X n i (X i x). (proj_stoch_proc X n) -` {z})"
proof
  show "X i -` {X i x} \<subseteq> (\<Union>z\<in>comp_proj_i X n i (X i x). proj_stoch_proc X n -` {z})"
  proof
    fix w
    assume "w \<in> X i -` {X i x}"
    hence "X i w = X i x" by simp
    hence "snth (proj_stoch_proc X n w) i = X i x" using assms
      by (metis le_neq_implies_less proj_stoch_proc_component(1) proj_stoch_proc_component(2))
    hence "(proj_stoch_proc X n w) \<in> comp_proj_i X n i (X i x)" unfolding comp_proj_i_def by simp
    moreover have "w\<in> proj_stoch_proc X i -` {proj_stoch_proc X i w}" by simp
    ultimately show "w\<in> (\<Union>z\<in>comp_proj_i X n i (X i x). proj_stoch_proc X n -` {z})" by simp
  qed
  show "(\<Union>z\<in>comp_proj_i X n i (X i x). proj_stoch_proc X n -` {z}) \<subseteq> X i -` {X i x}"
  proof -
    have "\<forall>z\<in> comp_proj_i X n i (X i x). proj_stoch_proc X n -` {z} \<subseteq> X i -` {X i x}"
    proof
      fix z
      assume "z\<in> comp_proj_i X n i (X i x)"
      hence "z\<in> range (proj_stoch_proc X n)" and "snth z i = X i x" unfolding comp_proj_i_def by auto
      show "proj_stoch_proc X n -` {z} \<subseteq> X i -` {X i x}"
      proof
        fix w
        assume "w\<in>proj_stoch_proc X n -` {z}"
        have "X i w = snth (proj_stoch_proc X n w) i" using assms
          by (metis le_neq_implies_less proj_stoch_proc_component(1) proj_stoch_proc_component(2))
        also have "... = snth z i" using \<open>w\<in>proj_stoch_proc X n -` {z}\<close> by auto
        also have "... = X i x" using \<open>snth z i = X i x\<close> by simp
        finally have "X i w = X i x" .
        thus "w\<in> X i -` {X i x}" by simp
      qed
    qed
    thus ?thesis by auto
  qed
qed



(* comp_proj to remove? *)
definition comp_proj where
  "comp_proj X n y = {z\<in> range (proj_stoch_proc X n). snth z n = y}"

lemma (in infinite_cts_filtration) comp_proj_finite:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "borel_adapt_stoch_proc F X"
  shows "finite (comp_proj X n y)"
proof -
  have "finite (range (proj_stoch_proc X n))"
    using proj_stoch_set_finite_range[of X] assms by simp
  thus ?thesis unfolding comp_proj_def by simp
qed


lemma stoch_proc_comp_proj_preimage:
  shows "(X n) -` {X n x} = (\<Union>z\<in> comp_proj X n (X n x). (proj_stoch_proc X n) -` {z})"
proof
  show "X n -` {X n x} \<subseteq> (\<Union>z\<in>comp_proj X n (X n x). proj_stoch_proc X n -` {z})"
  proof
    fix w
    assume "w \<in> X n -` {X n x}"
    hence "X n w = X n x" by simp
    hence "snth (proj_stoch_proc X n w) n = X n x" by (simp add: proj_stoch_proc_component(2))
    hence "(proj_stoch_proc X n w) \<in> comp_proj X n (X n x)" unfolding comp_proj_def by simp
    moreover have "w\<in> proj_stoch_proc X n -` {proj_stoch_proc X n w}" by simp
    ultimately show "w\<in> (\<Union>z\<in>comp_proj X n (X n x). proj_stoch_proc X n -` {z})" by simp
  qed
  show "(\<Union>z\<in>comp_proj X n (X n x). proj_stoch_proc X n -` {z}) \<subseteq> X n -` {X n x}"
  proof -
    have "\<forall>z\<in> comp_proj X n (X n x). proj_stoch_proc X n -` {z} \<subseteq> X n -` {X n x}"
    proof
      fix z
      assume "z\<in> comp_proj X n (X n x)"
      hence "z\<in> range (proj_stoch_proc X n)" and "snth z n = X n x" unfolding comp_proj_def by auto
      show "proj_stoch_proc X n -` {z} \<subseteq> X n -` {X n x}"
      proof
        fix w
        assume "w\<in>proj_stoch_proc X n -` {z}"
        have "X n w = snth (proj_stoch_proc X n w) n" by (simp add: proj_stoch_proc_component(2))
        also have "... = snth z n" using \<open>w\<in>proj_stoch_proc X n -` {z}\<close> by auto
        also have "... = X n x" using \<open>snth z n = X n x\<close> by simp
        finally have "X n w = X n x" .
        thus "w\<in> X n -` {X n x}" by simp
      qed
    qed
    thus ?thesis by auto
  qed
qed


lemma comp_proj_stoch_proc_preimage:
  shows "(proj_stoch_proc X n) -` {proj_stoch_proc X n x} = (\<Inter> i\<in> {m. m\<le>n}. (X i) -`{X i x})"
proof
  show "proj_stoch_proc X n -` {proj_stoch_proc X n x} \<subseteq> (\<Inter>i\<in>{m. m \<le> n}. X i -` {X i x})"
  proof
    fix z
    assume "z\<in> proj_stoch_proc X n -` {proj_stoch_proc X n x}"
    hence "proj_stoch_proc X n z = proj_stoch_proc X n x" by simp
    hence "\<forall>i\<le>n. X i z = X i x" using proj_stoch_proc_component by (metis less_le)
    hence "\<forall>i\<le>n. z\<in> X i -`{X i x}" by simp
    thus "z\<in> (\<Inter>i\<in>{m. m \<le> n}. X i -` {X i x})" by simp
  qed
  show "(\<Inter>i\<in>{m. m \<le> n}. X i -` {X i x}) \<subseteq> proj_stoch_proc X n -` {proj_stoch_proc X n x}"
  proof
    fix z
    assume "z\<in> (\<Inter>i\<in>{m. m \<le> n}. X i -` {X i x})"
    hence "\<forall>i\<le> n. X i z = X i x" by auto
    hence "\<forall>i. snth (proj_stoch_proc X n z) i = snth (proj_stoch_proc X n x) i"
      using proj_stoch_proc_component by (metis nat_le_linear not_less)
    hence "proj_stoch_proc X n z = proj_stoch_proc X n x" using diff_streams_only_if by auto
    thus "z\<in> proj_stoch_proc X n -` {proj_stoch_proc X n x}" by simp
  qed
qed



definition  stoch_proc_filt where
  "stoch_proc_filt M X N (n::nat) = gen_subalgebra M (sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets N }))"



lemma  stoch_proc_filt_space:
  shows "space (stoch_proc_filt M X N n) = space M" unfolding stoch_proc_filt_def by (simp add:gen_subalgebra_space)




lemma  stoch_proc_filt_sets:
assumes "\<And>i. i \<le> n\<Longrightarrow> (X i) \<in> measurable M N"
  shows "sets (stoch_proc_filt M X N n) = (sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets N }))"
  unfolding stoch_proc_filt_def
proof (rule gen_subalgebra_sigma_sets)
  show "sigma_algebra (space M) (sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}))" using assms
    by (simp add: adapt_sigma_sets)
  show "sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}) \<subseteq> sets M"
  proof (rule sigma_algebra.sigma_sets_subset, rule Sigma_Algebra.sets.sigma_algebra_axioms, rule UN_subset_iff[THEN iffD2], intro ballI)
    fix i
    assume "i\<in> {m. m\<le>n}"
    thus "{X i -` A \<inter> space M |A. A \<in> sets N} \<subseteq> sets M" using assms measurable_sets by blast
  qed
qed


lemma stoch_proc_filt_adapt:
  assumes "\<And>n. X n \<in> measurable M N"
  shows "adapt_stoch_proc (stoch_proc_filt M X N) X N" unfolding adapt_stoch_proc_def
proof
  fix m
  show "X m \<in> measurable (stoch_proc_filt M X N m) N" unfolding measurable_def
  proof ((intro CollectI), (intro conjI))
    have "space (stoch_proc_filt M X N m) = space M" by (simp add: stoch_proc_filt_space)
    thus "X m \<in> space (stoch_proc_filt M X N m) \<rightarrow> space N" using assms unfolding measurable_def by simp
    show "\<forall>y\<in>sets N. X m -` y \<inter> space (stoch_proc_filt M X N m) \<in> sets (stoch_proc_filt M X N m)"
    proof
      fix B
      assume "B\<in> sets N"
      have "X m -` B \<inter> space (stoch_proc_filt M X N m) = X m -`B \<inter> space M"
        using \<open>space (stoch_proc_filt M X N m) = space M\<close> by simp
      also have "... \<in> (\<Union> i\<in> {p. p\<le> m}. {(X i -`A) \<inter> (space M) | A. A\<in> sets N })" using \<open>B\<in> sets N\<close> by auto
      also have "... \<subseteq> sigma_sets (space M) (\<Union> i\<in> {p. p\<le> m}. {(X i -`A) \<inter> (space M) | A. A\<in> sets N })" by auto
      also have "... = sets (stoch_proc_filt M X N m)" using assms stoch_proc_filt_sets by blast
      finally show "X m -` B \<inter> space (stoch_proc_filt M X N m) \<in> sets (stoch_proc_filt M X N m)" .
    qed
  qed
qed



lemma  stoch_proc_filt_disc_filtr:
  assumes "\<And>i. (X i) \<in> measurable M N"
  shows "disc_filtr M (stoch_proc_filt M X N)" unfolding disc_filtr_def
proof (intro conjI allI impI)
{
  fix n
  show "subalgebra M (stoch_proc_filt M X N n)" unfolding subalgebra_def
  proof
    show "space (stoch_proc_filt M X N n) = space M" by (simp add:stoch_proc_filt_space)
    show "sets (stoch_proc_filt M X N n) \<subseteq> sets M"
    proof -
      have "sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}) \<subseteq> sets M"
      proof (rule sigma_algebra.sigma_sets_subset, rule Sigma_Algebra.sets.sigma_algebra_axioms, rule UN_subset_iff[THEN iffD2], intro ballI)
        fix i
        assume "i\<in> {m. m\<le>n}"
        thus "{X i -` A \<inter> space M |A. A \<in> sets N} \<subseteq> sets M" using assms measurable_sets by blast
      qed
      thus ?thesis using assms by (simp add:stoch_proc_filt_sets)
    qed
  qed
}
{
  fix n
  fix p
  assume "(n::nat) \<le> p"
  show "subalgebra (stoch_proc_filt M X N p) (stoch_proc_filt M X N n)" unfolding subalgebra_def
  proof
    have "space (stoch_proc_filt M X N n) = space M" by (simp add: stoch_proc_filt_space)
    also have "... = space (stoch_proc_filt M X N p)" by (simp add: stoch_proc_filt_space)
    finally show "space (stoch_proc_filt M X N n) = space (stoch_proc_filt M X N p)" .
    show "sets (stoch_proc_filt M X N n) \<subseteq> sets (stoch_proc_filt M X N p)"
    proof -
      have "sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}) \<subseteq>
        sigma_sets (space M) (\<Union>i\<in>{m. m \<le> p}. {X i -` A \<inter> space M |A. A \<in> sets N})"
      proof (rule sigma_sets_mono')
        show "(\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N}) \<subseteq> (\<Union>i\<in>{m. m \<le> p}. {X i -` A \<inter> space M |A. A \<in> sets N})"
        proof (rule UN_subset_iff[THEN iffD2], intro ballI)
          fix i
          assume "i\<in> {m. m\<le>n}"
          show "{X i -` A \<inter> space M |A. A \<in> sets N} \<subseteq> (\<Union>i\<in>{m. m \<le> p}. {X i -` A \<inter> space M |A. A \<in> sets N})"
            using \<open>i \<in> {m. m \<le> n}\<close> \<open>n \<le> p\<close> order_trans by auto
        qed
      qed
      thus ?thesis using assms by (simp add:stoch_proc_filt_sets)
    qed
  qed
}
qed


lemma gen_subalgebra_eq_space_sets:
  assumes "space M = space N"
  and "P = Q"
  and "P\<subseteq> Pow (space M)"
  shows "sets (gen_subalgebra M P) = sets (gen_subalgebra N Q)" unfolding gen_subalgebra_def using assms by simp

lemma stoch_proc_filt_eq_sets:
  assumes "space M = space N"
  shows "sets (stoch_proc_filt M X P n) = sets (stoch_proc_filt N X P n)" unfolding stoch_proc_filt_def
proof (rule gen_subalgebra_eq_space_sets, (simp add: assms)+)
  show "sigma_sets (space N) (\<Union>x\<in>{m. m \<le> n}. {X x -` A \<inter> space N |A. A \<in> sets P}) \<subseteq> Pow (space N)"
  proof (rule sigma_algebra.sigma_sets_subset)
    show "sigma_algebra (space N) (Pow (space N))" by (simp add: sigma_algebra_Pow)
    show "(\<Union>x\<in>{m. m \<le> n}. {X x -` A \<inter> space N |A. A \<in> sets P}) \<subseteq> Pow (space N)" by auto
  qed
qed


lemma (in infinite_cts_filtration) stoch_proc_filt_triv_init:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> real"
  assumes "borel_adapt_stoch_proc nat_filtration X"
  shows "init_triv_filt M (stoch_proc_filt M X borel)" unfolding init_triv_filt_def
proof
  show "filtration M (stoch_proc_filt M X borel)" using stoch_proc_filt_disc_filtr unfolding  filtration_def
    by (metis adapt_stoch_proc_def assms disc_filtr_def  measurable_from_subalg nat_filtration_subalgebra)
  show "sets (stoch_proc_filt M X borel bot) = {{}, space M}"
  proof -
    have seteq: "sets (stoch_proc_filt M X borel 0) =
      (sigma_sets (space M) (\<Union> i\<in> {m. m\<le> 0}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel}))"
    proof (rule stoch_proc_filt_sets)
      show "\<And>i. i \<le> 0 \<Longrightarrow> random_variable borel (X i)"
      proof -
        fix i::nat
        assume "i \<le> 0"
        show "random_variable borel (X i)" using assms unfolding adapt_stoch_proc_def
          using filtration_measurable nat_discrete_filtration
          using natural_filtration by blast
      qed
    qed
  have "triv_init_disc_filtr_prob_space M nat_filtration"
    proof (unfold_locales, intro conjI)
      show "disc_filtr M nat_filtration" unfolding disc_filtr_def
        using filtrationE2 nat_discrete_filtration nat_filtration_subalgebra  by auto
      show "sets (nat_filtration \<bottom>) = {{}, space M}" using nat_info_filtration unfolding init_triv_filt_def by simp
    qed
    hence "\<exists>c. \<forall>w \<in> space M. ((X 0 w)::real) = c" using assms
        triv_init_disc_filtr_prob_space.adapted_init[of M nat_filtration X] by simp
    from this obtain c where img: "\<forall>w \<in> space M. (X 0 w) = c" by auto
    have "(\<Union> i\<in> {m. m\<le> 0}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel}) =
      {(X 0 -`A) \<inter> (space M) | A. A\<in> sets borel}" by auto
    also have "... = {{}, space M}"
    proof
      show "{X 0 -` A \<inter> space M |A. A \<in> sets borel} \<subseteq> {{}, space M}"
      proof -
        have "\<forall>A \<in> sets borel. (X 0 -`A) \<inter> (space M) \<in> {{}, space M}"
        proof
          fix A::"real set"
          assume "A\<in> sets borel"
          show "(X 0 -`A) \<inter> (space M) \<in> {{}, space M}"
          proof (cases "c\<in> A")
            case True
            hence "X 0 -` A \<inter> space M = space M" using img by auto
            thus ?thesis by simp
          next
            case False
            hence "X 0 -` A \<inter> space M = {}" using img by auto
            thus ?thesis by simp
          qed
        qed
        thus ?thesis by auto
      qed
      show "{{}, space M} \<subseteq> {X 0 -` A \<inter> space M |A. A \<in> sets borel}"
      proof -
        have "{} \<in> {X 0 -` A \<inter> space M |A. A \<in> sets borel}" by blast
        moreover have "space M \<in> {X 0 -` A \<inter> space M |A. A \<in> sets borel}"
        proof -
          have "UNIV \<subseteq> X 0 -` space borel"
            using space_borel by blast
          then show ?thesis
            using bernoulli_stream_space by blast
        qed
        ultimately show ?thesis by auto
      qed
    qed
    finally have "(\<Union> i\<in> {m. m\<le> 0}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel}) = {{}, space M}" .
    moreover have "sigma_sets (space M) {{}, space M} = {{}, space M}"
    proof -
      have "sigma_sets (space M) {space M} = {{}, space M}" by simp
      have "sigma_sets (space M) (sigma_sets (space M) {space M}) = sigma_sets (space M) {space M}"
        by (rule sigma_sets_sigma_sets_eq, simp)
      also have "... = {{}, space M}" by simp
      finally show ?thesis by simp
    qed
    ultimately show ?thesis using seteq by (simp add: bot_nat_def)
  qed
qed

lemma (in infinite_cts_filtration) stream_space_borel_union:
fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  and "i\<le> n"
  and "A\<in> sets borel"
shows "\<forall>y\<in> A\<inter> range (X i). X i -`{y} = (proj_stoch_proc X n) -` (\<Union>z\<in> comp_proj_i X n i y.
    (stream_space_single (proj_stoch_proc X n) z))"
proof
  fix y
  assume "y\<in> A\<inter> range (X i)"
  hence "\<exists>x. y = X i x" by auto
  from this obtain x where "y = X i x" by auto
  hence "X i -`{y} = X i -`{X i x}" by simp
  also have "... = (\<Union>z\<in> comp_proj_i X n i (X i x). (proj_stoch_proc X n) -` {z})"
    using \<open>i\<le> n\<close> by (simp add: stoch_proc_comp_proj_i_preimage)
  also have "... = (\<Union>z\<in> comp_proj_i X n i (X i x). (proj_stoch_proc X n) -`
    (stream_space_single (proj_stoch_proc X n) z))"
  proof -
    have "\<forall>z\<in> comp_proj_i X n i (X i x). (proj_stoch_proc X n) -` {z} = (proj_stoch_proc X n) -`
      (stream_space_single (proj_stoch_proc X n) z)"
    proof
      fix z
      assume "z \<in> comp_proj_i X n i (X i x)"
      have "stream_space_single (proj_stoch_proc X n) z \<inter> range (proj_stoch_proc X n) = {z}"
        using stream_space_single_preimage assms
      proof -
        have "z \<in> range (proj_stoch_proc X n)"
          using \<open>z \<in> comp_proj_i X n i (X i x)\<close> comp_proj_i_def by force
        then show ?thesis
          by (meson assms stream_space_single_preimage)
      qed
      thus "(proj_stoch_proc X n) -` {z} = (proj_stoch_proc X n) -`
        (stream_space_single (proj_stoch_proc X n) z)" by auto
    qed
    thus ?thesis by auto
  qed
  also have "... = proj_stoch_proc X n -` (\<Union>z\<in> comp_proj_i X n i y. (stream_space_single (proj_stoch_proc X n) z))"
    by (simp add: \<open>y = X i x\<close> vimage_Union)
  finally show "X i -`{y} = (proj_stoch_proc X n) -` (\<Union>z\<in> comp_proj_i X n i y.
    (stream_space_single (proj_stoch_proc X n) z))" using \<open>y = X i x\<close> by simp
qed



lemma (in infinite_cts_filtration) proj_stoch_pre_borel:
  fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  shows "proj_stoch_proc X n -` {proj_stoch_proc X n x} \<in> sets (stoch_proc_filt M X borel n)"
proof -
  have "proj_stoch_proc X n -` {proj_stoch_proc X n x} = (\<Inter> i\<in> {m. m\<le>n}. (X i) -`{X i x})"
    by (simp add:comp_proj_stoch_proc_preimage)
  also have "... \<in> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})"
  proof -
    have inset: "\<forall>i\<le>n. (X i) -`{X i x} \<in> {X i -` A \<inter> space M |A. A \<in> sets borel}"
    proof (intro allI impI)
      fix i
      assume "i \<le> n"
      have "\<exists>U. open U \<and> U\<inter> (range (X i)) = {X i x}"
      proof -
        have "\<exists>U. open U \<and> X i x\<in> U \<and> U\<inter> ((range (X i))-{X i x}) = {}"
        proof (rule open_except_set)
          have "finite (range (X i))" using assms
            by (metis adapt_stoch_proc_def bernoulli bernoulli_stream_space
              nat_filtration_vimage_finite natural_filtration streams_UNIV)
          thus "finite (range (X i) -{X i x})" by auto
          show "X i x\<notin> (range (X i)) -{X i x}" by simp
        qed
        thus ?thesis using assms by auto
      qed
      from this obtain U where "open U" and "U\<inter> (range (X i)) = {X i x}" by auto
      have "X i -` {X i x} = X i -`U" using \<open>U\<inter> (range (X i)) = {X i x}\<close> by auto
      also have "... = X i -` U \<inter> space M" using bernoulli bernoulli_stream_space by simp
      finally have "X i -` {X i x} = X i -` U \<inter> space M" .
      moreover have "U \<in> sets borel" using \<open>open U\<close> by simp
      ultimately show "(X i) -`{X i x} \<in> {X i -` A \<inter> space M |A. A \<in> sets borel}" by auto
    qed
    show ?thesis
    proof (rule sigma_set_inter_init)
      show "(\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel}) \<subseteq> Pow (space M)" by auto
      show "\<And>i. i \<le> n \<Longrightarrow> X i -` {X i x} \<in> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})"
        using inset by (metis (no_types, lifting) UN_I mem_Collect_eq sigma_sets.Basic)
    qed
  qed
  also have "... = sets (stoch_proc_filt M X borel n)"
  proof (rule stoch_proc_filt_sets[symmetric])
    fix i
    assume "i \<le> n"
    show "random_variable borel (X i)" using assms borel_adapt_stoch_proc_borel_measurable by blast
  qed
  finally show "proj_stoch_proc X n -` {proj_stoch_proc X n x}
    \<in> sets (stoch_proc_filt M X borel n)" .
qed



lemma (in infinite_cts_filtration) stoch_proc_filt_gen:
fixes X::"nat \<Rightarrow> bool stream \<Rightarrow> ('b::t2_space)"
  assumes "borel_adapt_stoch_proc F X"
  shows "stoch_proc_filt M X borel n = fct_gen_subalgebra M (stream_space borel) (proj_stoch_proc X n)"
proof -
  have "(\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})
    \<subseteq> {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}"
  proof (rule UN_subset_iff[THEN iffD2], intro ballI)
    fix i
    assume "i\<in> {m. m\<le>n}"
    hence "i \<le> n" by simp
    show "{X i -` A \<inter> space M |A. A \<in> sets borel} \<subseteq>
      {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}"
    proof -
      have "\<And>A. A\<in> sets borel \<Longrightarrow> X i -` A \<inter> space M \<in> {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}"
      proof -
        fix A::"'b set"
        assume "A\<in> sets borel"
        have "X i -`A \<inter> space M = X i -` A" using bernoulli bernoulli_stream_space by simp
        also have "... = X i -`(A\<inter> range (X i))" by auto
        also have "... = (\<Union> y\<in> A\<inter> range (X i). X i -`{y})" by auto
        also have "... = (\<Union> y\<in> A\<inter> range (X i). (proj_stoch_proc X n) -` (\<Union>z\<in> comp_proj_i X n i y.
            (stream_space_single (proj_stoch_proc X n) z)))" using stream_space_borel_union assms \<open>i\<le>n\<close> \<open>A\<in>sets borel\<close>
          by (metis (mono_tags, lifting) image_cong)
        also have "... = (proj_stoch_proc X n) -` (\<Union> y\<in> A\<inter> range (X i). (\<Union>z\<in> comp_proj_i X n i y.
            (stream_space_single (proj_stoch_proc X n) z)))" by (simp add: vimage_Union)
        finally have "X i -`A \<inter> space M = (proj_stoch_proc X n) -` (\<Union> y\<in> A\<inter> range (X i). (\<Union>z\<in> comp_proj_i X n i y.
            (stream_space_single (proj_stoch_proc X n) z)))" .
        moreover have "(\<Union> y\<in> A\<inter> range (X i). (\<Union>z\<in> comp_proj_i X n i y.
            (stream_space_single (proj_stoch_proc X n) z))) \<in> sets (stream_space borel)"
        proof -
          have "finite (A\<inter> range (X i))"
          proof -
            have "finite (range (X i))" using assms
              by (metis adapt_stoch_proc_def bernoulli bernoulli_stream_space
                  nat_filtration_vimage_finite natural_filtration streams_UNIV)
            thus ?thesis by auto
          qed
          moreover have "\<forall>y\<in> A\<inter> range (X i). (\<Union>z\<in> comp_proj_i X n i y.
            (stream_space_single (proj_stoch_proc X n) z)) \<in> sets (stream_space borel)"
          proof
            fix y
            assume "y\<in> A\<inter> range (X i)"
            have "finite (comp_proj_i X n i y)" by (simp add: assms comp_proj_i_finite)
            moreover have "\<forall>z\<in> comp_proj_i X n i y. (stream_space_single (proj_stoch_proc X n) z) \<in> sets (stream_space borel)"
            proof
              fix z
              assume "z\<in> comp_proj_i X n i y"
              thus "(stream_space_single (proj_stoch_proc X n) z) \<in> sets (stream_space borel)" using assms
                stream_space_single_set unfolding comp_proj_i_def by auto
            qed
            ultimately show "(\<Union>z\<in> comp_proj_i X n i y. (stream_space_single (proj_stoch_proc X n) z)) \<in>
              sets (stream_space borel)" by blast
          qed
          ultimately show ?thesis by blast
        qed
        ultimately show "X i -` A \<inter> space M \<in> {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}"
          by (metis (mono_tags, lifting) \<open>X i -` A \<inter> space M = X i -` A\<close> mem_Collect_eq)
      qed
      thus ?thesis by auto
    qed
  qed
  hence l: "sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel}) \<subseteq>
    sigma_sets (space M) {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}"
    by (rule sigma_sets_mono')
  have "{proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}
      \<subseteq> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})"
  proof -
    have "\<forall>B\<in> sets (stream_space borel). proj_stoch_proc X n -` B \<inter> space M \<in>
      sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel })"
    proof
      fix B::"'b stream set"
      assume "B\<in> sets (stream_space borel)"
      have "proj_stoch_proc X n -` B \<inter> space M = proj_stoch_proc X n -`B" using bernoulli bernoulli_stream_space by simp
      also have "... = proj_stoch_proc X n -` (B \<inter> range (proj_stoch_proc X n))" by auto
      also have "... = proj_stoch_proc X n -` (\<Union> y\<in> (B \<inter> range (proj_stoch_proc X n)). {y})" by simp
      also have "... = (\<Union> y\<in> (B \<inter> range (proj_stoch_proc X n)).  proj_stoch_proc X n -`{y})" by auto
      finally have eqB: "proj_stoch_proc X n -` B \<inter> space M =
        (\<Union> y\<in> (B \<inter> range (proj_stoch_proc X n)). proj_stoch_proc X n -`{y})" .
      have "\<forall>y\<in> (B \<inter> range (proj_stoch_proc X n)). proj_stoch_proc X n -`{y} \<in>
        sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel })"
      proof
        fix y
        assume "y \<in> B \<inter> range (proj_stoch_proc X n)"
        hence "\<exists>x. y = proj_stoch_proc X n x" by auto
        from this obtain x where "y = proj_stoch_proc X n x" by auto
        have "proj_stoch_proc X n -`{proj_stoch_proc X n x} \<in> sets (stoch_proc_filt M X borel n)"
          by (rule proj_stoch_pre_borel, simp add:assms)
        also have "... = sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel })"
        proof (rule stoch_proc_filt_sets)
          fix i
          assume "i\<le> n"
          show "random_variable borel (X i)" using assms borel_adapt_stoch_proc_borel_measurable by blast
        qed
        finally show "proj_stoch_proc X n -`{y} \<in>
          sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel })"
          using \<open>y = proj_stoch_proc X n x\<close> by simp
      qed
      hence "(\<Union> y\<in> (B \<inter> range (proj_stoch_proc X n)). proj_stoch_proc X n -`{y}) \<in>
        sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel })"
      proof (rule sigma_set_union_count)
        have "finite (range (proj_stoch_proc X n))"
          by (simp add: assms proj_stoch_set_finite_range)
        thus "countable (B \<inter> range (proj_stoch_proc X n))"
          by (simp add: countable_finite)
      qed
      thus "proj_stoch_proc X n -` B \<inter> space M \<in>
        sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})" using eqB by simp
    qed
    thus ?thesis by auto
  qed
  hence "sigma_sets (space M) {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}
    \<subseteq> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})" by (rule sigma_sets_mono)
  hence "sigma_sets (space M) {proj_stoch_proc X n -` B \<inter> space M |B. B \<in> sets (stream_space borel)}
    = sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel})" using l by simp
  thus ?thesis unfolding stoch_proc_filt_def fct_gen_subalgebra_def by simp
qed


lemma (in infinite_coin_toss_space) stoch_proc_subalg_nat_filt:
  assumes "borel_adapt_stoch_proc nat_filtration X"
  shows "subalgebra (nat_filtration n) (stoch_proc_filt M X borel n)" unfolding subalgebra_def
proof
  show "space (stoch_proc_filt M X borel n) = space (nat_filtration n)"
    by (simp add: fct_gen_subalgebra_space nat_filtration_def stoch_proc_filt_space)
  show "sets (stoch_proc_filt M X borel n) \<subseteq> sets (nat_filtration n)"
  proof -
    have "\<forall>i \<le> n. (\<forall> A\<in> sets borel. X i -`A \<inter> space M \<in> sets (nat_filtration n))"
    proof (intro allI impI)
      fix i
      assume "i \<le> n"
      have "X i \<in> borel_measurable (nat_filtration n)"
        by (metis \<open>i \<le> n\<close> adapt_stoch_proc_def assms filtrationE2 measurable_from_subalg nat_discrete_filtration)
      show "\<forall>A\<in>sets borel. X i -` A \<inter> space M \<in> sets (nat_filtration n)"
      proof
        fix A::"'a set"
        assume "A\<in> sets borel"
        thus "X i -` A \<inter> space M \<in> sets (nat_filtration n)" using \<open>X i \<in> borel_measurable (nat_filtration n)\<close>
          by (metis bernoulli bernoulli_stream_space measurable_sets nat_filtration_space streams_UNIV)
      qed
    qed
    hence "(\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel }) \<subseteq> sets (nat_filtration n)" by auto
    hence "sigma_sets (space M) (\<Union> i\<in> {m. m\<le> n}. {(X i -`A) \<inter> (space M) | A. A\<in> sets borel }) \<subseteq> sets (nat_filtration n)"
      by (metis (no_types, lifting) bernoulli bernoulli_stream_space nat_filtration_space sets.sigma_sets_subset streams_UNIV)
    thus ?thesis using assms stoch_proc_filt_sets unfolding adapt_stoch_proc_def
    proof -
    assume "\<forall>t. X t \<in> borel_measurable (nat_filtration t)"
      then have f1: "\<forall>n m. X n \<in> borel_measurable m \<or> \<not> subalgebra m (nat_filtration n)"
        by (meson measurable_from_subalg)
      have "\<forall>n. subalgebra M (nat_filtration n)"
        by (metis infinite_coin_toss_space.nat_filtration_subalgebra infinite_coin_toss_space_axioms)
      then show ?thesis
        using f1 \<open>\<And>n X N M. (\<And>i. i \<le> n \<Longrightarrow> X i \<in> M \<rightarrow>\<^sub>M N) \<Longrightarrow> sets (stoch_proc_filt M X N n) = sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets N})\<close> \<open>sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {X i -` A \<inter> space M |A. A \<in> sets borel}) \<subseteq> sets (nat_filtration n)\<close> by blast
    qed
  qed
qed




lemma (in infinite_coin_toss_space)
  assumes "N = bernoulli_stream q"
  and "0 \<le> q"
  and "q \<le> 1"
  and "0 < p"
  and "p < 1"
  and "filt_equiv nat_filtration M N"
  shows filt_equiv_sgt: "0 < q" and filt_equiv_slt: "q < 1"
proof -
  have "space M = space N" using assms filt_equiv_space by simp
  have eqs: "{w\<in> space M. (snth w 0)} = pseudo_proj_True (Suc 0) -`{True ##sconst True}"
  proof
    show "{w \<in> space M. w !! 0} \<subseteq> pseudo_proj_True (Suc 0) -` {True ##sconst True}"
    proof
      fix w
      assume "w \<in> {w \<in> space M. w !! 0}"
      hence "snth w 0" by simp
      hence "pseudo_proj_True (Suc 0) w = True##sconst True" by (simp add: pseudo_proj_True_def)
      thus "w \<in> pseudo_proj_True (Suc 0) -` {True##sconst True}" by simp
    qed
    show "pseudo_proj_True (Suc 0) -` {True##sconst True} \<subseteq> {w \<in> space M. w !! 0}"
    proof
      fix w
      assume "w \<in> pseudo_proj_True (Suc 0) -` {True##sconst True}"
      hence "pseudo_proj_True (Suc 0) w = True##sconst True" by simp
      hence "snth w 0"
        by (metis pseudo_proj_True_Suc_prefix stream_eq_Stream_iff)
      thus "w\<in> {w \<in> space M. w !! 0}" using bernoulli bernoulli_stream_space by simp
    qed
  qed
  hence natset: "{w\<in> space M. (snth w 0)} \<in> sets (nat_filtration (Suc 0))"
  proof -
    have "pseudo_proj_True (Suc 0) -` {True##sconst True} \<in> sets (nat_filtration (Suc 0))"
    proof (rule nat_filtration_singleton)
      show "pseudo_proj_True (Suc 0) (True##sconst True) = True## sconst True" unfolding pseudo_proj_True_def by simp
    qed
    thus ?thesis using eqs by simp
  qed
  have eqf: "{w\<in> space M. \<not>(snth w 0)} = pseudo_proj_True (Suc 0) -`{False ##sconst True}"
  proof
    show "{w \<in> space M. \<not>(snth w 0)} \<subseteq> pseudo_proj_True (Suc 0) -` {False ##sconst True}"
    proof
      fix w
      assume "w \<in> {w \<in> space M. \<not>(snth w 0)}"
      hence "\<not>(snth w 0)" by simp
      hence "pseudo_proj_True (Suc 0) w = False ##sconst True"
        by (simp add: pseudo_proj_True_def)
      thus "w \<in> pseudo_proj_True (Suc 0) -` {False ## sconst True}" by simp
    qed
    show "pseudo_proj_True (Suc 0) -` {False ## sconst True} \<subseteq> {w \<in> space M. \<not>(snth w 0)}"
    proof
      fix w
      assume "w \<in> pseudo_proj_True (Suc 0) -` {False##sconst True}"
      hence "pseudo_proj_True (Suc 0) w = False##sconst True" by simp
      hence "\<not>(snth w 0)"
        by (metis pseudo_proj_True_Suc_prefix  stream_eq_Stream_iff)
      thus "w\<in> {w \<in> space M. \<not>(snth w 0)}" using bernoulli bernoulli_stream_space by simp
    qed
  qed
  hence natsetf: "{w\<in> space M. \<not>(snth w 0)} \<in> sets (nat_filtration (Suc 0))"
  proof -
    have "pseudo_proj_True (Suc 0) -` {False##sconst True} \<in> sets (nat_filtration (Suc 0))"
    proof (rule nat_filtration_singleton)
      show "pseudo_proj_True (Suc 0) (False##sconst True) = False##sconst True" unfolding pseudo_proj_True_def by simp
    qed
    thus ?thesis using eqf by simp
  qed
  (*have "prob_space N" using assms
        by (simp add: bernoulli_stream_def prob_space.prob_space_stream_space
            prob_space_measure_pmf)*)
  show "0 < q"
  proof (rule ccontr)
    assume "\<not> 0 < q"
    hence "q = 0" using assms by simp
    hence "emeasure N {w\<in> space N. (snth w 0)} = q" using bernoulli_stream_component_probability[of N q]
        assms by blast
    hence "emeasure N {w\<in> space N. (snth w 0)} = 0" using \<open>q = 0\<close> by simp
    hence "emeasure M {w\<in> space M. (snth w 0)} = 0" using assms natset unfolding filt_equiv_def
      by (simp add: \<open>space M = space N\<close>)
    moreover have "emeasure M {w\<in> space M. (snth w 0)} = p" using bernoulli_stream_component_probability[of M p] bernoulli
        p_lt_1 p_gt_0 by blast
    ultimately show False using assms by simp
  qed
  show "q < 1"
  proof (rule ccontr)
    assume "\<not> q < 1"
    hence "q = 1" using assms by simp
    hence "emeasure N {w\<in> space N. \<not>(snth w 0)} = 1 -q" using bernoulli_stream_component_probability_compl[of N q]
        assms by blast
    hence "emeasure N {w\<in> space N. \<not>(snth w 0)} = 0" using \<open>q = 1\<close> by simp
    hence "emeasure M {w\<in> space M. \<not>(snth w 0)} = 0" using assms natsetf unfolding filt_equiv_def
      by (simp add: \<open>space M = space N\<close>)
    moreover have "emeasure M {w\<in> space M. \<not>(snth w 0)} = 1-p" using bernoulli_stream_component_probability_compl[of M p] bernoulli
        p_lt_1 p_gt_0 by blast
    ultimately show False using assms by simp
  qed
qed

lemma stoch_proc_filt_filt_equiv:
  assumes "filt_equiv F M N"
  shows "stoch_proc_filt M f P n = stoch_proc_filt N f P n" using assms filt_equiv_space filt_equiv_sets
  unfolding stoch_proc_filt_def
proof -
  have "space N = space M"
    by (metis assms filt_equiv_space)
  then show "gen_subalgebra M (sigma_sets (space M) (\<Union>n\<in>{na. na \<le> n}. {f n -` C \<inter> space M |C. C \<in> sets P})) =
    gen_subalgebra N (sigma_sets (space N) (\<Union>n\<in>{na. na \<le> n}. {f n -` C \<inter> space N |C. C \<in> sets P}))"
    by (simp add: gen_subalgebra_def)
qed

lemma  filt_equiv_filt:
  assumes "filt_equiv F M N"
and "filtration M G"
shows "filtration N G" unfolding filtration_def
proof (intro allI conjI impI)
  {
    fix t
    show "subalgebra N (G t)" using assms unfolding filtration_def filt_equiv_def
      by (metis sets_eq_imp_space_eq subalgebra_def)
  }
  {
    fix s::'c
    fix t
    assume "s \<le> t"
    thus "subalgebra (G t) (G s)" using assms unfolding filtration_def by simp
  }
qed


lemma  filt_equiv_borel_AE_eq_iff:
  fixes f::"'a\<Rightarrow> real"
  assumes "filt_equiv F M N"
and "f\<in> borel_measurable (F t)"
and "g\<in> borel_measurable (F t)"
and "prob_space N"
and "prob_space M"
shows "(AE w in M. f w = g w) \<longleftrightarrow> (AE w in N. f w = g w)"
proof -
  {
    assume fst: "AE w in M. f w = g w"
    have set0: "{w\<in> space M. f w \<noteq> g w} \<in> sets (F t) \<and> emeasure M {w\<in> space M. f w \<noteq> g w} = 0"
    proof (rule filtrated_prob_space.AE_borel_eq, (auto simp add: assms))
      show "filtrated_prob_space M F" using assms  unfolding filt_equiv_def
        by (simp add: filtrated_prob_space_axioms.intro filtrated_prob_space_def)
      show "AE w in M. f w =  g w" using fst .
    qed
    hence "emeasure N {w\<in> space M. f w \<noteq> g w} = 0" using assms unfolding filt_equiv_def by auto
    moreover have "{w\<in> space M. f w \<noteq> g w} \<in> sets N" using set0 assms unfolding filt_equiv_def
      filtration_def subalgebra_def by auto
    ultimately have "AE w in N. f w = g w"
    proof -
    have "space M = space N"
      by (metis assms(1) filt_equiv_space)
      then have "\<forall>p. almost_everywhere N p \<or> {a \<in> space N. \<not> p a} \<noteq> {a \<in> space N. f a \<noteq> g a}"
        using AE_iff_measurable \<open>emeasure N {w \<in> space M. f w \<noteq> g w} = 0\<close> \<open>{w \<in> space M. f w \<noteq> g w} \<in> sets N\<close>
        by auto
      then show ?thesis
        by metis
    qed
  } note a = this
  {
    assume scd: "AE w in N. f w = g w"
    have "space M = space N"
      by (metis assms(1) filt_equiv_space)
    have set0: "{w\<in> space N. f w \<noteq> g w} \<in> sets (F t) \<and> emeasure N {w\<in> space N. f w \<noteq> g w} = 0"
    proof (rule filtrated_prob_space.AE_borel_eq, (auto simp add: assms))
      show "filtrated_prob_space N F" using assms unfolding filt_equiv_def
        by (metis \<open>prob_space N\<close> assms(1) filt_equiv_filtration filtrated_prob_space_axioms.intro filtrated_prob_space_def)
      show "AE w in N. f w = g w" using scd .
    qed
    hence "emeasure M {w\<in> space M. f w \<noteq> g w} = 0" using assms unfolding filt_equiv_def
      by (metis (full_types) assms(1) filt_equiv_space)
    moreover have "{w\<in> space M. f w \<noteq> g w} \<in> sets M" using set0 assms unfolding filt_equiv_def
      filtration_def subalgebra_def
      by (metis (mono_tags) \<open>space M = space N\<close> contra_subsetD)
    ultimately have "AE w in M. f w=  g w"
    proof -
       have "\<forall>p. almost_everywhere M p \<or> {a \<in> space M. \<not> p a} \<noteq> {a \<in> space M. f a \<noteq> g a}"
        using AE_iff_measurable \<open>emeasure M {w \<in> space M. f w \<noteq> g w} = 0\<close> \<open>{w \<in> space M. f w \<noteq> g w} \<in> sets M\<close>
        by auto
      then show ?thesis
        by metis
    qed
  }
  thus ?thesis using a by auto
qed

lemma (in infinite_coin_toss_space) filt_equiv_triv_init:
  assumes "filt_equiv F M N"
and "init_triv_filt M G"
shows "init_triv_filt N G" unfolding init_triv_filt_def
proof
  show "filtration N G" using assms filt_equiv_filt[of F M N G] unfolding init_triv_filt_def by simp
  show "sets (G \<bottom>) = {{}, space N}" using assms filt_equiv_space[of F M N] unfolding init_triv_filt_def by simp
qed



lemma (in infinite_coin_toss_space) fct_gen_subalgebra_meas_info:
  assumes "\<forall>w. f (g w) = f w"
  and "f \<in> space M \<rightarrow> space N"
and "g \<in> space M \<rightarrow> space M"
  shows "g \<in> measurable (fct_gen_subalgebra M N f) (fct_gen_subalgebra M N f)" unfolding measurable_def
proof (intro CollectI conjI)
  show "g \<in> space (fct_gen_subalgebra M N f) \<rightarrow> space (fct_gen_subalgebra M N f)" using assms
    by (simp add: fct_gen_subalgebra_space)
  show "\<forall>y\<in>sets (fct_gen_subalgebra M N f). g -` y \<inter> space (fct_gen_subalgebra M N f) \<in> sets (fct_gen_subalgebra M N f)"
  proof
    fix B
    assume "B\<in> sets (fct_gen_subalgebra M N f)"
    hence "B \<in> {f -` B \<inter> space M |B. B \<in> sets N}" using assms by (simp add:fct_gen_subalgebra_sigma_sets)
    from this obtain C where "C\<in> sets N" and "B = f -`C \<inter> space M" by auto note Cprops = this
    have "g -` B \<inter> space (fct_gen_subalgebra M N f) = g -` B \<inter> space M" using assms
      by (simp add: fct_gen_subalgebra_space)
    also have "... = g -` (f -` C \<inter> space M) \<inter> space M" using Cprops by simp
    also have "... = g -` (f -` C)" using bernoulli bernoulli_stream_space by simp
    also have "... = (f\<circ> g) -` C" by auto
    also have "... = f -` C"
    proof
      show "(f \<circ> g) -` C \<subseteq> f -` C"
      proof
        fix w
        assume "w \<in> (f \<circ> g) -` C"
        hence "f (g w) \<in> C" by simp
        hence "f w \<in> C" using assms by simp
        thus "w\<in> f -`C" by simp
      qed
      show "f -` C \<subseteq> (f \<circ> g) -` C"
      proof
        fix w
        assume "w\<in> f -`C"
        hence "f w \<in> C" by simp
        hence "f (g w) \<in> C" using assms by simp
        thus "w\<in> (f \<circ> g) -` C" by simp
      qed
    qed
    also have "... \<in> sets (fct_gen_subalgebra M N f)"
      using Cprops(2) \<open>B \<in> sets (fct_gen_subalgebra M N f)\<close> bernoulli bernoulli_stream_space
        inf_top.right_neutral by auto
    finally show "g -` B \<inter> space (fct_gen_subalgebra M N f) \<in> sets (fct_gen_subalgebra M N f)" .
  qed
qed



end