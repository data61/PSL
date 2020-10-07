(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Discrete-Time Markov Chain\<close>

theory Discrete_Time_Markov_Chain
  imports Markov_Models_Auxiliary
begin

text \<open>

Markov chain with discrete time steps and discrete state space.

\<close>

lemma sstart_eq': "sstart \<Omega> (x # xs) = {\<omega>. shd \<omega> = x \<and> stl \<omega> \<in> sstart \<Omega> xs}"
  by (auto simp: sstart_eq)

lemma measure_eq_stream_space_coinduct[consumes 1, case_names left right cont]:
  assumes "R N M"
  assumes R_1: "\<And>N M. R N M \<Longrightarrow> N \<in> space (prob_algebra (stream_space (count_space UNIV)))"
    and R_2: "\<And>N M. R N M \<Longrightarrow> M \<in> space (prob_algebra (stream_space (count_space UNIV)))"
    and cont: "\<And>N M. R N M \<Longrightarrow> \<exists>N' M' p. (\<forall>y\<in>set_pmf p. R (N' y) (M' y)) \<and>
      (\<forall>x. N' x \<in> space (prob_algebra (stream_space (count_space UNIV)))) \<and> (\<forall>x. M' x \<in> space (prob_algebra (stream_space (count_space UNIV)))) \<and> 
      N = (measure_pmf p \<bind> (\<lambda>y. distr (N' y) (stream_space (count_space UNIV)) ((##) y))) \<and>
      M = (measure_pmf p \<bind> (\<lambda>y. distr (M' y) (stream_space (count_space UNIV)) ((##) y)))"
  shows "N = M"
proof -
  let ?S = "stream_space (count_space UNIV)"
  have "\<forall>N M. R N M \<longrightarrow> (\<exists>N' M' p. (\<forall>y\<in>set_pmf p. R (N' y) (M' y)) \<and>
      (\<forall>x. N' x \<in> space (prob_algebra ?S)) \<and> (\<forall>x. M' x \<in> space (prob_algebra ?S)) \<and>
      N = (measure_pmf p \<bind> (\<lambda>y. distr (N' y) ?S ((##) y))) \<and>
      M = (measure_pmf p \<bind> (\<lambda>y. distr (M' y) ?S ((##) y))))"
    using cont by auto
  then obtain n m p where
    p: "\<And>N M y. R N M \<Longrightarrow> y \<in> set_pmf (p N M) \<Longrightarrow> R (n N M y) (m N M y)" and
    n: "\<And>N M x. R N M \<Longrightarrow> n N M x \<in> space (prob_algebra ?S)" and
    n_eq: "\<And>N M y. R N M \<Longrightarrow> N = (measure_pmf (p N M) \<bind> (\<lambda>y. distr (n N M y) ?S ((##) y)))" and
    m: "\<And>N M x. R N M \<Longrightarrow> m N M x \<in> space (prob_algebra ?S)" and
    m_eq: "\<And>N M y. R N M \<Longrightarrow> M = (measure_pmf (p N M) \<bind> (\<lambda>y. distr (m N M y) ?S ((##) y)))"
    unfolding choice_iff' choice_iff by blast

  define A where "A = (SIGMA nm:UNIV. (\<lambda>x. (n (fst nm) (snd nm) x, m (fst nm) (snd nm) x)) ` p (fst nm) (snd nm))"
  have A_singleton: "A `` {nm} = (\<lambda>x. (n (fst nm) (snd nm) x, m (fst nm) (snd nm) x)) ` p (fst nm) (snd nm)" for nm
    by (auto simp: A_def)

  have sets_n[measurable_cong, simp]: "sets (n N M y) = sets ?S" if "R N M" for N M y
    using n[OF that, of y] by (auto simp: space_prob_algebra)
  have sets_m[measurable_cong, simp]: "sets (m N M y) = sets ?S" if "R N M" for N M y
    using m[OF that, of y] by (auto simp: space_prob_algebra)
  have [simp]: "R N M \<Longrightarrow> prob_space (n N M y)" for N M y
    using n[of N M y] by (auto simp: space_prob_algebra)
  have [simp]: "R N M \<Longrightarrow> prob_space (m N M y)" for N M y
    using m[of N M y] by (auto simp: space_prob_algebra)
  have [measurable]: "R N M \<Longrightarrow> n N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    by (rule measurable_prob_algebraD) (auto intro: n)
  have [measurable]: "R N M \<Longrightarrow> m N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    by (rule measurable_prob_algebraD) (auto intro: m)

  define n' where "n' N M y = distr (n N M y) ?S ((##) y)" for N M y
  define m' where "m' N M y = distr (m N M y) ?S ((##) y)" for N M y
  have n'_eq: "R N M \<Longrightarrow> N = (measure_pmf (p N M) \<bind> n' N M)" for N M unfolding n'_def by (rule n_eq)
  have m'_eq: "R N M \<Longrightarrow> M = (measure_pmf (p N M) \<bind> m' N M)" for N M unfolding m'_def by (rule m_eq)
  have [measurable]: "R N M \<Longrightarrow> n' N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    unfolding n'_def by (rule measurable_distr2[where M="?S"]) measurable
  have [measurable]: "R N M \<Longrightarrow> m' N M \<in> count_space UNIV \<rightarrow>\<^sub>M subprob_algebra ?S" for N M
    unfolding m'_def by (rule measurable_distr2[where M="?S"]) measurable

  have n'_shd: "R N M \<Longrightarrow> distr (n' N M y) (count_space UNIV) shd = measure_pmf (return_pmf y)" for N M y
    unfolding n'_def by (subst distr_distr) (auto simp: comp_def prob_space.distr_const return_pmf.rep_eq)
  have m'_shd: "R N M \<Longrightarrow> distr (m' N M y) (count_space UNIV) shd = measure_pmf (return_pmf y)" for N M y
    unfolding m'_def by (subst distr_distr) (auto simp: comp_def prob_space.distr_const return_pmf.rep_eq)
  have n'_stl: "R N M \<Longrightarrow> distr (n' N M y) ?S stl = n N M y" for N M y
    unfolding n'_def by (subst distr_distr) (auto simp: comp_def distr_id2)
  have m'_stl: "R N M \<Longrightarrow> distr (m' N M y) ?S stl = m N M y" for N M y
    unfolding m'_def by (subst distr_distr) (auto simp: comp_def distr_id2)

  define F where "F = (A\<^sup>* `` {(N, M)})"
  have "countable F"
    unfolding F_def
    apply (intro countable_rtrancl countable_insert[of _ "(N, M)"] countable_empty)
    apply (rule countable_Image)
     apply (auto simp: A_singleton)
    done
  have F_NM[simp]: "(N, M) \<in> F" unfolding F_def by auto
  have R_F[simp]: "R N' M'" if "(N', M') \<in> F" for N' M'
  proof -
    have "((N, M), (N', M')) \<in> A\<^sup>*" using that by (auto simp: F_def)
    then show "R N' M'"
      by (induction p=="(N', M')" arbitrary: N' M' rule: rtrancl_induct) (auto simp: \<open>R N M\<close> A_def p)
  qed
  have nm_F: "(n N' M' y, m N' M' y) \<in> F" if "y \<in> p N' M'" "(N', M') \<in> F" for N' M' y
  proof -
    have *: "((N, M), (N', M')) \<in> A\<^sup>*" using that by (auto simp: F_def)
    with that show ?thesis
      apply (simp add: F_def)
      apply (intro rtrancl.rtrancl_into_rtrancl[OF *])
      apply (auto simp: A_def)
      done
  qed

  define \<Omega> where "\<Omega> = (\<Union>(n, m)\<in>F. set_pmf (p n m))"
  have [measurable]: "\<Omega> \<in> sets (count_space UNIV)" by auto
  have in_\<Omega>: "(N, M) \<in> F \<Longrightarrow> y \<in> p N M \<Longrightarrow> y \<in> \<Omega>" for N M y
    by (auto simp: \<Omega>_def Bex_def)

  show ?thesis
  proof (intro stream_space_eq_sstart)
    from \<open>countable F\<close> show "countable \<Omega>"
      by (auto simp add: \<Omega>_def)
    show "prob_space N" "prob_space M" "sets N = sets ?S" "sets M = sets ?S"
      using R_1[OF \<open>R N M\<close>] R_2[OF \<open>R N M\<close>] by (auto simp add: space_prob_algebra)
    have "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in N. x !! i \<in> \<Omega>" for i
    proof (induction i)
      case 0 note NM = 0[THEN R_F, simp] show ?case
        apply (subst n'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=shd and M'="count_space UNIV"]
                    simp: AE_measure_pmf_iff n[OF NM] n'_shd in_\<Omega>[OF 0] cong: AE_cong_simp)
        done
    next
      case (Suc i) note NM = Suc(2)[THEN R_F, simp]
      show ?case
        apply (subst n'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=stl and M'="?S"] Suc(1)[OF nm_F] Suc(2)
          simp: AE_measure_pmf_iff n'_stl cong: AE_cong_simp)
        done
    qed
    then have AE_N: "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in N. x \<in> streams \<Omega>"
      unfolding streams_iff_snth AE_all_countable by auto
    then show "AE x in N. x \<in> streams \<Omega>" by (blast intro: F_NM)

    have "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in M. x !! i \<in> \<Omega>" for i
    proof (induction i arbitrary: N M)
      case 0 note NM = 0[THEN R_F, simp] show ?case
        apply (subst m'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=shd and M'="count_space UNIV"]
                    simp: AE_measure_pmf_iff m[OF NM] m'_shd in_\<Omega>[OF 0] cong: AE_cong_simp)
        done
    next
      case (Suc i) note NM = Suc(2)[THEN R_F, simp]
      show ?case
        apply (subst m'_eq[OF NM])
        apply (subst AE_bind[where B="?S"])
          apply measurable
        apply (auto intro!: AE_distrD[where f=stl and M'="?S"] Suc(1)[OF nm_F] Suc(2)
          simp: AE_measure_pmf_iff m'_stl cong: AE_cong_simp)
        done
    qed
    then have AE_M: "\<And>N M. (N, M) \<in> F \<Longrightarrow> AE x in M. x \<in> streams \<Omega>"
      unfolding streams_iff_snth AE_all_countable by auto
    then show "AE x in M. x \<in> streams \<Omega>" by (blast intro: F_NM)

    fix xs assume "xs \<in> lists \<Omega>"
    with \<open>(N, M) \<in> F\<close> show "emeasure N (sstart \<Omega> xs) = emeasure M (sstart \<Omega> xs)"
    proof (induction xs arbitrary: N M)
      case Nil
      have "prob_space N" "prob_space M" "sets N = sets ?S" "sets M = sets ?S"
        using R_1[OF R_F[OF Nil(1)]] R_2[OF R_F[OF Nil(1)]] by (auto simp add: space_prob_algebra)
      have "emeasure N (streams \<Omega>) = 1"
        by (rule prob_space.emeasure_eq_1_AE[OF \<open>prob_space N\<close> _ AE_N[OF Nil(1)]])
           (auto simp add: \<open>sets N = sets ?S\<close> intro!: streams_sets)
      moreover have "emeasure M (streams \<Omega>) = 1"
        by (rule prob_space.emeasure_eq_1_AE[OF \<open>prob_space M\<close> _ AE_M[OF Nil(1)]])
           (auto simp add: \<open>sets M = sets ?S\<close> intro!: streams_sets)
      ultimately show ?case by simp
    next
      case (Cons x xs)
      note NM = Cons(2)[THEN R_F, simp]
      have *: "(##) y -` sstart \<Omega> (x # xs) = (if x = y then sstart \<Omega> xs else {})" for y
        by auto
      show ?case
        apply (subst n'_eq[OF NM])
        apply (subst (3) m'_eq[OF NM])
        apply (subst emeasure_bind[OF _ _ sstart_sets])
          apply simp []
         apply measurable []
        apply (subst emeasure_bind[OF _ _ sstart_sets])
          apply simp []
         apply measurable []
        apply (intro nn_integral_cong_AE AE_pmfI)
        apply (subst n'_def)
        apply (subst m'_def)
        using Cons(3)
        apply (auto intro!: Cons nm_F
          simp add: emeasure_distr sets_eq_imp_space_eq[OF sets_n] sets_eq_imp_space_eq[OF sets_m]
                    space_stream_space *)
        done
    qed
  qed
qed

subsection \<open>Discrete Markov Kernel\<close>

locale MC_syntax =
  fixes K :: "'s \<Rightarrow> 's pmf"
begin

abbreviation acc :: "('s \<times> 's) set" where
  "acc \<equiv> (SIGMA s:UNIV. K s)\<^sup>*"

abbreviation acc_on :: "'s set \<Rightarrow> ('s \<times> 's) set" where
  "acc_on S \<equiv> (SIGMA s:UNIV. K s \<inter> S)\<^sup>*"

lemma countable_reachable: "countable (acc `` {s})"
  by (auto intro!: countable_rtrancl countable_set_pmf simp: Sigma_Image)

lemma countable_acc: "countable X \<Longrightarrow> countable (acc `` X)"
  apply (rule countable_Image)
  apply (rule countable_reachable)
  apply assumption
  done

context
  notes [[inductive_internals]]
begin

coinductive enabled where
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> shd \<omega> \<in> K s \<Longrightarrow> enabled s \<omega>"

end

lemma alw_enabled: "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> alw (\<lambda>\<omega>. enabled (shd \<omega>) (stl \<omega>)) \<omega>"
  by (coinduction arbitrary: \<omega> rule: alw_coinduct) (auto elim: enabled.cases)

abbreviation "S \<equiv> stream_space (count_space UNIV)"

lemma in_S [measurable (raw)]: "x \<in> space S"
  by (simp add: space_stream_space)

inductive_simps enabled_iff: "enabled s \<omega>"

lemma enabled_Stream: "enabled x (y ## \<omega>) \<longleftrightarrow> y \<in> K x \<and> enabled y \<omega>"
  by (subst enabled_iff)  auto

lemma measurable_enabled[measurable]:
  "Measurable.pred (stream_space (count_space UNIV)) (enabled s)" (is "Measurable.pred ?S _")
  unfolding enabled_def
proof (coinduction arbitrary: s rule: measurable_gfp2_coinduct)
  case (step A s)
  then have [measurable]: "\<And>t. Measurable.pred ?S (A t)" by auto
  have *: "\<And>x. (\<exists>\<omega> t. s = t \<and> x = \<omega> \<and> A (shd \<omega>) (stl \<omega>) \<and> shd \<omega> \<in> set_pmf (K t)) \<longleftrightarrow>
    (\<exists>t\<in>K s. A t (stl x) \<and> t = shd x)"
    by auto
  note countable_set_pmf[simp]
  show ?case
    unfolding * by measurable
qed (auto simp: inf_continuous_def)

lemma enabled_iff_snth: "enabled s \<omega> \<longleftrightarrow> (\<forall>i. \<omega> !! i \<in> K ((s ## \<omega>) !! i))"
proof safe
  fix i assume "enabled s \<omega>" then show "\<omega> !! i \<in> K ((s ## \<omega>) !! i)"
    by (induct i arbitrary: s \<omega>)
       (force elim: enabled.cases)+
next
  assume "\<forall>i. \<omega> !! i \<in> set_pmf (K ((s ## \<omega>) !! i))" then show "enabled s \<omega>"
    by (coinduction arbitrary: s \<omega>)
       (auto elim: allE[of _ "Suc i" for i] allE[of _ 0])
qed

primcorec force_enabled where
  "force_enabled x \<omega> =
    (let y = if shd \<omega> \<in> K x then shd \<omega> else (SOME y. y \<in> K x) in y ## force_enabled y (stl \<omega>))"

lemma force_enabled_in_set_pmf[simp, intro]: "shd (force_enabled x \<omega>) \<in> K x"
  by (auto simp: some_in_eq set_pmf_not_empty)

lemma enabled_force_enabled: "enabled x (force_enabled x \<omega>)"
  by (coinduction arbitrary: x \<omega>) (auto simp: some_in_eq set_pmf_not_empty)

lemma force_enabled: "enabled x \<omega> \<Longrightarrow> force_enabled x \<omega> = \<omega>"
  by (coinduction arbitrary: x \<omega>) (auto elim: enabled.cases)

lemma Ex_enabled: "\<exists>\<omega>. enabled x \<omega>"
  by (rule exI[of _ "force_enabled x undefined"] enabled_force_enabled)+

lemma measurable_force_enabled: "force_enabled x \<in> measurable S S"
proof (rule measurable_stream_space2)
  fix n show "(\<lambda>\<omega>. force_enabled x \<omega> !! n) \<in> measurable S (count_space UNIV)"
  proof (induction n arbitrary: x)
    case (Suc n) show ?case
      apply simp
      apply (rule measurable_compose_countable'[OF measurable_compose[OF measurable_stl Suc], where I="set_pmf (K x)"])
      apply (rule measurable_compose[OF measurable_shd])
      apply (auto simp: countable_set_pmf some_in_eq set_pmf_not_empty)
      done
  qed (auto intro!: measurable_compose[OF measurable_shd])
qed

abbreviation "D \<equiv> stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"

lemma sets_D: "sets D = sets (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (intro sets_stream_space_cong sets_PiM_cong) simp_all

lemma space_D: "space D = space (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  using sets_eq_imp_space_eq[OF sets_D] .

lemma measurable_D_D: "measurable D D =
    measurable (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV)) (stream_space (\<Pi>\<^sub>M s\<in>UNIV. count_space UNIV))"
  by (simp add: measurable_def space_D sets_D)

primcorec walk :: "'s \<Rightarrow> ('s \<Rightarrow> 's) stream \<Rightarrow> 's stream" where
  "shd (walk s \<omega>) = (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s))"
| "stl (walk s \<omega>) = walk (if shd \<omega> s \<in> K s then shd \<omega> s else (SOME t. t \<in> K s)) (stl \<omega>)"

lemma enabled_walk: "enabled s (walk s \<omega>)"
  by (coinduction arbitrary: s \<omega>) (auto simp: some_in_eq set_pmf_not_empty)

lemma measurable_walk[measurable]: "walk s \<in> measurable D S"
proof -
  note measurable_compose[OF measurable_snth, intro!]
  note measurable_compose[OF measurable_component_singleton, intro!]
  note if_weak_cong[cong del]
  note measurable_g = measurable_compose_countable'[OF _ _ countable_reachable]

  define n :: nat where "n = 0"
  define g where "g = (\<lambda>_::('s \<Rightarrow> 's) stream. s)"
  then have "g \<in> measurable D (count_space (acc `` {s}))"
    by auto
  then have "(\<lambda>x. walk (g x) (sdrop n x)) \<in> measurable D S"
  proof (coinduction arbitrary: g n rule: measurable_stream_coinduct)
    case (shd g) show ?case
      by (fastforce intro: measurable_g[OF _ shd])
  next
    case (stl g) show ?case
      by (fastforce simp add: sdrop.simps[symmetric] some_in_eq set_pmf_not_empty
                    simp del: sdrop.simps intro: rtrancl_into_rtrancl measurable_g[OF _ stl])
  qed
  then show ?thesis
    by (simp add: g_def n_def)
qed

subsection \<open>Trace Space for Discrete-Time Markov Chains\<close>

definition T :: "'s \<Rightarrow> 's stream measure" where
  "T s = distr (stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)) S (walk s)"

lemma space_T[simp]: "space (T s) = space S"
  by (simp add: T_def)

lemma sets_T[simp, measurable_cong]: "sets (T s) = sets S"
  by (simp add: T_def)

lemma measurable_T1[simp]: "measurable (T s) M = measurable S M"
  by (intro measurable_cong_sets) simp_all

lemma measurable_T2[simp]: "measurable M (T s) = measurable M S"
  by (intro measurable_cong_sets) simp_all

lemma in_measurable_T1[measurable (raw)]: "f \<in> measurable S M \<Longrightarrow> f \<in> measurable (T s) M"
  by simp

lemma in_measurable_T2[measurable (raw)]: "f \<in> measurable M S \<Longrightarrow> f \<in> measurable M (T s)"
  by simp

lemma AE_T_enabled: "AE \<omega> in T s. enabled s \<omega>"
  unfolding T_def by (simp add: AE_distr_iff enabled_walk)

sublocale T: prob_space "T s" for s
proof -
  interpret P: product_prob_space K UNIV ..
  interpret prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule P.prob_space_stream_space)
  fix s show "prob_space (T s)"
    by (simp add: T_def prob_space_distr)
qed

lemma emeasure_T_const[simp]: "emeasure (T s) (space S) = 1"
  using T.emeasure_space_1[of s] by simp

lemma nn_integral_T:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+t. (\<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t) \<partial>K s)"
proof -
  interpret product_prob_space K UNIV ..
  interpret D: prob_space "stream_space (\<Pi>\<^sub>M s\<in>UNIV. K s)"
    by (rule prob_space_stream_space)

  have T: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (simp add: T_def nn_integral_distr)

  have "(\<integral>\<^sup>+X. f X \<partial>T s) = (\<integral>\<^sup>+\<omega>. f (walk s \<omega>) \<partial>D)"
    by (rule T) measurable
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (walk s (d ## \<omega>)) \<partial>D \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (simp add: P.nn_integral_stream_space)
  also have "\<dots> = (\<integral>\<^sup>+d. (\<integral>\<^sup>+\<omega>. f (d s ## walk (d s) \<omega>) * indicator {t. t \<in> K s} (d s) \<partial>D) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    apply (rule nn_integral_cong_AE)
    apply (subst walk.ctr)
    apply (simp cong del: if_weak_cong)
    apply (intro UNIV_I AE_component)
    apply (auto simp: AE_measure_pmf_iff)
    done
  also have "\<dots> = (\<integral>\<^sup>+d. \<integral>\<^sup>+\<omega>. f (d s ## \<omega>) * indicator (K s) (d s) \<partial>T (d s) \<partial>\<Pi>\<^sub>M i\<in>UNIV. K i)"
    by (subst T) (simp_all split: split_indicator)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) * indicator (K s) t \<partial>T t \<partial>K s)"
    by (subst (2) PiM_component[symmetric]) (simp_all add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+t. \<integral>\<^sup>+\<omega>. f (t ## \<omega>) \<partial>T t \<partial>K s)"
    by (rule nn_integral_cong_AE) (simp add: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma nn_integral_T_gfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes [measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g[THEN inf_continuous_compose, order_continuous_intros]: "\<And>s. inf_continuous (g s)"
  assumes int_g: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+\<omega>. g s (f \<omega>) \<partial>T s) = g s (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s)"
  assumes bnd_g: "\<And>f s. g s f \<le> b" "0 \<le> b" "b < \<infinity>"
  shows "(\<integral>\<^sup>+\<omega>. gfp l \<omega> \<partial>T s) = gfp (\<lambda>f s. \<integral>\<^sup>+t. g t (f t) \<partial>K s) s"
proof (rule nn_integral_gfp)
  show "\<And>s. sets (T s) = sets S" "\<And>F. F \<in> borel_measurable S \<Longrightarrow> l F \<in> borel_measurable S"
    by (auto simp: l_def)
  show "\<And>s. emeasure (T s) (space (T s)) \<noteq> 0"
   by (rewrite T.emeasure_space_1) simp
  { fix s F
    have "integral\<^sup>N (T s) (l F) \<le> (\<integral>\<^sup>+x. b \<partial>T s)"
      by (intro nn_integral_mono) (simp add: l_def bnd_g)
    also have "\<dots> < \<infinity>"
      using bnd_g by simp
    finally show "integral\<^sup>N (T s) (l F) < \<infinity>" . }
  show "inf_continuous (\<lambda>f s. \<integral>\<^sup>+ t. g t (f t) \<partial>K s)"
  proof (intro order_continuous_intros)
    fix f s
    have "(\<integral>\<^sup>+ t. g t (f t) \<partial>K s) \<le> (\<integral>\<^sup>+ t. b \<partial>K s)"
      by (intro nn_integral_mono bnd_g)
    also have "\<dots> < \<infinity>"
      using bnd_g by simp
    finally show "(\<integral>\<^sup>+ t. g t (f t) \<partial>K s) \<noteq> \<infinity>"
      by simp
  qed simp
next
  fix s and F :: "'s stream \<Rightarrow> ennreal" assume "F \<in> borel_measurable S"
  then show "integral\<^sup>N (T s) (l F) = (\<integral>\<^sup>+ t. g t (integral\<^sup>N (T t) F) \<partial>K s) "
    by (rewrite nn_integral_T) (simp_all add: l_def int_g)
qed (auto intro!: order_continuous_intros simp: l_def)

lemma nn_integral_T_lfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes [measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g[THEN sup_continuous_compose, order_continuous_intros]: "\<And>s. sup_continuous (g s)"
  assumes int_g: "\<And>f s. f \<in> borel_measurable S \<Longrightarrow> (\<integral>\<^sup>+\<omega>. g s (f \<omega>) \<partial>T s) = g s (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s)"
  shows "(\<integral>\<^sup>+\<omega>. lfp l \<omega> \<partial>T s) = lfp (\<lambda>f s. \<integral>\<^sup>+t. g t (f t) \<partial>K s) s"
proof (rule nn_integral_lfp)
  show "\<And>s. sets (T s) = sets S" "\<And>F. F \<in> borel_measurable S \<Longrightarrow> l F \<in> borel_measurable S"
    by (auto simp: l_def)
next
  fix s and F :: "'s stream \<Rightarrow> ennreal" assume "F \<in> borel_measurable S"
  then show "integral\<^sup>N (T s) (l F) = (\<integral>\<^sup>+ t. g t (integral\<^sup>N (T t) F) \<partial>K s) "
    by (rewrite nn_integral_T) (simp_all add: l_def int_g)
qed (auto simp: l_def intro!: order_continuous_intros)

lemma emeasure_Collect_T:
  assumes f[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). P x} = (\<integral>\<^sup>+t. emeasure (T t) {x\<in>space (T t). P (t ## x)} \<partial>K s)"
  apply (subst (1 2) nn_integral_indicator[symmetric])
  apply simp
  apply simp
  apply (subst nn_integral_T)
  apply (auto intro!: nn_integral_cong simp add: space_stream_space indicator_def)
  done

lemma AE_T_iff:
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (\<forall>y\<in>K x. AE \<omega> in T y. P (y ## \<omega>))"
  by (simp add: AE_iff_nn_integral nn_integral_T[where s=x])
     (auto simp add: nn_integral_0_iff_AE AE_measure_pmf_iff split: split_indicator)

lemma AE_T_alw:
  assumes [measurable]: "Measurable.pred S P"
  assumes P: "\<And>s. (x, s) \<in> acc \<Longrightarrow> AE \<omega> in T s. P \<omega>"
  shows "AE \<omega> in T x. alw P \<omega>"
proof -
  define F where "F = (\<lambda>p x. P x \<and> p (stl x))"
  have [measurable]: "\<And>p. Measurable.pred S p \<Longrightarrow> Measurable.pred S (F p)"
    by (auto simp: F_def)
  have "almost_everywhere (T s) ((F ^^ i) top)"
    if "(x, s) \<in> acc" for i s
    using that
  proof (induction i arbitrary: s)
    case (Suc i) then show ?case
      apply simp
      apply (subst F_def)
      apply (simp add: P)
      apply (subst AE_T_iff)
      apply (measurable; simp)
      apply (auto dest: rtrancl_into_rtrancl)
      done
  qed simp
  then have "almost_everywhere (T x) (gfp F)"
    by (subst inf_continuous_gfp) (auto simp: inf_continuous_def AE_all_countable F_def)
  then show ?thesis
    by (simp add: alw_def F_def)
qed

lemma emeasure_suntil_disj:
  assumes [measurable]: "Measurable.pred S P"
  assumes *: "\<And>t. AE \<omega> in T t. \<not> (P \<sqinter> (HLD X \<sqinter> nxt (HLD X suntil P))) \<omega>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (HLD X suntil P) \<omega>} =
    lfp (\<lambda>F s. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} + (\<integral>\<^sup>+t. F t * indicator X t \<partial>K s)) s"
  unfolding suntil_lfp
proof (rule emeasure_lfp[where s=s])
  fix F t assume [measurable]: "Measurable.pred (T s) F" and
    F: "F \<le> lfp (\<lambda>a b. P b \<or> HLD X b \<and> a (stl b))"
  have "emeasure (T t) {\<omega> \<in> space (T s). P \<omega> \<or> HLD X \<omega> \<and> F (stl \<omega>)} =
    emeasure (T t) {\<omega> \<in> space (T t). P \<omega>} + emeasure (T t) {\<omega>\<in>space (T t). HLD X \<omega> \<and> F (stl \<omega>)}"
  proof (rule emeasure_add_AE)
    show "AE x in T t. \<not> (x \<in> {\<omega> \<in> space (T t). P \<omega>} \<and> x \<in> {\<omega> \<in> space (T t). HLD X \<omega> \<and> F (stl \<omega>)})"
      using * by eventually_elim (insert F, auto simp: suntil_lfp[symmetric])
  qed auto
  also have "emeasure (T t) {\<omega>\<in>space (T t). HLD X \<omega> \<and> F (stl \<omega>)} =
    (\<integral>\<^sup>+t. emeasure (T t) {\<omega> \<in> space (T s). F \<omega>} * indicator X t \<partial>K t)"
    by (subst emeasure_Collect_T) (auto intro!: nn_integral_cong split: split_indicator)
  finally show "emeasure (T t) {\<omega> \<in> space (T s). P \<omega> \<or> HLD X \<omega> \<and> F (stl \<omega>)} =
    emeasure (T t) {\<omega> \<in> space (T t). P \<omega>} + (\<integral>\<^sup>+ t. emeasure (T t) {\<omega> \<in> space (T s). F \<omega>} * indicator X t \<partial>K t)" .
qed (auto intro!: order_continuous_intros split: split_indicator)

lemma emeasure_HLD_nxt:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (X \<cdot> P) \<omega>} =
    (\<integral>\<^sup>+x. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>} * indicator X x \<partial>K s)"
  by (subst emeasure_Collect_T)
     (auto intro!: nn_integral_cong_AE simp: AE_measure_pmf_iff split: split_indicator)

lemma emeasure_HLD:
  "emeasure (T s) {\<omega>\<in>space (T s). HLD X \<omega>} = emeasure (K s) X"
  using emeasure_HLD_nxt[of "\<lambda>\<omega>. True" s X] T.emeasure_space_1 by simp

lemma emeasure_suntil_HLD:
  assumes [measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {x\<in>space (T s). (not (HLD {t}) suntil (HLD {t} aand nxt P)) x} =
   emeasure (T s) {x\<in>space (T s). ev (HLD {t}) x} * emeasure (T t) {x\<in>space (T t). P x}"
proof -
  let ?P = "emeasure (T t) {\<omega>\<in>space (T t). P \<omega>}"
  let ?F = "\<lambda>Q F s. emeasure (T s) {\<omega>\<in>space (T s). Q \<omega>} + (\<integral>\<^sup>+t'. F t' * indicator (- {t}) t' \<partial>K s)"
  have "emeasure (T s) {x\<in>space (T s). (HLD (-{t}) suntil ({t} \<cdot> P)) x} = lfp (?F ({t} \<cdot> P)) s"
    by (rule emeasure_suntil_disj) (auto simp: HLD_iff)
  also have "lfp (?F ({t} \<cdot> P)) = (\<lambda>s. lfp (?F (HLD {t})) s * ?P)"
  proof (rule lfp_transfer[symmetric, where \<alpha>="\<lambda>x s. x s * emeasure (T t) {\<omega>\<in>space (T t). P \<omega>}"])
    fix F show "(\<lambda>s. ?F (HLD {t}) F s * ?P) = ?F ({t} \<cdot> P) (\<lambda>s. F s * ?P)"
      unfolding emeasure_HLD emeasure_HLD_nxt[OF assms] distrib_right
      by (auto simp: fun_eq_iff nn_integral_multc[symmetric]
               intro!: arg_cong2[where f="(+)"] nn_integral_cong ac_simps
               split: split_indicator)
  qed (auto intro!: order_continuous_intros sup_continuous_mono lfp_upperbound
            intro: le_funI add_nonneg_nonneg
            simp: bot_ennreal split: split_indicator)
  also have "lfp (?F (HLD {t})) s = emeasure (T s) {x\<in>space (T s). (HLD (-{t}) suntil HLD {t}) x}"
    by (rule emeasure_suntil_disj[symmetric]) (auto simp: HLD_iff)
  finally show ?thesis
    by (simp add: HLD_iff[abs_def] ev_eq_suntil)
qed

lemma AE_suntil:
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T s. (not (HLD {t}) suntil (HLD {t} aand nxt P)) x) \<longleftrightarrow>
   (AE x in T s. ev (HLD {t}) x) \<and> (AE x in T t. P x)"
  apply (subst (1 2 3) T.prob_Collect_eq_1[symmetric])
  apply simp
  apply simp
  apply simp
  apply (simp_all add: measure_def emeasure_suntil_HLD del: space_T nxt.simps)
  apply (auto simp: T.emeasure_eq_measure mult_eq_1)
  done

subsection \<open>Fairness\<close>

definition fair :: "'s \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> bool" where
  "fair s t = alw (ev (HLD {s})) impl alw (ev (HLD {s} aand nxt (HLD {t})))"

lemma AE_T_fair:
  assumes "t' \<in> K t"
  shows "AE \<omega> in T s. fair t t' \<omega>"
proof -
  let ?M = "\<lambda>P s. emeasure (T s) {\<omega>\<in>space (T s). P \<omega>}"
  let ?t = "HLD {t}" and ?t' = "HLD {t'}"
  define N where "N = alw (ev ?t) aand alw (not (?t aand nxt ?t'))"
  let ?until = "not ?t suntil (?t aand nxt (not ?t' aand nxt N))"
  have N_stl: "\<And>\<omega>. N \<omega> \<Longrightarrow> N (stl \<omega>)"
    by (auto simp: N_def)
  have [measurable]: "Measurable.pred S N"
    unfolding N_def by measurable

  let ?c = "pmf (K t) t'"
  let ?R = "\<lambda>x. 1 \<sqinter> x * (1 - ennreal ?c)"
  have "mono ?R"
    by (intro monoI mult_right_mono inf_mono) (auto simp: mono_def field_simps )
  have "\<And>s. ?M N s \<le> gfp ?R"
  proof (induction rule: gfp_ordinal_induct[OF \<open>mono ?R\<close>])
    fix x s assume x: "\<And>s. ?M N s \<le> x"
    { fix \<omega> assume "N \<omega>"
      then have "ev (HLD {t}) \<omega>" "N \<omega>"
        by (auto simp: N_def)
      then have "?until \<omega>"
        by (induct rule: ev_induct_strong) (auto simp: N_def intro: suntil.intros dest: N_stl) }
    then have "?M N s \<le> ?M ?until s"
      by (intro emeasure_mono_AE) auto
    also have "\<dots> = ?M (ev ?t) s * ?M (not ?t' aand nxt N) t"
      by (simp_all add: emeasure_suntil_HLD del: nxt.simps space_T)
    also have "\<dots> \<le> ?M (ev ?t) s * (\<integral>\<^sup>+s'. 1 \<sqinter> x * indicator (UNIV - {t'}) s' \<partial>K t)"
      by (auto intro!: mult_left_mono nn_integral_mono T.measure_le_1 emeasure_mono
               split: split_indicator simp add: x emeasure_Collect_T[of _ t] simp del: space_T)
    also have "\<dots> \<le> 1 * (\<integral>\<^sup>+s'. 1 \<sqinter> x * indicator (UNIV - {t'}) s' \<partial>K t)"
      by (intro mult_right_mono T.measure_le_1) simp
    finally show "?M N s \<le> 1 \<sqinter> x * (1 - ennreal ?c)"
      by (subst (asm) nn_integral_cmult_indicator) (auto simp: emeasure_Diff emeasure_pmf_single)
  qed (auto intro: Inf_greatest)
  also
  from \<open>mono ?R\<close> have "gfp ?R = ?R (gfp ?R)" by (rule gfp_unfold)
  then have "gfp ?R \<le> ?R (gfp ?R)" by simp
  with assms[THEN pmf_positive] have "gfp ?R \<le> 0"
    by (cases "gfp ?R")
       (auto simp: top_unique inf_ennreal.rep_eq field_simps mult_le_0_iff ennreal_1[symmetric]
                   pmf_le_1 ennreal_minus ennreal_mult[symmetric] ennreal_le_iff2 inf_min min_def
             simp del: ennreal_1
             split: if_split_asm)
  finally have "\<And>s. AE \<omega> in T s. \<not> N \<omega>"
    by (subst AE_iff_measurable[OF _ refl]) (auto intro: antisym simp: le_fun_def)
  then have "AE \<omega> in T s. alw (not N) \<omega>"
    by (intro AE_T_alw) auto
  moreover
  { fix \<omega> assume "alw (ev (HLD {t})) \<omega>"
    then have "alw (alw (ev (HLD {t}))) \<omega>"
      unfolding alw_alw .
    moreover assume "alw (not N) \<omega>"
    then have "alw (alw (ev (HLD {t})) impl ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      unfolding N_def not_alw_iff not_ev_iff de_Morgan_disj de_Morgan_conj not_not imp_conv_disj .
    ultimately have "alw (ev (HLD {t} aand nxt (HLD {t'}))) \<omega>"
      by (rule alw_mp) }
  then have "\<forall>\<omega>. alw (not N) \<omega> \<longrightarrow> fair t t' \<omega>"
    by (auto simp: fair_def)
  ultimately show ?thesis
    by (simp add: eventually_mono)
qed

lemma enabled_imp_trancl:
  assumes "alw (HLD B) \<omega>" "enabled s \<omega>"
  shows "alw (HLD (acc_on B `` {s})) \<omega>"
proof -
  define t where "t = s"
  then have "(s, t) \<in> acc_on B"
    by auto
  moreover note \<open>alw (HLD B) \<omega>\<close>
  moreover note \<open>enabled s \<omega>\<close>[unfolded \<open>t == s\<close>[symmetric]]
  ultimately show ?thesis
  proof (coinduction arbitrary: t \<omega> rule: alw_coinduct)
    case stl from this(1,2,3) show ?case
      by (auto simp: enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] HLD_iff
                 intro!: exI[of _ "shd \<omega>"] rtrancl_trans[of s t])
  next
    case (alw t \<omega>) then show ?case
     by (auto simp: HLD_iff enabled.simps[of _ \<omega>] alw.simps[of _ \<omega>] intro!: rtrancl_trans[of s t])
  qed
qed

lemma AE_T_reachable: "AE \<omega> in T s. alw (HLD (acc `` {s})) \<omega>"
  using AE_T_enabled
proof eventually_elim
  fix \<omega> assume "enabled s \<omega>"
  from enabled_imp_trancl[of UNIV, OF _ this]
  show "alw (HLD (acc `` {s})) \<omega>"
    by (auto simp: HLD_iff[abs_def] all_imp_alw)
qed

lemma AE_T_all_fair: "AE \<omega> in T s. \<forall>(t,t')\<in>SIGMA t:UNIV. K t. fair t t' \<omega>"
proof -
  let ?Rn = "SIGMA s:(acc `` {s}). K s"
  have "AE \<omega> in T s. \<forall>(t,t')\<in>?Rn. fair t t' \<omega>"
  proof (subst AE_ball_countable)
    show "countable ?Rn"
      by (intro countable_SIGMA countable_rtrancl[OF countable_Image]) (auto simp: Image_def)
  qed (auto intro!: AE_T_fair)
  then show ?thesis
    using AE_T_reachable
  proof (eventually_elim, safe)
    fix \<omega> t t' assume "\<forall>(t,t')\<in>?Rn. fair t t' \<omega>" "t' \<in> K t" and alw: "alw (HLD (acc `` {s})) \<omega>"
    moreover
    { assume "t \<notin> acc `` {s}"
      then have "alw (not (HLD {t})) \<omega>"
        by (intro alw_mono[OF alw]) (auto simp: HLD_iff)
      then have "not (alw (ev (HLD {t}))) \<omega>"
        unfolding not_alw_iff not_ev_iff by auto
      then have "fair t t' \<omega>"
        unfolding fair_def by auto }
    ultimately show "fair t t' \<omega>"
      by auto
  qed
qed

lemma fair_imp: assumes "fair t t' \<omega>" "alw (ev (HLD {t})) \<omega>" shows "alw (ev (HLD {t'})) \<omega>"
proof -
  { fix \<omega> assume "ev (HLD {t} aand nxt (HLD {t'})) \<omega>" then have "ev (HLD {t'}) \<omega>"
      by induction auto }
  with assms show ?thesis
    by (auto simp: fair_def elim!: alw_mp intro: all_imp_alw)
qed

lemma AE_T_ev_HLD:
  assumes exiting: "\<And>t. (s, t) \<in> acc_on (-B) \<Longrightarrow> \<exists>t'\<in>B. (t, t') \<in> acc"
  assumes fin: "finite (acc_on (-B) `` {s})"
  shows "AE \<omega> in T s. ev (HLD B) \<omega>"
  using AE_T_all_fair AE_T_enabled
proof eventually_elim
  fix \<omega> assume fair: "\<forall>(t, t')\<in>(SIGMA s:UNIV. K s). fair t t' \<omega>" and "enabled s \<omega>"

  show "ev (HLD B) \<omega>"
  proof (rule ccontr)
    assume "\<not> ev (HLD B) \<omega>"
    then have "alw (HLD (- B)) \<omega>"
      by (simp add: not_ev_iff HLD_iff[abs_def])
    from enabled_imp_trancl[OF this \<open>enabled s \<omega>\<close>]
    have "alw (HLD (acc_on (-B) `` {s})) \<omega>"
      by (simp add: Diff_eq)
    from pigeonhole_stream[OF this fin]
    obtain t where "(s, t) \<in> acc_on (-B)" "alw (ev (HLD {t})) \<omega>"
      by auto
    from exiting[OF this(1)] obtain t' where "(t, t') \<in> acc" "t' \<in> B"
      by auto
    from this(1) have "alw (ev (HLD {t'})) \<omega>"
    proof induction
      case (step u w) then show ?case
        using fair fair_imp[of u w \<omega>] by auto
    qed fact
    { assume "ev (HLD {t'}) \<omega>" then have "ev (HLD B) \<omega>"
      by (rule ev_mono) (auto simp: HLD_iff \<open>t' \<in> B\<close>) }
    then show False
      using \<open>alw (ev (HLD {t'})) \<omega>\<close> \<open>\<not> ev (HLD B) \<omega>\<close> by auto
  qed
qed

lemma AE_T_ev_HLD':
  assumes exiting: "\<And>s. s \<notin> X \<Longrightarrow> \<exists>t\<in>X. (s, t) \<in> acc"
  assumes fin: "finite (-X)"
  shows "AE \<omega> in T s. ev (HLD X) \<omega>"
proof (rule AE_T_ev_HLD)
  show "\<And>t. (s, t) \<in> acc_on (- X) \<Longrightarrow> \<exists>t'\<in>X. (t, t') \<in> acc"
    using exiting by (auto elim: rtrancl.cases)
  have "acc_on (- X) `` {s} \<subseteq> -X \<union> {s}"
    by (auto elim: rtrancl.cases)
  with fin show "finite (acc_on (- X) `` {s})"
    by (auto dest: finite_subset )
qed

lemma AE_T_max_sfirst:
  assumes [measurable]: "Measurable.pred S X"
  assumes AE: "AE \<omega> in T c. sfirst X (c ## \<omega>) < \<infinity>" and "0 < e"
  shows "\<exists>N::nat. \<P>(\<omega> in T c. N < sfirst X (c ## \<omega>)) < e" (is "\<exists>N. ?P N < e")
proof -
  have "?P \<longlonglongrightarrow> measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < sfirst X (c ## bT)})"
    using dual_order.strict_trans enat_ord_simps(2)
    by (intro T.finite_Lim_measure_decseq) (force simp: decseq_Suc_iff simp del: enat_ord_simps)+
  also have "measure (T c) (\<Inter>N::nat. {bT \<in> space (T c). N < sfirst X (c ## bT)}) =
      \<P>(bT in T c. sfirst X (c ## bT) = \<infinity>)"
    by (auto simp del: not_infinity_eq intro!: arg_cong[where f="measure (T c)"])
       (metis less_irrefl not_infinity_eq)
  also have "\<P>(bT in T c. sfirst X (c ## bT) = \<infinity>) = 0"
    using AE by (intro T.prob_eq_0_AE) auto
  finally have "\<exists>N. \<forall>n\<ge>N. norm (?P n - 0) < e"
    using \<open>0 < e\<close> by (rule LIMSEQ_D)
  then show ?thesis
    by (auto simp: measure_nonneg)
qed

subsection \<open>First Hitting Time\<close>

lemma nn_integral_sfirst_finite':
  assumes "s \<notin> H"
  assumes [simp]: "finite (acc_on (-H) `` {s})"
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) \<omega> \<partial>T s) \<noteq> \<infinity>"
proof -
  have R_ne[simp]: "acc_on (-H) `` {s} \<noteq> {}"
    by auto
  have [measurable]: "H \<in> sets (count_space UNIV)"
    by simp

  let ?Pf = "\<lambda>n t. \<P>(\<omega> in T t. enat n < sfirst (HLD H) (t ## \<omega>))"
  have Pf_mono: "\<And>N n t. N \<le> n \<Longrightarrow> ?Pf n t \<le> ?Pf N t"
    by (auto intro!: T.finite_measure_mono simp del: enat_ord_code(1) simp: enat_ord_code(1)[symmetric])

  have not_H: "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> t \<notin> H"
    using \<open>s \<notin> H\<close> by (auto elim: rtrancl.cases)

  have "\<forall>\<^sub>F n in sequentially. \<forall>t\<in>acc_on (-H)``{s}. ?Pf n t < 1"
  proof (safe intro!: eventually_ball_finite)
    fix t assume "(s, t) \<in> acc_on (-H)"
    then have "AE \<omega> in T t. sfirst (HLD H) (t ## \<omega>) < \<infinity>"
      unfolding sfirst_finite
    proof induction
      case (step t u) with step.IH show ?case
        by (subst (asm) AE_T_iff) (auto simp: ev_Stream not_H)
    qed (simp add: ev_Stream eventually_frequently_simps until)
    from AE_T_max_sfirst[OF _ this, of 1]
    obtain N where "?Pf N t < 1" by auto
    with Pf_mono[of N] show "\<forall>\<^sub>F n in sequentially. ?Pf n t < 1"
      by (auto simp: eventually_sequentially intro: le_less_trans)
  qed simp
  then obtain n where "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> ?Pf n t < 1"
    by (auto simp: eventually_sequentially)
  moreover define d where "d = Max (?Pf n ` acc_on (-H) `` {s})"
  ultimately have d: "0 \<le> d" "d < 1" "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> ?Pf (Suc n) t \<le> d"
    using Pf_mono[of n "Suc n"] by (auto simp: Max_ge_iff measure_nonneg)

  let ?F = "\<lambda>F \<omega>. if shd \<omega> \<in> H then 0 else F (stl \<omega>) + 1 :: ennreal"
  have "sup_continuous ?F"
    by (intro order_continuous_intros)
  then have "mono ?F"
    by (rule sup_continuous_mono)
  have lfp_nonneg[simp]: "\<And>\<omega>. 0 \<le> lfp ?F \<omega>"
    by (subst lfp_unfold[OF \<open>mono ?F\<close>]) auto

  let ?I = "\<lambda>F s. \<integral>\<^sup>+t. (if t \<in> H then 0 else F t + 1) \<partial>K s"
  have "sup_continuous ?I"
    by (intro order_continuous_intros) auto
  then have "mono ?I"
    by (rule sup_continuous_mono)

  define p where "p = Suc n / (1 - d)"
  have p: "p = Suc n + d * p"
    unfolding p_def using d(1,2) by (auto simp: field_simps)
  have [simp]: "0 \<le> p"
    using d(1,2) by (auto simp: p_def)

  have "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) \<omega> \<partial>T s) = (\<integral>\<^sup>+ \<omega>. lfp ?F \<omega> \<partial>T s)"
  proof (intro nn_integral_cong_AE)
    show "AE x in T s. sfirst (HLD H) x = lfp ?F x"
      using until
    proof eventually_elim
      fix \<omega> assume "ev (HLD H) \<omega>" then show "sfirst (HLD H) \<omega> = lfp ?F \<omega>"
        by (induction rule: ev_induct_strong;
            subst lfp_unfold[OF \<open>mono ?F\<close>], simp add: HLD_iff[abs_def] ac_simps max_absorb2)
    qed
  qed
  also have "\<dots> = lfp (?I^^Suc n) s"
    unfolding lfp_funpow[OF \<open>mono ?I\<close>]
    by (subst nn_integral_T_lfp)
       (auto simp: nn_integral_add max_absorb2 intro!: order_continuous_intros)
  also have "lfp (?I^^Suc n) t \<le> p" if "(s, t) \<in> acc_on (-H)" for t
    using that
  proof (induction arbitrary: t rule: lfp_ordinal_induct[of "?I^^Suc n"])
    case (step S)
    have "(?I^^i) S t \<le> i + ?Pf i t * ennreal p" for i
      using step(3)
    proof (induction i arbitrary: t)
      case 0 then show ?case
        using T.prob_space step(1)
        by (auto simp add: zero_ennreal_def[symmetric] not_H zero_enat_def[symmetric] one_ennreal_def[symmetric])
    next
      case (Suc i)
      then have "t \<notin> H"
        by (auto simp: not_H)
      from Suc.prems have "\<And>t'. t' \<in> K t \<Longrightarrow> t' \<notin> H \<Longrightarrow> (s, t') \<in> acc_on (-H)"
        by (rule rtrancl_into_rtrancl) (insert Suc.prems, auto dest: not_H)
      then have "(?I ^^ Suc i) S t \<le> ?I (\<lambda>t. i + ennreal (?Pf i t) * p) t"
        by (auto simp: AE_measure_pmf_iff simp del: sfirst_eSuc space_T
                 intro!: nn_integral_mono_AE add_mono max.mono Suc)
      also have "\<dots> \<le> (\<integral>\<^sup>+ t. ennreal (Suc i) + ennreal \<P>(\<omega> in T t. enat i < sfirst (HLD H) (t ## \<omega>)) * p \<partial>K t)"
        by (intro nn_integral_mono) auto
      also have "\<dots> \<le> Suc i + ennreal (?Pf (Suc i) t) * p"
        unfolding T.emeasure_eq_measure[symmetric]
        by (subst (2) emeasure_Collect_T)
           (auto simp: \<open>t \<notin> H\<close> eSuc_enat[symmetric] nn_integral_add nn_integral_multc ennreal_of_nat_eq_real_of_nat)
      finally show ?case
        by (simp add: ennreal_of_nat_eq_real_of_nat)
    qed
    then have "(?I^^Suc n) S t \<le> Suc n + ?Pf (Suc n) t * ennreal p" .
    also have "\<dots> \<le> p"
      using d step by (subst (2) p) (auto intro!: mult_right_mono simp: ennreal_of_nat_eq_real_of_nat ennreal_mult)
    finally show ?case .
  qed (auto simp: SUP_least intro!: mono_pow \<open>mono ?I\<close> simp del: funpow.simps)
  finally show ?thesis
    unfolding p_def by (auto simp: top_unique)
qed

lemma nn_integral_sfirst_finite:
  assumes [simp]: "finite (acc_on (-H) `` {s})"
  assumes until: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. sfirst (HLD H) (s ## \<omega>) \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<notin> H" then show ?thesis
    using nn_integral_sfirst_finite'[of s H] until by (simp add: nn_integral_add)
qed (simp add: sfirst.simps)

lemma prob_T:
  assumes P: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>t. \<P>(\<omega> in T t. P (t ## \<omega>)) \<partial>K s)"
  using emeasure_Collect_T[OF P, of s] unfolding T.emeasure_eq_measure
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: measure_pmf.integrable_const_bound[where B=1])

lemma T_subprob[measurable]: "T \<in> measurable (measure_pmf I) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

subsection \<open>Markov chain with Initial Distribution\<close>

definition T' :: "'s pmf \<Rightarrow> 's stream measure" where
  "T' I = bind I (\<lambda>s. distr (T s) S ((##) s))"

lemma distr_Stream_subprob:
  "(\<lambda>s. distr (T s) S ((##) s)) \<in> measurable (measure_pmf I) (subprob_algebra S)"
  apply (intro measurable_distr2[OF _ T_subprob])
  apply (subst measurable_cong_sets[where M'="count_space UNIV \<Otimes>\<^sub>M S" and N'=S])
  apply (rule sets_pair_measure_cong)
  apply auto
  done

lemma sets_T': "sets (T' I) = sets S"
  by (simp add: T'_def)

lemma prob_space_T': "prob_space (T' I)"
  unfolding T'_def
proof (rule measure_pmf.prob_space_bind)
  show "AE s in I. prob_space (distr (T s) S ((##) s))"
    by (intro AE_measure_pmf_iff[THEN iffD2] ballI T.prob_space_distr) simp
qed (rule distr_Stream_subprob)

lemma AE_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "(AE x in T' I. P x) \<longleftrightarrow> (\<forall>s\<in>I. AE x in T s. P (s ## x))"
  unfolding T'_def by (simp add: AE_bind[OF distr_Stream_subprob] AE_measure_pmf_iff AE_distr_iff)

lemma emeasure_T':
  assumes [measurable]: "X \<in> sets S"
  shows "emeasure (T' I) X = (\<integral>\<^sup>+s. emeasure (T s) {\<omega>\<in>space S. s ## \<omega> \<in> X} \<partial>I)"
  unfolding T'_def
  by (simp add: emeasure_bind[OF _ distr_Stream_subprob] emeasure_distr vimage_def Int_def conj_ac)

lemma prob_T':
  assumes [measurable]: "Measurable.pred S P"
  shows "\<P>(x in T' I. P x) = (\<integral>s. \<P>(x in T s. P (s ## x)) \<partial>I)"
proof -
  interpret T': prob_space "T' I" by (rule prob_space_T')
  show ?thesis
    using emeasure_T'[of "{x\<in>space (T' I). P x}" I]
    unfolding T'.emeasure_eq_measure T.emeasure_eq_measure sets_eq_imp_space_eq[OF sets_T']
    apply simp
    apply (subst (asm) nn_integral_eq_integral)
    apply (auto intro!: measure_pmf.integrable_const_bound[where B=1] integral_cong arg_cong2[where f=measure]
                simp: AE_measure_pmf measure_nonneg space_stream_space)
    done
qed

lemma T_eq_T': "T s = T' (K s)"
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets (T s)"
  then have [measurable]: "X \<in> sets S"
    by simp
  have X_eq: "X = {x\<in>space (T s). x \<in> X}"
    using sets.sets_into_space[OF X] by auto
  show "emeasure (T s) X = emeasure (T' (K s)) X"
    apply (subst X_eq)
    apply (subst emeasure_Collect_T, simp)
    apply (subst emeasure_T', simp)
    apply simp
    done
qed (simp add: sets_T')

lemma T_eq_bind: "T s = (measure_pmf (K s) \<bind> (\<lambda>t. distr (T t) S ((##) t)))"
  by (subst T_eq_T') (simp add: T'_def)

lemma T_split:
  "T s = (T s \<bind> (\<lambda>\<omega>. distr (T ((s ## \<omega>) !! n)) S (\<lambda>\<omega>'. stake n \<omega> @- \<omega>')))"
proof (induction n arbitrary: s)
  case 0 then show ?case
    apply (simp add: distr_cong[OF refl sets_T[symmetric, of s] refl])
    apply (subst bind_const')
    apply unfold_locales
    ..
next
  case (Suc n)
  let ?K = "measure_pmf (K s)" and ?m = "\<lambda>n \<omega> \<omega>'. stake n \<omega> @- \<omega>'"
  note sets_stream_space_cong[simp, measurable_cong]

  have "T s = (?K \<bind> (\<lambda>t. distr (T t) S ((##) t)))"
    by (rule T_eq_bind)
  also have "\<dots> = (?K \<bind> (\<lambda>t. distr (T t \<bind> (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>))) S ((##) t)))"
    unfolding Suc[symmetric] ..
  also have "\<dots> = (?K \<bind> (\<lambda>t. T t \<bind> (\<lambda>\<omega>. distr (distr (T ((t ## \<omega>) !! n)) S (?m n \<omega>)) S ((##) t))))"
    by (simp add: distr_bind[where K=S, OF measurable_distr2[where M=S]] space_stream_space)
  also have "\<dots> = (?K \<bind> (\<lambda>t. T t \<bind> (\<lambda>\<omega>. distr (T ((t ## \<omega>) !! n)) S (?m (Suc n) (t ## \<omega>)))))"
    by (simp add: distr_distr space_stream_space comp_def)
  also have "\<dots> = (?K \<bind> (\<lambda>t. distr (T t) S ((##) t) \<bind> (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>))))"
    by (simp add: space_stream_space bind_distr[OF _ measurable_distr2[where M=S]] del: stake.simps)
  also have "\<dots> = (T s \<bind> (\<lambda>\<omega>. distr (T (\<omega> !! n)) S (?m (Suc n) \<omega>)))"
    unfolding T_eq_bind[of s]
    by (subst bind_assoc[OF measurable_distr2[where M=S] measurable_distr2[where M=S], OF _ T_subprob])
       (simp_all add: space_stream_space del: stake.simps)
  finally show ?case
    by simp
qed

lemma nn_integral_T_split:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T s) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (stake n \<omega> @- \<omega>') \<partial>T ((s ## \<omega>) !! n)) \<partial>T s)"
  apply (subst T_split[of s n])
  apply (simp add: nn_integral_bind[OF f measurable_distr2[where M=S]])
  apply (subst nn_integral_distr)
  apply (simp_all add: space_stream_space)
  done

lemma emeasure_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} =
      (\<integral>\<^sup>+\<omega>. emeasure (T ((s ## \<omega>) !! n)) {\<omega>'\<in>space (T ((s ## \<omega>) !! n)). P (stake n \<omega> @- \<omega>')} \<partial>T s)"
  apply (subst T_split[of s n])
  apply (subst emeasure_bind[OF _ measurable_distr2[where M=S]])
  apply (simp_all add: )
  apply (simp add: space_stream_space)
  apply (subst emeasure_distr)
  apply simp_all
  apply (simp_all add: space_stream_space)
  done

lemma prob_T_split:
  assumes P[measurable]: "Measurable.pred S P"
  shows "\<P>(\<omega> in T s. P \<omega>) = (\<integral>\<omega>. \<P>(\<omega>' in T ((s ## \<omega>) !! n). P (stake n \<omega> @- \<omega>')) \<partial>T s)"
  using emeasure_T_split[OF P, of s n]
  unfolding T.emeasure_eq_measure
  by (subst (asm) nn_integral_eq_integral)
     (auto intro!: T.integrable_const_bound[where B=1] measure_measurable_subprob_algebra2[where N=S]
           simp: T.emeasure_eq_measure SIGMA_Collect_eq)

lemma enabled_imp_alw:
  "(\<Union>s\<in>X. set_pmf (K s)) \<subseteq> X \<Longrightarrow> x \<in> X \<Longrightarrow> enabled x \<omega> \<Longrightarrow> alw (HLD X) \<omega>"
proof (coinduction arbitrary: \<omega> x)
  case alw then show ?case
    unfolding enabled.simps[of _ \<omega>]
    by (auto simp: HLD_iff)
qed

lemma alw_HLD_iff_sconst:
  "alw (HLD {x}) \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "alw (HLD {x}) \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto simp: HLD_iff)
qed (auto simp: alw_sconst HLD_iff)

lemma enabled_iff_sconst:
  assumes [simp]: "set_pmf (K x) = {x}" shows "enabled x \<omega> \<longleftrightarrow> \<omega> = sconst x"
proof
  assume "enabled x \<omega>" then show "\<omega> = sconst x"
    by (coinduction arbitrary: \<omega>) (auto elim: enabled.cases)
next
  assume "\<omega> = sconst x" then show "enabled x \<omega>"
    by (coinduction arbitrary: \<omega>) auto
qed

lemma AE_sconst:
  assumes [simp]: "set_pmf (K x) = {x}"
  shows "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> P (sconst x)"
proof -
  have "(AE \<omega> in T x. P \<omega>) \<longleftrightarrow> (AE \<omega> in T x. P \<omega> \<and> \<omega> = sconst x)"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x) \<and> \<omega> = sconst x)"
    by (simp del: AE_conj_iff cong: rev_conj_cong)
  also have "\<dots> = (AE \<omega> in T x. P (sconst x))"
    using AE_T_enabled[of x] by (simp add: enabled_iff_sconst)
  finally show ?thesis
    by simp
qed

lemma ev_eq_lfp: "ev P = lfp (\<lambda>F \<omega>. P \<omega> \<or> (\<not> P \<omega> \<and> F (stl \<omega>)))"
  unfolding ev_def by (intro antisym lfp_mono) blast+

lemma INF_eq_zero_iff_ennreal: "((\<Sqinter>i\<in>A. f i) = (0::ennreal)) = (\<forall>x>0. \<exists>i\<in>A. f i < x)"
  using INF_eq_bot_iff[where 'a=ennreal] unfolding bot_ennreal_def zero_ennreal_def by auto

lemma inf_continuous_cmul: 
  fixes c :: ennreal
  assumes f: "inf_continuous f" and c: "c < \<top>" 
  shows "inf_continuous (\<lambda>x. c * f x)"
proof (rule inf_continuous_compose[OF _ f], clarsimp simp add: inf_continuous_def)
  fix M :: "nat \<Rightarrow> ennreal" assume M: "decseq M" 
  show "c * (\<Sqinter>i. M i) = (\<Sqinter>i. c * M i)"
    using M
    by (intro LIMSEQ_unique[OF ennreal_tendsto_cmult[OF c] LIMSEQ_INF] LIMSEQ_INF)
       (auto simp: decseq_def mult_left_mono)
qed

lemma AE_T_ev_HLD_infinite:
  fixes X :: "'s set" and r :: real
  assumes "r < 1"
  assumes r: "\<And>x. x \<in> X \<Longrightarrow> measure (K x) X \<le> r"
  shows "AE \<omega> in T x. ev (HLD (- X)) \<omega>"
proof -
  { fix x assume "x \<in> X"
    have "0 \<le> r" using r[OF \<open>x \<in> X\<close>] measure_nonneg[of "K x" X] by (blast  intro: order.trans)
    define P where "P F x = \<integral>\<^sup>+y. indicator X y * (F y \<sqinter> 1) \<partial>K x" for F x
    have [measurable]: "X \<in> sets (count_space UNIV)" by auto
    have bnd: "(\<integral>\<^sup>+ y. indicator X y * (f y \<sqinter> 1) \<partial>K x) \<le> 1" for x f
      by (intro measure_pmf.nn_integral_le_const AE_pmfI) (auto split: split_indicator)
    have "emeasure (T x) {\<omega>\<in>space (T x). alw (HLD X) \<omega>} =
      emeasure (T x) {\<omega>\<in>space (T x). gfp (\<lambda>F \<omega>. shd \<omega> \<in> X \<and> F (stl \<omega>)) \<omega>}"
      by (simp add: alw_def HLD_def)
    also have "\<dots> = gfp P x"
      apply (rule emeasure_gfp)
      apply (auto intro!: order_continuous_intros inf_continuous_cmul split: split_indicator simp: P_def)
      subgoal for x f using bnd[of x f] by (auto simp: top_unique)
      subgoal for P x
        apply (subst T_eq_bind)
        apply (subst emeasure_bind[where N=S])
        apply simp
        apply (rule measurable_distr2[where M=S])
        apply (auto intro: T_subprob[THEN measurable_space] intro!: nn_integral_cong_AE AE_pmfI
            simp: emeasure_distr split: split_indicator)
        apply (simp_all add: space_stream_space T.emeasure_le_1 inf.absorb1)
        done
      apply (intro le_funI)
      apply (subst nn_integral_indicator[symmetric])
      apply simp
      apply (intro nn_integral_mono)
      apply (auto split: split_indicator)
      done
    also have "\<dots> \<le> (INF n. ennreal r ^ n)"
    proof (intro INF_greatest)
      have mono_P: "mono P"
        by (force simp: le_fun_def mono_def P_def intro!: nn_integral_mono intro: le_infI1 split: split_indicator)
      fix n show "gfp P x \<le> ennreal r ^ n"
        using \<open>x \<in> X\<close>
      proof (induction n arbitrary: x)
        case 0 then show ?case
          by (subst gfp_unfold[OF mono_P]) (auto intro!: measure_pmf.nn_integral_le_const AE_pmfI split: split_indicator simp: P_def)
      next
        case (Suc n x)
        have "gfp P x = P (gfp P) x" by (subst gfp_unfold[OF mono_P]) rule
        also have "\<dots> \<le> P (\<lambda>x. ennreal r ^ n) x"
          unfolding P_def[of _ x] by (auto intro!: nn_integral_mono le_infI1 Suc split: split_indicator)
        also have "\<dots> \<le> ennreal r ^ (Suc n)"
          using Suc by (auto simp: P_def nn_integral_multc measure_pmf.emeasure_eq_measure intro!: mult_mono ennreal_leI r)
        finally show ?case .
      qed
    qed
    also have "\<dots> = 0"
      unfolding ennreal_power[OF \<open>0 \<le> r\<close>]
    proof (intro LIMSEQ_unique[OF LIMSEQ_INF])
      show "decseq (\<lambda>i. ennreal (r ^ i))"
        using \<open>0 \<le> r\<close> \<open>r < 1\<close> by (auto intro!: ennreal_leI power_decreasing simp: decseq_def)
      have "(\<lambda>i. ennreal (r ^ i)) \<longlonglongrightarrow> ennreal 0"
        using \<open>0 \<le> r\<close> \<open>r < 1\<close> by (intro tendsto_ennrealI LIMSEQ_power_zero) auto
      then show "(\<lambda>i. ennreal (r ^ i)) \<longlonglongrightarrow> 0" by simp
    qed
    finally have *: "emeasure (T x) {\<omega>\<in>space (T x). alw (HLD X) \<omega>} = 0" by auto
    have "AE \<omega> in T x. ev (HLD (- X)) \<omega>"
      by (rule AE_I[OF _ *]) (auto simp: not_ev_iff not_HLD[symmetric]) }
  note * = this
  show ?thesis
    apply (clarsimp simp add: AE_T_iff[of _ x])
    subgoal for x'
      by (cases "x' \<in> X") (auto simp add: ev_Stream *)
    done
qed
  
subsection \<open>Trace space with Restriction\<close>

definition "rT x = restrict_space (T x) {\<omega>. enabled x \<omega>}"

lemma space_rT: "\<omega> \<in> space (rT x) \<longleftrightarrow> enabled x \<omega>"
  by (auto simp: rT_def space_restrict_space space_stream_space)

lemma Collect_enabled_S[measurable]: "Collect (enabled x) \<in> sets S"
proof -
  have "Collect (enabled x) = {\<omega>\<in>space S. enabled x \<omega>}"
    by (auto simp: space_stream_space)
  then show ?thesis
    by simp
qed

lemma space_rT_in_S: "space (rT x) \<in> sets S"
  by (simp add: rT_def space_restrict_space)

lemma sets_rT: "A \<in> sets (rT x) \<longleftrightarrow> A \<in> sets S \<and> A \<subseteq> {\<omega>. enabled x \<omega>}"
  by (auto simp: rT_def sets_restrict_space space_stream_space)

lemma prob_space_rT: "prob_space (rT x)"
  unfolding rT_def by (auto intro!: prob_space_restrict_space T.emeasure_eq_1_AE AE_T_enabled)

lemma measurable_force_enabled2[measurable]: "force_enabled x \<in> measurable S (rT x)"
  unfolding rT_def
  by (rule measurable_restrict_space2)
     (auto intro: measurable_force_enabled enabled_force_enabled)

lemma space_rT_not_empty[simp]: "space (rT x) \<noteq> {}"
  by (simp add: rT_def space_restrict_space Ex_enabled)

lemma T_eq_bind': "T x = do { y \<leftarrow> measure_pmf (K x) ; \<omega> \<leftarrow> T y ; return S (y ## \<omega>) }"
  apply (subst T_eq_bind)
  apply (subst bind_return_distr[symmetric])
  apply (simp_all add: space_stream_space comp_def)
  done

lemma rT_eq_bind: "rT x = do { y \<leftarrow> measure_pmf (K x) ; \<omega> \<leftarrow> rT y ; return (rT x) (y ## \<omega>) }"
  unfolding rT_def
  apply (subst T_eq_bind)
  apply (subst restrict_space_bind[where K=S])
  apply (rule measurable_distr2[where M=S])
  apply (auto simp del: measurable_pmf_measure1
              simp add: Ex_enabled return_restrict_space intro!: bind_cong )
  apply (subst restrict_space_bind[symmetric, where K=S])
  apply (auto simp add: Ex_enabled space_restrict_space return_cong[OF sets_T]
              intro!:  measurable_restrict_space1 measurable_compose[OF _ return_measurable]
              arg_cong2[where f=restrict_space])
  apply (subst bind_return_distr[unfolded comp_def])
  apply (simp add: space_restrict_space Ex_enabled)
  apply (simp add: measurable_restrict_space1)
  apply (rule measure_eqI)
  apply simp
  apply (subst (1 2) emeasure_distr)
  apply (auto simp: measurable_restrict_space1)
  apply (subst emeasure_restrict_space)
  apply (auto simp: space_restrict_space intro!: emeasure_eq_AE)
  using AE_T_enabled
  apply eventually_elim
  apply (simp add: space_stream_space)
  apply (rule sets_Int_pred)
  apply auto
  apply (simp add: space_stream_space)
  done

lemma snth_rT: "(\<lambda>x. x !! n) \<in> measurable (rT x) (count_space (acc `` {x}))"
proof -
  have "\<And>\<omega>. enabled x \<omega> \<Longrightarrow> (x, \<omega> !! n) \<in> acc"
  proof (induction n arbitrary: x)
    case (Suc n) from Suc.prems Suc.IH[of "shd \<omega>" "stl \<omega>"] show ?case
      by (auto simp: enabled.simps[of x \<omega>] intro: rtrancl_trans)
  qed (auto elim: enabled.cases)
  moreover
  { fix X :: "'s set"
    have [measurable]: "X \<in> count_space UNIV" by simp
    have *: "(\<lambda>x. x !! n) -` X \<inter> space (rT x) =  {\<omega>\<in>space S. \<omega> !! n \<in> X \<and> enabled x \<omega>}"
      by (auto simp: space_stream_space space_rT)
    have "(\<lambda>x. x !! n) -` X \<inter> space (rT x) \<in> sets S"
      unfolding * by measurable }
  ultimately show ?thesis
    by (auto simp: measurable_def space_rT sets_rT)
qed

subsection \<open>Bisimulation\<close>

lemma T_coinduct[consumes 1, case_names prob sets cont]:
  assumes "R x M"
  assumes prob: "\<And>x M. R x M \<Longrightarrow> prob_space M"
    and sets: "\<And>x M. R x M \<Longrightarrow> sets M = sets S"
    and cont': "\<And>x M. R x M \<Longrightarrow> \<exists>M'. (\<forall>y\<in>K x. R y (M' y)) \<and> (\<forall>y. sets (M' y) = S \<and> prob_space (M' y)) \<and>
      M = (measure_pmf (K x) \<bind> (\<lambda>y. distr (M' y) S ((##) y)))"
  shows "T x = M"
  using \<open>R x M\<close>
proof (coinduction arbitrary: x M rule: measure_eq_stream_space_coinduct)
  case left then show ?case using T.prob_space_axioms[of x] sets_T[of x] by (auto simp: space_prob_algebra)
next
  case (right M) with prob[of M] sets[of M] show ?case by (auto simp: space_prob_algebra)
next
  case (cont x M) with cont'[OF cont] obtain M' where *:
    "(\<forall>y\<in>K x. R y (M' y))"
    "(\<forall>y. sets (M' y) = S \<and> prob_space (M' y))"
    "M = (measure_pmf (K x) \<bind> (\<lambda>y. distr (M' y) S ((##) y)))"
    by auto
  show ?case
    apply (rule exI[of _ T])
    apply (rule exI[of _ M'])
    apply (rule exI[of _ "K x"])
    using * T.prob_space_axioms sets_T[of x]
    apply (auto simp: space_prob_algebra intro: T_eq_bind)
    done
qed

lemma T_bisim:
  assumes M: "\<And>x. prob_space (M x)" "\<And>x. sets (M x) = sets S"
    and M_eq: "\<And>x. M x = (measure_pmf (K x) \<bind> (\<lambda>s. distr (M s) S ((##) s)))"
  shows "T = M"
proof
  fix x show "T x = M x"
  proof (coinduction arbitrary: x rule: T_coinduct)
    case (cont x) then show ?case
      apply (intro exI[of _ M])
      apply (subst M_eq[of x])
      apply (simp add: M)
      done
  qed fact+
qed

lemma T_subprob'[measurable]: "T \<in> measurable (count_space UNIV) (subprob_algebra S)"
  by (auto intro!: space_bind simp: space_subprob_algebra) unfold_locales

lemma T_subprob''[simp]: "T a \<in> space (subprob_algebra S)"
  using measurable_space[OF T_subprob', of a] by simp

lemma AE_not_suntil_coinduct [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes \<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes \<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)"
proof -
  { fix \<omega> have "\<not> (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>) \<longleftrightarrow>
      (\<forall>n. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>))"
      unfolding suntil_def
      by (subst sup_continuous_lfp)
         (auto simp add: sup_continuous_def) }
  moreover
  { fix n from \<open>P s\<close> have "AE \<omega> in T s. \<not> ((\<lambda>R. HLD \<psi> or (HLD \<phi> aand nxt R)) ^^ n) \<bottom> (s ## \<omega>)"
    proof (induction n arbitrary: s)
      case (Suc n) then show ?case
        apply (subst AE_T_iff)
        apply (rule measurable_compose[OF measurable_Stream, where M1="count_space UNIV"])
        apply measurable
        apply simp
        apply (auto simp: bot_fun_def intro!: AE_impI dest: \<phi> \<psi>)
        done
    qed simp }
  ultimately show ?thesis
    by (simp add: AE_all_countable)
qed

lemma AE_not_suntil_coinduct_strong [consumes 1, case_names \<psi> \<phi>]:
  assumes "P s"
  assumes P_\<psi>: "\<And>s. P s \<Longrightarrow> s \<notin> \<psi>"
  assumes P_\<phi>: "\<And>s t. P s \<Longrightarrow> s \<in> \<phi> \<Longrightarrow> t \<in> K s \<Longrightarrow> P t \<or>
    (AE \<omega> in T t. not (HLD \<phi> suntil HLD \<psi>) (t ## \<omega>))"
  shows "AE \<omega> in T s. not (HLD \<phi> suntil HLD \<psi>) (s ## \<omega>)" (is "?nuntil s")
proof -
  have "P s \<or> ?nuntil s"
    using \<open>P s\<close> by auto
  then show ?thesis
  proof (coinduction arbitrary: s rule: AE_not_suntil_coinduct)
    case (\<phi> t s) then show ?case
      by (auto simp: AE_T_iff[of _ s] suntil_Stream[of _ _ s] dest: P_\<phi>)
  qed (auto simp: suntil_Stream dest: P_\<psi>)
qed

end

subsection \<open>Reward Structure on Markov Chains\<close>

locale MC_with_rewards = MC_syntax K for K :: "'s \<Rightarrow> 's pmf" +
  fixes \<iota> :: "'s \<Rightarrow> 's \<Rightarrow> ennreal" and \<rho> :: "'s \<Rightarrow> ennreal"
  assumes \<iota>_nonneg: "\<And>s t. 0 \<le> \<iota> s t" and \<rho>_nonneg: "\<And>s. 0 \<le> \<rho> s"
  assumes measurable_\<iota>[measurable]: "(\<lambda>(a, b). \<iota> a b) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
begin

definition reward_until :: "'s set \<Rightarrow> 's \<Rightarrow> 's stream \<Rightarrow> ennreal" where
  "reward_until X = lfp (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (F (shd \<omega>) (stl \<omega>)))"

lemma measurable_\<rho>[measurable]: "\<rho> \<in> borel_measurable (count_space UNIV)"
  by simp

lemma measurable_reward_until[measurable (raw)]:
  assumes [measurable]: "f \<in> measurable M (count_space UNIV)"
  assumes [measurable]: "g \<in> measurable M S"
  shows "(\<lambda>x. reward_until X (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>F (s, \<omega>). if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (F (shd \<omega>, stl \<omega>))"
  { fix s \<omega>
    have "reward_until X s \<omega> = lfp ?F (s, \<omega>)"
      unfolding reward_until_def lfp_pair[symmetric] .. }
  note * = this

  have [measurable]: "lfp ?F \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
  proof (rule borel_measurable_lfp)
    fix f :: "('s \<times> 's stream) \<Rightarrow> ennreal"
    assume [measurable]: "f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
    show "?F f \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M S)"
      unfolding split_beta'
      apply (intro measurable_If)
      apply measurable []
      apply measurable []
      apply (rule predE)
      apply (rule measurable_compose[OF measurable_fst])
      apply measurable []
      done
  qed (auto intro!: \<iota>_nonneg \<rho>_nonneg order_continuous_intros)
  show ?thesis
    unfolding * by measurable
qed

lemma continuous_reward_until:
  "sup_continuous (\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (F (shd \<omega>) (stl \<omega>)))"
  by (intro \<iota>_nonneg \<rho>_nonneg order_continuous_intros) (auto simp: sup_continuous_def image_comp)

lemma
  shows reward_until_unfold: "reward_until X s \<omega> =
        (if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>))"
      (is ?unfold)
proof -
  let ?F = "\<lambda>F s \<omega>. if s \<in> X then 0 else \<rho> s + \<iota> s (shd \<omega>) + (F (shd \<omega>) (stl \<omega>))"
  { fix s \<omega> have "reward_until X s \<omega> = ?F (reward_until X) s \<omega>"
      unfolding reward_until_def
      apply (subst lfp_unfold)
      apply (rule continuous_reward_until[THEN sup_continuous_mono, of X])
      apply rule
      done }
  note step = this
  show ?unfold
    by (subst step) (auto intro!: arg_cong2[where f="(+)"])
qed

lemma reward_until_simps[simp]:
  shows "s \<in> X \<Longrightarrow> reward_until X s \<omega> = 0"
    and "s \<notin> X \<Longrightarrow> reward_until X s \<omega> = \<rho> s + \<iota> s (shd \<omega>) + reward_until X (shd \<omega>) (stl \<omega>)"
  unfolding reward_until_unfold[of X s \<omega>] by simp_all

lemma reward_until_SCons[simp]:
  "reward_until X s (t ## \<omega>) = (if s \<in> X then 0 else \<rho> s + \<iota> s t + reward_until X t \<omega>)"
  by simp

lemma nn_integral_reward_until_finite:
  assumes [simp]: "finite (acc `` {s})" (is "finite (?R `` {s})")
  assumes \<rho>: "\<And>t. (s, t) \<in> acc_on (-H) \<Longrightarrow> \<rho> t < \<infinity>"
  assumes \<iota>: "\<And>t t'. (s, t) \<in> acc_on (-H) \<Longrightarrow> t' \<in> K t \<Longrightarrow> \<iota> t t' < \<infinity>"
  assumes ev: "AE \<omega> in T s. ev (HLD H) \<omega>"
  shows "(\<integral>\<^sup>+ \<omega>. reward_until H s \<omega> \<partial>T s) \<noteq> \<infinity>"
proof cases
  assume "s \<in> H" then show ?thesis
    by simp
next
  assume "s \<notin>  H"
  let ?L = "acc_on (-H)"
  define M where "M = Max ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
  have "?L \<subseteq> ?R"
    by (intro rtrancl_mono) auto
  with \<open>s \<notin> H\<close> have subset: "(SIGMA t:?L``{s}. K t) \<subseteq> (?R``{s} \<times> ?R``{s})"
    by (auto intro: rtrancl_into_rtrancl elim: rtrancl.cases)
  then have [simp, intro!]: "finite ((\<lambda>(s, t). \<rho> s + \<iota> s t) ` (SIGMA t:?L``{s}. K t))"
    by (intro finite_imageI) (auto dest: finite_subset)
  { fix t t' assume "(s, t) \<in> ?L" "t \<notin> H" "t' \<in> K t"
    then have "(t, t') \<in> (SIGMA t:?L``{s}. K t)"
      by (auto intro: rtrancl_into_rtrancl)
    then have "\<rho> t + \<iota> t t' \<le> M"
      unfolding M_def by (intro Max_ge) auto }
  note le_M = this

  have fin_L: "finite (?L `` {s})"
    by (intro finite_subset[OF _ assms(1)] Image_mono \<open>?L \<subseteq> ?R\<close> order_refl)

  have "M < \<infinity>"
    unfolding M_def
  proof (subst Max_less_iff, safe)
    show "(SIGMA x:?L `` {s}. set_pmf (K x)) = {} \<Longrightarrow> False"
      using \<open>s \<notin> H\<close> by (auto simp add: Sigma_empty_iff set_pmf_not_empty)
    fix t t' assume "(s, t) \<in> ?L" "t' \<in> K t" then show "\<rho> t + \<iota> t t' < \<infinity>"
      using \<rho>[of t] \<iota>[of t t'] by simp
  qed

  from set_pmf_not_empty[of "K s"] obtain t where "t \<in> K s"
    by auto
  with le_M[of s t] have "0 \<le> M"
    using set_pmf_not_empty[of "K s"] \<open>s \<notin> H\<close> le_M[of s] \<iota>_nonneg[of s] \<rho>_nonneg[of s]
    by (intro order_trans[OF _ le_M]) auto

  have "AE \<omega> in T s. reward_until H s \<omega> \<le> M * sfirst (HLD H) (s ## \<omega>)"
    using ev AE_T_enabled
  proof eventually_elim
    fix \<omega> assume "ev (HLD H) \<omega>" "enabled s \<omega>"
    moreover define t where "t = s"
    ultimately have "ev (HLD H) \<omega>" "enabled t \<omega>" "t \<in> ?L``{s}"
      by auto
    then show "reward_until H t \<omega> \<le> M * sfirst (HLD H) (t ## \<omega>)"
    proof (induction arbitrary: t rule: ev_induct_strong)
      case (base \<omega> t) then show ?case
        by (auto simp: HLD_iff sfirst_Stream elim: enabled.cases intro: le_M)
    next
      case (step \<omega> t) from step.IH[of "shd \<omega>"] step.prems step.hyps show ?case
        by (auto simp add: HLD_iff enabled.simps[of t] distrib_left sfirst_Stream
                           reward_until_simps[of t]
                 simp del: reward_until_simps
                 intro!: add_mono le_M intro: rtrancl_into_rtrancl)
    qed
  qed
  then have "(\<integral>\<^sup>+\<omega>. reward_until H s \<omega> \<partial>T s) \<le> (\<integral>\<^sup>+\<omega>. M * sfirst (HLD H) (s ## \<omega>) \<partial>T s)"
    by (rule nn_integral_mono_AE)
  also have "\<dots> < \<infinity>"
    using \<open>0 \<le> M\<close> \<open>M < \<infinity>\<close> nn_integral_sfirst_finite[OF fin_L ev]
    by (simp add: nn_integral_cmult  less_top[symmetric] ennreal_mult_eq_top_iff)
  finally show ?thesis
    by simp
qed

end

subsection \<open>Bisimulation on a relation\<close>

definition rel_set_strong :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_set_strong R A B \<longleftrightarrow> (\<forall>x y. R x y \<longrightarrow> (x \<in> A \<longleftrightarrow> y \<in> B))"

lemma T_eq_rel_half[consumes 4, case_names prob sets cont]:
  fixes R :: "'s \<Rightarrow> 't \<Rightarrow> bool" and f :: "'s \<Rightarrow> 't" and S :: "'s set"
  assumes R_def: "\<And>s t. R s t \<longleftrightarrow> (s \<in> S \<and> f s = t)"
  assumes A[measurable]: "A \<in> sets (stream_space (count_space UNIV))"
    and B[measurable]: "B \<in> sets (stream_space (count_space UNIV))"
    and AB: "rel_set_strong (stream_all2 R) A B" and KL: "rel_fun R (rel_pmf R) K L" and xy: "R x y"
  shows "MC_syntax.T K x A = MC_syntax.T L y B"
proof -
  interpret K: MC_syntax K by unfold_locales
  interpret L: MC_syntax L by unfold_locales

  have "x \<in> S" using \<open>R x y\<close> by (auto simp: R_def)

  define g where "g t = (SOME s. R s t)" for t
  have measurable_g: "g \<in> count_space UNIV \<rightarrow>\<^sub>M count_space UNIV" by auto
  have g: "R i j \<Longrightarrow> R (g j) j" for i j
    unfolding g_def by (rule someI)
  
  have K_subset: "x \<in> S \<Longrightarrow> K x \<subseteq> S" for x
    using KL[THEN rel_funD, of x "f x", THEN rel_pmf_imp_rel_set] by (auto simp: rel_set_def R_def)

  have in_S: "AE \<omega> in K.T x. \<omega> \<in> streams S"
    using K.AE_T_enabled
  proof eventually_elim 
    case (elim \<omega>) with \<open>x \<in> S\<close> show ?case
      apply (coinduction arbitrary: x \<omega>)
      subgoal for x \<omega> using K_subset by (cases \<omega>) (auto simp: K.enabled_Stream)
      done
  qed

  have L_eq: "L y = map_pmf f (K x)" if xy: "R x y" for x y
  proof -
    have "rel_pmf (\<lambda>x y. x = y) (map_pmf f (K x)) (L y)"
      using KL[THEN rel_funD, OF xy] by (auto intro: pmf.rel_mono_strong simp: R_def pmf.rel_map)
    then show ?thesis unfolding pmf.rel_eq by simp
  qed

  let ?D = "\<lambda>x. distr (K.T x) K.S (smap f)"
  have prob_space_D: "?D x \<in> space (prob_algebra K.S)" for x 
    by (auto simp: space_prob_algebra K.T.prob_space_distr)

  have D_eq_D: "?D x = ?D x'" if "R x y" "R x' y" for x x' y
  proof (rule stream_space_eq_sstart)
    define A where "A = K.acc `` {x, x'}"
    have x_A: "x \<in> A" "x' \<in> A" by (auto simp: A_def)
    let ?\<Omega> = "f ` A"
    show "countable ?\<Omega>"
      unfolding A_def by (intro countable_image K.countable_acc) auto
    show "prob_space (?D x)" "prob_space (?D x')" by (auto intro!: K.T.prob_space_distr)
    show "sets (?D x) = sets L.S" "sets (?D x') = sets L.S" by auto
    have AE_streams: "AE x in ?D x''. x \<in> streams ?\<Omega>" if "x'' \<in> A" for x''
      apply (simp add: space_stream_space streams_sets AE_distr_iff)
      using K.AE_T_reachable[of x''] unfolding alw_HLD_iff_streams
    proof eventually_elim
      fix s assume "s \<in> streams (K.acc `` {x''})"
      moreover have "K.acc `` {x''} \<subseteq> A"
        using \<open>x'' \<in> A\<close> by (auto simp: A_def Image_def intro: rtrancl_trans)
      ultimately show "smap f s \<in> streams (f ` A)"
        by (auto intro: smap_streams)
    qed
    with x_A show "AE x in ?D x'. x \<in> streams ?\<Omega>" "AE x in ?D x. x \<in> streams ?\<Omega>"
      by auto
    from \<open>x \<in> A\<close> \<open>x' \<in> A\<close> that show "?D x (sstart (f ` A) xs) = ?D x' (sstart (f ` A) xs)" for xs
    proof (induction xs arbitrary: x x' y)
      case Nil
      moreover have "?D x (streams (f ` A)) = 1" if "x \<in> A" for x
        using AE_streams[of x] that
        by (intro prob_space.emeasure_eq_1_AE[OF K.T.prob_space_distr]) (auto simp: streams_sets)
      ultimately show ?case by simp
    next
      case (Cons z zs x x' y)
      have "rel_pmf (R OO R\<inverse>\<inverse>) (K x) (K x')"
        using KL[THEN rel_funD, OF Cons(4)] KL[THEN rel_funD, OF Cons(5)]
        unfolding pmf.rel_compp pmf.rel_flip by auto
      then obtain p :: "('s \<times> 's) pmf" where p: "\<And>a b. (a, b) \<in> p \<Longrightarrow> (R OO R\<inverse>\<inverse>) a b" and
        eq: "map_pmf fst p = K x" "map_pmf snd p = K x'"
        by (auto simp: pmf.in_rel)
      let ?S = "stream_space (count_space UNIV)"
      have *: "(##) y -` smap f -` sstart (f ` A) (z # zs) = (if f y = z then smap f -` sstart (f ` A) zs else {})" for y z zs
        by auto
      have **: "?D x (sstart (f ` A) (z # zs)) = (\<integral>\<^sup>+ y'. (if f y' = z then ?D y' (sstart (f ` A) zs) else 0) \<partial>K x)" for x
        apply (simp add: emeasure_distr)
        apply (subst K.T_eq_bind)
        apply (subst emeasure_bind[where N="?S"])
           apply simp
          apply (rule measurable_distr2[where M="?S"])
           apply measurable
        apply (intro nn_integral_cong_AE AE_pmfI)
        apply (auto simp add: emeasure_distr)
        apply (simp_all add: * space_stream_space)
        done
      have fst_A: "fst ab \<in> A" if "ab \<in> p" for ab
      proof -
        have "fst ab \<in> K x" using \<open>ab \<in> p\<close> set_map_pmf [of fst p] by (auto simp: eq)
        with \<open>x \<in> A\<close> show "fst ab \<in> A"
          by (auto simp: A_def intro: rtrancl.rtrancl_into_rtrancl)
      qed
      have snd_A: "snd ab \<in> A" if "ab \<in> p" for ab
      proof -
        have "snd ab \<in> K x'" using \<open>ab \<in> p\<close> set_map_pmf [of snd p] by (auto simp: eq)
        with \<open>x' \<in> A\<close> show "snd ab \<in> A"
          by (auto simp: A_def intro: rtrancl.rtrancl_into_rtrancl)
      qed
      show ?case
        unfolding ** eq[symmetric] nn_integral_map_pmf
        apply (intro nn_integral_cong_AE AE_pmfI)
        subgoal for ab using p[of "fst ab" "snd ab"] by (auto simp: R_def intro!: Cons(1) fst_A snd_A)
        done
    qed
  qed

  have L_eq_D: "L.T y = ?D x"
    using \<open>R x y\<close>
  proof (coinduction arbitrary: x y rule: L.T_coinduct)
    case (cont x y)
    then have Kx_Ly: "rel_pmf R (K x) (L y)"
      by (rule KL[THEN rel_funD])
    then have *: "y' \<in> L y \<Longrightarrow> \<exists>x'\<in>K x. R x' y'" for y'
      by (auto dest!: rel_pmf_imp_rel_set simp: rel_set_def)
    have **: "y' \<in> L y \<Longrightarrow> R (g y') y'" for y'
      using *[of y'] unfolding g_def by (auto intro: someI)

    have D_SCons_eq_D_D: "distr (K.T i) K.S (\<lambda>x. z ## smap f x) = distr (?D i) K.S (\<lambda>x. z ## x)" for i z
      by (subst distr_distr) (auto simp: comp_def)
    have D_eq_D_gi: "?D i = ?D (g (f i))" if i: "i \<in> K x" for i
    proof -
      obtain j where "j \<in> L y" "R i j" "f i = j"
        using Kx_Ly i by (force dest!: rel_pmf_imp_rel_set simp: rel_set_def R_def)
      then show ?thesis
        by (auto intro!: D_eq_D[OF \<open>R i j\<close>] g)
    qed

    have ***: "?D x = measure_pmf (L y) \<bind> (\<lambda>y. distr (?D (g y)) K.S ((##) y))"
      apply (subst K.T_eq_bind)
      apply (subst distr_bind[of _ _ K.S])
         apply (rule measurable_distr2[of _  _ "K.S"])
          apply (simp_all add: Pi_iff)
      apply (simp add: distr_distr comp_def L_eq[OF cont] map_pmf_rep_eq)
      apply (subst bind_distr[where K=K.S])
         apply measurable []
        apply (rule measurable_distr2[of _  _ "K.S"])
        apply measurable []
        apply (rule measurable_compose[OF measurable_g])
        apply measurable []
       apply simp
      apply (rule bind_measure_pmf_cong[where N="K.S"])
        apply (auto simp: space_subprob_algebra space_stream_space intro!: K.T.subprob_space_distr)
        unfolding D_SCons_eq_D_D D_eq_D_gi ..
    show ?case
      by (intro exI[of _ "\<lambda>t. distr (K.T (g t)) (stream_space (count_space UNIV)) (smap f)"])
         (auto simp add: K.T.prob_space_distr *** dest: **)
  qed (auto intro: K.T.prob_space_distr)

  have "stream_all2 R s t \<longleftrightarrow> (s \<in> streams S \<and> smap f s = t)" for s t 
  proof safe
    show "stream_all2 R s t \<Longrightarrow> s \<in> streams S"
      apply (coinduction arbitrary: s t)
      subgoal for s t by (cases s; cases t) (auto simp: R_def)
      done
    show "stream_all2 R s t \<Longrightarrow> smap f s = t"
      apply (coinduction arbitrary: s t)
      subgoal for s t by (cases s; cases t) (auto simp: R_def)
      done
  qed (auto intro!: stream.rel_refl_strong simp: stream.rel_map R_def streams_iff_sset)
  then have "\<omega> \<in> streams S \<Longrightarrow> \<omega> \<in> A \<longleftrightarrow> smap f \<omega> \<in> B" for \<omega>
    using AB by (auto simp: rel_set_strong_def)
  with in_S have "K.T x A = K.T x (smap f -` B \<inter> space (K.T x))"
    by (auto intro!: emeasure_eq_AE streams_sets)
  also have "\<dots> = (distr (K.T x) K.S (smap f)) B"
    by (intro emeasure_distr[symmetric]) auto
  also have "\<dots> = (L.T y) B" unfolding L_eq_D ..
  finally show ?thesis .
qed

subsection \<open>Product Construction\<close>

locale MC_pair =
  K1: MC_syntax K1 + K2: MC_syntax K2 for K1 K2
begin

definition "Kp \<equiv> \<lambda>(a, b). pair_pmf (K1 a) (K2 b)"

sublocale MC_syntax Kp .

definition
  "szip\<^sub>E a b \<equiv> \<lambda>(\<omega>1, \<omega>2). szip (K1.force_enabled a \<omega>1) (K2.force_enabled b \<omega>2)"

lemma szip_rT[measurable]: "(\<lambda>(\<omega>1, \<omega>2). szip \<omega>1 \<omega>2) \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) S"
proof (rule measurable_stream_space2)
  fix n
  have "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) = (\<lambda>\<omega>. (fst \<omega> !! n, snd \<omega> !! n))"
    by auto
  also have "\<dots> \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) (count_space UNIV)"
    apply (rule measurable_compose_countable'[OF _ measurable_compose[OF measurable_fst K1.snth_rT, of n]])
    apply (rule measurable_compose_countable'[OF _ measurable_compose[OF measurable_snd K2.snth_rT, of n]])
    apply (auto intro!: K1.countable_acc K2.countable_acc)
    done
  finally show "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) \<in> measurable (K1.rT x1 \<Otimes>\<^sub>M K2.rT x2) (count_space UNIV)"
    .
qed

lemma measurable_szipE[measurable]: "szip\<^sub>E a b \<in> measurable (K1.S \<Otimes>\<^sub>M K2.S) S"
  unfolding szip\<^sub>E_def by measurable

lemma T_eq_prod: "T = (\<lambda>(x1, x2). do { \<omega>1 \<leftarrow> K1.T x1 ; \<omega>2 \<leftarrow> K2.T x2 ; return S (szip\<^sub>E x1 x2 (\<omega>1, \<omega>2)) })"
  (is "_ = ?B")
proof (rule T_bisim)
  have T1x: "\<And>x. subprob_space (K1.T x)"
    by (rule prob_space_imp_subprob_space) unfold_locales

  interpret T12: pair_prob_space "K1.T x" "K2.T y" for x y
    by unfold_locales
  interpret T1K2: pair_prob_space "K1.T x" "K2 y" for x y
    by unfold_locales

  let ?P = "\<lambda>x1 x2. K1.T x1 \<Otimes>\<^sub>M K2.T x2"

  fix x show "prob_space (?B x)"
    by (auto simp: space_stream_space split: prod.splits
                intro!: prob_space.prob_space_bind prob_space_return
                        measurable_bind[where N=S] measurable_compose[OF _ return_measurable] AE_I2)
       unfold_locales

  show "sets (?B x) = sets S"
    by (simp split: prod.splits add: measurable_bind[where N=S] sets_bind[where N=S] space_stream_space)

  obtain a b where x_eq: "x = (a, b)"
    by (cases x) auto
  show "?B x = (measure_pmf (Kp x) \<bind> (\<lambda>s. distr (?B s) S ((##) s)))"
    unfolding x_eq
    apply (subst K1.T_eq_bind')
    apply (subst K2.T_eq_bind')
    apply (auto
         simp add: space_stream_space bind_assoc[where R=S and N=S] bind_return_distr[symmetric]
                   Kp_def T1K2.bind_rotate[where N=S] split_beta' set_pair_pmf space_subprob_algebra
                   bind_pair_pmf[of "case_prod M" for M, unfolded split, symmetric, where N=S] szip\<^sub>E_def
                   stream_eq_Stream_iff bind_return[where N=S] space_bind[where N=S]
         simp del: measurable_pmf_measure1
         intro!: bind_measure_pmf_cong[where N=S] subprob_space_bind[where N=S] subprob_space_measure_pmf
                 T1x bind_cong[where M="MC_syntax.T K x" for K x] arg_cong2[where f=return])
    done
qed

lemma nn_integral_pT:
  fixes f assumes [measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T (x, y)) = (\<integral>\<^sup>+\<omega>1. \<integral>\<^sup>+\<omega>2. f (szip\<^sub>E x y (\<omega>1, \<omega>2)) \<partial>K2.T y \<partial>K1.T x)"
  by (simp add: nn_integral_bind[where B=S] nn_integral_return in_S T_eq_prod)

lemma prod_eq_prob_T:
  assumes [measurable]: "Measurable.pred K1.S P1" "Measurable.pred K2.S P2"
  shows "\<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>) =
    \<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>))"
proof -
  have "\<P>(\<omega> in T (x1, x2). P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>)) =
    (\<integral> x. \<integral> xa. indicator {\<omega> \<in> space S. P1 (smap fst \<omega>) \<and> P2 (smap snd \<omega>)} (szip\<^sub>E x1 x2 (x, xa)) \<partial>MC_syntax.T K2 x2 \<partial>MC_syntax.T K1 x1)"
    by (subst T_eq_prod)
       (simp add: K1.T.measure_bind[where N=S] K2.T.measure_bind[where N=S] measure_return)
  also have "... = (\<integral>\<omega>1. \<integral>\<omega>2. indicator {\<omega>\<in>space K1.S. P1 \<omega>} \<omega>1 * indicator {\<omega>\<in>space K2.S. P2 \<omega>} \<omega>2 \<partial>K2.T x2 \<partial>K1.T x1)"
    apply (intro integral_cong_AE)
    apply measurable
    using K1.AE_T_enabled
    apply eventually_elim
    apply (intro integral_cong_AE)
    apply measurable
    using K2.AE_T_enabled
    apply eventually_elim
    apply (auto simp: space_stream_space szip\<^sub>E_def K1.force_enabled K2.force_enabled
                      smap_szip_snd[where g="\<lambda>x. x"] smap_szip_fst[where f="\<lambda>x. x"]
                split: split_indicator)
    done
  also have "\<dots> = \<P>(\<omega> in K1.T x1. P1 \<omega>) * \<P>(\<omega> in K2.T x2. P2 \<omega>)"
    by simp
  finally show ?thesis ..
qed

end

end
