(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Discrete-time Markov Processes\<close>

text \<open>In this file we construct discrete-time Markov processes, e.g. with arbitrary state spaces.\<close>

theory Discrete_Time_Markov_Process
  imports Markov_Models_Auxiliary
begin

lemma measure_eqI_PiM_sequence:
  fixes M :: "nat \<Rightarrow> 'a measure"
  assumes *[simp]: "sets P = PiM UNIV M" "sets Q = PiM UNIV M"
  assumes eq: "\<And>A n. (\<And>i. A i \<in> sets (M i)) \<Longrightarrow>
    P (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A)) = Q (prod_emb UNIV M {..n} (Pi\<^sub>E {..n} A))"
  assumes A: "finite_measure P"
  shows "P = Q"
proof (rule measure_eqI_PiM_infinite[OF * _ A])
  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets (M i)"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space (M i))" for i
  then have F[simp, measurable]: "F i \<in> sets (M i)" for i
    using J by auto
  have emb_eq: "prod_emb UNIV M J (Pi\<^sub>E J F') = prod_emb UNIV M {..n} (Pi\<^sub>E {..n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  show "emeasure P (prod_emb UNIV M J (Pi\<^sub>E J F')) = emeasure Q (prod_emb UNIV M J (Pi\<^sub>E J F'))"
    unfolding emb_eq by (rule eq) fact
qed

lemma distr_cong_simp:
  "M = K \<Longrightarrow> sets N = sets L \<Longrightarrow> (\<And>x. x \<in> space M =simp=> f x = g x) \<Longrightarrow> distr M N f = distr K L g"
  unfolding simp_implies_def by (rule distr_cong)

subsection \<open>Constructing Discrete-Time Markov Processes\<close>

locale discrete_Markov_process =
  fixes M :: "'a measure" and K :: "'a \<Rightarrow> 'a measure"
  assumes K[measurable]: "K \<in> M \<rightarrow>\<^sub>M prob_algebra M"
begin

lemma space_K: "x \<in> space M \<Longrightarrow> space (K x) = space M"
  using K unfolding prob_algebra_def unfolding measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma sets_K[measurable_cong]: "x \<in> space M \<Longrightarrow> sets (K x) = sets M"
  using K unfolding prob_algebra_def unfolding measurable_restrict_space2_iff
  by (auto dest: subprob_measurableD)

lemma prob_space_K: "x \<in> space M \<Longrightarrow> prob_space (K x)"
  using measurable_space[OF K] by (simp add: space_prob_algebra)

definition K' :: "'a \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a measure"
where
  "K' x n' \<omega>' = K (case_nat x \<omega>' n')"

lemma IT_K':
  assumes x: "x \<in> space M" shows "Ionescu_Tulcea (K' x) (\<lambda>_. M)"
  unfolding Ionescu_Tulcea_def K'_def[abs_def]
proof safe
  fix i show "(\<lambda>\<omega>'. K (case i of 0 \<Rightarrow> x | Suc x \<Rightarrow> \<omega>' x)) \<in> Pi\<^sub>M {0..<i} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra M"
    using x by (intro measurable_prob_algebraD measurable_compose[OF _ K]) measurable
next
  fix i :: nat and \<omega> assume \<omega>: "\<omega> \<in> space (Pi\<^sub>M {0..<i} (\<lambda>_. M))"
  with x have "(case i of 0 \<Rightarrow> x | Suc x \<Rightarrow> \<omega> x) \<in> space M"
    by (auto simp: space_PiM split: nat.split)
  then show "prob_space (K (case i of 0 \<Rightarrow> x | Suc x \<Rightarrow> \<omega> x))"
    using K unfolding measurable_restrict_space2_iff prob_algebra_def by auto
qed

definition lim_sequence :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) measure"
where
  "lim_sequence x = projective_family.lim UNIV (Ionescu_Tulcea.CI (K' x) (\<lambda>_. M)) (\<lambda>_. M)"

lemma
  assumes x: "x \<in> space M"
  shows space_lim_sequence: "space (lim_sequence x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and sets_lim_sequence[measurable_cong]: "sets (lim_sequence x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    and emeasure_lim_sequence_emb: "\<And>J X. finite J \<Longrightarrow> X \<in> sets (\<Pi>\<^sub>M j\<in>J. M) \<Longrightarrow>
      emeasure (lim_sequence x) (prod_emb UNIV (\<lambda>_. M) J X) =
      emeasure (Ionescu_Tulcea.CI (K' x) (\<lambda>_. M) J) X"
    and emeasure_lim_sequence_emb_I0o: "\<And>n X. X \<in> sets (\<Pi>\<^sub>M i \<in> {0..<n}. M) \<Longrightarrow>
      emeasure (lim_sequence x) (prod_emb UNIV (\<lambda>_. M) {0..<n} X) =
      emeasure (Ionescu_Tulcea.C (K' x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) X"
proof -
  interpret Ionescu_Tulcea "K' x" "\<lambda>_. M"
    using x by (rule IT_K')
  show "space (lim_sequence x) = space (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp
  show "sets (lim_sequence x) = sets (\<Pi>\<^sub>M i\<in>UNIV. M)"
    unfolding lim_sequence_def by simp

  { fix J :: "nat set" and X assume "finite J" "X \<in> sets (\<Pi>\<^sub>M j\<in>J. M)"
    then show "emeasure (lim_sequence x) (PF.emb UNIV J X) = emeasure (CI J) X"
      unfolding lim_sequence_def by (rule lim) }
  note emb = this

  have up_to_I0o[simp]: "up_to {0..<n} = n" for n
    unfolding up_to_def by (rule Least_equality) auto

  { fix n :: nat and X assume "X \<in> sets (\<Pi>\<^sub>M j\<in>{0..<n}. M)"
    then show "emeasure (lim_sequence x) (PF.emb UNIV {0..<n} X) = emeasure (C 0 n (\<lambda>x. undefined)) X"
      by (simp add: space_C emb CI_def space_PiM distr_id2 sets_C cong: distr_cong_simp) }
qed

lemma lim_sequence[measurable]: "lim_sequence \<in> M \<rightarrow>\<^sub>M prob_algebra (\<Pi>\<^sub>M i\<in>UNIV. M)"
proof (intro measurable_prob_algebra_generated[OF sets_PiM Int_stable_prod_algebra prod_algebra_sets_into_space])
  fix a assume [simp]: "a \<in> space M"
  interpret Ionescu_Tulcea "K' a" "\<lambda>_. M"
    by (rule IT_K') simp
  have sp: "space (lim_sequence a) = prod_emb UNIV (\<lambda>_. M) {} (\<Pi>\<^sub>E j\<in>{}. space M)" "space (CI {}) = {} \<rightarrow>\<^sub>E space M"
    by (auto simp: space_lim_sequence space_PiM prod_emb_def PF.space_P)
  show "prob_space (lim_sequence a)"
    apply standard
    using PF.prob_space_P[THEN prob_space.emeasure_space_1, of "{}"]
    apply (simp add: sp emeasure_lim_sequence_emb del: PiE_empty_domain)
    done
  show "sets (lim_sequence a) = sets (Pi\<^sub>M UNIV (\<lambda>i. M))"
    by (simp add: sets_lim_sequence)
next
  fix X :: "(nat \<Rightarrow> 'a) set" assume "X \<in> prod_algebra UNIV (\<lambda>i. M)"
  then obtain J :: "nat set" and F where J: "J \<noteq> {}" "finite J" "F \<in> J \<rightarrow> sets M"
    and X: "X = prod_emb UNIV (\<lambda>_. M) J (Pi\<^sub>E J F)"
    unfolding prod_algebra_def by auto
  then have Pi_F: "finite J" "Pi\<^sub>E J F \<in> sets (Pi\<^sub>M J (\<lambda>_. M))"
    by (auto intro: sets_PiM_I_finite)

  define n where "n = (LEAST n. \<forall>i\<ge>n. i \<notin> J)"
  have J_le_n: "J \<subseteq> {0..<n}"
    unfolding n_def
    using \<open>finite J\<close>
    apply -
    apply (rule LeastI2[of _ "Suc (Max J)"])
    apply (auto simp: Suc_le_eq not_le[symmetric])
    done

  have C: "(\<lambda>x. Ionescu_Tulcea.C (K' x) (\<lambda>_. M) 0 n (\<lambda>x. undefined)) \<in> M \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    apply (induction n)
    apply (subst measurable_cong)
    apply (rule Ionescu_Tulcea.C.simps[OF IT_K'])
    apply assumption
    apply (rule measurable_compose[OF _ return_measurable])
    apply simp
    apply (subst measurable_cong)
    apply (rule Ionescu_Tulcea.C.simps[OF IT_K'])
    apply assumption
    apply (rule measurable_bind')
    apply assumption
    apply (subst measurable_cong)
  proof -
    fix n :: nat and w assume "w \<in> space (M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M))"
    then show "(case w of (x, xa) \<Rightarrow> Ionescu_Tulcea.eP (K' x) (\<lambda>_. M) (0 + n) xa) =
      (case w of (x, xa) \<Rightarrow> distr (K' x n xa) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) (fun_upd xa n))"
      by (auto simp: space_pair_measure Ionescu_Tulcea.eP_def[OF IT_K'] split: prod.split)
  next
    fix n show "(\<lambda>w. case w of (x, xa) \<Rightarrow> distr (K' x n xa) (Pi\<^sub>M {0..<Suc n} (\<lambda>i. M)) (fun_upd xa n))
         \<in> M \<Otimes>\<^sub>M Pi\<^sub>M {0..<n} (\<lambda>_. M) \<rightarrow>\<^sub>M subprob_algebra (Pi\<^sub>M {0..<Suc n} (\<lambda>_. M))"
      unfolding K'_def
      apply measurable
      apply (rule measurable_distr2[where M=M])
      apply (rule measurable_PiM_single')
      apply (simp add: split_beta')
      subgoal for i by (cases "i = n") auto
      subgoal by (auto simp: split_beta' PiE_iff extensional_def Pi_iff space_pair_measure space_PiM)
      apply (rule measurable_prob_algebraD)
      apply (rule measurable_compose[OF _ K])
      apply measurable
      done
  qed

  have "(\<lambda>a. emeasure (lim_sequence a) X) \<in> borel_measurable M \<longleftrightarrow>
    (\<lambda>a. emeasure (Ionescu_Tulcea.CI (K' a) (\<lambda>_. M) J) (Pi\<^sub>E J F)) \<in> borel_measurable M"
    unfolding X using J Pi_F by (intro measurable_cong emeasure_lim_sequence_emb) auto
  also have "\<dots>"
    apply (intro measurable_compose[OF _ measurable_emeasure_subprob_algebra[OF Pi_F(2)]])
    apply (subst measurable_cong)
    apply (subst Ionescu_Tulcea.CI_def[OF IT_K'])
    apply assumption
    apply (subst Ionescu_Tulcea.up_to_def[OF IT_K'])
    apply assumption
    unfolding n_def[symmetric]
    apply (rule refl)
    apply (rule measurable_compose[OF _ measurable_distr[OF measurable_restrict_subset[OF J_le_n]]])
    apply (rule C)
    done
  finally show "(\<lambda>a. emeasure (lim_sequence a) X) \<in> borel_measurable M" .
qed

lemma step_C:
  assumes x: "x \<in> space M"
  shows "Ionescu_Tulcea.C (K' x) (\<lambda>_. M) 0 1 (\<lambda>_. undefined) \<bind> Ionescu_Tulcea.C (K' x) (\<lambda>_. M) 1 n =
    K x \<bind> (\<lambda>y. Ionescu_Tulcea.C (K' x) (\<lambda>_. M) 1 n (case_nat y (\<lambda>_. undefined)))"
proof -
  interpret Ionescu_Tulcea "K' x" "\<lambda>_. M"
    using x by (rule IT_K')

  have [simp]: "space (K x) \<noteq> {}"
    using space_K[OF x] x by auto

  have [simp]: "((\<lambda>_. undefined::'a)(0 := x)) = case_nat x (\<lambda>_. undefined)" for x
    by (auto simp: fun_eq_iff split: nat.split)

  have "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = eP 0 (\<lambda>_. undefined) \<bind> C 1 n"
    using measurable_eP[of 0] measurable_C[of 1 n, measurable del]
    by (simp add: bind_return[where N="Pi\<^sub>M {0} (\<lambda>_. M)"])
  also have "\<dots> = K x \<bind> (\<lambda>y. C 1 n (case_nat y (\<lambda>_. undefined)))"
    using measurable_C[of 1 n, measurable del] x[THEN sets_K]
    by (simp add: eP_def K'_def bind_distr cong: measurable_cong_sets)
  finally show "C 0 1 (\<lambda>_. undefined) \<bind> C 1 n = K x \<bind> (\<lambda>y. C 1 n (case_nat y (\<lambda>_. undefined)))" .
qed

lemma lim_sequence_eq:
  assumes x: "x \<in> space M"
  shows "lim_sequence x = bind (K x) (\<lambda>y. distr (lim_sequence y) (\<Pi>\<^sub>M j\<in>UNIV. M) (case_nat y))"
    (is "_ = ?B x")
proof (rule measure_eqI_PiM_infinite)
  show "sets (lim_sequence x) = sets (\<Pi>\<^sub>M j\<in>UNIV. M)"
    using x by (rule sets_lim_sequence)
  have [simp]: "space (K x) \<noteq> {}"
    using space_K[OF x] x by auto
  show "sets (?B x) = sets (Pi\<^sub>M UNIV (\<lambda>j. M))"
    using x by (subst sets_bind) auto
  interpret lim_sequence: prob_space "lim_sequence x"
    using lim_sequence x by (auto simp: measurable_restrict_space2_iff prob_algebra_def)
  show "finite_measure (lim_sequence x)"
    by (rule lim_sequence.finite_measure)

  interpret Ionescu_Tulcea "K' x" "\<lambda>_. M"
    using x by (rule IT_K')

  let ?U = "\<lambda>_::nat. undefined :: 'a"

  fix J :: "nat set" and F'
  assume J: "finite J" "\<And>i. i \<in> J \<Longrightarrow> F' i \<in> sets M"

  define n where "n = (if J = {} then 0 else Max J)"
  define F where "F i = (if i \<in> J then F' i else space M)" for i
  then have F[simp, measurable]: "F i \<in> sets M" for i
    using J by auto
  have emb_eq: "PF.emb UNIV J (Pi\<^sub>E J F') = PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F)"
  proof cases
    assume "J = {}" then show ?thesis
      by (auto simp add: n_def F_def[abs_def] prod_emb_def PiE_def)
  next
    assume "J \<noteq> {}" then show ?thesis
      by (auto simp: prod_emb_def PiE_iff F_def n_def less_Suc_eq_le \<open>finite J\<close> split: if_split_asm)
  qed

  have "emeasure (lim_sequence x) (PF.emb UNIV J (Pi\<^sub>E J F')) = emeasure (C 0 (Suc n) ?U) (Pi\<^sub>E {0..<Suc n} F)"
    using x unfolding emb_eq by (rule emeasure_lim_sequence_emb_I0o) (auto intro!: sets_PiM_I_finite)
  also have "C 0 (Suc n) ?U = K x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))"
    using split_C[of ?U 0 "Suc 0" n] step_C[OF x] by simp
  also have "emeasure (K x \<bind> (\<lambda>y. C 1 n (case_nat y ?U))) (Pi\<^sub>E {0..<Suc n} F) =
    (\<integral>\<^sup>+y. C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) \<partial>K x)"
    using measurable_C[of 1 n, measurable del] x[THEN sets_K] F x
    by (intro emeasure_bind[OF  _ measurable_compose[OF _ measurable_C]])
       (auto cong: measurable_cong_sets intro!: measurable_PiM_single' split: nat.split_asm)
  also have "\<dots> = (\<integral>\<^sup>+y. distr (lim_sequence y) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y) (PF.emb UNIV J (Pi\<^sub>E J F')) \<partial>K x)"
  proof (intro nn_integral_cong)
    fix y assume "y \<in> space (K x)"
    then have y: "y \<in> space M"
      using x by (simp add: space_K)
    then interpret y: Ionescu_Tulcea "K' y" "\<lambda>_. M"
      by (rule IT_K')

    let ?y = "case_nat y"
    have [simp]: "?y ?U \<in> space (Pi\<^sub>M {0} (\<lambda>i. M))"
      using y by (auto simp: space_PiM PiE_iff extensional_def split: nat.split)
    have yM[measurable]: "?y \<in> Pi\<^sub>M {0..<m} (\<lambda>_. M) \<rightarrow>\<^sub>M Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)" for m
      using y by (intro measurable_PiM_single') (auto simp: space_PiM PiE_iff extensional_def split: nat.split)

    have y': "?y ?U \<in> space (Pi\<^sub>M {0..<1} (\<lambda>i. M))"
      by (simp add: space_PiM PiE_def y extensional_def split: nat.split)

    have eq1: "?y -` Pi\<^sub>E {0..<Suc n} F \<inter> space (Pi\<^sub>M {0..<n} (\<lambda>_. M)) =
        (if y \<in> F 0 then Pi\<^sub>E {0..<n} (F\<circ>Suc) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff extensional_def Ball_def split: nat.split nat.split_asm)

    have eq2: "?y -` PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F) \<inter> space (Pi\<^sub>M UNIV (\<lambda>_. M)) =
        (if y \<in> F 0 then PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F\<circ>Suc)) else {})"
      unfolding set_eq_iff using y sets.sets_into_space[OF F]
      by (auto simp: space_PiM PiE_iff prod_emb_def extensional_def Ball_def split: nat.split nat.split_asm)

    let ?I = "indicator (F 0) y"

    have "C 1 n (?y ?U) = distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y"
    proof (induction n)
      case (Suc m)

      have "C 1 (Suc m) (?y ?U) = distr (y.C 0 m ?U) (Pi\<^sub>M {0..<Suc m} (\<lambda>i. M)) ?y \<bind> eP (Suc m)"
        using Suc by simp
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. eP (Suc m) (?y x))"
        by (intro bind_distr[where K="Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>_. M)"]) (simp_all add: y y.space_C y.sets_C cong: measurable_cong_sets)
      also have "\<dots> = y.C 0 m ?U \<bind> (\<lambda>x. distr (y.eP m x) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y)"
      proof (intro bind_cong refl)
        fix \<omega>' assume \<omega>': "\<omega>' \<in> space (y.C 0 m ?U)"
        moreover have "K' x (Suc m) (?y \<omega>') = K' y m \<omega>'"
          by (auto simp: K'_def)
        ultimately show "eP (Suc m) (?y \<omega>') = distr (y.eP m \<omega>') (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
          unfolding eP_def y.eP_def
          by (subst distr_distr)
             (auto simp: y.space_C y.sets_P split: nat.split cong: measurable_cong_sets
                   intro!: distr_cong measurable_fun_upd[where J="{0..<m}"])
      qed
      also have "\<dots> = distr (y.C 0 m ?U \<bind> y.eP m) (Pi\<^sub>M {0..<Suc (Suc m)} (\<lambda>i. M)) ?y"
        by (intro distr_bind[symmetric, OF _ _ yM]) (auto simp: y.space_C y.sets_C cong: measurable_cong_sets)
      finally show ?case
        by simp
    qed (use y in \<open>simp add: PiM_empty distr_return\<close>)
    then have "C 1 n (case_nat y ?U) (Pi\<^sub>E {0..<Suc n} F) =
      (distr (y.C 0 n ?U) (\<Pi>\<^sub>M i\<in>{0..<Suc n}. M) ?y) (Pi\<^sub>E {0..<Suc n} F)" by simp
    also have "\<dots> = ?I * y.C 0 n ?U (Pi\<^sub>E {0..<n} (F \<circ> Suc))"
      by (subst emeasure_distr) (auto simp: y.sets_C y.space_C eq1 cong: measurable_cong_sets)
    also have "\<dots> = ?I * lim_sequence y (PF.emb UNIV {0..<n} (Pi\<^sub>E {0..<n} (F \<circ> Suc)))"
      using y by (simp add: emeasure_lim_sequence_emb_I0o sets_PiM_I_finite)
    also have "\<dots> = distr (lim_sequence y) (Pi\<^sub>M UNIV (\<lambda>j. M)) ?y (PF.emb UNIV {0..<Suc n} (Pi\<^sub>E {0..<Suc n} F))"
      using y by (subst emeasure_distr) (simp_all add: eq2 space_lim_sequence)
    finally show "emeasure (C 1 n (case_nat y (\<lambda>_. undefined))) (Pi\<^sub>E {0..<Suc n} F) =
        emeasure (distr (lim_sequence y) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)) (PF.emb UNIV J (Pi\<^sub>E J F'))"
      unfolding emb_eq .
  qed
  also have "\<dots> =
    emeasure (K x \<bind> (\<lambda>y. distr (lim_sequence y) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y))) (PF.emb UNIV J (Pi\<^sub>E J F'))"
    using J
    by (subst emeasure_bind[where N="PiM UNIV (\<lambda>_. M)"])
       (auto simp: sets_K x intro!: measurable_distr2[OF _ measurable_prob_algebraD[OF lim_sequence]] cong: measurable_cong_sets)
  finally show "emeasure (lim_sequence x) (PF.emb UNIV J (Pi\<^sub>E J F')) =
    emeasure (K x \<bind> (\<lambda>y. distr (lim_sequence y) (Pi\<^sub>M UNIV (\<lambda>j. M)) (case_nat y)))
            (PF.emb UNIV J (Pi\<^sub>E J F'))" .
qed

lemma AE_lim_sequence:
  assumes x[simp]: "x \<in> space M" and P[measurable]: "Measurable.pred (\<Pi>\<^sub>M i\<in>UNIV. M) P"
  shows "(AE \<omega> in lim_sequence x. P \<omega>) \<longleftrightarrow> (AE y in K x. AE \<omega> in lim_sequence y. P (case_nat y \<omega>))"
  apply (simp add: lim_sequence_eq cong del: AE_cong)
  apply (subst AE_bind)
  apply (rule measurable_prob_algebraD)
  apply measurable
  apply (auto intro!: AE_cong simp add: space_K AE_distr_iff)
  done

definition lim_stream :: "'a \<Rightarrow> 'a stream measure"
where
  "lim_stream x = distr (lim_sequence x) (stream_space M) to_stream"

lemma space_lim_stream: "space (lim_stream x) = streams (space M)"
  unfolding lim_stream_def by (simp add: space_stream_space)

lemma sets_lim_stream[measurable_cong]: "sets (lim_stream x) = sets (stream_space M)"
  unfolding lim_stream_def by simp

lemma lim_stream[measurable]: "lim_stream \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
  unfolding lim_stream_def[abs_def] by (intro measurable_distr_prob_space2[OF lim_sequence]) auto

lemma space_stream_space_M_ne: "x \<in> space M \<Longrightarrow> space (stream_space M) \<noteq> {}"
  using sconst_streams[of x "space M"] by (auto simp: space_stream_space)

lemma prob_space_lim_stream: "x \<in> space M \<Longrightarrow> prob_space (lim_stream x)"
  using measurable_space[OF lim_stream, of x] by (simp add: space_prob_algebra)

lemma lim_stream_eq:
  assumes x: "x \<in> space M"
  shows "lim_stream x = do { y \<leftarrow> K x; \<omega> \<leftarrow> lim_stream y; return (stream_space M) (y ## \<omega>) }"
  unfolding lim_stream_def
  apply (subst lim_sequence_eq[OF x])
  apply (subst distr_bind[OF _ _ measurable_to_stream])
  subgoal
    by (auto simp: sets_K x cong: measurable_cong_sets
             intro!: measurable_prob_algebraD measurable_distr_prob_space2[where M="Pi\<^sub>M UNIV (\<lambda>j. M)"] lim_sequence) []
  subgoal
    using x by (auto simp add: space_K)
  apply (intro bind_cong refl)
  apply (subst distr_distr)
  apply (auto simp: space_K sets_lim_sequence x cong: measurable_cong_sets intro!: distr_cong)
  apply (subst bind_return_distr')
  apply (auto simp: space_stream_space_M_ne)
  apply (subst distr_distr)
  apply (auto simp: space_K sets_lim_sequence x to_stream_nat_case cong: measurable_cong_sets intro!: distr_cong)
  done

lemma AE_lim_stream:
  assumes x[simp]: "x \<in> space M" and P[measurable]: "Measurable.pred (stream_space M) P"
  shows "(AE \<omega> in lim_stream x. P \<omega>) \<longleftrightarrow> (AE y in K x. AE \<omega> in lim_stream y. P (y ## \<omega>))"
  unfolding lim_stream_eq[OF x]
  by (simp_all add: space_K space_lim_stream space_stream_space AE_return AE_bind[OF measurable_prob_algebraD P] cong: AE_cong_simp)

lemma emeasure_lim_stream:
  assumes x[measurable, simp]: "x \<in> space M" and A[measurable, simp]: "A \<in> sets (stream_space M)"
  shows "lim_stream x A = (\<integral>\<^sup>+y. emeasure (lim_stream y) (((##) y) -` A \<inter> space (stream_space M)) \<partial>K x)"
  apply (subst lim_stream_eq, simp)
  apply (subst emeasure_bind[OF _ _ A], simp add: prob_space.not_empty prob_space_K)
   apply (rule measurable_prob_algebraD)
   apply measurable
  apply (intro nn_integral_cong)
  apply (subst bind_return_distr')
    apply (auto intro!: prob_space.not_empty prob_space_lim_stream simp: space_K emeasure_distr)
  apply (simp add: space_lim_stream space_stream_space)
  done

lemma lim_stream_eq_coinduct[case_names in_space step]:
  fixes R :: "'a \<Rightarrow> 'a stream measure \<Rightarrow> bool"
  assumes x: "R x B" "x \<in> space M"
  assumes R: "\<And>x B. R x B \<Longrightarrow> \<exists>B'\<in>M \<rightarrow>\<^sub>M prob_algebra (stream_space M).
    (AE y in K x. R y (B' y) \<or> lim_stream y = B' y) \<and>
    B = do { y \<leftarrow> K x; \<omega> \<leftarrow> B' y; return (stream_space M) (y ## \<omega>) }"
  shows "lim_stream x = B"
  using x
proof (coinduction arbitrary: x B rule: stream_space_coinduct[where M=M, case_names step])
  case (step x B)
  from R[OF \<open>R x B\<close>] obtain B' where B': "B' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
    and ae: "AE y in K x. R y (B' y) \<or> lim_stream y = B' y"
    and eq: "B = K x \<bind> (\<lambda>y. B' y \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>)))"
    by blast
  show ?case
    apply (rule bexI[of _ "K x"], rule bexI[OF _ lim_stream], rule bexI[OF _ B'])
    apply (intro conjI)
    subgoal
      using ae AE_space by eventually_elim (insert \<open>x\<in>space M\<close>, auto simp: space_K)
    subgoal
      by (rule lim_stream_eq) fact
    subgoal
      by (rule eq)
    subgoal
      using K \<open>x \<in> space M\<close> by (rule measurable_space)
    done
qed

lemma prob_space_lim_sequence: "x \<in> space M \<Longrightarrow> prob_space (lim_sequence x)"
  using measurable_space[OF lim_sequence, of x] by (simp add: space_prob_algebra)

end

subsection \<open>Strong Markov Property for Discrete-Time Markov Processes\<close>

text \<open>The filtration adopted to streams, i.e. to the $n$-th projection.\<close>

definition stream_filtration :: "'a measure \<Rightarrow> enat \<Rightarrow> 'a stream measure"
  where "stream_filtration M n = (SUP i\<in>{i::nat. i \<le> n}. vimage_algebra (streams (space M)) (\<lambda>\<omega> . \<omega> !! i) M)"

lemma measurable_stream_filtration1: "enat i \<le> n \<Longrightarrow> (\<lambda>\<omega>. \<omega> !! i) \<in> stream_filtration M n \<rightarrow>\<^sub>M M"
  by (auto intro!: measurable_SUP1 measurable_vimage_algebra1 snth_in simp: stream_filtration_def)

lemma measurable_stream_filtration2:
  "f \<in> space N \<rightarrow> streams (space M) \<Longrightarrow> (\<And>i. enat i \<le> n \<Longrightarrow> (\<lambda>x. f x !! i) \<in> N \<rightarrow>\<^sub>M M) \<Longrightarrow> f \<in> N \<rightarrow>\<^sub>M stream_filtration M n"
  by (auto simp: stream_filtration_def enat_0
           intro!: measurable_SUP2 measurable_vimage_algebra2 elim!: allE[of _ "0::nat"])

lemma space_stream_filtration: "space (stream_filtration M n) = space (stream_space M)"
  by (auto simp add: space_stream_space space_Sup_eq_UN stream_filtration_def enat_0 elim!: allE[of _ 0])

lemma sets_stream_filteration_le_stream_space: "sets (stream_filtration M n) \<subseteq> sets (stream_space M)"
  unfolding sets_stream_space_eq stream_filtration_def
  by (intro SUP_subset_mono le_measureD2) (auto simp: space_Sup_eq_UN enat_0 elim!: allE[of _ 0])

interpretation stream_filtration: filtration "space (stream_space M)" "stream_filtration M"
proof
  show "space (stream_filtration M i) = space (stream_space M)" for i
    by (simp add: space_stream_filtration)
  show "sets (stream_filtration M i) \<subseteq> sets (stream_filtration M j)" if "i \<le> j" for i j
  proof (rule le_measureD2)
    show "stream_filtration M i \<le> stream_filtration M j"
      using \<open>i \<le> j\<close> unfolding stream_filtration_def by (intro SUP_subset_mono) auto
  qed (simp add: space_stream_filtration)
qed

lemma measurable_stopping_time_stream:
  "stopping_time (stream_filtration M) T \<Longrightarrow> T \<in> stream_space M \<rightarrow>\<^sub>M count_space UNIV"
  using sets_stream_filteration_le_stream_space
  by (subst measurable_cong_sets[OF refl sets_borel_eq_count_space[symmetric, where 'a=enat]])
     (auto intro!: measurable_stopping_time simp: space_stream_filtration)

lemma measurable_stopping_time_All_eq_0:
  assumes T: "stopping_time (stream_filtration M) T"
  shows "{x\<in>space M. \<forall>\<omega>\<in>streams (space M). T (x ## \<omega>) = 0} \<in> sets M"
proof -
  have "{\<omega>\<in>streams (space M). T \<omega> = 0} \<in> vimage_algebra (streams (space M)) (\<lambda>\<omega>. \<omega> !! 0) M"
    using stopping_timeD[OF T, of 0] by (simp add: stream_filtration_def pred_def enat_0_iff)
  then obtain A
    where A: "A \<in> sets M"
      and *: "{\<omega> \<in> streams (space M). T \<omega> = 0} = (\<lambda>\<omega>. \<omega> !! 0) -` A \<inter> streams (space M)"
    by (auto simp: sets_vimage_algebra2 streams_shd)
  have "A = {x\<in>space M. \<forall>\<omega>\<in>streams (space M). T (x ## \<omega>) = 0}"
  proof safe
    fix x \<omega> assume "x \<in> A" "\<omega> \<in> streams (space M)"
    then have "x ## \<omega> \<in> {\<omega> \<in> streams (space M). T \<omega> = 0}"
      unfolding * using A[THEN sets.sets_into_space] by auto
    then show "T (x ## \<omega>) = 0" by auto
  next
    fix x assume "x \<in> space M" "\<forall>\<omega>\<in>streams (space M). T (x ## \<omega>) = 0 "
    then have "\<forall>\<omega>\<in>streams (space M). x ## \<omega> \<in> {\<omega> \<in> streams (space M). T \<omega> = 0}"
      by simp
    with \<open>x\<in>space M\<close> show "x \<in> A"
      unfolding * by (auto simp: streams_empty_iff)
  qed (use A[THEN sets.sets_into_space] in auto)
  with \<open>A \<in> sets M\<close> show ?thesis by auto
qed

lemma stopping_time_0:
  assumes T: "stopping_time (stream_filtration M) T"
    and x: "x \<in> space M" and \<omega>: "\<omega> \<in> streams (space M)" "T (x ## \<omega>) > 0"
    and \<omega>': "\<omega>' \<in> streams (space M)"
  shows "T (x ## \<omega>') > 0"
  unfolding zero_less_iff_neq_zero
proof
  assume "T (x ## \<omega>') = 0"
  with x \<omega>' have x': "x ## \<omega>' \<in> {\<omega> \<in> streams (space M). T \<omega> = 0}"
    by auto

  have "{\<omega>\<in>streams (space M). T \<omega> = 0} \<in> vimage_algebra (streams (space M)) (\<lambda>\<omega>. \<omega> !! 0) M"
    using stopping_timeD[OF T, of 0] by (simp add: stream_filtration_def pred_def enat_0_iff)
  then obtain A
    where A: "A \<in> sets M"
      and *: "{\<omega> \<in> streams (space M). T \<omega> = 0} = (\<lambda>\<omega>. \<omega> !! 0) -` A \<inter> streams (space M)"
    by (auto simp: sets_vimage_algebra2 streams_shd)
  with x' have "x \<in> A"
    by auto
  with \<omega> x have "x ## \<omega> \<in> (\<lambda>\<omega>. \<omega> !! 0) -` A \<inter> streams (space M)"
    by auto
  with \<omega> show False
    unfolding *[symmetric] by auto
qed

lemma stopping_time_epred_SCons:
  assumes T: "stopping_time (stream_filtration M) T"
    and x: "x \<in> space M" and \<omega>: "\<omega> \<in> streams (space M)" "T (x ## \<omega>) > 0"
  shows "stopping_time (stream_filtration M) (\<lambda>\<omega>. epred (T (x ## \<omega>)))"
proof (rule stopping_timeI, rule measurable_cong[THEN iffD2])
  show "\<omega> \<in> space (stream_filtration M t) \<Longrightarrow> (epred (T (x ## \<omega>)) \<le> t) = (T (x ## \<omega>) \<le> eSuc t)" for t \<omega>
    by (cases "T (x ## \<omega>)" rule: enat_coexhaust)
       (auto simp add: space_stream_filtration space_stream_space dest!: stopping_time_0[OF T x \<omega>])
  show "Measurable.pred (stream_filtration M t) (\<lambda>w. T (x ## w) \<le> eSuc t)" for t
  proof (rule measurable_compose[of "SCons x"])
    show "(##) x \<in> stream_filtration M t \<rightarrow>\<^sub>M stream_filtration M (eSuc t)"
    proof (intro measurable_stream_filtration2)
      show "enat i \<le> eSuc t \<Longrightarrow> (\<lambda>xa. (x ## xa) !! i) \<in> stream_filtration M t \<rightarrow>\<^sub>M M" for i
        using \<open>x\<in>space M\<close>
        by (cases i) (auto simp: eSuc_enat[symmetric] intro!: measurable_stream_filtration1)
    qed (auto simp: space_stream_filtration space_stream_space \<open>x\<in>space M\<close>)
  qed (rule T[THEN stopping_timeD])
qed

context discrete_Markov_process
begin

lemma lim_stream_strong_Markov:
  assumes x: "x \<in> space M" and T: "stopping_time (stream_filtration M) T"
  shows "lim_stream x =
    lim_stream x \<bind> (\<lambda>\<omega>. case T \<omega> of
      enat i \<Rightarrow> distr (lim_stream (\<omega> !! i)) (stream_space M) (\<lambda>\<omega>'. stake (Suc i) \<omega> @- \<omega>')
    | \<infinity>     \<Rightarrow> return (stream_space M) \<omega>)"
  (is "_ = ?L T x")
  using assms
proof (coinduction arbitrary: x T rule: lim_stream_eq_coinduct)
  case (step x T)
  note T = \<open>stopping_time (stream_filtration M) T\<close>[THEN measurable_stopping_time_stream, measurable]
  define L where "L T x = ?L T x" for T x
  have L[measurable (raw)]:
    "(\<lambda>(x, \<omega>). T x \<omega>) \<in> N \<Otimes>\<^sub>M stream_space M \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow>
    f \<in> N \<rightarrow>\<^sub>M M \<Longrightarrow> (\<lambda>x. L (T x) (f x)) \<in> N \<rightarrow>\<^sub>M prob_algebra (stream_space M)" for f :: "'a \<Rightarrow> 'a" and N T
    unfolding L_def
    by (intro measurable_bind_prob_space2[OF measurable_compose[OF _ lim_stream]] measurable_case_enat
        measurable_distr_prob_space2[OF measurable_compose[OF _ lim_stream]]
        measurable_return_prob_space measurable_stopping_time_stream)
       auto

  define S where "S x = (if \<forall>\<omega>\<in>streams (space M). T (x##\<omega>) = 0 then lim_stream x else L (\<lambda>\<omega>. epred (T (x ## \<omega>))) x)" for x
  then have S_eq: "\<forall>\<omega>\<in>streams (space M). T (x##\<omega>) = 0 \<Longrightarrow> S x = lim_stream x"
    "\<not> (\<forall>\<omega>\<in>streams (space M). T (x##\<omega>) = 0) \<Longrightarrow> S x = L (\<lambda>\<omega>. epred (T (x ## \<omega>))) x" for x
    by auto
  have [measurable]: "S \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
    unfolding S_def[abs_def]
    by (subst measurable_If_restrict_space_iff, safe intro!: L)
       (auto intro!: measurable_stopping_time_All_eq_0 step measurable_restrict_space1 lim_stream
                     measurable_compose[OF _ measurable_epred] measurable_compose[OF _ T]
                     measurable_Stream measurable_compose[OF measurable_fst]
             simp: measurable_split_conv)

  show ?case
    unfolding L_def[symmetric]
  proof (intro bexI[of _ S] conjI AE_I2)
    fix y assume "y \<in> space (K x)"
    then show "(\<exists>x T. y = x \<and> S y = L T x \<and> x \<in> space M \<and> stopping_time (stream_filtration M) T) \<or>
      lim_stream y = S y"
      using \<open>x\<in>space M\<close>
      by (cases "\<forall>\<omega>\<in>streams (space M). T (y##\<omega>) = 0")
         (auto simp add: S_eq space_K intro!: exI[of _ "\<lambda>\<omega>. epred (T (y ## \<omega>))"] stopping_time_epred_SCons step)
  next
    note \<open>x\<in>space M\<close>[simp]
    have "L T x = K x \<bind>
      (\<lambda>y. lim_stream y \<bind> (\<lambda>\<omega>. case T (y##\<omega>) of
            enat i \<Rightarrow> distr (lim_stream ((y##\<omega>) !! i)) (stream_space M) (\<lambda>\<omega>'. stake (Suc i) (y##\<omega>) @- \<omega>')
          | \<infinity>     \<Rightarrow> return (stream_space M) (y##\<omega>)))" (is "_ = K x \<bind> ?L'")
      unfolding L_def
      apply (subst lim_stream_eq[OF \<open>x\<in>space M\<close>])
      apply (subst bind_assoc[where N="stream_space M" and R="stream_space M", OF measurable_prob_algebraD measurable_prob_algebraD];
          measurable)
      apply (rule bind_cong[OF refl])
      apply (simp add: space_K)
      apply (subst bind_assoc[where N="stream_space M" and R="stream_space M", OF measurable_prob_algebraD measurable_prob_algebraD];
          measurable)
      apply (rule bind_cong[OF refl])
      apply (simp add: space_lim_stream)
      apply (subst bind_return[where N="stream_space M", OF measurable_prob_algebraD])
        apply (measurable; fail) []
       apply (simp add: space_stream_space)
      apply rule
      done
    also have "\<dots> = K x \<bind> (\<lambda>y. S y \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>)))"
    proof (intro bind_cong[of "K x"] refl)
      fix y assume "y \<in> space (K x)"
      then have [simp]: "y \<in> space M"
        by (simp add: space_K)
      show "?L' y = S y \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>))"
      proof cases
        assume "\<forall>\<omega>\<in>streams (space M). T (y##\<omega>) = 0"
        with x show ?thesis
          by (auto simp: S_eq space_lim_stream shift.simps[abs_def] streams_empty_iff
                bind_const'[OF _ prob_space_imp_subprob_space] prob_space_lim_stream prob_space.prob_space_distr
              intro!: bind_return_distr'[symmetric]
              cong: bind_cong_simp)
      next
        assume *: "\<not> (\<forall>\<omega>\<in>streams (space M). T (y##\<omega>) = 0)"
        then have T_pos: "\<omega> \<in> streams (space M) \<Longrightarrow> T (y ## \<omega>) \<noteq> 0" for \<omega>
          using stopping_time_0[OF \<open>stopping_time (stream_filtration M) T\<close>, of y _ \<omega>] by auto
        show ?thesis
          apply (simp add: S_eq(2)[OF *] L_def)
          apply (subst bind_assoc[where N="stream_space M" and R="stream_space M", OF measurable_prob_algebraD measurable_prob_algebraD];
            measurable)
          apply (intro bind_cong refl)
          apply (auto simp: T_pos enat_0 space_lim_stream shift.simps[abs_def] diff_Suc space_stream_space
                      intro!: bind_return[where N="stream_space M", OF measurable_prob_algebraD, symmetric]
                        bind_distr_return[symmetric]
                      split: nat.split enat.split)
          done
      qed
    qed
    finally show "L T x = K x \<bind> (\<lambda>y. S y \<bind> (\<lambda>\<omega>. return (stream_space M) (y ## \<omega>)))" .
  qed fact
qed fact

end

end
