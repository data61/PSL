(*  Title:       Termination of the Goodstein Sequence
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2017
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Termination of the Goodstein Sequence\<close>

theory Goodstein_Sequence
imports Multiset_More Syntactic_Ordinal
begin

text \<open>
The \<open>goodstein\<close> function returns the successive values of the Goodstein
sequence. It is defined in terms of \<open>encode\<close> and \<open>decode\<close> functions,
which convert between natural numbers and ordinals. The development culminates
with a proof of Goodstein's theorem.
\<close>


subsection \<open>Lemmas about Division\<close>

lemma div_mult_le: "m div n * n \<le> m" for m n :: nat
  by (fact div_times_less_eq_dividend)

lemma power_div_same_base:
  "b ^ y \<noteq> 0 \<Longrightarrow> x \<ge> y \<Longrightarrow> b ^ x div b ^ y = b ^ (x - y)" for b :: "'a::semidom_divide"
  by (metis add_diff_inverse leD nonzero_mult_div_cancel_left power_add)


subsection \<open>Hereditary and Nonhereditary Base-\<open>n\<close> Systems\<close>

context
  fixes base :: nat
  assumes base_ge_2: "base \<ge> 2"
begin

inductive well_base :: "'a multiset \<Rightarrow> bool" where
  "(\<forall>n. count M n < base) \<Longrightarrow> well_base M"

lemma well_base_filter: "well_base M \<Longrightarrow> well_base {#m \<in># M. p m#}"
  by (auto simp: well_base.simps)

lemma well_base_image_inj: "well_base M \<Longrightarrow> inj_on f (set_mset M) \<Longrightarrow> well_base (image_mset f M)"
  unfolding well_base.simps by (metis count_image_mset_le_count_inj_on le_less_trans)

lemma well_base_bound:
  assumes
    "well_base M" and
    "\<forall>m \<in># M. m < n"
  shows "(\<Sum>m \<in># M. base ^ m) < base ^ n"
  using assms
proof (induct n arbitrary: M)
  case (Suc n)
  note ih = this(1) and well_M = this(2) and in_M_lt_Sn = this(3)

  let ?Meq = "{#m \<in># M. m = n#}"
  let ?Mne = "{#m \<in># M. m \<noteq> n#}"
  let ?K = "{#base ^ m. m \<in># M#}"

  have M: "M = ?Meq + ?Mne"
    by (simp)

  have well_Mne: "well_base ?Mne"
    by (rule well_base_filter[OF well_M])

  have in_Mne_lt_n: "\<forall>m \<in># ?Mne. m < n"
    using in_M_lt_Sn by auto

  have "sum_mset (image_mset ((^) base) ?Meq) \<le> (base - 1) * base ^ n"
    unfolding filter_eq_replicate_mset using base_ge_2
    by simp (metis Suc_pred diff_self_eq_0 le_SucE less_imp_le less_le_trans less_numeral_extra(3)
      pos2 well_M well_base.cases zero_less_diff)
  moreover have "base * base ^ n = base ^ n + (base - Suc 0) * base ^ n"
    using base_ge_2 mult_eq_if by auto
  ultimately show ?case
    using ih[OF well_Mne in_Mne_lt_n] by (subst M) (simp del: union_filter_mset_complement)
qed simp

inductive well_base\<^sub>h :: "hmultiset \<Rightarrow> bool" where
  "(\<forall>N \<in># hmsetmset M. well_base\<^sub>h N) \<Longrightarrow> well_base (hmsetmset M) \<Longrightarrow> well_base\<^sub>h M"

lemma well_base\<^sub>h_mono_hmset: "well_base\<^sub>h M \<Longrightarrow> hmsetmset N \<subseteq># hmsetmset M \<Longrightarrow> well_base\<^sub>h N"
  by (induct rule: well_base\<^sub>h.induct, rule well_base\<^sub>h.intros, blast)
    (meson leD leI order_trans subseteq_mset_def well_base.simps)

lemma well_base\<^sub>h_imp_well_base: "well_base\<^sub>h M \<Longrightarrow> well_base (hmsetmset M)"
  by (erule well_base\<^sub>h.cases) simp


subsection \<open>Encoding of Natural Numbers into Ordinals\<close>

function encode :: "nat \<Rightarrow> nat \<Rightarrow> hmultiset" where
  "encode e n =
   (if n = 0 then 0 else of_nat (n mod base) * \<omega>^(encode 0 e) + encode (e + 1) (n div base))"
  by pat_completeness auto
termination
  using base_ge_2
proof (relation "measure (\<lambda>(e, n). n * (base ^ e + 1))"; simp)
  fix e n :: nat
  assume n_ge_0: "n > 0"

  have "e + e \<le> 2 ^ e"
    by (induct e; simp) (metis add_diff_cancel_left' add_leD1 diff_is_0_eq' double_not_eq_Suc_double
      le_antisym mult_2 not_less_eq_eq power_eq_0_iff zero_neq_numeral)
  also have "\<dots> \<le> base ^ e"
    using base_ge_2 by (simp add: power_mono)
  also have "\<dots> \<le> n * base ^ e"
    using n_ge_0 by (simp add: Suc_leI)
  also have "\<dots> < n + n * base ^ e"
    using n_ge_0 by simp
  finally show "e + e < n + n * base ^ e"
    by assumption

  have "n div base * (base * base ^ e) \<le> n * base ^ e"
    using base_ge_2 by (auto intro: div_mult_le)
  moreover have "n div base < n"
    using n_ge_0 base_ge_2 by simp
  ultimately show "n div base + n div base * (base * base ^ e) < n + n * base ^ e"
    by linarith
qed

declare encode.simps[simp del]

lemma encode_0[simp]: "encode e 0 = 0"
  by (subst encode.simps) simp

lemma encode_Suc:
  "encode e (Suc n) = of_nat (Suc n mod base) * \<omega>^(encode 0 e) + encode (e + 1) (Suc n div base)"
  by (subst encode.simps) simp

lemma encode_0_iff: "encode e n = 0 \<longleftrightarrow> n = 0"
proof (induct n arbitrary: e rule: less_induct)
  case (less n)
  note ih = this

  show ?case
  proof (cases n)
    case 0
    thus ?thesis
      by simp
  next
    case n: (Suc m)
    show ?thesis
    proof (cases "n mod base = 0")
      case True
      hence "n div base \<noteq> 0"
        using div_eq_0_iff n by fastforce
      thus ?thesis
        using ih[of "Suc m div base"] n
        by (simp add: encode_Suc) (metis One_nat_def base_ge_2 div_eq_dividend_iff div_le_dividend
          leD lessI nat_neq_iff numeral_2_eq_2)
    next
      case False
      thus ?thesis
        using n plus_hmultiset_def by (simp add: encode_Suc[unfolded of_nat_times_\<omega>_exp])
    qed
  qed
qed

lemma encode_Suc_exp: "encode (Suc e) n = encode e (base * n)"
  using base_ge_2
  by (subst (1 2) encode.simps, subst (4) encode.simps, simp add: zero_hmultiset_def[symmetric])

lemma encode_exp_0: "encode e n = encode 0 (base ^ e * n)"
  by (induct e arbitrary: n) (simp_all add: encode_Suc_exp mult.assoc mult.commute)

lemma mem_hmsetmset_encodeD: "M \<in># hmsetmset (encode e n) \<Longrightarrow> \<exists>e' \<ge> e. M = encode 0 e'"
proof (induct e n rule: encode.induct)
  case (1 e n)
  note ih = this(1-2) and M_in = this(3)

  show ?case
  proof (cases n)
    case 0
    thus ?thesis
      using M_in by simp
  next
    case n: (Suc m)

    {
      assume "M \<in># replicate_mset (n mod base) (encode 0 e)"
      hence ?thesis
        by (meson in_replicate_mset order_refl)
    }
    moreover
    {
      assume "M \<in># hmsetmset (encode (e + 1) (n div base))"
      hence ?thesis
        using ih(2) le_add1 n order_trans by blast
    }
    ultimately show ?thesis
      using M_in[unfolded n encode_Suc[unfolded of_nat_times_\<omega>_exp], folded n]
      unfolding hmsetmset_plus by auto
  qed
qed

lemma less_imp_encode_less: "n < p \<Longrightarrow> encode e n < encode e p"
proof (induct e n arbitrary: p rule: encode.induct)
  case (1 e n)
  note ih = this(1-2) and n_lt_p = this(3)

  show ?case
  proof (cases "n = 0")
    case True
    thus ?thesis
      using n_lt_p base_ge_2 encode_0_iff[of e p] le_less by fastforce
  next
    case n_nz: False

    let ?Ma = "replicate_mset (n mod base) (encode 0 e)"
    let ?Na = "replicate_mset (p mod base) (encode 0 e)"
    let ?Pa = "replicate_mset (n mod base - p mod base) (encode 0 e)"

    have "HMSet ?Ma + encode (Suc e) (n div base) < HMSet ?Na + encode (Suc e) (p div base)"
    proof (cases "n mod base < p mod base")
      case mod_lt: True
      show ?thesis
        by (rule add_less_le_mono, simp add: mod_lt,
          metis ih(2)[of "p div base", OF n_nz] Suc_eq_plus1 div_le_mono le_less n_lt_p)
    next
      case mod_ge: False
      hence div_lt: "n div base < p div base"
        by (metis add_le_cancel_left div_le_mono div_mult_mod_eq le_neq_implies_less less_imp_le
          n_lt_p nat_neq_iff)

      let ?M = "hmsetmset (encode (Suc e) (n div base))"
      let ?N = "hmsetmset (encode (Suc e) (p div base))"

      have "?M < ?N"
        by (auto intro!: ih(2)[folded Suc_eq_plus1] n_nz div_lt)
      then obtain X Y where
        X_nemp: "X \<noteq> {#}" and
        X_sub: "X \<subseteq># ?N" and
        M: "?M = ?N - X + Y" and
        ex_gt: "\<forall>y. y \<in># Y \<longrightarrow> (\<exists>x. x \<in># X \<and> x > y)"
        using less_multiset\<^sub>D\<^sub>M by metis

      {
        fix x
        assume x_in_X: "x \<in># X"
        hence x_in_N: "x \<in># ?N"
          using X_sub by blast
        then obtain e' where
          e'_gt: "e' > e" and
          x: "x = encode 0 e'"
          by (auto simp: Suc_le_eq dest: mem_hmsetmset_encodeD)

        have "x > encode 0 e"
          unfolding x using ih(1)[OF n_nz] e'_gt by (blast dest: Suc_lessD)
      }
      hence ex_gt_e: "\<exists>x \<in># X. x > encode 0 e"
        using X_nemp by auto

      have X_sub': "X \<subseteq># ?Na + ?N"
        using X_sub by (simp add: subset_mset.add_increasing)
      have mam_eq: "?Ma + ?M = ?Na + ?N - X + (Y + ?Pa)"
      proof -
        from mod_ge have "?Ma = ?Na + ?Pa"
          by (simp add: replicate_mset_plus [symmetric])
        moreover have "?Na + ?N - X = ?Na + (?N - X)"
          by (meson X_sub multiset_diff_union_assoc)
        ultimately show ?thesis
          by (simp add: M)
      qed
      have max_X: "\<And>k. k \<in># Y + ?Pa \<Longrightarrow> \<exists>a. a \<in># X \<and> k < a"
        using ex_gt mod_ge ex_gt_e by (metis in_replicate_mset union_iff)

      show ?thesis
        by (subst (4 8) hmultiset.collapse[symmetric],
          unfold HMSet_plus[symmetric] HMSet_less less_multiset\<^sub>D\<^sub>M,
          rule exI[of _ X], rule exI[of _ "Y + ?Pa"],
          intro conjI impI allI X_nemp X_sub' mam_eq, elim max_X)
    qed
    thus ?thesis
      using n_nz n_lt_p by (subst (1 2) encode.simps[unfolded of_nat_times_\<omega>_exp]) auto
  qed
qed

inductive aligned\<^sub>e :: "nat \<Rightarrow> hmultiset \<Rightarrow> bool" where
  "(\<forall>m \<in># hmsetmset M. m \<ge> encode 0 e) \<Longrightarrow> aligned\<^sub>e e M"

lemma aligned\<^sub>e_encode: "aligned\<^sub>e e (encode e M)"
  by (subst encode_exp_0, rule aligned\<^sub>e.intros,
    metis encode_exp_0 leD leI lessI less_imp_encode_less lift_Suc_mono_less_iff
      mem_hmsetmset_encodeD)

lemma well_base\<^sub>h_encode: "well_base\<^sub>h (encode e n)"
proof (induct e n rule: encode.induct)
  case (1 e n)
  note ih = this

  have well2: "\<forall>M \<in># hmsetmset (encode (Suc e) (n div base)). well_base\<^sub>h M"
    using ih(2) well_base\<^sub>h.cases by (metis Suc_eq_plus1 Zero_not_Suc count_empty div_0
      encode_0_iff hmsetmset_empty_iff in_countE)

  have cnt1: "count (hmsetmset (encode (Suc e) (n div base))) (encode 0 e) = 0"
    using aligned\<^sub>e_encode[unfolded aligned\<^sub>e.simps]
      less_imp_encode_less[of n "Suc n" for n, simplified]
    by (meson count_inI leD)

  show ?case
  proof (rule well_base\<^sub>h.intros)
    show "\<forall>M \<in># hmsetmset (encode e n). well_base\<^sub>h M"
      by (subst encode.simps[unfolded of_nat_times_\<omega>_exp],
        simp add: zero_hmultiset_def hmsetmset_plus, use ih(1) well2 in blast)
  next
    show "well_base (hmsetmset (encode e n))"
      using cnt1 base_ge_2
      by (subst encode.simps[unfolded of_nat_times_\<omega>_exp],
        simp add: well_base.simps zero_hmultiset_def hmsetmset_plus,
        metis ih(2) well_base\<^sub>h.simps Suc_eq_plus1 less_numeral_extra(3) well_base.simps)
  qed
qed


subsection \<open>Decoding of Natural Numbers from Ordinals\<close>

primrec decode :: "nat \<Rightarrow> hmultiset \<Rightarrow> nat" where
  "decode e (HMSet M) = (\<Sum>m \<in># M. base ^ decode 0 m) div base ^ e"

lemma decode_unfold: "decode e M = (\<Sum>m \<in># hmsetmset M. base ^ decode 0 m) div base ^ e"
  by (cases M) simp

lemma decode_0[simp]: "decode e 0 = 0"
  unfolding zero_hmultiset_def by simp

inductive aligned\<^sub>d :: "nat \<Rightarrow> hmultiset \<Rightarrow> bool" where
  "(\<forall>m \<in># hmsetmset M. decode 0 m \<ge> e) \<Longrightarrow> aligned\<^sub>d e M"

lemma aligned\<^sub>d_0[simp]: "aligned\<^sub>d 0 M"
  by (rule aligned\<^sub>d.intros) simp

lemma aligned\<^sub>d_mono_exp_Suc: "aligned\<^sub>d (Suc e) M \<Longrightarrow> aligned\<^sub>d e M"
  by (auto simp: aligned\<^sub>d.simps)

lemma aligned\<^sub>d_mono_hmset:
  assumes "aligned\<^sub>d e M" and "hmsetmset M' \<subseteq># hmsetmset M"
  shows "aligned\<^sub>d e M'"
  using assms by (auto simp: aligned\<^sub>d.simps)

lemma decode_exp_shift_Suc:
  assumes align\<^sub>d: "aligned\<^sub>d (Suc e) M"
  shows "decode e M = base * decode (Suc e) M"
proof (subst (1 2) decode_unfold, subst (1 2) sum_mset_distrib_div_if_dvd)
  note align' = align\<^sub>d[unfolded aligned\<^sub>d.simps, simplified, unfolded Suc_le_eq]

  show "\<forall>m \<in># hmsetmset M. base ^ Suc e dvd base ^ decode 0 m"
    using align' Suc_leI le_imp_power_dvd by blast

  show "\<forall>m \<in># hmsetmset M. base ^ e dvd base ^ decode 0 m"
    using align' by (simp add: le_imp_power_dvd le_less)

  have base_e_nz: "base ^ e \<noteq> 0"
    using base_ge_2 by simp

  have mult_base:
    "base ^ decode 0 m div base ^ e = base * (base ^ decode 0 m div (base * base ^ e))"
    if m_in: "m \<in># hmsetmset M" for m
    using m_in align'
    by (subst power_div_same_base[OF base_e_nz], force,
      metis Suc_diff_Suc Suc_leI mult_is_0 power_Suc power_div_same_base power_not_zero)

  show "(\<Sum>m\<in>#hmsetmset M. base ^ decode 0 m div base ^ e) =
    base * (\<Sum>m\<in>#hmsetmset M. base ^ decode 0 m div base ^ Suc e)"
    by (auto simp: sum_mset_distrib_left intro!: arg_cong[of _ _ sum_mset] image_mset_cong
      elim!: mult_base)
qed

lemma decode_exp_shift:
  assumes "aligned\<^sub>d e M"
  shows "decode 0 M = base ^ e * decode e M"
  using assms by (induct e) (auto simp: decode_exp_shift_Suc dest: aligned\<^sub>d_mono_exp_Suc)

lemma decode_plus:
  assumes align\<^sub>d_M: "aligned\<^sub>d e M"
  shows "decode e (M + N) = decode e M + decode e N"
  using align\<^sub>d_M[unfolded aligned\<^sub>d.simps, simplified]
  by (subst (1 2 3) decode_unfold) (auto simp: hmsetmset_plus
    intro!: le_imp_power_dvd div_plus_div_distrib_dvd_left[OF sum_mset_dvd])

lemma less_imp_decode_less:
  assumes
    "well_base\<^sub>h M" and
    "aligned\<^sub>d e M" and
    "aligned\<^sub>d e N" and
    "M < N"
  shows "decode e M < decode e N"
  using assms
proof (induct M arbitrary: N e rule: less_induct)
  case (less M)
  note ih = this(1) and well\<^sub>h_M = this(2) and align\<^sub>d_M = this(3) and align\<^sub>d_N = this(4) and
    M_lt_N = this(5)

  obtain K Ma Na where
    M: "M = K + Ma" and
    N: "N = K + Na" and
    hds: "head_\<omega> Ma < head_\<omega> Na"
    using hmset_pair_decompose_less[OF M_lt_N] by blast

  obtain H where
    H: "head_\<omega> Na = \<omega>^H"
    using hds head_\<omega>_def by fastforce
  have H_in: "H \<in># hmsetmset Na"
    by (metis (no_types) H Max_in add_mset_eq_single add_mset_not_empty finite_set_mset head_\<omega>_def
      hmsetmset_empty_iff hmultiset.simps(1) set_mset_eq_empty_iff zero_hmultiset_def)

  have well\<^sub>h_Ma: "well_base\<^sub>h Ma"
    by (rule well_base\<^sub>h_mono_hmset[OF well\<^sub>h_M]) (simp add: M hmsetmset_plus)
  have align\<^sub>d_K: "aligned\<^sub>d e K"
    using M align\<^sub>d_M aligned\<^sub>d_mono_hmset hmsetmset_plus by auto
  have align\<^sub>d_Ma: "aligned\<^sub>d e Ma"
    using M align\<^sub>d_M aligned\<^sub>d_mono_hmset hmsetmset_plus by auto
  have align\<^sub>d_Na: "aligned\<^sub>d e Na"
    using N align\<^sub>d_N aligned\<^sub>d_mono_hmset hmsetmset_plus by auto

  have "inj_on (decode 0) (set_mset (hmsetmset Ma))"
    unfolding inj_on_def
  proof clarify
    fix x y
    assume
      x_in: "x \<in># hmsetmset Ma" and
      y_in: "y \<in># hmsetmset Ma" and
      dec_eq: "decode 0 x = decode 0 y"

    {
      fix x y
      assume
        x_in: "x \<in># hmsetmset Ma" and
        y_in: "y \<in># hmsetmset Ma" and
        x_lt_y: "x < y"

      have x_lt_M: "x < M"
        unfolding M using mem_hmsetmset_imp_less[OF x_in] by (simp add: trans_less_add2_hmset)
      have well\<^sub>h_x: "well_base\<^sub>h x"
        using well\<^sub>h_Ma well_base\<^sub>h.simps x_in by blast

      have "decode 0 x < decode 0 y"
        by (rule ih[OF x_lt_M well\<^sub>h_x aligned\<^sub>d_0 aligned\<^sub>d_0 x_lt_y])
    }
    thus "x = y"
      using x_in y_in dec_eq by (metis leI less_irrefl_nat order.not_eq_order_implies_strict)
  qed
  hence well_dec_Ma: "well_base (image_mset (decode 0) (hmsetmset Ma))"
    by (rule well_base_image_inj[OF well_base\<^sub>h_imp_well_base[OF well\<^sub>h_Ma]])

  have H_bound: "\<forall>m \<in># hmsetmset Ma. decode 0 m < decode 0 H"
  proof
    fix m
    assume m_in: "m \<in># hmsetmset Ma"

    have "\<forall>m \<in># hmsetmset (head_\<omega> Ma). m < H"
      using hds[unfolded H] using head_\<omega>_def by auto
    hence m_lt_H: "m < H"
      using m_in
      by (metis Max_less_iff empty_iff finite_set_mset head_\<omega>_def hmultiset.sel insert_iff
        set_mset_add_mset_insert)

    have m_lt_M: "m < M"
      using mem_hmsetmset_imp_less[OF m_in] by (simp add: M trans_less_add2_hmset)

    have well\<^sub>h_m: "well_base\<^sub>h m"
      using m_in well\<^sub>h_Ma well_base\<^sub>h.cases by blast

    show "decode 0 m < decode 0 H"
      by (rule ih[OF m_lt_M well\<^sub>h_m aligned\<^sub>d_0 aligned\<^sub>d_0 m_lt_H])
  qed

  have "decode 0 Ma < base ^ decode 0 H"
    using well_base_bound[OF well_dec_Ma, simplified, OF H_bound] by (subst decode_unfold) simp
  also have "\<dots> \<le> decode 0 Na"
    by (subst (2) decode_unfold, simp, rule sum_image_mset_mono_mem[OF H_in])
  finally have "decode e Ma < decode e Na"
    using decode_exp_shift[OF align\<^sub>d_Ma] decode_exp_shift[OF align\<^sub>d_Na] by simp
  thus "decode e M < decode e N"
    unfolding M N by (simp add: decode_plus[OF align\<^sub>d_K])
qed

lemma inj_decode: "inj_on (decode e) {M. well_base\<^sub>h M \<and> aligned\<^sub>d e M}"
  unfolding inj_on_def Ball_def mem_Collect_eq
  by (metis less_imp_decode_less less_irrefl_nat neqE)

lemma decode_0_iff: "well_base\<^sub>h M \<Longrightarrow> aligned\<^sub>d e M \<Longrightarrow> decode e M = 0 \<longleftrightarrow> M = 0"
  by (metis aligned\<^sub>d_0 decode_0 decode_exp_shift encode_0 less_imp_decode_less mult_0_right neqE
    not_less_zero well_base\<^sub>h_encode)

lemma decode_encode: "decode e (encode e n) = n"
proof (induct e n rule: encode.induct)
  case (1 e n)
  note ih = this

  show ?case
  proof (cases "n = 0")
    case n_nz: False

    have align\<^sub>d1: "aligned\<^sub>d e (of_nat (n mod base) * \<omega>^(encode 0 e))"
      unfolding of_nat_times_\<omega>_exp using n_nz by (auto simp: ih(1) aligned\<^sub>d.simps)
    have align\<^sub>d2: "aligned\<^sub>d (Suc e) (encode (Suc e) (n div base))"
      by (safe intro!: aligned\<^sub>d.intros, subst ih(1)[OF n_nz, symmetric],
        auto dest: mem_hmsetmset_encodeD intro!: Suc_le_eq[THEN iffD2]
          less_imp_decode_less[OF well_base\<^sub>h_encode aligned\<^sub>d_0 aligned\<^sub>d_0] less_imp_encode_less)

    show ?thesis
      using ih base_ge_2
      by (subst encode.simps[unfolded of_nat_times_\<omega>_exp])
        (simp add: decode_plus[OF align\<^sub>d1[unfolded of_nat_times_\<omega>_exp]]
           decode_exp_shift_Suc[OF align\<^sub>d2])
  qed simp
qed

lemma encode_decode_exp_0: "well_base\<^sub>h M \<Longrightarrow> encode 0 (decode 0 M) = M"
  by (auto intro: inj_onD[OF inj_decode] decode_encode well_base\<^sub>h_encode)

end

lemma well_base\<^sub>h_mono_base:
  assumes
    well\<^sub>h: "well_base\<^sub>h base M" and
    two: "2 \<le> base" and
    bases: "base \<le> base'"
  shows "well_base\<^sub>h base' M"
  using two well\<^sub>h
  by (induct rule: well_base\<^sub>h.induct)
    (meson two bases less_le_trans order_trans well_base\<^sub>h.intros well_base.simps)


subsection \<open>The Goodstein Sequence and Goodstein's Theorem\<close>

context
  fixes start :: nat
begin

primrec goodstein :: "nat \<Rightarrow> nat" where
  "goodstein 0 = start"
| "goodstein (Suc i) = decode (i + 3) 0 (encode (i + 2) 0 (goodstein i)) - 1"

lemma goodstein_step:
  assumes gi_gt_0: "goodstein i > 0"
  shows "encode (i + 2) 0 (goodstein i) > encode (i + 3) 0 (goodstein (i + 1))"
proof -
  let ?Ei = "encode (i + 2) 0 (goodstein i)"
  let ?reencode = "encode (i + 3) 0"
  let ?decoded_Ei = "decode (i + 3) 0 ?Ei"

  have two_le: "2 \<le> i + 3"
    by simp

  have "well_base\<^sub>h (i + 2) ?Ei"
    by (rule well_base\<^sub>h_encode) simp
  hence well\<^sub>h: "well_base\<^sub>h (i + 3) ?Ei"
    by (rule well_base\<^sub>h_mono_base) simp_all

  have decoded_Ei_gt_0: "?decoded_Ei > 0"
    by (metis gi_gt_0 gr0I encode_0_iff le_add2 decode_0_iff[OF _ well\<^sub>h aligned\<^sub>d_0] two_le)

  have "?reencode (?decoded_Ei - 1) < ?reencode ?decoded_Ei"
    by (rule less_imp_encode_less[OF two_le]) (use decoded_Ei_gt_0 in linarith)
  also have "\<dots> = ?Ei"
    by (simp only: encode_decode_exp_0[OF two_le well\<^sub>h])
  finally show ?thesis
    by simp
qed

theorem goodsteins_theorem: "\<exists>i. goodstein i = 0"
proof -
  let ?G = "\<lambda>i. encode (i + 2) 0 (goodstein i)"

  obtain i where
    "\<not> ?G i > ?G (i + 1)"
    using wf_iff_no_infinite_down_chain[THEN iffD1, OF wf,
      unfolded not_ex not_all mem_Collect_eq prod.case, rule_format, of ?G]
    by auto
  hence "goodstein i = 0"
    using goodstein_step by (metis add.assoc gr0I one_plus_numeral semiring_norm(3))
  thus ?thesis
    by blast
qed

end

end
