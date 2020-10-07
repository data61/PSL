(*  Title:       Real Euclidean space and Tarski's axioms
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "Real Euclidean space and Tarski's axioms"

theory Euclid_Tarski
imports Tarski
begin

subsection "Real Euclidean space satisfies the first five axioms"

abbreviation
  real_euclid_C :: "[real^('n::finite), real^('n), real^('n), real^('n)] \<Rightarrow> bool"
  ("_ _ \<congruent>\<^sub>\<real> _ _" [99,99,99,99] 50) where
    "real_euclid_C \<equiv> norm_metric.smC"

definition real_euclid_B :: "[real^('n::finite), real^('n), real^('n)] \<Rightarrow> bool"
  ("B\<^sub>\<real> _ _ _" [99,99,99] 50) where
    "B\<^sub>\<real> a b c \<equiv> \<exists>l. 0 \<le> l \<and> l \<le> 1 \<and> b - a = l *\<^sub>R (c - a)"

interpretation real_euclid: tarski_first5 real_euclid_C real_euclid_B
proof
  txt \<open>By virtue of being a semimetric space,
    real Euclidean space is already known to satisfy the first three axioms.\<close>
  { fix q a b c
    have "\<exists>x. B\<^sub>\<real> q a x \<and> a x \<congruent>\<^sub>\<real> b c"
    proof cases
      assume "q = a"
      let ?x = "a + c - b"
      have "B\<^sub>\<real> q a ?x"
      proof -
        let ?l = "0 :: real"
        note real_euclid_B_def [of q a ?x]
        moreover
          have "?l \<ge> 0" and "?l \<le> 1" by auto
        moreover
          from \<open>q = a\<close> have "a - q = 0" by simp
          hence "a - q = ?l *\<^sub>R (?x - q)" by simp
        ultimately show ?thesis by auto
      qed
      moreover
        have "a - ?x = b - c" by simp
        hence "a ?x \<congruent>\<^sub>\<real> b c" by (simp add: field_simps)
      ultimately show ?thesis by blast
    next
      assume "q \<noteq> a"
      hence "norm_dist q a > 0" by simp
      let ?k = "norm_dist b c / norm_dist q a"
      let ?x = "a + ?k *\<^sub>R (a - q)"
      have "B\<^sub>\<real> q a ?x"
      proof -
        let ?l = "1 / (1 + ?k)"
        have "?l > 0" by (simp add: add_pos_nonneg)
        note real_euclid_B_def [of q a ?x]
        moreover
          have "?l \<ge> 0" and "?l \<le> 1" by (auto simp add: add_pos_nonneg)
        moreover
          from scaleR_left_distrib [of 1 ?k "a - q"]
            have "(1 + ?k) *\<^sub>R (a - q) = ?x - q" by simp
          hence "?l *\<^sub>R ((1 + ?k) *\<^sub>R (a - q)) = ?l *\<^sub>R (?x - q)" by simp
          with \<open>?l > 0\<close> and scaleR_right_diff_distrib [of ?l ?x q]
            have "a - q = ?l *\<^sub>R (?x - q)" by simp
        ultimately show "B\<^sub>\<real> q a ?x" by blast
      qed
      moreover
        have "a ?x \<congruent>\<^sub>\<real> b c"
        proof -
          from norm_scaleR [of ?k "a - q"] have
            "norm_dist a ?x = \<bar>?k\<bar> * norm (a - q)" by simp
          also have
            "\<dots> = ?k * norm (a - q)" by simp
          also from norm_metric.symm [of q a] have
            "\<dots> = ?k * norm_dist q a" by simp
          finally have
            "norm_dist a ?x = norm_dist b c / norm_dist q a * norm_dist q a" .
          with \<open>norm_dist q a > 0\<close> show "a ?x \<congruent>\<^sub>\<real> b c" by auto
        qed
      ultimately show ?thesis by blast
    qed }
  thus "\<forall>q a b c. \<exists>x. B\<^sub>\<real> q a x \<and> a x \<congruent>\<^sub>\<real> b c" by auto
  { fix a b c d a' b' c' d'
    assume "a \<noteq> b" and
      "B\<^sub>\<real> a b c" and
      "B\<^sub>\<real> a' b' c'" and
      "a b \<congruent>\<^sub>\<real> a' b'" and
      "b c \<congruent>\<^sub>\<real> b' c'" and
      "a d \<congruent>\<^sub>\<real> a' d'" and
      "b d \<congruent>\<^sub>\<real> b' d'"
    have "c d \<congruent>\<^sub>\<real> c' d'"
    proof -
      { fix m
        fix p q r :: "real^('n::finite)"
        assume "0 \<le> m" and
          "m \<le> 1" and
          "p \<noteq> q" and
          "q - p = m *\<^sub>R (r - p)"
        from \<open>p \<noteq> q\<close> and \<open>q - p = m *\<^sub>R (r - p)\<close> have "m \<noteq> 0"
        proof -
          { assume "m = 0"
            with \<open>q - p = m *\<^sub>R (r - p)\<close> have "q - p = 0" by simp
            with \<open>p \<noteq> q\<close> have False by simp }
          thus ?thesis ..
        qed
        with \<open>m \<ge> 0\<close> have "m > 0" by simp
        from \<open>q - p = m *\<^sub>R (r - p)\<close> and
            scaleR_right_diff_distrib [of m r p]
          have "q - p = m *\<^sub>R r - m *\<^sub>R p" by simp
        hence "q - p - q + p - m *\<^sub>R r =
            m *\<^sub>R r - m *\<^sub>R p - q + p - m *\<^sub>R r"
          by simp
        with scaleR_left_diff_distrib [of 1 m p] and
            scaleR_left_diff_distrib [of 1 m q]
          have "(1 - m) *\<^sub>R p - (1 - m) *\<^sub>R q = m *\<^sub>R q - m *\<^sub>R r" by auto
        with scaleR_right_diff_distrib [of "1 - m" p q] and
            scaleR_right_diff_distrib [of m q r]
          have "(1 - m) *\<^sub>R (p - q) = m *\<^sub>R (q - r)" by simp
        with norm_scaleR [of "1 - m" "p - q"] and norm_scaleR [of m "q - r"]
          have "\<bar>1 - m\<bar> * norm (p - q) = \<bar>m\<bar> * norm (q - r)" by simp
        with \<open>m > 0\<close> and \<open>m \<le> 1\<close>
          have "norm (q - r) = (1 - m) / m * norm (p - q)" by simp
        moreover from \<open>p \<noteq> q\<close> have "norm (p - q) \<noteq> 0" by simp
        ultimately
          have "norm (q - r) / norm (p - q) = (1 - m) / m" by simp
        with \<open>m \<noteq> 0\<close> have
          "norm_dist q r / norm_dist p q = (1 - m) / m" and "m \<noteq> 0" by auto }
      note linelemma = this
      from real_euclid_B_def [of a b c] and \<open>B\<^sub>\<real> a b c\<close>
        obtain l where "0 \<le> l" and "l \<le> 1" and  "b - a = l *\<^sub>R (c - a)" by auto
      from real_euclid_B_def [of a' b' c'] and \<open>B\<^sub>\<real> a' b' c'\<close>
        obtain l' where"0 \<le> l'" and "l' \<le> 1" and  "b' - a' = l' *\<^sub>R (c' - a')" by auto
      from \<open>a \<noteq> b\<close> and \<open>a b \<congruent>\<^sub>\<real> a' b'\<close> have "a' \<noteq> b'" by auto
      from linelemma [of l a b c] and
          \<open>l \<ge> 0\<close> and
          \<open>l \<le> 1\<close> and
          \<open>a \<noteq> b\<close> and
          \<open>b - a = l *\<^sub>R (c - a)\<close>
        have "l \<noteq> 0" and "(1 - l) / l = norm_dist b c / norm_dist a b" by auto
      from \<open>(1 - l) / l = norm_dist b c / norm_dist a b\<close> and
          \<open>a b \<congruent>\<^sub>\<real> a' b'\<close> and
          \<open>b c \<congruent>\<^sub>\<real> b' c'\<close>
        have "(1 - l) / l = norm_dist b' c' / norm_dist a' b'" by simp
      with linelemma [of l' a' b' c'] and
          \<open>l' \<ge> 0\<close> and
          \<open>l' \<le> 1\<close> and
          \<open>a' \<noteq> b'\<close> and
          \<open>b' - a' = l' *\<^sub>R (c' - a')\<close>
        have "l' \<noteq> 0" and "(1 - l) / l = (1 - l') / l'" by auto
      from \<open>(1 - l) / l = (1 - l') / l'\<close>
        have "(1 - l) / l * l * l' = (1 - l') / l' * l * l'" by simp
      with \<open>l \<noteq> 0\<close> and \<open>l' \<noteq> 0\<close> have "(1 - l) * l' = (1 - l') * l" by simp
      with left_diff_distrib [of 1 l l'] and left_diff_distrib [of 1 l' l]
        have "l = l'" by simp
      { fix m
        fix p q r s :: "real^('n::finite)"
        assume "m \<noteq> 0" and
          "q - p = m *\<^sub>R (r - p)"
        with scaleR_scaleR have "r - p = (1/m) *\<^sub>R (q - p)" by simp
        with cosine_rule [of r s p]
          have "(norm_dist r s)\<^sup>2 = (norm_dist r p)\<^sup>2 + (norm_dist p s)\<^sup>2 +
              2 * (((1/m) *\<^sub>R (q - p)) \<bullet> (p - s))"
            by simp
        also from inner_scaleR_left [of "1/m" "q - p" "p - s"]
          have "\<dots> =
              (norm_dist r p)\<^sup>2 + (norm_dist p s)\<^sup>2 + 2/m * ((q - p) \<bullet> (p - s))"
            by simp
        also from \<open>m \<noteq> 0\<close> and cosine_rule [of q s p]
          have "\<dots> = (norm_dist r p)\<^sup>2 + (norm_dist p s)\<^sup>2 +
              1/m * ((norm_dist q s)\<^sup>2 - (norm_dist q p)\<^sup>2 - (norm_dist p s)\<^sup>2)"
            by simp
        finally have "(norm_dist r s)\<^sup>2 = (norm_dist r p)\<^sup>2 + (norm_dist p s)\<^sup>2 +
          1/m * ((norm_dist q s)\<^sup>2 - (norm_dist q p)\<^sup>2 - (norm_dist p s)\<^sup>2)" .
        moreover
        { from norm_dist_dot [of r p] and \<open>r - p = (1/m) *\<^sub>R (q - p)\<close>
            have "(norm_dist r p)\<^sup>2 = ((1/m) *\<^sub>R (q - p)) \<bullet> ((1/m) *\<^sub>R (q - p))"
              by simp
          also from inner_scaleR_left [of "1/m" "q - p"] and
              inner_scaleR_right [of _ "1/m" "q - p"]
            have "\<dots> = 1/m\<^sup>2 * ((q - p) \<bullet> (q - p))"
              by (simp add: power2_eq_square)
          also from norm_dist_dot [of q p] have "\<dots> = 1/m\<^sup>2 * (norm_dist q p)\<^sup>2"
            by simp
          finally have "(norm_dist r p)\<^sup>2 = 1/m\<^sup>2 * (norm_dist q p)\<^sup>2" . }
        ultimately have
          "(norm_dist r s)\<^sup>2 = 1/m\<^sup>2 * (norm_dist q p)\<^sup>2 + (norm_dist p s)\<^sup>2 +
            1/m * ((norm_dist q s)\<^sup>2 - (norm_dist q p)\<^sup>2 - (norm_dist p s)\<^sup>2)"
          by simp
        with norm_metric.symm [of q p]
          have "(norm_dist r s)\<^sup>2 = 1/m\<^sup>2 * (norm_dist p q)\<^sup>2 + (norm_dist p s)\<^sup>2 +
              1/m * ((norm_dist q s)\<^sup>2 - (norm_dist p q)\<^sup>2 - (norm_dist p s)\<^sup>2)"
            by simp }
      note fiveseglemma = this
      from fiveseglemma [of l b a c d] and \<open>l \<noteq> 0\<close> and \<open>b - a = l *\<^sub>R (c - a)\<close>
        have "(norm_dist c d)\<^sup>2 = 1/l\<^sup>2 * (norm_dist a b)\<^sup>2 + (norm_dist a d)\<^sup>2 +
            1/l * ((norm_dist b d)\<^sup>2 - (norm_dist a b)\<^sup>2 - (norm_dist a d)\<^sup>2)"
          by simp
      also from \<open>l = l'\<close> and
          \<open>a b \<congruent>\<^sub>\<real> a' b'\<close> and
          \<open>a d \<congruent>\<^sub>\<real> a' d'\<close> and
          \<open>b d \<congruent>\<^sub>\<real> b' d'\<close>
        have "\<dots> = 1/l'\<^sup>2 * (norm_dist a' b')\<^sup>2 + (norm_dist a' d')\<^sup>2 +
            1/l' * ((norm_dist b' d')\<^sup>2 - (norm_dist a' b')\<^sup>2 - (norm_dist a' d')\<^sup>2)"
          by simp
      also from fiveseglemma [of l' b' a' c' d'] and
          \<open>l' \<noteq> 0\<close> and
          \<open>b' - a' = l' *\<^sub>R (c' - a')\<close>
        have "\<dots> = (norm_dist c' d')\<^sup>2" by simp
      finally have "(norm_dist c d)\<^sup>2 = (norm_dist c' d')\<^sup>2" .
      hence "sqrt ((norm_dist c d)\<^sup>2) = sqrt ((norm_dist c' d')\<^sup>2)" by simp
      with real_sqrt_abs show "c d \<congruent>\<^sub>\<real> c' d'" by simp
    qed }
  thus "\<forall>a b c d a' b' c' d'.
          a \<noteq> b \<and> B\<^sub>\<real> a b c \<and> B\<^sub>\<real> a' b' c' \<and>
          a b \<congruent>\<^sub>\<real> a' b' \<and> b c \<congruent>\<^sub>\<real> b' c' \<and> a d \<congruent>\<^sub>\<real> a' d' \<and> b d \<congruent>\<^sub>\<real> b' d' \<longrightarrow>
            c d \<congruent>\<^sub>\<real> c' d'"
    by blast
qed

subsection "Real Euclidean space also satisfies axioms 6, 7, and 11"

lemma rearrange_real_euclid_B:
  fixes w y z :: "real^('n)" and h
  shows "y - w = h *\<^sub>R (z - w) \<longleftrightarrow> y = h *\<^sub>R z + (1 - h) *\<^sub>R w"
proof
  assume "y - w = h *\<^sub>R (z - w)"
  hence "y - w + w = h *\<^sub>R (z - w) + w" by simp
  hence "y = h *\<^sub>R (z - w) + w" by simp
  with scaleR_right_diff_distrib [of h z w]
    have "y = h *\<^sub>R z + w - h *\<^sub>R w" by simp
  with scaleR_left_diff_distrib [of 1 h w]
    show "y = h *\<^sub>R z + (1 - h) *\<^sub>R w" by simp
next
  assume "y = h *\<^sub>R z + (1 - h) *\<^sub>R w"
  with scaleR_left_diff_distrib [of 1 h w]
    have "y = h *\<^sub>R z + w - h *\<^sub>R w" by simp
  with scaleR_right_diff_distrib [of h z w]
    have "y = h *\<^sub>R (z - w) + w" by simp
  hence "y - w + w = h *\<^sub>R (z - w) + w" by simp
  thus "y - w = h *\<^sub>R (z - w)" by simp
qed

interpretation real_euclid: tarski_absolute_space real_euclid_C real_euclid_B
proof
  { fix a b
    assume "B\<^sub>\<real> a b a"
    with real_euclid_B_def [of a b a]
      obtain l where "b - a = l *\<^sub>R (a - a)" by auto
    hence "a = b" by simp }
  thus "\<forall>a b. B\<^sub>\<real> a b a \<longrightarrow> a = b" by auto
  { fix a b c p q
    assume "B\<^sub>\<real> a p c" and "B\<^sub>\<real> b q c"
    from real_euclid_B_def [of a p c] and \<open>B\<^sub>\<real> a p c\<close>
      obtain i where "i \<ge> 0" and "i \<le> 1" and "p - a = i *\<^sub>R (c - a)" by auto
    have "\<exists>x. B\<^sub>\<real> p x b \<and> B\<^sub>\<real> q x a"
    proof cases
      assume "i = 0"
      with \<open>p - a = i *\<^sub>R (c - a)\<close> have "p = a" by simp
      hence "p - a = 0 *\<^sub>R (b - p)" by simp
      moreover have "(0::real) \<ge> 0" and "(0::real) \<le> 1" by auto
      moreover note real_euclid_B_def [of p a b]
      ultimately have "B\<^sub>\<real> p a b" by auto
      moreover
      { have "a - q = 1 *\<^sub>R (a - q)" by simp
        moreover have "(1::real) \<ge> 0" and "(1::real) \<le> 1" by auto
        moreover note real_euclid_B_def [of q a a]
        ultimately have "B\<^sub>\<real> q a a" by blast }
      ultimately have "B\<^sub>\<real> p a b \<and> B\<^sub>\<real> q a a" by simp
      thus "\<exists>x. B\<^sub>\<real> p x b \<and> B\<^sub>\<real> q x a" by auto
    next
      assume "i \<noteq> 0"
      from real_euclid_B_def [of b q c] and \<open>B\<^sub>\<real> b q c\<close>
        obtain j where "j \<ge> 0" and "j \<le> 1" and "q - b = j *\<^sub>R (c - b)" by auto
      from \<open>i \<ge> 0\<close> and \<open>i \<le> 1\<close>
        have "1 - i \<ge> 0" and "1 - i \<le> 1" by auto
      from \<open>j \<ge> 0\<close> and \<open>1 - i \<ge> 0\<close>
        have "j * (1 - i) \<ge> 0" by auto
      with \<open>i \<ge> 0\<close> and \<open>i \<noteq> 0\<close> have "i + j * (1 - i) > 0" by simp
      hence "i + j * (1 - i) \<noteq> 0" by simp
      let ?l = "j * (1 - i) / (i + j * (1 - i))"
      from diff_divide_distrib [of "i + j * (1 - i)" "j * (1 - i)" "i + j * (1 - i)"] and
          \<open>i + j * (1 - i) \<noteq> 0\<close>
        have "1 - ?l = i / (i + j * (1 - i))" by simp
      let ?k = "i * (1 - j) / (j + i * (1 - j))"
      from right_diff_distrib [of i 1 j] and
          right_diff_distrib [of j 1 i] and
          mult.commute [of i j] and
          add.commute [of i j]
        have "j + i * (1 - j) = i + j * (1 - i)" by simp
      with \<open>i + j * (1 - i) \<noteq> 0\<close> have "j + i * (1 - j) \<noteq> 0" by simp
      with diff_divide_distrib [of "j + i * (1 - j)" "i * (1 - j)" "j + i * (1 - j)"]
        have "1 - ?k = j / (j + i * (1 - j))" by simp
      with \<open>1 - ?l = i / (i + j * (1 - i))\<close> and
          \<open>j + i * (1 - j) = i + j * (1 - i)\<close> and
          times_divide_eq_left [of _ "i + j * (1 - i)"] and
          mult.commute [of i j]
        have "(1 - ?l) * j = (1 - ?k) * i" by simp
      moreover
      { from \<open>1 - ?k = j / (j + i * (1 - j))\<close> and
            \<open>j + i * (1 - j) = i + j * (1 - i)\<close>
          have "?l = (1 - ?k) * (1 - i)" by simp }
      moreover
      { from \<open>1 - ?l = i / (i + j * (1 - i))\<close> and
            \<open>j + i * (1 - j) = i + j * (1 - i)\<close>
          have "(1 - ?l) * (1 - j) = ?k" by simp }
      ultimately
        have "?l *\<^sub>R a + ((1 - ?l) * j) *\<^sub>R c + ((1 - ?l) * (1 - j)) *\<^sub>R b =
            ?k *\<^sub>R b + ((1 - ?k) * i) *\<^sub>R c + ((1 - ?k) * (1 - i)) *\<^sub>R a"
          by simp
      with scaleR_scaleR
        have "?l *\<^sub>R a + (1 - ?l) *\<^sub>R j *\<^sub>R c + (1 - ?l) *\<^sub>R (1 - j) *\<^sub>R b =
            ?k *\<^sub>R b + (1 - ?k) *\<^sub>R i *\<^sub>R c + (1 - ?k) *\<^sub>R (1 - i) *\<^sub>R a"
          by simp
      with scaleR_right_distrib [of "(1 - ?l)" "j *\<^sub>R c" "(1 - j) *\<^sub>R b"] and
          scaleR_right_distrib [of "(1 - ?k)" "i *\<^sub>R c" "(1 - i) *\<^sub>R a"] and
          add.assoc [of "?l *\<^sub>R a" "(1 - ?l) *\<^sub>R j *\<^sub>R c" "(1 - ?l) *\<^sub>R (1 - j) *\<^sub>R b"] and
          add.assoc [of "?k *\<^sub>R b" "(1 - ?k) *\<^sub>R i *\<^sub>R c" "(1 - ?k) *\<^sub>R (1 - i) *\<^sub>R a"]
        have "?l *\<^sub>R a + (1 - ?l) *\<^sub>R (j *\<^sub>R c + (1 - j) *\<^sub>R b) =
            ?k *\<^sub>R b + (1 - ?k) *\<^sub>R (i *\<^sub>R c + (1 - i) *\<^sub>R a)"
          by arith
      from \<open>?l *\<^sub>R a + (1 - ?l) *\<^sub>R (j *\<^sub>R c + (1 - j) *\<^sub>R b) =
            ?k *\<^sub>R b + (1 - ?k) *\<^sub>R (i *\<^sub>R c + (1 - i) *\<^sub>R a)\<close> and
          \<open>p - a = i *\<^sub>R (c - a)\<close> and
          \<open>q - b = j *\<^sub>R (c - b)\<close> and
          rearrange_real_euclid_B [of p a i c] and
          rearrange_real_euclid_B [of q b j c]
        have "?l *\<^sub>R a + (1 - ?l) *\<^sub>R q = ?k *\<^sub>R b + (1 - ?k) *\<^sub>R p" by simp
      let ?x = "?l *\<^sub>R a + (1 - ?l) *\<^sub>R q"
      from rearrange_real_euclid_B [of ?x q ?l a]
        have "?x - q = ?l *\<^sub>R (a - q)" by simp
      from \<open>?x = ?k *\<^sub>R b + (1 - ?k) *\<^sub>R p\<close> and
          rearrange_real_euclid_B [of ?x p ?k b]
        have "?x - p = ?k *\<^sub>R (b - p)" by simp
      from \<open>i + j * (1 - i) > 0\<close> and
          \<open>j * (1 - i) \<ge> 0\<close> and
          zero_le_divide_iff [of "j * (1 - i)" "i + j * (1 - i)"]
        have "?l \<ge> 0" by simp
      from \<open>i + j * (1 - i) > 0\<close> and
          \<open>i \<ge> 0\<close> and
          zero_le_divide_iff [of i "i + j * (1 - i)"] and
          \<open>1 - ?l = i / (i + j * (1 - i))\<close>
        have "1 - ?l \<ge> 0" by simp
      hence "?l \<le> 1" by simp
      with \<open>?l \<ge> 0\<close> and
          \<open>?x - q = ?l *\<^sub>R (a - q)\<close> and
          real_euclid_B_def [of q ?x a]
        have "B\<^sub>\<real> q ?x a" by auto
      from \<open>j \<le> 1\<close> have "1 - j \<ge> 0" by simp
      with \<open>1 - ?l \<ge> 0\<close> and
          \<open>(1 - ?l) * (1 - j) = ?k\<close> and
          zero_le_mult_iff [of "1 - ?l" "1 - j"]
        have "?k \<ge> 0" by simp
      from \<open>j \<ge> 0\<close> have "1 - j \<le> 1" by simp
      from \<open>?l \<ge> 0\<close> have "1 - ?l \<le> 1" by simp
      with \<open>1 - j \<le> 1\<close> and
          \<open>1 - j \<ge> 0\<close> and
          mult_mono [of "1 - ?l" 1 "1 - j" 1] and
          \<open>(1 - ?l) * (1 - j) = ?k\<close>
        have "?k \<le> 1" by simp
      with \<open>?k \<ge> 0\<close> and
          \<open>?x - p = ?k *\<^sub>R (b - p)\<close> and
          real_euclid_B_def [of p ?x b]
        have "B\<^sub>\<real> p ?x b" by auto
      with \<open>B\<^sub>\<real> q ?x a\<close> show ?thesis by auto
    qed }
  thus "\<forall>a b c p q. B\<^sub>\<real> a p c \<and> B\<^sub>\<real> b q c \<longrightarrow> (\<exists>x. B\<^sub>\<real> p x b \<and> B\<^sub>\<real> q x a)" by auto
  { fix X Y
    assume "\<exists>a. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y"
    then obtain a where "\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y" by auto
    have "\<exists>b. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> x b y"
    proof cases
      assume "X \<subseteq> {a} \<or> Y = {}"
      let ?b = a
      { fix x y
        assume "x \<in> X" and "y \<in> Y"
        with \<open>X \<subseteq> {a} \<or> Y = {}\<close> have "x = a" by auto
        from \<open>\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y\<close> and \<open>x \<in> X\<close> and \<open>y \<in> Y\<close>
          have "B\<^sub>\<real> a x y" by simp
        with \<open>x = a\<close> have "B\<^sub>\<real> x ?b y" by simp }
      hence "\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> x ?b y" by simp
      thus ?thesis by auto
    next
      assume "\<not>(X \<subseteq> {a} \<or> Y = {})"
      hence "X - {a} \<noteq> {}" and "Y \<noteq> {}" by auto
      from \<open>X - {a} \<noteq> {}\<close> obtain c where "c \<in> X" and "c \<noteq> a" by auto
      from \<open>c \<noteq> a\<close> have "c - a \<noteq> 0" by simp
      { fix y
        assume "y \<in> Y"
        with \<open>\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y\<close> and \<open>c \<in> X\<close>
          have "B\<^sub>\<real> a c y" by simp
        with real_euclid_B_def [of a c y]
          obtain l where "l \<ge> 0" and "l \<le> 1" and "c - a = l *\<^sub>R (y - a)" by auto
        from \<open>c - a = l *\<^sub>R (y - a)\<close> and \<open>c - a \<noteq> 0\<close> have "l \<noteq> 0" by simp
        with \<open>l \<ge> 0\<close> have "l > 0" by simp
        with \<open>c - a = l *\<^sub>R (y - a)\<close> have "y - a = (1/l) *\<^sub>R (c - a)" by simp
        from \<open>l > 0\<close> and \<open>l \<le> 1\<close> have "1/l \<ge> 1" by simp
        with \<open>y - a = (1/l) *\<^sub>R (c - a)\<close>
          have "\<exists>j\<ge>1. y - a = j *\<^sub>R (c - a)" by auto }
      note ylemma = this
      from \<open>Y \<noteq> {}\<close> obtain d where "d \<in> Y" by auto
      with ylemma [of d]
        obtain "jd" where "jd \<ge> 1" and "d - a = jd *\<^sub>R (c - a)" by auto
      { fix x
        assume "x \<in> X"
        with \<open>\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y\<close> and \<open>d \<in> Y\<close>
          have "B\<^sub>\<real> a x d" by simp
        with real_euclid_B_def [of a x d]
          obtain l where "l \<ge> 0" and "x - a = l *\<^sub>R (d - a)" by auto
        from \<open>x - a = l *\<^sub>R (d - a)\<close> and
            \<open>d - a = jd *\<^sub>R (c - a)\<close> and
            scaleR_scaleR
          have "x - a = (l * jd) *\<^sub>R (c - a)" by simp
        hence "\<exists>i. x - a = i *\<^sub>R (c - a)" by auto }
      note xlemma = this
      let ?S = "{j. j \<ge> 1 \<and> (\<exists>y\<in>Y. y - a = j *\<^sub>R (c - a))}"
      from \<open>d \<in> Y\<close> and \<open>jd \<ge> 1\<close> and \<open>d - a = jd *\<^sub>R (c - a)\<close>
        have "?S \<noteq> {}" by auto
      let ?k = "Inf ?S"
      let ?b = "?k *\<^sub>R c + (1 - ?k) *\<^sub>R a"
      from rearrange_real_euclid_B [of ?b a ?k c]
        have "?b - a = ?k *\<^sub>R (c - a)" by simp
      { fix x y
        assume "x \<in> X" and "y \<in> Y"
        from xlemma [of x] and \<open>x \<in> X\<close>
          obtain i where "x - a = i *\<^sub>R (c - a)" by auto
        from ylemma [of y] and \<open>y \<in> Y\<close>
          obtain j where "j \<ge> 1" and "y - a = j *\<^sub>R (c - a)" by auto
        with \<open>y \<in> Y\<close> have "j \<in> ?S" by auto
        then have "?k \<le> j" by (auto intro: cInf_lower)
        { fix h
          assume "h \<in> ?S"
          hence "h \<ge> 1" by simp
          from \<open>h \<in> ?S\<close>
            obtain z where "z \<in> Y" and "z - a = h *\<^sub>R (c - a)" by auto
          from \<open>\<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y\<close> and \<open>x \<in> X\<close> and \<open>z \<in> Y\<close>
            have "B\<^sub>\<real> a x z" by simp
          with real_euclid_B_def [of a x z]
            obtain l where "l \<le> 1" and "x - a = l *\<^sub>R (z - a)" by auto
          with \<open>z - a = h *\<^sub>R (c - a)\<close> and scaleR_scaleR
            have "x - a = (l * h) *\<^sub>R (c - a)" by simp
          with \<open>x - a = i *\<^sub>R (c - a)\<close>
            have "i *\<^sub>R (c - a) = (l * h) *\<^sub>R (c - a)" by auto
          with scaleR_cancel_right and \<open>c - a \<noteq> 0\<close> have "i = l * h" by blast
          with \<open>l \<le> 1\<close> and \<open>h \<ge> 1\<close> have "i \<le> h" by simp }
        with \<open>?S \<noteq> {}\<close> and cInf_greatest [of ?S] have "i \<le> ?k" by simp
        have "y - x = (y - a) - (x - a)" by simp
        with \<open>y - a = j *\<^sub>R (c - a)\<close> and \<open>x - a = i *\<^sub>R (c - a)\<close>
          have "y - x = j *\<^sub>R (c - a) - i *\<^sub>R (c - a)" by simp
        with scaleR_left_diff_distrib [of j i "c - a"]
          have "y - x = (j - i) *\<^sub>R (c - a)" by simp
        have "?b - x = (?b - a) - (x - a)" by simp
        with \<open>?b - a = ?k *\<^sub>R (c - a)\<close> and \<open>x - a = i *\<^sub>R (c - a)\<close>
          have "?b - x = ?k *\<^sub>R (c - a) - i *\<^sub>R (c - a)" by simp
        with scaleR_left_diff_distrib [of ?k i "c - a"]
          have "?b - x = (?k - i) *\<^sub>R (c - a)" by simp
        have "B\<^sub>\<real> x ?b y"
        proof cases
          assume "i = j"
          with \<open>i \<le> ?k\<close> and \<open>?k \<le> j\<close> have "?k = i" by simp
          with \<open>?b - x = (?k - i) *\<^sub>R (c - a)\<close> have "?b - x = 0" by simp
          hence "?b - x = 0 *\<^sub>R (y - x)" by simp
          with real_euclid_B_def [of x ?b y] show "B\<^sub>\<real> x ?b y" by auto
        next
          assume "i \<noteq> j"
          with \<open>i \<le> ?k\<close> and \<open>?k \<le> j\<close> have "j - i > 0" by simp
          with \<open>y - x = (j - i) *\<^sub>R (c - a)\<close> and scaleR_scaleR
            have "c - a = (1 / (j - i)) *\<^sub>R (y - x)" by simp
          with \<open>?b - x = (?k - i) *\<^sub>R (c - a)\<close> and scaleR_scaleR
            have "?b - x = ((?k - i) / (j - i)) *\<^sub>R (y - x)" by simp
          let ?l = "(?k - i) / (j - i)"
          from \<open>?k \<le> j\<close> have "?k - i \<le> j - i" by simp
          with \<open>j - i > 0\<close> have "?l \<le> 1" by simp
          from \<open>i \<le> ?k\<close> and \<open>j - i > 0\<close> and pos_le_divide_eq [of "j - i" 0 "?k - i"]
            have "?l \<ge> 0" by simp
          with real_euclid_B_def [of x ?b y] and
              \<open>?l \<le> 1\<close> and
              \<open>?b - x = ?l *\<^sub>R (y - x)\<close>
            show "B\<^sub>\<real> x ?b y" by auto
        qed }
      thus "\<exists>b. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> x b y" by auto
    qed }
  thus "\<forall>X Y. (\<exists>a. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> a x y) \<longrightarrow>
          (\<exists>b. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B\<^sub>\<real> x b y)"
    by auto
qed

subsection "Real Euclidean space satisfies the Euclidean axiom"

lemma rearrange_real_euclid_B_2:
  fixes a b c :: "real^('n::finite)"
  assumes "l \<noteq> 0"
  shows "b - a = l *\<^sub>R (c - a) \<longleftrightarrow> c = (1/l) *\<^sub>R b + (1 - 1/l) *\<^sub>R a"
proof
  from scaleR_right_diff_distrib [of "1/l" b a]
    have "(1/l) *\<^sub>R (b - a) = c - a \<longleftrightarrow> (1/l) *\<^sub>R b - (1/l) *\<^sub>R a + a = c" by auto
  also with scaleR_left_diff_distrib [of 1 "1/l" a]
    have "\<dots> \<longleftrightarrow> c = (1/l) *\<^sub>R b + (1 - 1/l) *\<^sub>R a" by auto
  finally have eq:
    "(1/l) *\<^sub>R (b - a) = c - a \<longleftrightarrow> c = (1/l) *\<^sub>R b + (1 - 1/l) *\<^sub>R a" .
  { assume "b - a = l *\<^sub>R (c - a)"
    with \<open>l \<noteq> 0\<close> have "(1/l) *\<^sub>R (b - a) = c - a" by simp
    with eq show "c = (1/l) *\<^sub>R b + (1 - 1/l) *\<^sub>R a" .. }
  { assume "c = (1/l) *\<^sub>R b + (1 - 1/l) *\<^sub>R a"
    with eq have "(1/l) *\<^sub>R (b - a) = c - a" ..
    hence "l *\<^sub>R (1/l) *\<^sub>R (b - a) = l *\<^sub>R (c - a)" by simp
    with \<open>l \<noteq> 0\<close> show "b - a = l *\<^sub>R (c - a)" by simp }
qed

interpretation real_euclid: tarski_space real_euclid_C real_euclid_B
proof
  { fix a b c d t
    assume "B\<^sub>\<real> a d t" and "B\<^sub>\<real> b d c" and "a \<noteq> d"
    from real_euclid_B_def [of a d t] and \<open>B\<^sub>\<real> a d t\<close>
      obtain j where "j \<ge> 0" and "j \<le> 1" and "d - a = j *\<^sub>R (t - a)" by auto
    from \<open>d - a = j *\<^sub>R (t - a)\<close> and \<open>a \<noteq> d\<close> have "j \<noteq> 0" by auto
    with \<open>d - a = j *\<^sub>R (t - a)\<close> and rearrange_real_euclid_B_2
      have "t = (1/j) *\<^sub>R d + (1 - 1/j) *\<^sub>R a" by auto
    let ?x = "(1/j) *\<^sub>R b + (1 - 1/j) *\<^sub>R a"
    let ?y = "(1/j) *\<^sub>R c + (1 - 1/j) *\<^sub>R a"
    from \<open>j \<noteq> 0\<close> and rearrange_real_euclid_B_2 have
      "b - a = j *\<^sub>R (?x - a)" and "c - a = j *\<^sub>R (?y - a)" by auto
    with real_euclid_B_def and \<open>j \<ge> 0\<close> and \<open>j \<le> 1\<close> have
      "B\<^sub>\<real> a b ?x" and "B\<^sub>\<real> a c ?y" by auto
    from real_euclid_B_def and \<open>B\<^sub>\<real> b d c\<close> obtain k where
      "k \<ge> 0" and "k \<le> 1" and "d - b = k *\<^sub>R (c - b)" by blast
    from \<open>t = (1/j) *\<^sub>R d + (1 - 1/j) *\<^sub>R a\<close> have
      "t - ?x = (1/j) *\<^sub>R d - (1/j) *\<^sub>R b" by simp
    also from scaleR_right_diff_distrib [of "1/j" d b] have
      "\<dots> = (1/j) *\<^sub>R (d - b)" by simp
    also from \<open>d - b = k *\<^sub>R (c - b)\<close> have
      "\<dots> = k *\<^sub>R (1/j) *\<^sub>R (c - b)" by simp
    also from scaleR_right_diff_distrib [of "1/j" c b] have
      "\<dots> = k *\<^sub>R (?y - ?x)" by simp
    finally have "t - ?x = k *\<^sub>R (?y - ?x)" .
    with real_euclid_B_def and \<open>k \<ge> 0\<close> and \<open>k \<le> 1\<close> have "B\<^sub>\<real> ?x t ?y" by blast
    with \<open>B\<^sub>\<real> a b ?x\<close> and \<open>B\<^sub>\<real> a c ?y\<close> have
      "\<exists>x y. B\<^sub>\<real> a b x \<and> B\<^sub>\<real> a c y \<and> B\<^sub>\<real> x t y" by auto }
  thus "\<forall>a b c d t. B\<^sub>\<real> a d t \<and> B\<^sub>\<real> b d c \<and> a \<noteq> d \<longrightarrow>
            (\<exists>x y. B\<^sub>\<real> a b x \<and> B\<^sub>\<real> a c y \<and> B\<^sub>\<real> x t y)"
    by auto
qed

subsection "The real Euclidean plane"

lemma Col_dep2:
  "real_euclid.Col a b c \<longleftrightarrow> dep2 (b - a) (c - a)"
proof -
  from real_euclid.Col_def have
    "real_euclid.Col a b c \<longleftrightarrow> B\<^sub>\<real> a b c \<or> B\<^sub>\<real> b c a \<or> B\<^sub>\<real> c a b" by auto
  moreover from dep2_def have
    "dep2 (b - a) (c - a) \<longleftrightarrow> (\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w)"
    by auto
  moreover
  { assume "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> b c a \<or> B\<^sub>\<real> c a b"
    moreover
    { assume "B\<^sub>\<real> a b c"
      with real_euclid_B_def obtain l where "b - a = l *\<^sub>R (c - a)" by blast
      moreover have "c - a = 1 *\<^sub>R (c - a)" by simp
      ultimately have "\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w" by blast }
    moreover
    { assume "B\<^sub>\<real> b c a"
      with real_euclid_B_def obtain l where "c - b = l *\<^sub>R (a - b)" by blast
      moreover have "c - a = (c - b) - (a - b)" by simp
      ultimately have "c - a = l *\<^sub>R (a - b) - (a - b)" by simp
      with scaleR_left_diff_distrib [of l 1 "a - b"] have
        "c - a = (l - 1) *\<^sub>R (a - b)" by simp
      moreover from scaleR_minus_left [of 1 "a - b"] have
        "b - a = (-1) *\<^sub>R (a - b)" by simp
      ultimately have "\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w" by blast }
    moreover
    { assume "B\<^sub>\<real> c a b"
      with real_euclid_B_def obtain l where "a - c = l *\<^sub>R (b - c)" by blast
      moreover have "c - a = -(a - c)" by simp
      ultimately have "c - a = -(l *\<^sub>R (b - c))" by simp
      with scaleR_minus_left have "c - a = (-l) *\<^sub>R (b - c)" by simp
      moreover have "b - a = (b - c) + (c - a)" by simp
      ultimately have "b - a = 1 *\<^sub>R (b - c) + (-l) *\<^sub>R (b - c)" by simp
      with scaleR_left_distrib [of 1 "-l" "b - c"] have
        "b - a = (1 + (-l)) *\<^sub>R (b - c)" by simp
      with \<open>c - a = (-l) *\<^sub>R (b - c)\<close> have
        "\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w" by blast }
    ultimately have "\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w" by auto }
  moreover
  { assume "\<exists>w r s. b - a = r *\<^sub>R w \<and> c - a = s *\<^sub>R w"
    then obtain w r s where "b - a = r *\<^sub>R w" and "c - a = s *\<^sub>R w" by auto
    have "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> b c a \<or> B\<^sub>\<real> c a b"
    proof cases
      assume "s = 0"
      with \<open>c - a = s *\<^sub>R w\<close> have "a = c" by simp
      with real_euclid.th3_1 have "B\<^sub>\<real> b c a" by simp
      thus ?thesis by simp
    next
      assume "s \<noteq> 0"
      with \<open>c - a = s *\<^sub>R w\<close> have "w = (1/s) *\<^sub>R (c - a)" by simp
      with \<open>b - a = r *\<^sub>R w\<close> have "b - a = (r/s) *\<^sub>R (c - a)" by simp
      have "r/s < 0 \<or> (r/s \<ge> 0 \<and> r/s \<le> 1) \<or> r/s > 1" by arith
      moreover
      { assume "r/s \<ge> 0 \<and> r/s \<le> 1"
        with real_euclid_B_def and \<open>b - a = (r/s) *\<^sub>R (c - a)\<close> have "B\<^sub>\<real> a b c"
          by auto
        hence ?thesis by simp }
      moreover
      { assume "r/s > 1"
        with \<open>b - a = (r/s) *\<^sub>R (c - a)\<close> have "c - a = (s/r) *\<^sub>R (b - a)" by auto
        from \<open>r/s > 1\<close> and le_imp_inverse_le [of 1 "r/s"] have
          "s/r \<le> 1" by simp
        from \<open>r/s > 1\<close> and inverse_positive_iff_positive [of "r/s"] have
          "s/r \<ge> 0" by simp
        with real_euclid_B_def
          and \<open>c - a = (s/r) *\<^sub>R (b - a)\<close>
          and \<open>s/r \<le> 1\<close>
        have "B\<^sub>\<real> a c b" by auto
        with real_euclid.th3_2 have "B\<^sub>\<real> b c a" by auto
        hence ?thesis by simp }
      moreover
      { assume "r/s < 0"
        have "b - c = (b - a) + (a - c)" by simp
        with \<open>b - a = (r/s) *\<^sub>R (c - a)\<close> have
          "b - c = (r/s) *\<^sub>R (c - a) + (a - c)" by simp
        have "c - a = -(a - c)" by simp
        with scaleR_minus_right [of "r/s" "a - c"] have
          "(r/s) *\<^sub>R (c - a) = -((r/s) *\<^sub>R (a - c))" by arith
        with \<open>b - c = (r/s) *\<^sub>R (c - a) + (a - c)\<close> have
          "b - c = -(r/s) *\<^sub>R (a - c) + (a - c)" by simp
        with scaleR_left_distrib [of "-(r/s)" 1 "a - c"] have
          "b - c = (-(r/s) + 1) *\<^sub>R (a - c)" by simp
        moreover from \<open>r/s < 0\<close> have "-(r/s) + 1 > 1" by simp
        ultimately have "a - c = (1 / (-(r/s) + 1)) *\<^sub>R (b - c)" by auto
        let ?l = "1 / (-(r/s) + 1)"
        from \<open>-(r/s) + 1 > 1\<close> and le_imp_inverse_le [of 1 "-(r/s) + 1"] have
          "?l \<le> 1" by simp
        from \<open>-(r/s) + 1 > 1\<close>
          and inverse_positive_iff_positive [of "-(r/s) + 1"]
        have
          "?l \<ge> 0" by simp
        with real_euclid_B_def and \<open>?l \<le> 1\<close> and \<open>a - c = ?l *\<^sub>R (b - c)\<close> have
          "B\<^sub>\<real> c a b" by blast
        hence ?thesis by simp }
      ultimately show ?thesis by auto
    qed }
  ultimately show ?thesis by blast
qed

lemma non_Col_example:
  "\<not>(real_euclid.Col 0 (vector [1/2,0] :: real^2) (vector [0,1/2]))"
  (is "\<not> (real_euclid.Col ?a ?b ?c)")
proof -
  { assume "dep2 (?b - ?a) (?c - ?a)"
    with dep2_def [of "?b - ?a" "?c - ?a"] obtain w r s where
      "?b - ?a = r *\<^sub>R w" and "?c - ?a = s *\<^sub>R w" by auto
    have "?b$1 = 1/2" by simp
    with \<open>?b - ?a = r *\<^sub>R w\<close> have "r * (w$1) = 1/2" by simp
    hence "w$1 \<noteq> 0" by auto
    have "?c$1 = 0" by simp
    with \<open>?c - ?a = s *\<^sub>R w\<close> have "s * (w$1) = 0" by simp
    with \<open>w$1 \<noteq> 0\<close> have "s = 0" by simp
    have "?c$2 = 1/2" by simp
    with \<open>?c - ?a = s *\<^sub>R w\<close> have "s * (w$2) = 1/2" by simp
    with \<open>s = 0\<close> have False by simp }
  hence "\<not>(dep2 (?b - ?a) (?c - ?a))" by auto
  with Col_dep2 show "\<not>(real_euclid.Col ?a ?b ?c)" by blast
qed

interpretation real_euclid:
  tarski "real_euclid_C::([real^2, real^2, real^2, real^2] \<Rightarrow> bool)" real_euclid_B
proof
  { let ?a = "0 :: real^2"
    let ?b = "vector [1/2, 0] :: real^2"
    let ?c = "vector [0, 1/2] :: real^2"
    from non_Col_example and real_euclid.Col_def have
      "\<not> B\<^sub>\<real> ?a ?b ?c \<and> \<not> B\<^sub>\<real> ?b ?c ?a \<and> \<not> B\<^sub>\<real> ?c ?a ?b" by auto }
  thus "\<exists>a b c :: real^2. \<not> B\<^sub>\<real> a b c \<and> \<not> B\<^sub>\<real> b c a \<and> \<not> B\<^sub>\<real> c a b"
    by auto
  { fix p q a b c :: "real^2"
    assume "p \<noteq> q" and "a p \<congruent>\<^sub>\<real>  a q" and "b p \<congruent>\<^sub>\<real> b q" and "c p \<congruent>\<^sub>\<real> c q"
    let ?m = "(1/2) *\<^sub>R (p + q)"
    from scaleR_right_distrib [of "1/2" p q] and
      scaleR_right_diff_distrib [of "1/2" q p] and
      scaleR_left_diff_distrib [of "1/2" 1 p]
    have "?m - p = (1/2) *\<^sub>R (q - p)" by simp
    with \<open>p \<noteq> q\<close> have "?m - p \<noteq> 0" by simp
    from scaleR_right_distrib [of "1/2" p q] and
      scaleR_right_diff_distrib [of "1/2" p q] and
      scaleR_left_diff_distrib [of "1/2" 1 q]
    have "?m - q = (1/2) *\<^sub>R (p - q)" by simp
    with \<open>?m - p = (1/2) *\<^sub>R (q - p)\<close>
      and scaleR_minus_right [of "1/2" "q - p"]
    have "?m - q = -(?m - p)" by simp
    with norm_minus_cancel [of "?m - p"] have
      "(norm (?m - q))\<^sup>2 = (norm (?m - p))\<^sup>2" by (simp only: norm_minus_cancel)
    { fix d
      assume "d p \<congruent>\<^sub>\<real> d q"
      hence "(norm (d - p))\<^sup>2 = (norm (d - q))\<^sup>2" by simp
      have "(d - ?m) \<bullet> (?m - p) = 0"
      proof -
        have "d + (-q) = d - q" by simp
        have "d + (-p) = d - p" by simp
        with dot_norm [of "d - ?m" "?m - p"] have
          "(d - ?m) \<bullet> (?m - p) =
          ((norm (d - p))\<^sup>2 - (norm (d - ?m))\<^sup>2 - (norm(?m - p))\<^sup>2) / 2"
          by simp
        also from \<open>(norm (d - p))\<^sup>2 = (norm (d - q))\<^sup>2\<close>
          and \<open>(norm (?m - q))\<^sup>2 = (norm (?m - p))\<^sup>2\<close>
        have
          "\<dots> = ((norm (d - q))\<^sup>2 - (norm (d - ?m))\<^sup>2 - (norm(?m - q))\<^sup>2) / 2"
          by simp
        also from dot_norm [of "d - ?m" "?m - q"]
          and \<open>d + (-q) = d - q\<close>
        have
          "\<dots> = (d - ?m) \<bullet> (?m - q)" by simp
        also from inner_minus_right [of "d - ?m" "?m - p"]
          and \<open>?m - q = -(?m - p)\<close>
        have
          "\<dots> = -((d - ?m) \<bullet> (?m - p))" by (simp only: inner_minus_left)
        finally have "(d - ?m) \<bullet> (?m - p) = -((d - ?m) \<bullet> (?m - p))" .
        thus "(d - ?m) \<bullet> (?m - p) = 0" by arith
      qed }
    note m_lemma = this
    with \<open>a p \<congruent>\<^sub>\<real> a q\<close> have "(a - ?m) \<bullet> (?m - p) = 0" by simp
    { fix d
      assume "d p \<congruent>\<^sub>\<real> d q"
      with m_lemma have "(d - ?m) \<bullet> (?m - p) = 0" by simp
      with dot_left_diff_distrib [of "d - ?m" "a - ?m" "?m - p"]
        and \<open>(a - ?m) \<bullet> (?m - p) = 0\<close>
      have "(d - a) \<bullet> (?m - p) = 0" by (simp add: inner_diff_left inner_diff_right) }
    with \<open>b p \<congruent>\<^sub>\<real> b q\<close> and \<open>c p \<congruent>\<^sub>\<real> c q\<close> have
      "(b - a) \<bullet> (?m - p) = 0" and "(c - a) \<bullet> (?m - p) = 0" by simp+
    with real2_orthogonal_dep2 and \<open>?m - p \<noteq> 0\<close> have "dep2 (b - a) (c - a)"
      by blast
    with Col_dep2 have "real_euclid.Col a b c" by auto
    with real_euclid.Col_def have "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> b c a \<or> B\<^sub>\<real> c a b" by auto }
  thus "\<forall>p q a b c :: real^2.
          p \<noteq> q \<and> a p \<congruent>\<^sub>\<real> a q \<and> b p \<congruent>\<^sub>\<real> b q \<and> c p \<congruent>\<^sub>\<real> c q \<longrightarrow>
            B\<^sub>\<real> a b c \<or> B\<^sub>\<real> b c a \<or> B\<^sub>\<real> c a b"
    by blast
qed

subsection \<open>Special cases of theorems of Tarski's geometry\<close>

lemma real_euclid_B_disjunction:
  assumes "l \<ge> 0" and "b - a = l *\<^sub>R (c - a)"
  shows "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b"
proof cases
  assume "l \<le> 1"
  with \<open>l \<ge> 0\<close> and \<open>b - a = l *\<^sub>R (c - a)\<close>
  have "B\<^sub>\<real> a b c" by (unfold real_euclid_B_def) (simp add: exI [of _ l])
  thus "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b" ..
next
  assume "\<not> (l \<le> 1)"
  hence "1/l \<le> 1" by simp

  from \<open>l \<ge> 0\<close> have "1/l \<ge> 0" by simp

  from \<open>b - a = l *\<^sub>R (c - a)\<close>
  have "(1/l) *\<^sub>R (b - a) = (1/l) *\<^sub>R (l *\<^sub>R (c - a))" by simp
  with \<open>\<not> (l \<le> 1)\<close> have "c - a = (1/l) *\<^sub>R (b - a)" by simp
  with \<open>1/l \<ge> 0\<close> and \<open>1/l \<le> 1\<close>
  have "B\<^sub>\<real> a c b" by (unfold real_euclid_B_def) (simp add: exI [of _ "1/l"])
  thus "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b" ..
qed

text \<open>The following are true in Tarski's geometry,
  but to prove this would require much more development of it,
  so only the Euclidean case is proven here.\<close>

theorem real_euclid_th5_1:
  assumes "a \<noteq> b" and "B\<^sub>\<real> a b c" and "B\<^sub>\<real> a b d"
  shows "B\<^sub>\<real> a c d \<or> B\<^sub>\<real> a d c"
proof -
  from \<open>B\<^sub>\<real> a b c\<close> and \<open>B\<^sub>\<real> a b d\<close>
  obtain l and m where "l \<ge> 0" and "b - a = l *\<^sub>R (c - a)"
    and "m \<ge> 0" and "b - a = m *\<^sub>R (d - a)"
    by (unfold real_euclid_B_def) auto
  from \<open>b - a = m *\<^sub>R (d - a)\<close> and \<open>a \<noteq> b\<close> have "m \<noteq> 0" by auto

  from \<open>l \<ge> 0\<close> and \<open>m \<ge> 0\<close> have "l/m \<ge> 0" by (simp add: zero_le_divide_iff)

  from \<open>b - a = l *\<^sub>R (c - a)\<close> and \<open>b - a = m *\<^sub>R (d - a)\<close>
  have "m *\<^sub>R (d - a) = l *\<^sub>R (c - a)" by simp
  hence "(1/m) *\<^sub>R (m *\<^sub>R (d - a)) = (1/m) *\<^sub>R (l *\<^sub>R (c - a))" by simp
  with \<open>m \<noteq> 0\<close> have "d - a = (l/m) *\<^sub>R (c - a)" by simp
  with \<open>l/m \<ge> 0\<close> and real_euclid_B_disjunction
  show "B\<^sub>\<real> a c d \<or> B\<^sub>\<real> a d c" by auto
qed

theorem real_euclid_th5_3:
  assumes "B\<^sub>\<real> a b d" and "B\<^sub>\<real> a c d"
  shows "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b"
proof -
  from \<open>B\<^sub>\<real> a b d\<close> and \<open>B\<^sub>\<real> a c d\<close>
  obtain l and m where "l \<ge> 0" and "b - a = l *\<^sub>R (d - a)"
    and "m \<ge> 0" and "c - a = m *\<^sub>R (d - a)"
    by (unfold real_euclid_B_def) auto

  show "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b"
  proof cases
    assume "l = 0"
    with \<open>b - a = l *\<^sub>R (d - a)\<close> have "b - a = l *\<^sub>R (c - a)" by simp
    with \<open>l = 0\<close>
    have "B\<^sub>\<real> a b c" by (unfold real_euclid_B_def) (simp add: exI [of _ l])
    thus "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b" ..
  next
    assume "l \<noteq> 0"

    from \<open>l \<ge> 0\<close> and \<open>m \<ge> 0\<close> have "m/l \<ge> 0" by (simp add: zero_le_divide_iff)

    from \<open>b - a = l *\<^sub>R (d - a)\<close>
    have "(1/l) *\<^sub>R (b - a) = (1/l) *\<^sub>R (l *\<^sub>R (d - a))" by simp
    with \<open>l \<noteq> 0\<close> have "d - a = (1/l) *\<^sub>R (b - a)" by simp
    with \<open>c - a = m *\<^sub>R (d - a)\<close> have "c - a = (m/l) *\<^sub>R (b - a)" by simp
    with \<open>m/l \<ge> 0\<close> and real_euclid_B_disjunction
    show "B\<^sub>\<real> a b c \<or> B\<^sub>\<real> a c b" by auto
  qed
qed

end
