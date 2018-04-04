(*  Title:       Tarski's geometry
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "Tarski's geometry"

theory Tarski
  imports Complex_Main Miscellany Metric
begin

subsection "The axioms"
text {* The axioms, and all theorems beginning with \emph{th}
  followed by a number, are based on corresponding axioms and
  theorems in \cite{schwabhauser}. *}

locale tarski_first3 =
  fixes C :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"     ("_ _ \<congruent> _ _" [99,99,99,99] 50)
  assumes A1: "\<forall>a b. a b \<congruent> b a"
  and A2: "\<forall>a b p q r s. a b \<congruent> p q \<and> a b \<congruent> r s \<longrightarrow> p q \<congruent> r s"
  and A3: "\<forall>a b c. a b \<congruent> c c \<longrightarrow> a = b"

locale tarski_first5 = tarski_first3 +
  fixes B :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes A4: "\<forall>q a b c. \<exists>x. B q a x \<and> a x \<congruent> b c"
  and A5: "\<forall>a b c d a' b' c' d'. a \<noteq> b \<and> B a b c \<and> B a' b' c'
                                               \<and> a b \<congruent> a' b' \<and> b c \<congruent> b' c' \<and> a d \<congruent> a' d' \<and> b d \<congruent> b' d'
                                       \<longrightarrow> c d \<congruent> c' d'"

locale tarski_absolute_space = tarski_first5 +
  assumes A6: "\<forall>a b. B a b a \<longrightarrow> a = b"
  and A7: "\<forall>a b c p q. B a p c \<and> B b q c \<longrightarrow> (\<exists>x. B p x b \<and> B q x a)"
  and A11: "\<forall>X Y. (\<exists>a. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B a x y)
                        \<longrightarrow> (\<exists>b. \<forall>x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B x b y)"

locale tarski_absolute = tarski_absolute_space +
  assumes A8: "\<exists>a b c. \<not> B a b c \<and> \<not> B b c a \<and> \<not> B c a b"
  and A9: "\<forall>p q a b c. p \<noteq> q \<and> a p \<congruent> a q \<and> b p \<congruent> b q \<and> c p \<congruent> c q
                             \<longrightarrow> B a b c \<or> B b c a \<or> B c a b"

locale tarski_space = tarski_absolute_space +
  assumes A10: "\<forall>a b c d t. B a d t \<and> B b d c \<and> a \<noteq> d 
                                    \<longrightarrow> (\<exists>x y. B a b x \<and> B a c y \<and> B x t y)"

locale tarski = tarski_absolute + tarski_space

subsection "Semimetric spaces satisfy the first three axioms"

context semimetric
begin
  definition smC :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" ("_ _ \<congruent>\<^sub>s\<^sub>m _ _" [99,99,99,99] 50)
    where [simp]: "a b \<congruent>\<^sub>s\<^sub>m c d \<equiv> dist a b = dist c d"
end

sublocale semimetric < tarski_first3 smC
proof
  from symm show "\<forall>a b. a b \<congruent>\<^sub>s\<^sub>m b a" by simp
  show "\<forall>a b p q r s. a b \<congruent>\<^sub>s\<^sub>m p q \<and> a b \<congruent>\<^sub>s\<^sub>m r s \<longrightarrow> p q \<congruent>\<^sub>s\<^sub>m r s" by simp
  show "\<forall>a b c. a b \<congruent>\<^sub>s\<^sub>m c c \<longrightarrow> a = b" by simp
qed

subsection "Some consequences of the first three axioms"

context tarski_first3
begin
  notation %invisible C ("_ _ \<equiv> _ _" [99,99,99,99] 50)
  lemma A1': "a b \<congruent> b a"
    by (simp add: A1)

  lemma A2': "\<lbrakk>a b \<congruent> p q; a b \<congruent> r s\<rbrakk> \<Longrightarrow> p q \<congruent> r s"
  proof -
    assume "a b \<congruent> p q" and "a b \<congruent> r s"
    with A2 show ?thesis by blast
  qed

  lemma A3': "a b \<congruent> c c \<Longrightarrow> a = b"
    by (simp add: A3)

  theorem th2_1: "a b \<congruent> a b"
  proof -
    from A2' [of b a a b a b] and A1' [of b a] show ?thesis by simp
  qed

  theorem th2_2: "a b \<congruent> c d \<Longrightarrow> c d \<congruent> a b"
  proof -
    assume "a b \<congruent> c d"
    with A2' [of a b c d a b] and th2_1 [of a b] show ?thesis by simp
  qed

  theorem th2_3: "\<lbrakk>a b \<congruent> c d; c d \<congruent> e f\<rbrakk> \<Longrightarrow> a b \<congruent> e f"
  proof -
    assume "a b \<congruent> c d"
    with th2_2 [of a b c d] have "c d \<congruent> a b" by simp
    assume "c d \<congruent> e f"
    with A2' [of c d a b e f] and `c d \<congruent> a b` show ?thesis by simp
  qed

  theorem th2_4: "a b \<congruent> c d \<Longrightarrow> b a \<congruent> c d"
  proof -
    assume "a b \<congruent> c d"
    with th2_3 [of b a a b c d] and A1' [of b a] show ?thesis by simp
  qed

  theorem th2_5: "a b \<congruent> c d \<Longrightarrow> a b \<congruent> d c"
  proof -
    assume "a b \<congruent> c d"
    with th2_3 [of a b c d d c] and A1' [of c d] show ?thesis by simp
  qed

  definition is_segment :: "'p set \<Rightarrow> bool" where
  "is_segment X \<equiv> \<exists>x y. X = {x, y}"

  definition segments :: "'p set set" where
  "segments = {X. is_segment X}"

  definition SC :: "'p set \<Rightarrow> 'p set \<Rightarrow> bool" where
  "SC X Y \<equiv> \<exists>w x y z. X = {w, x} \<and> Y = {y, z} \<and> w x \<congruent> y z"

  definition SC_rel :: "('p set \<times> 'p set) set" where
  "SC_rel = {(X, Y) | X Y. SC X Y}"

  lemma left_segment_congruence:
    assumes "{a, b} = {p, q}" and "p q \<congruent> c d"
    shows "a b \<congruent> c d"
  proof cases
    assume "a = p"
    with unordered_pair_element_equality [of a b p q] and `{a, b} = {p, q}`
      have "b = q" by simp
    with `p q \<congruent> c d` and `a = p` show ?thesis by simp
  next
    assume "a \<noteq> p"
    with `{a, b} = {p, q}` have "a = q" by auto
    with unordered_pair_element_equality [of a b q p] and `{a, b} = {p, q}`
      have "b = p" by auto
    with `p q \<congruent> c d` and `a = q` have "b a \<congruent> c d" by simp
    with th2_4 [of b a c d] show ?thesis by simp
  qed

  lemma right_segment_congruence:
    assumes "{c, d} = {p, q}" and "a b \<congruent> p q"
    shows "a b \<congruent> c d"
  proof -
    from th2_2 [of a b p q] and `a b \<congruent> p q` have "p q \<congruent> a b" by simp
    with left_segment_congruence [of c d p q a b] and `{c, d} = {p, q}`
      have "c d \<congruent> a b" by simp
    with th2_2 [of c d a b] show ?thesis by simp
  qed

  lemma C_SC_equiv: "a b \<congruent> c d = SC {a, b} {c, d}"
  proof
    assume "a b \<congruent> c d"
    with SC_def [of "{a, b}" "{c, d}"] show "SC {a, b} {c, d}" by auto
  next
    assume "SC {a, b} {c, d}"
    with SC_def [of "{a, b}" "{c, d}"]
      obtain w x y z where "{a, b} = {w, x}" and "{c, d} = {y, z}" and "w x \<congruent> y z"
        by blast
    from left_segment_congruence [of a b w x y z] and
        `{a, b} = {w, x}` and
        `w x \<congruent> y z`
      have "a b \<congruent> y z" by simp
    with right_segment_congruence [of c d y z a b] and `{c, d} = {y, z}`
      show "a b \<congruent> c d" by simp
  qed

  lemmas SC_refl = th2_1 [simplified]

  lemma SC_rel_refl: "refl_on segments SC_rel"
  proof -
    note refl_on_def [of segments SC_rel]
    moreover
    { fix Z
      assume "Z \<in> SC_rel"
      with SC_rel_def obtain X Y where "Z = (X, Y)" and "SC X Y" by auto
      from `SC X Y` and SC_def [of X Y]
        have "\<exists>w x. X = {w, x}" and "\<exists>y z. Y = {y, z}" by auto
      with is_segment_def [of X] and is_segment_def [of Y]
        have "is_segment X" and "is_segment Y" by auto
      with segments_def have "X \<in> segments" and "Y \<in> segments" by auto
      with `Z = (X, Y)` have "Z \<in> segments \<times> segments" by simp }
    hence "SC_rel \<subseteq> segments \<times> segments" by auto
    moreover
    { fix X
      assume "X \<in> segments"
      with segments_def have "is_segment X" by auto
      with is_segment_def [of X] obtain x y where "X = {x, y}" by auto
      with SC_def [of X X] and SC_refl have "SC X X" by (simp add: C_SC_equiv)
      with SC_rel_def have "(X, X) \<in> SC_rel" by simp }
    hence "\<forall>X. X \<in> segments \<longrightarrow> (X, X) \<in> SC_rel" by simp
    ultimately show ?thesis by simp
  qed

  lemma SC_sym:
    assumes "SC X Y"
    shows "SC Y X"
  proof -
    from SC_def [of X Y] and `SC X Y`
      obtain w x y z where "X = {w, x}" and "Y = {y, z}" and "w x \<congruent> y z"
        by auto
    from th2_2 [of w x y z] and `w x \<congruent> y z` have "y z \<congruent> w x" by simp
    with SC_def [of Y X] and `X = {w, x}` and `Y = {y, z}`
      show "SC Y X" by (simp add: C_SC_equiv)
  qed

  lemma SC_sym': "SC X Y = SC Y X"
  proof
    assume "SC X Y"
    with SC_sym [of X Y] show "SC Y X" by simp
  next
    assume "SC Y X"
    with SC_sym [of Y X] show "SC X Y" by simp
  qed

  lemma SC_rel_sym: "sym SC_rel"
  proof -
    { fix X Y
      assume "(X, Y) \<in> SC_rel"
      with SC_rel_def have "SC X Y" by simp
      with SC_sym' have "SC Y X" by simp
      with SC_rel_def have "(Y, X) \<in> SC_rel" by simp }
    with sym_def [of SC_rel] show ?thesis by blast
  qed

  lemma SC_trans:
    assumes "SC X Y" and "SC Y Z"
    shows "SC X Z"
  proof -
    from SC_def [of X Y] and `SC X Y`
      obtain w x y z where "X = {w, x}" and "Y = {y, z}" and "w x \<congruent> y z"
        by auto
    from SC_def [of Y Z] and `SC Y Z`
      obtain p q r s where "Y = {p, q}" and "Z = {r, s}" and "p q \<congruent> r s" by auto
    from `Y = {y, z}` and `Y = {p, q}` and `p q \<congruent> r s`
      have "y z \<congruent> r s" by (simp add: C_SC_equiv)
    with th2_3 [of w x y z r s] and `w x \<congruent> y z` have "w x \<congruent> r s" by simp
    with SC_def [of X Z] and `X = {w, x}` and `Z = {r, s}`
      show "SC X Z" by (simp add: C_SC_equiv)
  qed

  lemma SC_rel_trans: "trans SC_rel"
  proof -
    { fix X Y Z
      assume "(X, Y) \<in> SC_rel" and "(Y, Z) \<in> SC_rel"
      with SC_rel_def have "SC X Y" and "SC Y Z" by auto
      with SC_trans [of X Y Z] have "SC X Z" by simp
      with SC_rel_def have "(X, Z) \<in> SC_rel" by simp }
    with trans_def [of SC_rel] show ?thesis by blast
  qed

  lemma A3_reversed:
    assumes "a a \<congruent> b c"
    shows "b = c"
  proof -
    from `a a \<congruent> b c` have "b c \<congruent> a a" by (rule th2_2)
    thus "b = c" by (rule A3')
  qed
  
  lemma equiv_segments_SC_rel: "equiv segments SC_rel"
    by (simp add: equiv_def SC_rel_refl SC_rel_sym SC_rel_trans)
    
end

subsection "Some consequences of the first five axioms"

context tarski_first5
begin
  lemma A4': "\<exists>x. B q a x \<and> a x \<congruent> b c"
    by (simp add: A4 [simplified])

  theorem th2_8: "a a \<congruent> b b"
  proof -
    from A4' [of _ a b b] obtain x where "a x \<congruent> b b" by auto
    with A3' [of a x b] have "x = a" by simp
    with `a x \<congruent> b b` show ?thesis by simp
  qed

  definition OFS :: "['p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool" where
   "OFS a b c d a' b' c' d' \<equiv>
      B a b c \<and> B a' b' c' \<and> a b \<congruent> a' b' \<and> b c \<congruent> b' c' \<and> a d \<congruent> a' d' \<and> b d \<congruent> b' d'"

  lemma A5': "\<lbrakk>OFS a b c d a' b' c' d'; a \<noteq> b\<rbrakk> \<Longrightarrow> c d \<congruent> c' d'"
  proof -
    assume "OFS a b c d a' b' c' d'" and "a \<noteq> b"
    with A5 and OFS_def show ?thesis by blast
  qed

  theorem th2_11:
    assumes hypotheses:
      "B a b c"
      "B a' b' c'"
      "a b \<congruent> a' b'"
      "b c \<congruent> b' c'"
    shows "a c \<congruent> a' c'"
  proof cases
    assume "a = b"
    with `a b \<congruent> a' b'` have "a' = b'" by (simp add: A3_reversed)
    with `b c \<congruent> b' c'` and `a = b` show ?thesis by simp
  next
    assume "a \<noteq> b"
    moreover
      note A5' [of a b c a a' b' c' a'] and
        unordered_pair_equality [of a c] and
        unordered_pair_equality [of a' c']
    moreover
      from OFS_def [of a b c a a' b' c' a'] and
          hypotheses and
          th2_8 [of a a'] and
          unordered_pair_equality [of a b] and
          unordered_pair_equality [of a' b']
        have "OFS a b c a a' b' c' a'" by (simp add: C_SC_equiv)
    ultimately show ?thesis by (simp add: C_SC_equiv)
  qed

  lemma A4_unique:
    assumes "q \<noteq> a" and "B q a x" and "a x \<congruent> b c"
    and "B q a x'" and "a x' \<congruent> b c"
    shows "x = x'"
  proof -
    from SC_sym' and SC_trans and C_SC_equiv and `a x' \<congruent> b c` and `a x \<congruent> b c`
      have "a x \<congruent> a x'" by blast
    with th2_11 [of q a x q a x'] and `B q a x` and `B q a x'` and SC_refl
      have "q x \<congruent> q x'" by simp
    with OFS_def [of q a x x q a x x'] and
        `B q a x` and
        SC_refl and
        `a x \<congruent> a x'`
      have "OFS q a x x q a x x'" by simp
    with A5' [of q a x x q a x x'] and `q \<noteq> a` have "x x \<congruent> x x'" by simp
    thus "x = x'" by (rule A3_reversed)
  qed

  theorem th2_12:
    assumes "q \<noteq> a"
    shows "\<exists>!x. B q a x \<and> a x \<congruent> b c"
    using `q \<noteq> a` and A4' and A4_unique
    by blast
end

subsection "Simple theorems about betweenness"

theorem (in tarski_first5) th3_1: "B a b b"
proof -
  from A4 [rule_format, of a b b b] obtain x where "B a b x" and "b x \<congruent> b b" by auto
  from A3 [rule_format, of b x b] and `b x \<congruent> b b` have "b = x" by simp
  with `B a b x` show "B a b b" by simp
qed

context tarski_absolute_space
begin
  lemma A6':
    assumes "B a b a"
    shows "a = b"
  proof -
    from A6 and `B a b a` show "a = b" by simp
  qed
    
  lemma A7':
    assumes "B a p c" and "B b q c"
    shows "\<exists>x. B p x b \<and> B q x a"
  proof -
    from A7 and `B a p c` and `B b q c` show ?thesis by blast
  qed

  lemma A11':
    assumes "\<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B a x y"
    shows "\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B x b y"
  proof -
    from assms have "\<exists> a. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B a x y" by (rule exI)
    thus "\<exists> b. \<forall> x y. x \<in> X \<and> y \<in> Y \<longrightarrow> B x b y" by (rule A11 [rule_format])
  qed

  theorem th3_2:
    assumes "B a b c"
    shows "B c b a"
  proof -
    from th3_1 have "B b c c" by simp
    with A7' and `B a b c` obtain x where "B b x b" and "B c x a" by blast
    from A6' and `B b x b` have "x = b" by auto
    with `B c x a` show "B c b a" by simp
  qed

  theorem th3_4:
    assumes "B a b c" and "B b a c"
    shows "a = b"
  proof -
    from `B a b c` and `B b a c` and A7' [of a b c b a]
    obtain x where "B b x b" and "B a x a" by auto
    hence "b = x" and "a = x" by (simp_all add: A6')
    thus "a = b" by simp
  qed

  theorem th3_5_1:
    assumes "B a b d" and "B b c d"
    shows "B a b c"
  proof -
    from `B a b d` and `B b c d` and A7' [of a b d b c]
    obtain x where "B b x b" and "B c x a" by auto
    from `B b x b` have "b = x" by (rule A6')
    with `B c x a` have "B c b a" by simp
    thus "B a b c" by (rule th3_2)
  qed

  theorem th3_6_1:
    assumes "B a b c" and "B a c d"
    shows "B b c d"
  proof -
    from `B a c d` and `B a b c` and th3_2 have "B d c a" and "B c b a" by fast+
    hence "B d c b" by (rule th3_5_1)
    thus "B b c d" by (rule th3_2)
  qed

  theorem th3_7_1:
    assumes "b \<noteq> c" and "B a b c" and "B b c d"
    shows "B a c d"
  proof -
    from A4' obtain x where "B a c x" and "c x \<congruent> c d" by fast
    from `B a b c` and `B a c x` have "B b c x" by (rule th3_6_1)
    have "c d \<congruent> c d" by (rule th2_1)
    with `b \<noteq> c` and `B b c x` and `c x \<congruent> c d` and `B b c d`
    have "x = d" by (rule A4_unique)
    with `B a c x` show "B a c d" by simp
  qed

  theorem th3_7_2:
    assumes "b \<noteq> c" and "B a b c" and "B b c d"
    shows "B a b d"
  proof -
    from `B b c d` and `B a b c` and th3_2 have "B d c b" and "B c b a" by fast+
    with `b \<noteq> c` and th3_7_1 [of c b d a] have "B d b a" by simp
    thus "B a b d" by (rule th3_2)
  qed
end

subsection "Simple theorems about congruence and betweenness"

definition (in tarski_first5) Col :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "Col a b c \<equiv> B a b c \<or> B b c a \<or> B c a b"

end
