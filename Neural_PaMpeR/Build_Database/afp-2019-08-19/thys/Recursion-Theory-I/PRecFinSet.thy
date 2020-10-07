(*  Title:       Primitive recursive coding of finite sets
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Finite sets\<close>

theory PRecFinSet
imports PRecFun
begin

text \<open>
  We introduce a particular mapping \<open>nat_to_set\<close> from natural
  numbers to finite sets of natural numbers and a particular mapping
  \<open>set_to_nat\<close> from finite sets of natural numbers to natural
  numbers.  See \cite{Rogers} and \cite{Soare} for more information.
\<close>

definition
  c_in :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_in = (\<lambda> x u. (u div (2 ^ x)) mod 2)"

lemma c_in_is_pr: "c_in \<in> PrimRec2"
proof -
  from mod_is_pr power_is_pr div_is_pr have "(\<lambda> x u. (u div (2 ^ x)) mod 2) \<in> PrimRec2" by prec
  with c_in_def show ?thesis by auto
qed

definition
  nat_to_set :: "nat \<Rightarrow> nat set" where
  "nat_to_set u \<equiv> {x. 2^x \<le> u \<and> c_in x u = 1}"

lemma c_in_upper_bound: "c_in x u = 1 \<Longrightarrow> 2 ^ x \<le> u"
proof -
  assume A: "c_in x u = 1"
  then have S1: "(u div (2^x)) mod 2 = 1" by (unfold c_in_def)
  then have S2: "u div (2^x) > 0" by arith
  show ?thesis
  proof (rule ccontr)
    assume "\<not> 2 ^ x \<le> u"
    then have "u < 2^x" by auto
    then have "u div (2^x) = 0" by (rule div_less)
    with S2 show False by auto
  qed
qed

lemma nat_to_set_upper_bound: "x \<in> nat_to_set u \<Longrightarrow> 2 ^ x \<le> u" by (simp add: nat_to_set_def)

lemma x_lt_2_x: "x < 2 ^ x" by (induct x) auto

lemma nat_to_set_upper_bound1: "x \<in> nat_to_set u \<Longrightarrow> x < u"
proof -
  assume "x \<in> nat_to_set u"
  then have S1: "2 ^ x \<le> u" by (simp add: nat_to_set_def)
  have S2: "x < 2 ^ x" by (rule x_lt_2_x)
  from S1 S2 show ?thesis by auto
qed

lemma nat_to_set_upper_bound2: "nat_to_set u \<subseteq> {i. i < u}"
proof -
  from nat_to_set_upper_bound1 show ?thesis by blast
qed

lemma nat_to_set_is_finite: "finite (nat_to_set u)"
proof -
  have S1: "finite {i. i<u}"
  proof -
    let ?B = "{i. i<u}"
    let ?f = "(\<lambda> (x::nat). x)"
    have "?B = ?f ` ?B" by auto
    then show "finite ?B" by (rule nat_seg_image_imp_finite)
  qed
  have S2: "nat_to_set u \<subseteq> {i. i<u}" by (rule nat_to_set_upper_bound2)
  from S2 S1 show ?thesis by (rule finite_subset)
qed

lemma x_in_u_eq: "(x \<in> nat_to_set u) = (c_in x u = 1)" by (auto simp add: nat_to_set_def c_in_upper_bound)

definition
  log2 :: "nat \<Rightarrow> nat" where
  "log2 = (\<lambda> x. Least(%z. x < 2^(z+1)))"

lemma log2_at_0: "log2 0 = 0"
proof -
  let ?v = "log2 0"
  have S1: "0 \<le> ?v" by auto
  have S2: "?v = Least(%(z::nat). (0::nat)<2^(z+1))" by (simp add: log2_def)
  have S3: "(0::nat)<2^(0+1)" by auto
  from S3 have S4: "Least(%(z::nat). (0::nat)<2^(z+1)) \<le> 0" by (rule Least_le)
  from S2 S4 have S5: "?v \<le> 0" by auto
  from S1 S5 have S6: "?v = 0" by auto
  thus ?thesis by auto
qed

lemma log2_at_1: "log2 1 = 0"
proof -
  let ?v = "log2 1"
  have S1: "0 \<le> ?v" by auto
  have S2: "?v = Least(%(z::nat). (1::nat)<2^(z+1))" by (simp add: log2_def)
  have S3: "(1::nat)<2^(0+1)" by auto
  from S3 have S4: "Least(%(z::nat). (1::nat)<2^(z+1)) \<le> 0" by (rule Least_le)
  from S2 S4 have S5: "?v \<le> 0" by auto
  from S1 S5 have S6: "?v = 0" by auto
  thus ?thesis by auto
qed

lemma log2_le: "x > 0 \<Longrightarrow> 2 ^ log2 x \<le> x"
proof -
  assume A: "x > 0"
  show ?thesis
  proof (cases)
    assume A1: "log2 x = 0"
    with A show ?thesis by auto
  next
    assume A1: "log2 x \<noteq> 0"
    then have S1: "log2 x > 0" by auto
    define y where "y = log2 x - 1"
    from S1 y_def have S2: "log2 x = y + 1" by auto
    then have S3: "y < log2 x" by auto
    have "2^(y+1) \<le> x"
    proof (rule ccontr)
      assume A2: "\<not> 2^(y+1) \<le> x" then have "x < 2^(y+1)" by auto
      then have "log2 x \<le> y" by (simp add: log2_def Least_le)
      with S3 show False by auto
   qed
   with S2 show ?thesis by auto
  qed
qed

lemma log2_gt: "x < 2 ^ (log2 x + 1)"
proof -
  have "x < 2^x" by (rule x_lt_2_x)
  then have S1: "x < 2^(x+1)" by simp
  define y where "y = x"
  from S1 y_def have S2: "x < 2^(y+1)" by auto
  let ?P = "\<lambda> z. x < 2^(z+1)"
  from S2 have S3: "?P y" by auto
  then have S4: "?P (Least ?P)" by (rule LeastI)
  from log2_def have S5: "log2 x = Least ?P" by (unfold log2_def, auto)
  from S4 S5 show ?thesis by auto
qed

lemma x_div_x: "x > 0 \<Longrightarrow> (x::nat) div x = 1" by auto
lemma div_ge: "(k::nat) \<le> m div n \<Longrightarrow> n*k \<le> m"
proof -
  assume A: "k \<le> m div n"
  have S1: "n * (m div n) + m mod n = m" by (rule mult_div_mod_eq)
  have S2: "0 \<le> m mod n" by auto
  from S1 S2 have S3: "n * (m div n) \<le> m" by arith
  from A have S4: "n * k \<le>  n * (m div n)" by auto
  from S4 S3 show ?thesis by (rule order_trans)
qed
lemma div_lt: "m < n*k \<Longrightarrow> m div n < (k::nat)"
proof -
  assume A: "m < n*k"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> m div n < k"
    then have S1: "k \<le> m div n" by auto
    then have S2: "n*k \<le> m" by (rule div_ge)
    with A show False by auto
  qed
qed

lemma log2_lm1: "u > 0 \<Longrightarrow> u div 2 ^ (log2 u) = 1"
proof -
  assume A: "u > 0"
  then have S1: "2^(log2 u) \<le> u" by (rule log2_le)
  have S2: "u < 2^(log2 u+1)" by (rule log2_gt)
  then have S3: "u < (2^log2 u)*2" by simp
  have "(2::nat) > 0" by simp
  then have "(2::nat)^log2 u > 0" by simp
  then have S4: "(2::nat)^log2 u div 2^log2 u = 1" by auto
  from S1 have S5: "(2::nat)^log2 u div 2^log2 u  \<le> u div 2^log2 u" by (rule div_le_mono)
  with S4 have S6: "1 \<le> u div 2^log2 u" by auto
  from S3 have S7: "u div 2^log2 u < 2" by (rule div_lt)
  from S6 S7 show ?thesis by auto
qed

lemma log2_lm2: "u > 0 \<Longrightarrow> c_in (log2 u) u = 1"
proof -
  assume A: "u > 0"
  then have S1: "u div 2 ^ (log2 u) = 1" by (rule log2_lm1)
  have "c_in (log2 u) u = (u div 2 ^ (log2 u)) mod 2" by (simp add: c_in_def)
  also from S1 have "\<dots> = 1 mod 2" by simp
  also have "\<dots> = 1" by auto
  finally show ?thesis by auto
qed

lemma log2_lm3: "log2 u < x \<Longrightarrow> c_in x u = 0"
proof -
  assume A: "log2 u < x"
  then have S1: "(log2 u)+1 \<le> x" by auto
  have S2: "1 \<le> (2::nat)" by auto
  from S1 S2 have S3: "(2::nat)^ ((log2 u)+1) \<le> 2^x" by (rule power_increasing)
  have S4: "u < (2::nat)^ ((log2 u)+1)" by (rule log2_gt)
  from S3 S4 have S5: "u < 2^x" by auto
  then have S6: "u div 2^x = 0" by (rule div_less)
  have "c_in x u = (u div 2^x) mod 2" by (simp add: c_in_def)
  also from S6 have "\<dots> = 0 mod 2" by simp
  also have "\<dots> = 0" by auto
  finally have ?thesis by auto
  thus ?thesis by auto
qed

lemma log2_lm4: "c_in x u = 1 \<Longrightarrow> x \<le> log2 u"
proof -
  assume A: "c_in x u = 1"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> x \<le> log2 u"
    then have S1: "log2 u < x" by auto
    then have S2: "c_in x u = 0" by (rule log2_lm3)
    with A show False by auto
  qed
qed

lemma nat_to_set_lub: "x \<in> nat_to_set u \<Longrightarrow> x \<le> log2 u"
proof -
  assume "x \<in> nat_to_set u"
  then have S1: "c_in x u = 1" by (simp add: x_in_u_eq)
  then show ?thesis by (rule log2_lm4)
qed

lemma log2_lm5: "u > 0 \<Longrightarrow> log2 u \<in> nat_to_set u"
proof -
  assume A: "u > 0"
  then have "c_in (log2 u) u = 1" by (rule log2_lm2)
  then show ?thesis by (simp add: x_in_u_eq)
qed

lemma pos_imp_ne: "u > 0 \<Longrightarrow> nat_to_set u \<noteq> {}"
proof -
  assume "u > 0"
  then have "log2 u \<in> nat_to_set u" by (rule log2_lm5)
  thus ?thesis by auto
qed

lemma empty_is_zero: "nat_to_set u = {} \<Longrightarrow> u = 0"
proof (rule ccontr)
  assume A1: "nat_to_set u = {}"
  assume A2: "u \<noteq> 0" then have S1: "u > 0" by auto
  from S1 have "nat_to_set u \<noteq> {}" by (rule pos_imp_ne)
  with A1 show False by auto
qed

lemma log2_is_max: "u > 0 \<Longrightarrow> log2 u = Max (nat_to_set u)"
proof -
  assume A: "u > 0"
  then have S1: "log2 u \<in> nat_to_set u" by (rule log2_lm5)
  define max where "max = Max (nat_to_set u)"
  from A have ne: "nat_to_set u \<noteq> {}" by (rule pos_imp_ne)
  have finite: "finite (nat_to_set u)" by (rule nat_to_set_is_finite)
  from max_def finite ne have max_in: "max \<in> nat_to_set u" by simp
  from max_in have S2: "c_in max u = 1" by (simp add: x_in_u_eq)
  then have S3: "max \<le> log2 u" by (rule log2_lm4)
  from finite ne S1 max_def have S4: "log2 u \<le> max" by simp
  from S3 S4 max_def show ?thesis by auto
qed

lemma zero_is_empty: "nat_to_set 0 = {}"
proof -
  have S1: "{i. i<(0::nat)} = {}" by blast
  have S2: "nat_to_set 0 \<subseteq> {i. i<0}" by (rule nat_to_set_upper_bound2)
  from S1 S2 show ?thesis by auto
qed

lemma ne_imp_pos: "nat_to_set u \<noteq> {} \<Longrightarrow> u > 0"
proof (rule ccontr)
  assume A1: "nat_to_set u \<noteq> {}"
  assume "\<not> 0 < u" then have "u = 0" by auto
  then have "nat_to_set u = {}" by (simp add: zero_is_empty)
  with A1 show False by auto
qed

lemma div_mod_lm: "y < x \<Longrightarrow> ((u + (2::nat) ^ x) div (2::nat)^y) mod 2 = (u div (2::nat)^y) mod 2"
proof -
  assume y_lt_x: "y < x"
  let ?n = "(2::nat)^y"
  have n_pos: "0 < ?n" by auto
  let ?s = "x-y"
  from y_lt_x have s_pos: "0 < ?s" by auto
  from y_lt_x have S3: "x = y + ?s" by auto
  from S3 have "(2::nat)^x = (2::nat)^(y + ?s)" by auto
  moreover have "(2::nat)^(y +?s) = (2::nat)^y * 2^ ?s" by (rule power_add)
  ultimately have "(2::nat)^x = 2^y * 2^?s" by auto
  then have S4: "u + (2::nat)^x = u + (2::nat)^y * 2^?s" by auto
  from n_pos have S5: "(u + (2::nat)^y * 2^?s) div 2^y = 2^?s + (u div 2^y)" by simp
  from S4 S5 have S6: "(u + (2::nat)^x) div 2^y = 2^?s + (u div 2^y)" by auto
  from s_pos have S8: "?s = (?s - 1) + 1" by auto
  have "(2::nat) ^ ((?s - (1::nat)) + (1::nat)) = (2::nat) ^ (?s - (1::nat)) * 2^1" by (rule power_add)
  with S8 have S9: "(2::nat) ^ ?s = (2::nat) ^ (?s - (1::nat)) * 2" by auto
  then have S10: "2^?s + (u div 2^y) = (u div 2^y) + (2::nat) ^ (?s - (1::nat)) * 2" by auto
  have S11: "((u div 2^y) + (2::nat) ^ (?s - (1::nat)) * 2) mod 2 = (u div 2^y) mod 2" by (rule mod_mult_self1)
  from S6 S10 S11 show ?thesis by auto
qed

lemma add_power: "u < 2^x \<Longrightarrow> nat_to_set (u + 2^x) = nat_to_set u \<union> {x}"
proof -
  assume A: "u < 2^x"
  have log2_is_x: "log2 (u+2^x) = x"
  proof (unfold log2_def, rule Least_equality)
    from A show "u+2^x < 2^(x+1)" by auto
  next
    fix z
    assume A1: "u + 2^x < 2^(z+1)"
    show "x \<le> z"
    proof (rule ccontr)
      assume "\<not> x \<le> z"
      then have "z < x" by auto
      then have L1: "z+1 \<le> x" by auto
      have L2: "1 \<le> (2::nat)" by auto
      from L1 L2 have L3: "(2::nat)^(z+1) \<le> (2::nat)^x" by (rule power_increasing)
      with A1 show False by auto
    qed
  qed
  show ?thesis
  proof (rule subset_antisym)
    show "nat_to_set (u + 2 ^ x) \<subseteq> nat_to_set u \<union> {x}"
    proof fix y
      assume A1: "y \<in> nat_to_set (u + 2 ^ x)"
      show "y \<in> nat_to_set u \<union> {x}"
      proof
        assume "y \<notin> {x}" then have S1: "y \<noteq> x" by auto
        from A1 have "y \<le> log2 (u + 2 ^ x)" by (rule nat_to_set_lub)
        with log2_is_x have "y \<le> x" by auto
        with S1 have y_lt_x: "y < x" by auto
        from A1 have "c_in y (u + 2 ^ x) = 1" by (simp add: x_in_u_eq)
        then have S2: "((u + 2 ^ x) div 2^y) mod 2 = 1" by (unfold c_in_def)
        from y_lt_x have "((u + (2::nat) ^ x) div (2::nat)^y) mod 2 = (u div (2::nat)^y) mod 2" by (rule div_mod_lm)
        with S2 have "(u div 2^y) mod 2 = 1" by auto
        then have "c_in y u = 1" by (simp add: c_in_def)
        then show "y \<in> nat_to_set u" by (simp add: x_in_u_eq)
      qed
    qed
  next
  show "nat_to_set u \<union> {x} \<subseteq> nat_to_set (u + 2 ^ x)"
  proof fix y
    assume A1: "y \<in> nat_to_set u \<union> {x}"
    show "y \<in> nat_to_set (u + 2 ^ x)"
    proof cases
      assume "y \<in> {x}"
      then have "y=x" by auto
      then have "y = log2 (u + 2 ^ x)" by (simp add: log2_is_x)
      then show ?thesis by (simp add: log2_lm5)
    next
      assume y_notin: "y \<notin> {x}"
      then have y_ne_x: "y \<noteq> x" by auto
      from A1 y_notin have y_in: "y \<in> nat_to_set u" by auto
      have y_lt_x: "y < x"
      proof (rule ccontr)
        assume "\<not> y < x"
        with y_ne_x have y_gt_x: "x < y" by auto
        have "1 < (2::nat)" by auto
        from y_gt_x this have L1: "(2::nat)^x < 2^y" by (rule power_strict_increasing)
        from y_in have L2: "2^y \<le> u" by (rule nat_to_set_upper_bound)
        from L1 L2 have "(2::nat)^x < u" by arith
        with A show False by auto
      qed
      from y_in have "c_in y u = 1" by (simp add: x_in_u_eq)
      then have S2: "(u div 2^y) mod 2 = 1" by (unfold c_in_def)
      from y_lt_x have "((u + (2::nat) ^ x) div (2::nat)^y) mod 2 = (u div (2::nat)^y) mod 2" by (rule div_mod_lm)
      with S2 have "((u + (2::nat) ^ x)div 2^y) mod 2 = 1" by auto
      then have "c_in y (u + (2::nat) ^ x) = 1" by (simp add: c_in_def)
      then show "y \<in> nat_to_set (u + (2::nat) ^ x)" by (simp add: x_in_u_eq)
    qed
  qed
  qed
qed

theorem nat_to_set_inj: "nat_to_set u = nat_to_set v \<Longrightarrow> u = v"
proof -
  assume A: "nat_to_set u = nat_to_set v"
  let ?P = "\<lambda> (n::nat). (\<forall> (D::nat set). finite D \<and> card D \<le> n \<longrightarrow> (\<forall> u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v))"
  have P_at_0: "?P 0"
  proof fix D show "finite D \<and> card D \<le> 0 \<longrightarrow> (\<forall>u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v)"
    proof (rule impI)
      assume A1: "finite D \<and> card D \<le> 0"
      from A1 have S1: "finite D" by auto
      from A1 have S2: "card D = 0" by auto
      from S1 S2 have S3: "D = {}" by auto
      show "(\<forall>u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v)"
      proof (rule allI, rule allI) fix u v show "nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v"
        proof
          assume A2: " nat_to_set u = D \<and> nat_to_set v = D"
          from A2 have L1: "nat_to_set u = D" by auto
          from A2 have L2: "nat_to_set v = D" by auto
          from L1 S3 have "nat_to_set u = {}" by auto
          then have u_z: "u = 0" by (rule empty_is_zero)
          from L2 S3 have "nat_to_set v = {}" by auto
          then have v_z: "v = 0" by (rule empty_is_zero)
          from u_z v_z show "u=v" by auto
        qed
      qed
    qed
  qed
  have P_at_Suc: "\<And> n. ?P n \<Longrightarrow> ?P (Suc n)"
  proof - fix n
    assume A_n: "?P n"
    show "?P (Suc n)"
    proof fix D show "finite D \<and> card D \<le> Suc n \<longrightarrow> (\<forall>u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v)"
    proof (rule impI)
      assume A1: "finite D \<and> card D \<le> Suc n"
      from A1 have S1: "finite D" by auto
      from A1 have S2: "card D \<le> Suc n" by auto
      show "(\<forall>u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v)"
      proof (rule allI, rule allI, rule impI)
        fix u v
        assume A2: " nat_to_set u = D \<and> nat_to_set v = D"
        from A2 have d_u_d: "nat_to_set u = D" by auto
        from A2 have d_v_d: "nat_to_set v = D" by auto
        show "u = v"
        proof (cases)
          assume A3: "D = {}"
          from A3 d_u_d have "nat_to_set u = {}" by auto
          then have u_z: "u = 0" by (rule empty_is_zero)
          from A3 d_v_d have "nat_to_set v = {}" by auto
          then have v_z: "v = 0" by (rule empty_is_zero)
          from u_z v_z show "u = v" by auto
        next
          assume A3: "D \<noteq> {}"
          from A3 d_u_d have "nat_to_set u \<noteq> {}" by auto
          then have u_pos: "u > 0" by (rule ne_imp_pos)
          from A3 d_v_d have "nat_to_set v \<noteq> {}" by auto
          then have v_pos: "v > 0" by (rule ne_imp_pos)
          define m where "m = Max D"
          from S1 m_def A3 have m_in: "m \<in> D" by auto
          from d_u_d m_def have m_u: "m = Max (nat_to_set u)" by auto
          from d_v_d m_def have m_v: "m = Max (nat_to_set v)" by auto
          from u_pos m_u log2_is_max have m_log_u: "m = log2 u" by auto
          from v_pos m_v log2_is_max have m_log_v: "m = log2 v" by auto
          define D1 where "D1 = D - {m}"
          define u1 where "u1 = u - 2^m"
          define v1 where "v1 = v - 2^m"
          have card_D1: "card D1 \<le> n"
          proof -
            from D1_def S1 m_in have "card D1 = (card D) - 1" by (simp add: card_Diff_singleton)
            with S2 show ?thesis by auto
          qed
          have u_u1: "u = u1 + 2^m"
          proof -
            from u_pos have L1: "2 ^ log2 u \<le> u" by (rule log2_le)
            with m_log_u have L2: "2 ^ m \<le> u" by auto
            with u1_def show ?thesis by auto
          qed
          have u1_d1: "nat_to_set u1 = D1"
          proof -
            from m_log_u log2_gt have "u < 2^(m+1)" by auto
            with u_u1 have u1_lt_2_m: "u1 < 2^m" by auto
            with u_u1 have L1: "nat_to_set u = nat_to_set u1 \<union> {m}" by (simp add: add_power)
            have m_notin: "m \<notin> nat_to_set u1"
            proof (rule ccontr)
              assume "\<not> m \<notin> nat_to_set u1" then have "m \<in> nat_to_set u1" by auto
              then have "2^m \<le> u1" by (rule nat_to_set_upper_bound)
              with u1_lt_2_m show False by auto
            qed
            from L1 m_notin have "nat_to_set u1 = nat_to_set u - {m}" by auto
            with d_u_d have "nat_to_set u1 = D - {m}" by auto
            with D1_def show ?thesis by auto
          qed
          have v_v1: "v = v1 + 2^m"
          proof -
            from v_pos have L1: "2 ^ log2 v \<le> v" by (rule log2_le)
            with m_log_v have L2: "2 ^ m \<le> v" by auto
            with v1_def show ?thesis by auto
          qed
          have v1_d1: "nat_to_set v1 = D1"
          proof -
            from m_log_v log2_gt have "v < 2^(m+1)" by auto
            with v_v1 have v1_lt_2_m: "v1 < 2^m" by auto
            with v_v1 have L1: "nat_to_set v = nat_to_set v1 \<union> {m}" by (simp add: add_power)
            have m_notin: "m \<notin> nat_to_set v1"
            proof (rule ccontr)
              assume "\<not> m \<notin> nat_to_set v1" then have "m \<in> nat_to_set v1" by auto
              then have "2^m \<le> v1" by (rule nat_to_set_upper_bound)
              with v1_lt_2_m show False by auto
            qed
            from L1 m_notin have "nat_to_set v1 = nat_to_set v - {m}" by auto
            with d_v_d have "nat_to_set v1 = D - {m}" by auto
            with D1_def show ?thesis by auto
          qed
          from S1 D1_def have P1: "finite D1" by auto
          with card_D1 have P2: "finite D1 \<and> card D1 \<le> n" by auto
          from A_n P2 have "(\<forall>u v. nat_to_set u = D1 \<and> nat_to_set v = D1 \<longrightarrow> u = v)" by auto
          with u1_d1 v1_d1 have "u1 = v1" by auto
          with u_u1 v_v1 show "u = v" by auto
        qed
      qed
    qed
  qed
qed
  from P_at_0 P_at_Suc have main: "\<And> n. ?P n" by (rule nat.induct)
  define D where "D = nat_to_set u"
  from D_def A have P1: "nat_to_set u = D" by auto
  from D_def A have P2: "nat_to_set v = D" by auto
  from D_def nat_to_set_is_finite have d_finite: "finite D" by auto
  define n where "n = card D"
  from n_def d_finite have card_le: "card D \<le> n" by auto
  from d_finite card_le have P3: "finite D \<and> card D \<le> n" by auto
  with main have P4: "\<forall>u v. nat_to_set u = D \<and> nat_to_set v = D \<longrightarrow> u = v" by auto
  with P1 P2 show "u = v" by auto
qed

definition
  set_to_nat :: "nat set => nat" where
  "set_to_nat = (\<lambda> D. sum (\<lambda> x. 2 ^ x) D)"

lemma two_power_sum: "sum (\<lambda> x. (2::nat) ^ x) {i. i< Suc m} = (2 ^ Suc m) - 1"
proof (induct m)
  show "sum (\<lambda> x. (2::nat) ^ x) {i. i< Suc 0} = (2 ^ Suc 0) - 1" by auto
next
  fix n
  assume A: "sum (\<lambda> x. (2::nat) ^ x) {i. i< Suc n} = (2 ^ Suc n) - 1"
  show "sum (\<lambda> x. (2::nat) ^ x) {i. i< Suc (Suc n)} = (2 ^ Suc (Suc n)) - 1"
  proof -
    let ?f = "\<lambda> x. (2::nat) ^ x"
    have S1: "{i. i< Suc (Suc n)} = {i. i \<le> Suc n}" by auto
    have S2: "{i. i \<le> Suc n} = {i. i < Suc n} \<union> { Suc n}" by auto
    from S1 S2 have S3: "{i. i< Suc (Suc n)} = {i. i < Suc n} \<union> { Suc n}" by auto
    have S4: "{i. i < Suc n} = (\<lambda> x. x) ` {i. i < Suc n}" by auto
    then have S5: "finite {i. i < Suc n}" by (rule nat_seg_image_imp_finite)
    have S6: "Suc n \<notin> {i. i < Suc n}" by auto
    from S5 S6 sum.insert have S7: "sum ?f ({i. i< Suc n} \<union> {Suc n}) = 2 ^ Suc n + sum ?f {i. i< Suc n}" by auto
    from S3 have "sum ?f {i. i< Suc (Suc n)} = sum ?f ({i. i< Suc n} \<union> {Suc n})" by auto
    also from S7 have "\<dots> = 2 ^ Suc n + sum ?f {i. i< Suc n}" by auto
    also from A have "\<dots> = 2 ^ Suc n + (((2::nat) ^ Suc n)-(1::nat))" by auto
    also have "\<dots> = (2 ^ Suc (Suc n)) - 1" by auto
    finally show ?thesis by auto
  qed
qed

lemma finite_interval: "finite {i. (i::nat)<m}"
proof -
  have "{i. i < m} = (\<lambda> x. x) ` {i. i < m}" by auto
  then show ?thesis by (rule nat_seg_image_imp_finite)
qed

lemma set_to_nat_at_empty: "set_to_nat {} = 0" by (unfold set_to_nat_def, rule sum.empty)

lemma set_to_nat_of_interval: "set_to_nat {i. (i::nat)<m} = 2 ^ m - 1"
proof (induct m)
  show "set_to_nat {i. i < 0} = 2 ^ 0 - 1"
  proof -
    have S1: "{i. (i::nat) < 0} = {}" by auto
    with set_to_nat_at_empty have "set_to_nat {i. i<0} = 0" by auto
    thus ?thesis by auto
  qed
next
  fix n show "set_to_nat {i. i < Suc n} = 2 ^ Suc n - 1" by (unfold set_to_nat_def, rule two_power_sum)
qed

lemma set_to_nat_mono: "\<lbrakk> finite B; A \<subseteq> B\<rbrakk> \<Longrightarrow> set_to_nat A \<le> set_to_nat B"
proof -
  assume b_finite: "finite B"
  assume a_le_b: "A \<subseteq> B"
  let ?f = "\<lambda> (x::nat). (2::nat) ^ x"
  have S1: "set_to_nat A = sum ?f A" by (simp add: set_to_nat_def)
  have S2: "set_to_nat B = sum ?f B" by (simp add: set_to_nat_def)
  have S3: "\<And> x. x  \<in> B - A \<Longrightarrow> 0 \<le> ?f x" by auto
  from b_finite a_le_b S3 have "sum ?f A \<le> sum ?f B" by (rule sum_mono2)
  with S1 S2 show ?thesis by auto
qed

theorem nat_to_set_srj: "finite (D::nat set) \<Longrightarrow> nat_to_set (set_to_nat D) = D"
proof -
  assume A: "finite D"
  let ?P = "\<lambda> (n::nat). (\<forall> (D::nat set). finite D \<and> card D = n \<longrightarrow> nat_to_set (set_to_nat D) = D)"
  have P_at_0: "?P 0"
  proof (rule allI)
    fix D
    show "finite D \<and> card D = 0 \<longrightarrow> nat_to_set (set_to_nat D) = D"
    proof
      assume A1: "finite D \<and> card D = 0"
      from A1 have S1: "finite D" by auto
      from A1 have S2: "card D = 0" by auto
      from S1 S2 have S3: "D = {}" by auto
      with set_to_nat_def have "set_to_nat D = sum (\<lambda> x. 2 ^ x) D" by simp
      with S3 sum.empty have "set_to_nat D = 0" by auto
      with zero_is_empty S3 show "nat_to_set (set_to_nat D) = D" by auto
    qed
  qed
  have P_at_Suc: "\<And> n. ?P n \<Longrightarrow> ?P (Suc n)"
  proof - fix n
    assume A_n: "?P n"
    show "?P (Suc n)"
    proof
      fix D show "finite D \<and> card D = Suc n \<longrightarrow> nat_to_set (set_to_nat D) = D"
      proof
        assume A1: "finite D \<and> card D = Suc n"
        from A1 have S1: "finite D" by auto
        from A1 have S2: "card D = Suc n" by auto
        define m where "m = Max D"
        from S2 have D_ne: "D \<noteq> {}" by auto
        with S1 m_def have m_in: "m \<in> D" by auto
        define D1 where "D1 = D - {m}"
        from S1 D1_def have d1_finite: "finite D1" by auto
        from D1_def m_in S1 have "card D1 = card D - 1" by (simp add: card_Diff_singleton)
        with S2 have card_d1: "card D1 = n" by auto
        from d1_finite card_d1 have "finite D1 \<and> card D1 = n" by auto
        with A_n have S3: "nat_to_set (set_to_nat D1) = D1" by auto
        define u where "u = set_to_nat D"
        define u1 where "u1 = set_to_nat D1"
        from S1 m_in have "sum (\<lambda> (x::nat). (2::nat) ^ x) D = 2 ^ m + sum (\<lambda> x. 2 ^ x) (D - {m})"
          by (rule sum.remove)
        with set_to_nat_def have "set_to_nat D = 2 ^ m + set_to_nat (D - {m})" by auto
        with u_def u1_def D1_def have u_u1: "u = u1 + 2 ^ m" by auto
        from S3 u1_def have d1_u1: "nat_to_set u1 = D1" by auto
        have u1_lt: "u1 < 2 ^ m"
        proof -
          have L1: "D1 \<subseteq> {i. i<m}"
          proof fix x
            assume A1: "x \<in> D1"
            show "x \<in> {i. i<m}"
            proof
              from A1 D1_def have L1_1: "x \<in> D" by auto
              from S1 D_ne L1_1 m_def have L1_2: "x \<le> m" by auto
              with A1 L1_1 D1_def have "x \<noteq> m" by auto
              with L1_2 show "x < m" by auto
            qed
          qed
          have L2: "finite {i. i<m}" by (rule finite_interval)
          from L2 L1 have "set_to_nat D1 \<le> set_to_nat {i. i<m}" by (rule set_to_nat_mono)
          with u1_def have "u1 \<le> set_to_nat {i. i<m}" by auto
          with set_to_nat_of_interval have L3: "u1 \<le> 2 ^ m - 1" by auto
          have "0 < (2::nat) ^ m" by auto
          then have "(2::nat) ^ m - 1 < (2::nat) ^ m" by auto
          with L3 show ?thesis by arith
        qed
        from u_def have "nat_to_set (set_to_nat D) = nat_to_set u" by auto
        also from u_u1 have "\<dots> = nat_to_set (u1 + 2 ^ m)" by auto
        also from u1_lt have "\<dots> = nat_to_set u1 \<union> {m}" by (rule add_power)
        also from d1_u1 have "\<dots> = D1 \<union> {m}" by auto
        also from D1_def m_in have "\<dots> = D" by auto
        finally show "nat_to_set (set_to_nat D) = D" by auto
      qed
    qed
  qed
  from P_at_0 P_at_Suc have main: "\<And> n. ?P n" by (rule nat.induct)
  from A main show ?thesis by auto
qed

theorem nat_to_set_srj1: "finite (D::nat set) \<Longrightarrow> \<exists> u. nat_to_set u = D"
proof -
  assume A: "finite D"
  show " \<exists> u. nat_to_set u = D"
  proof
    from A show "nat_to_set (set_to_nat D) = D" by (rule nat_to_set_srj)
  qed
qed

lemma sum_of_pr_is_pr: "g \<in> PrimRec1 \<Longrightarrow> (\<lambda> n. sum g {i. i<n}) \<in> PrimRec1"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  define f where "f n = sum g {i. i<n}" for n
  from f_def have f_at_0: "f 0 = 0" by auto
  define h where "h a b = g a + b" for a b
  from g_is_pr have h_is_pr: "h \<in> PrimRec2" unfolding h_def by prec
  have f_at_Suc: "\<forall> y. f (Suc y) = h y (f y)"
  proof
    fix y show "f (Suc y) = h y (f y)"
    proof -
      from f_def have S1: "f (Suc y) = sum g {i. i < Suc y}" by auto
      have S2: "{i. i < Suc y} = {i. i < y} \<union> {y}" by auto
      have S3: "finite {i. i < y}" by (rule finite_interval)
      have S4: "y \<notin> {i. i < y}" by auto
      from S1 S2 have "f (Suc y) = sum g ({i. (i::nat) < y} \<union> {y})" by auto
      also from S3 S4 sum.insert have "\<dots> = g y + sum g {i. i<y}" by auto
      also from f_def have "\<dots> = g y + f y" by auto
      also from h_def have "\<dots> = h y (f y)" by auto
      finally show ?thesis by auto
    qed
  qed
  from h_is_pr f_at_0 f_at_Suc have f_is_pr: "f \<in> PrimRec1" by (rule pr_rec1_scheme)
  with f_def [abs_def] show ?thesis by auto
qed

lemma sum_of_pr_is_pr2: "p \<in> PrimRec2 \<Longrightarrow> (\<lambda> n m. sum (\<lambda> x. p x m) {i. i<n}) \<in> PrimRec2"
proof -
  assume p_is_pr: "p \<in> PrimRec2"
  define f where "f n m = sum (\<lambda> x. p x m) {i. i<n}" for n m
  define g :: "nat \<Rightarrow> nat" where "g x = 0" for x
  have g_is_pr: "g \<in> PrimRec1" by (unfold g_def, rule const_is_pr [where ?n=0])
  have f_at_0: "\<forall> x. f 0 x = g x"
  proof
    fix x from f_def g_def show "f 0 x = g x" by auto
  qed
  define h where "h a b c = p a c + b" for a b c
  from p_is_pr have h_is_pr: "h \<in> PrimRec3" unfolding h_def by prec
  have f_at_Suc: "\<forall> x y. f (Suc y) x = h y (f y x) x"
  proof (rule allI, rule allI)
    fix x y show "f (Suc y) x = h y (f y x) x"
    proof -
      from f_def have S1: "f (Suc y) x = sum (\<lambda> z. p z x)  {i. i < Suc y}" by auto
      have S2: "{i. i < Suc y} = {i. i < y} \<union> {y}" by auto
      have S3: "finite {i. i < y}" by (rule finite_interval)
      have S4: "y \<notin> {i. i < y}" by auto
      define g1 where "g1 z = p z x" for z
      from S1 S2 g1_def have "f (Suc y) x = sum g1 ({i. (i::nat) < y} \<union> {y})" by auto
      also from S3 S4 sum.insert have "\<dots> = g1 y + sum g1 {i. i<y}" by auto
      also from f_def g1_def have "\<dots> = g1 y + f y x" by auto
      also from h_def g1_def  have "\<dots> = h y (f y x) x" by auto
      finally show ?thesis by auto
    qed
  qed
  from g_is_pr h_is_pr f_at_0 f_at_Suc have f_is_pr: "f \<in> PrimRec2" by (rule pr_rec_scheme)
  with f_def [abs_def] show ?thesis by auto
qed

lemma sum_is_pr: "g \<in> PrimRec1 \<Longrightarrow> (\<lambda> u. sum g (nat_to_set u)) \<in> PrimRec1"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  define g1 where "g1 x u = (if (c_in x u = 1) then (g x) else 0)" for x u
  have g1_is_pr: "g1 \<in> PrimRec2"
  proof (unfold g1_def, rule if_eq_is_pr2)
    show "c_in \<in> PrimRec2" by (rule c_in_is_pr)
  next
    show "(\<lambda>x y. 1) \<in> PrimRec2" by (rule const_is_pr_2 [where ?n=1])
  next
    from g_is_pr show "(\<lambda>x y. g x) \<in> PrimRec2" by prec
  next
    show "(\<lambda>x y. 0) \<in> PrimRec2" by (rule const_is_pr_2 [where ?n=0])
  qed
  define f where "f u = sum (\<lambda> x. g1 x u) {i. (i::nat) < u}" for u
  define f1 where "f1 u v = sum (\<lambda> x. g1 x v) {i. (i::nat) < u}"  for u v
  from g1_is_pr have "(\<lambda> (u::nat) v. sum (\<lambda> x. g1 x v) {i. (i::nat) < u}) \<in> PrimRec2"
    by (rule sum_of_pr_is_pr2)
  with f1_def [abs_def] have f1_is_pr: "f1 \<in> PrimRec2" by auto
  from f_def f1_def have f_f1: "f = (\<lambda> u. f1 u u)" by auto
  from f1_is_pr have "(\<lambda> u. f1 u u) \<in> PrimRec1" by prec
  with f_f1 have f_is_pr: "f \<in> PrimRec1" by auto
  have f_is_result: "f = (\<lambda> u. sum g (nat_to_set u))"
  proof
    fix u show "f u = sum g (nat_to_set u)"
    proof -
      define U where "U = {i. i < u}"
      define A where "A = {x \<in> U. c_in x u = 1}"
      define B where "B = {x \<in> U. c_in x u \<noteq> 1}"
      have U_finite: "finite U" by (unfold U_def, rule finite_interval)
      from A_def U_finite have A_finite: "finite A" by auto
      from B_def U_finite have B_finite: "finite B" by auto
      from U_def A_def B_def have U_A_B: "U = A \<union> B" by auto
      from U_def A_def B_def have A_B: "A \<inter> B = {}" by auto
      from B_def g1_def have B_z: "sum (\<lambda> x. g1 x u) B = 0" by auto
      have u_in_U: "nat_to_set u \<subseteq> U" by (unfold U_def, rule nat_to_set_upper_bound2)
      from u_in_U x_in_u_eq A_def have A_u: "A = nat_to_set u" by auto
      from A_u x_in_u_eq g1_def have A_res: "sum (\<lambda> x. g1 x u) A = sum g (nat_to_set u)" by auto
      from f_def have "f u = sum (\<lambda> x. g1 x u) {i. (i::nat) < u}" by auto
      also from U_def have "\<dots> = sum (\<lambda> x. g1 x u) U" by auto
      also from U_A_B have "\<dots> = sum (\<lambda> x. g1 x u) (A \<union> B)" by auto
      also from A_finite B_finite A_B have "\<dots> = sum (\<lambda> x. g1 x u) A + sum (\<lambda> x. g1 x u) B" by (rule sum.union_disjoint)
      also from B_z have "\<dots> = sum (\<lambda> x. g1 x u) A" by auto
      also from A_res have "\<dots> = sum g (nat_to_set u)" by auto
      finally show ?thesis by auto
    qed
  qed
  with f_is_pr show ?thesis by auto
qed

definition
  c_card :: "nat \<Rightarrow> nat" where
  "c_card = (\<lambda> u. card (nat_to_set u))"

theorem c_card_is_pr: "c_card \<in> PrimRec1"
proof -
  define g :: "nat \<Rightarrow> nat" where "g x = 1" for x
  have g_is_pr: "g \<in> PrimRec1" by (unfold g_def, rule const_is_pr)
  have "c_card = (\<lambda> u. sum g (nat_to_set u))"
  proof
    fix u show "c_card u = sum g (nat_to_set u)" by (unfold c_card_def, unfold g_def, rule card_eq_sum)
  qed
  moreover from g_is_pr have "(\<lambda> u. sum g (nat_to_set u)) \<in> PrimRec1" by (rule sum_is_pr)
  ultimately show ?thesis by auto
qed

definition
  c_insert :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_insert = (\<lambda> x u. if c_in x u = 1 then u else u + 2^x)"

lemma c_insert_is_pr: "c_insert \<in> PrimRec2"
proof (unfold c_insert_def, rule if_eq_is_pr2)
  show "c_in \<in> PrimRec2" by (rule c_in_is_pr)
next
  show "(\<lambda>x y. 1) \<in> PrimRec2" by (rule const_is_pr_2)
next
  show "(\<lambda>x y. y) \<in> PrimRec2" by (rule pr_id2_2)
next
  from power_is_pr show "(\<lambda>x y. y + 2 ^ x) \<in> PrimRec2" by prec
qed

lemma [simp]: "set_to_nat (nat_to_set u) = u"
proof -
  define D where "D = nat_to_set u"
  from D_def nat_to_set_is_finite have D_finite: "finite D" by auto
  then have "nat_to_set (set_to_nat D) = D" by (rule nat_to_set_srj)
  with D_def have "nat_to_set (set_to_nat D) = nat_to_set u" by auto
  then have "set_to_nat D = u" by (rule nat_to_set_inj)
  with D_def show ?thesis by auto
qed

lemma insert_lemma: "x \<notin> nat_to_set u \<Longrightarrow> set_to_nat (nat_to_set u \<union> {x}) = u + 2 ^ x"
proof -
  assume A: "x \<notin> nat_to_set u"
  define D where "D = nat_to_set u"
  from A D_def have S1: "x \<notin> D" by auto
  have "finite (nat_to_set u)" by (rule nat_to_set_is_finite)
  with D_def have D_finite: "finite D" by auto
  let ?f = "\<lambda> (x::nat). (2::nat)^x"
  from set_to_nat_def have "set_to_nat (D \<union> {x}) = sum ?f (D \<union> {x})" by auto
  also from D_finite S1 have "\<dots> = ?f x + sum ?f D" by simp
  also from set_to_nat_def have "\<dots> = 2 ^ x + set_to_nat D" by auto
  finally have "set_to_nat (D \<union> {x}) = set_to_nat D + 2 ^ x" by auto
  with D_def show ?thesis by auto
qed

lemma c_insert_df: "c_insert = (\<lambda> x u. set_to_nat ((nat_to_set u) \<union> {x}))"
proof (rule ext, rule ext)
  fix x u show "c_insert x u = set_to_nat (nat_to_set u \<union> {x})"
  proof (cases)
    assume A: "x \<in> nat_to_set u"
    then have "nat_to_set u \<union> {x} = nat_to_set u" by auto
    then have S1: "set_to_nat (nat_to_set u \<union> {x}) = u" by auto
    from A have "c_in x u = 1" by (simp add: x_in_u_eq)
    then have "c_insert x u = u" by (unfold c_insert_def, simp)
    with S1 show ?thesis by auto
  next
    assume A: "x \<notin> nat_to_set u"
    then have S1: "c_in x u \<noteq> 1" by (simp add: x_in_u_eq)
    then have S2: "c_insert x u = u + 2 ^ x" by (unfold c_insert_def, simp)
    from A have "set_to_nat (nat_to_set u \<union> {x}) = u + 2 ^ x" by (rule insert_lemma)
    with S2 show ?thesis by auto
  qed
qed

definition
  c_remove :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_remove = (\<lambda> x u. if c_in x u = 0 then u else u - 2^x)"

lemma c_remove_is_pr: "c_remove \<in> PrimRec2"
proof (unfold c_remove_def, rule if_eq_is_pr2)
  show "c_in \<in> PrimRec2" by (rule c_in_is_pr)
next
  show "(\<lambda>x y. 0) \<in> PrimRec2" by (rule const_is_pr_2)
next
  show "(\<lambda>x y. y) \<in> PrimRec2" by (rule pr_id2_2)
next
  from power_is_pr show "(\<lambda>x y. y - 2 ^ x) \<in> PrimRec2" by prec
qed

lemma remove_lemma: "x \<in> nat_to_set u \<Longrightarrow> set_to_nat (nat_to_set u - {x}) = u - 2 ^ x"
proof -
  assume A: "x \<in> nat_to_set u"
  define D where "D = nat_to_set u - {x}"
  from A D_def have S1: "x \<notin> D" by auto
  have "finite (nat_to_set u)" by (rule nat_to_set_is_finite)
  with D_def have D_finite: "finite D" by auto
  let ?f = "\<lambda> (x::nat). (2::nat)^x"
  from set_to_nat_def have "set_to_nat (D \<union> {x}) = sum ?f (D \<union> {x})" by auto
  also from D_finite S1 have "\<dots> = ?f x + sum ?f D" by simp
  also from set_to_nat_def have "\<dots> = 2 ^ x + set_to_nat D" by auto
  finally have S2: "set_to_nat (D \<union> {x}) = set_to_nat D + 2 ^ x" by auto
  from A D_def have "D \<union> {x} = nat_to_set u" by auto
  with S2 have S3: "u = set_to_nat D + 2 ^ x" by auto
  from A have S4: "2 ^ x \<le> u" by (rule nat_to_set_upper_bound)
  with S3 D_def show ?thesis by auto
qed

lemma c_remove_df: "c_remove = (\<lambda> x u. set_to_nat ((nat_to_set u) - {x}))"
proof (rule ext, rule ext)
  fix x u show "c_remove x u = set_to_nat (nat_to_set u - {x})"
  proof (cases)
    assume A: "x \<in> nat_to_set u"
    then have S1: "c_in x u = 1" by (simp add: x_in_u_eq)
    then have S2: "c_remove x u = u - 2^x" by (simp add: c_remove_def)
    from A have "set_to_nat (nat_to_set u - {x}) = u - 2 ^ x" by (rule remove_lemma)
    with S2 show ?thesis by auto
  next
    assume A: "x \<notin> nat_to_set u"
    then have S1: "c_in x u \<noteq> 1" by (simp add: x_in_u_eq)
    then have S2: "c_remove x u = u" by (simp add: c_remove_def c_in_def)
    from A have "nat_to_set u - {x} = nat_to_set u" by auto
    with S2 show ?thesis by auto
  qed
qed

definition
  c_union :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_union = (\<lambda> u v. set_to_nat (nat_to_set u \<union> nat_to_set v))"

theorem c_union_is_pr: "c_union \<in> PrimRec2"
proof -
  define f where "f y x = set_to_nat ((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y})"
    for y x
  have f_is_pr: "f \<in> PrimRec2"
  proof -
    define g where "g = c_fst"
    from c_fst_is_pr g_def have g_is_pr: "g \<in> PrimRec1" by auto
    define h where "h a b c = (if c_in a (c_snd c) = 1 then c_insert a b else b)" for a b c
    from c_in_is_pr c_insert_is_pr have h_is_pr: "h \<in> PrimRec3" unfolding h_def by prec
    have f_at_0: "\<forall> x. f 0 x = g x"
    proof
      fix x show "f 0 x = g x" by (unfold f_def, unfold g_def, simp)
    qed
    have f_at_Suc: "\<forall> x y. f (Suc y) x = h y (f y x) x"
    proof (rule allI, rule allI)
      fix x y show "f (Suc y) x = h y (f y x) x"
      proof (cases)
        assume A: "c_in y (c_snd x) = 1"
        then have S1: "y \<in> (nat_to_set (c_snd x))" by (simp add: x_in_u_eq)
        from A h_def have S2: "h y (f y x) x = c_insert y (f y x)" by auto
        from S1 have S3: "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y} \<union> {y}" by auto
        from nat_to_set_is_finite have S4: "finite ((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y})" by auto
        with nat_to_set_srj f_def have S5: "nat_to_set (f y x) = (nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y}" by auto
        from f_def have S6: "f (Suc y) x = set_to_nat ((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < Suc y})" by simp
        also from S3 have "\<dots> = set_to_nat (((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y}) \<union> {y})" by auto
        also from S5 have "\<dots> = set_to_nat (nat_to_set (f y x) \<union> {y})" by auto
        also have "\<dots> = c_insert y (f y x)" by (simp add: c_insert_df)
        finally show ?thesis by (simp add: S2)
      next
        assume A: "\<not> c_in y (c_snd x) = 1"
        then have S1: "y \<notin> (nat_to_set (c_snd x))" by (simp add: x_in_u_eq)
        from A h_def have S2: "h y (f y x) x = f y x" by auto
        have S3: "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y}"
        proof -
          have "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y} \<union> {z \<in> nat_to_set (c_snd x). z = y}"
            by auto
          with S1 show ?thesis by auto
        qed
        from nat_to_set_is_finite have S4: "finite ((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y})" by auto
        with nat_to_set_srj f_def have S5: "nat_to_set (f y x) = (nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y}" by auto
        from f_def have S6: "f (Suc y) x = set_to_nat ((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < Suc y})" by simp
        also from S3 have "\<dots> = set_to_nat (((nat_to_set (c_fst x)) \<union> {z \<in> nat_to_set (c_snd x). z < y}))" by auto
        also from S5 have "\<dots> = set_to_nat (nat_to_set (f y x))" by auto
        also have "\<dots> = f y x" by simp
        finally show ?thesis by (simp add: S2)
      qed
    qed
    from g_is_pr h_is_pr f_at_0 f_at_Suc show ?thesis by (rule pr_rec_scheme)
  qed
  define union where "union u v = f v (c_pair u v)" for u v
  from f_is_pr have union_is_pr: "union \<in> PrimRec2" unfolding union_def by prec
  have "\<And> u v. union u v = set_to_nat (nat_to_set u \<union> nat_to_set v)"
  proof -
    fix u v show "union u v = set_to_nat (nat_to_set u \<union> nat_to_set v)"
    proof -
      from nat_to_set_upper_bound1 have "{z \<in> nat_to_set v. z < v} = nat_to_set v" by auto
      with union_def f_def show ?thesis by auto
    qed
  qed
  then have "union = (\<lambda> u v. set_to_nat (nat_to_set u \<union> nat_to_set v))" by (simp add: ext)
  with c_union_def have "c_union = union" by simp
  with union_is_pr show ?thesis by simp
qed

definition
  c_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_diff = (\<lambda> u v. set_to_nat (nat_to_set u - nat_to_set v))"

theorem c_diff_is_pr: "c_diff \<in> PrimRec2"
proof -
  define f where "f y x = set_to_nat ((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y})"
    for y x
  have f_is_pr: "f \<in> PrimRec2"
  proof -
    define g where "g = c_fst"
    from c_fst_is_pr g_def have g_is_pr: "g \<in> PrimRec1" by auto
    define h where "h a b c = (if c_in a (c_snd c) = 1 then c_remove a b else b)" for a b c
    from c_in_is_pr c_remove_is_pr have h_is_pr: "h \<in> PrimRec3" unfolding h_def by prec
    have f_at_0: "\<forall> x. f 0 x = g x"
    proof
      fix x show "f 0 x = g x" by (unfold f_def, unfold g_def, simp)
    qed
    have f_at_Suc: "\<forall> x y. f (Suc y) x = h y (f y x) x"
    proof (rule allI, rule allI)
      fix x y show "f (Suc y) x = h y (f y x) x"
      proof (cases)
        assume A: "c_in y (c_snd x) = 1"
        then have S1: "y \<in> (nat_to_set (c_snd x))" by (simp add: x_in_u_eq)
        from A h_def have S2: "h y (f y x) x = c_remove y (f y x)" by auto
        have "(nat_to_set (c_fst x)) - ({z \<in> nat_to_set (c_snd x). z < y} \<union> {y}) =
              ((nat_to_set (c_fst x)) - ({z \<in> nat_to_set (c_snd x). z < y}) - {y})" by auto
        then have lm1: "set_to_nat (nat_to_set (c_fst x) - ({z \<in> nat_to_set (c_snd x). z < y} \<union> {y})) =
                        set_to_nat (nat_to_set (c_fst x) - {z \<in> nat_to_set (c_snd x). z < y} - {y})" by auto
        from S1 have S3: "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y} \<union> {y}" by auto
        from nat_to_set_is_finite have S4: "finite ((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y})" by auto
        with nat_to_set_srj f_def have S5: "nat_to_set (f y x) = (nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y}" by auto
        from f_def have S6: "f (Suc y) x = set_to_nat ((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < Suc y})" by simp
        also from S3 have "\<dots> = set_to_nat ((nat_to_set (c_fst x)) - ({z \<in> nat_to_set (c_snd x). z < y} \<union> {y}))" by auto
        also have "\<dots> = set_to_nat (((nat_to_set (c_fst x)) - ({z \<in> nat_to_set (c_snd x). z < y}) - {y}))" by (rule lm1)
        also from S5 have "\<dots> = set_to_nat (nat_to_set (f y x) - {y})" by auto
        also have "\<dots> = c_remove y (f y x)" by (simp add: c_remove_df)
        finally show ?thesis by (simp add: S2)
      next
        assume A: "\<not> c_in y (c_snd x) = 1"
        then have S1: "y \<notin> (nat_to_set (c_snd x))" by (simp add: x_in_u_eq)
        from A h_def have S2: "h y (f y x) x = f y x" by auto
        have S3: "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y}"
        proof -
          have "{z \<in> nat_to_set (c_snd x). z < Suc y} = {z \<in> nat_to_set (c_snd x). z < y} \<union> {z \<in> nat_to_set (c_snd x). z = y}"
            by auto
          with S1 show ?thesis by auto
        qed
        from nat_to_set_is_finite have S4: "finite ((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y})" by auto
        with nat_to_set_srj f_def have S5: "nat_to_set (f y x) = (nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y}" by auto
        from f_def have S6: "f (Suc y) x = set_to_nat ((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < Suc y})" by simp
        also from S3 have "\<dots> = set_to_nat (((nat_to_set (c_fst x)) - {z \<in> nat_to_set (c_snd x). z < y}))" by auto
        also from S5 have "\<dots> = set_to_nat (nat_to_set (f y x))" by auto
        also have "\<dots> = f y x" by simp
        finally show ?thesis by (simp add: S2)
      qed
    qed
    from g_is_pr h_is_pr f_at_0 f_at_Suc show ?thesis by (rule pr_rec_scheme)
  qed
  define diff where "diff u v = f v (c_pair u v)" for u v
  from f_is_pr have diff_is_pr: "diff \<in> PrimRec2" unfolding diff_def by prec
  have "\<And> u v. diff u v = set_to_nat (nat_to_set u - nat_to_set v)"
  proof -
    fix u v show "diff u v = set_to_nat (nat_to_set u - nat_to_set v)"
    proof -
      from nat_to_set_upper_bound1 have "{z \<in> nat_to_set v. z < v} = nat_to_set v" by auto
      with diff_def f_def show ?thesis by auto
    qed
  qed
  then have "diff = (\<lambda> u v. set_to_nat (nat_to_set u - nat_to_set v))" by (simp add: ext)
  with c_diff_def have "c_diff = diff" by simp
  with diff_is_pr show ?thesis by simp
qed

definition
  c_intersect :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_intersect = (\<lambda> u v. set_to_nat (nat_to_set u \<inter> nat_to_set v))"

theorem c_intersect_is_pr: "c_intersect \<in> PrimRec2"
proof -
  define f where "f u v = c_diff (c_union u v) (c_union (c_diff u v) (c_diff v u))" for u v
  from c_diff_is_pr c_union_is_pr have f_is_pr: "f \<in> PrimRec2" unfolding f_def by prec
  have "\<And> u v. f u v = c_intersect u v"
  proof -
    fix u v show "f u v = c_intersect u v"
    proof -
      let ?A = "nat_to_set u"
      let ?B = "nat_to_set v"
      have A_fin: "finite ?A" by (rule nat_to_set_is_finite)
      have B_fin: "finite ?B" by (rule nat_to_set_is_finite)
      have S1: "c_union u v = set_to_nat (?A \<union> ?B)" by (simp add: c_union_def)
      have S2: "c_diff u v = set_to_nat (?A - ?B)" by (simp add: c_diff_def)
      have S3: "c_diff v u = set_to_nat (?B - ?A)" by (simp add: c_diff_def)
      from S2 A_fin B_fin have S4: "nat_to_set (c_diff u v) = ?A - ?B" by  (simp add: nat_to_set_srj)
      from S3 A_fin B_fin have S5: "nat_to_set (c_diff v u) = ?B - ?A" by  (simp add: nat_to_set_srj)
      from S4 S5 have S6: "c_union (c_diff u v) (c_diff v u) = set_to_nat ((?A - ?B) \<union> (?B - ?A))" by (simp add: c_union_def)
      from S1 A_fin B_fin have S7: "nat_to_set (c_union u v) = ?A \<union> ?B" by  (simp add: nat_to_set_srj)
      from S6 A_fin B_fin have S8: "nat_to_set (c_union (c_diff u v) (c_diff v u)) = (?A - ?B) \<union> (?B - ?A)" by  (simp add: nat_to_set_srj)
      from S7 S8 have S9: "f u v = set_to_nat ((?A \<union> ?B) - ((?A - ?B) \<union> (?B - ?A)))" by (simp add: c_diff_def f_def)
      have S10: "?A \<inter> ?B = (?A \<union> ?B) - ((?A - ?B) \<union> (?B - ?A))" by auto
      with S9 have S11: "f u v = set_to_nat (?A \<inter> ?B)" by auto
      have "c_intersect u v = set_to_nat (?A \<inter> ?B)" by (simp add: c_intersect_def)
      with S11 show ?thesis by auto
    qed
  qed
  then have "f = c_intersect" by (simp add: ext)
  with f_is_pr show ?thesis by auto
qed

end
