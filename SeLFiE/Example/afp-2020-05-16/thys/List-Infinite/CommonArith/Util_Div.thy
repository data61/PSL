(*  Title:      Util_Div.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Results for division and modulo operators on integers\<close>

theory Util_Div
imports Util_Nat
begin

subsection \<open>Additional (in-)equalities with \<open>div\<close> and \<open>mod\<close>\<close>

corollary Suc_mod_le_divisor: "0 < m \<Longrightarrow> Suc (n mod m) \<le> m"
by (rule Suc_leI, rule mod_less_divisor)

lemma mod_less_dividend: "\<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> n mod m < (n::nat)"
by (rule less_le_trans[OF mod_less_divisor])
(*lemma mod_le_dividend: "n mod m \<le> (n::nat)"*)
lemmas mod_le_dividend = mod_less_eq_dividend



lemma diff_mod_le: "(t - r) mod m \<le> (t::nat)"
by (rule le_trans[OF mod_le_dividend, OF diff_le_self])


(*corollary div_mult_cancel: "m div n * n = m - m mod (n::nat)"*)
lemmas div_mult_cancel = minus_mod_eq_div_mult [symmetric]

lemma mod_0_div_mult_cancel: "(n mod (m::nat) = 0) = (n div m * m = n)"
apply (insert eq_diff_left_iff[OF mod_le_dividend le0, of n m])
apply (simp add: mult.commute minus_mod_eq_mult_div [symmetric])
done

lemma div_mult_le: "(n::nat) div m * m \<le> n"
by (simp add: mult.commute minus_mod_eq_mult_div [symmetric])
lemma less_div_Suc_mult: "0 < (m::nat) \<Longrightarrow> n < Suc (n div m) * m"
apply (simp add: mult.commute minus_mod_eq_mult_div [symmetric])
apply (rule less_add_diff)
by (rule mod_less_divisor)

lemma nat_ge2_conv: "((2::nat) \<le> n) = (n \<noteq> 0 \<and> n \<noteq> 1)"
by fastforce

lemma Suc0_mod: "m \<noteq> Suc 0 \<Longrightarrow> Suc 0 mod m = Suc 0"
by (case_tac m, simp_all)
corollary Suc0_mod_subst: "
  \<lbrakk> m \<noteq> Suc 0; P (Suc 0) \<rbrakk> \<Longrightarrow> P (Suc 0 mod m)"
by (blast intro: subst[OF Suc0_mod[symmetric]])
corollary Suc0_mod_cong: "
  m \<noteq> Suc 0 \<Longrightarrow> f (Suc 0 mod m) = f (Suc 0)"
by (blast intro: arg_cong[OF Suc0_mod])


subsection \<open>Additional results for addition and subtraction with \<open>mod\<close>\<close>

lemma mod_Suc_conv: "
  ((Suc a) mod m = (Suc b) mod m) = (a mod m = b mod m)"
by (simp add: mod_Suc)

lemma mod_Suc': "
  0 < n \<Longrightarrow> Suc m mod n = (if m mod n < n - Suc 0 then Suc (m mod n) else 0)"
apply (simp add: mod_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma mod_add:"
  ((a + k) mod m = (b + k) mod m) =
  ((a::nat) mod m = b mod m)"
by (induct "k", simp_all add: mod_Suc_conv)

corollary mod_sub_add: "
  k \<le> (a::nat) \<Longrightarrow>
  ((a - k) mod m = b mod m) = (a mod m = (b + k) mod m)"
by (simp add: mod_add[where m=m and a="a-k" and b=b and k=k, symmetric])


lemma mod_sub_eq_mod_0_conv: "
  a + b \<le> (n::nat) \<Longrightarrow>
  ((n - a) mod m = b mod m) = ((n - (a + b)) mod m = 0)"
by (insert mod_add[of "n-(a+b)" b m 0], simp)
lemma mod_sub_eq_mod_swap: "
  \<lbrakk> a \<le> (n::nat); b \<le> n \<rbrakk> \<Longrightarrow>
  ((n - a) mod m = b mod m) = ((n - b) mod m = a mod m)"
by (simp add: mod_sub_add add.commute)

lemma le_mod_greater_imp_div_less: "
  \<lbrakk> a \<le> (b::nat); a mod m > b mod m \<rbrakk> \<Longrightarrow> a div m < b div m"
apply (rule ccontr, simp add: linorder_not_less)
apply (drule mult_le_mono1[of "b div m" _ m])
apply (drule add_less_le_mono[of "b mod m" "a mod m" "b div m * m" "a div m * m"])
apply simp_all
done

lemma less_mod_ge_imp_div_less: "\<lbrakk> a < (b::nat); a mod m \<ge> b mod m \<rbrakk> \<Longrightarrow> a div m < b div m"
apply (case_tac "m = 0", simp)
apply (rule mult_less_cancel1[of m, THEN iffD1, THEN conjunct2])
apply (simp add: minus_mod_eq_mult_div [symmetric])
apply (rule order_less_le_trans[of _ "b - a mod m"])
apply (rule diff_less_mono)
apply simp+
done
corollary less_mod_0_imp_div_less: "\<lbrakk> a < (b::nat); b mod m = 0 \<rbrakk> \<Longrightarrow> a div m < b div m"
by (simp add: less_mod_ge_imp_div_less)

lemma mod_diff_right_eq: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (b - a mod m) mod m"
proof -
  assume a_as:"a \<le> b"
  have "(b - a) mod m = (b - a + a div m * m) mod m" by simp
  also have "\<dots> = (b + a div m * m - a) mod m" using a_as by simp
  also have "\<dots> = (b + a div m * m - (a div m * m + a mod m)) mod m" by simp
  also have "\<dots> = (b + a div m * m - a div m * m - a mod m) mod m"
    by (simp only: diff_diff_left[symmetric])
  also have "\<dots> = (b - a mod m) mod m" by simp
  finally show ?thesis .
qed
corollary mod_eq_imp_diff_mod_eq: "
  \<lbrakk> x mod m = y mod m; x \<le> (t::nat); y \<le> t \<rbrakk> \<Longrightarrow>
  (t - x) mod m = (t - y) mod m"
by (simp only: mod_diff_right_eq)
lemma mod_eq_imp_diff_mod_eq2: "
  \<lbrakk> x mod m = y mod m; (t::nat) \<le> x; t \<le> y \<rbrakk> \<Longrightarrow>
  (x - t) mod m = (y - t) mod m"
apply (case_tac "m = 0", simp+)
apply (subst mod_mult_self2[of "x - t" m t, symmetric])
apply (subst mod_mult_self2[of "y - t" m t, symmetric])
apply (simp only: add_diff_assoc2 diff_add_assoc gr0_imp_self_le_mult2)
apply (simp only: mod_add)
done

lemma divisor_add_diff_mod_if: "
  (m + b mod m - a mod m) mod (m::nat)= (
  if a mod m \<le> b mod m
  then (b mod m - a mod m)
  else (m + b mod m - a mod m))"
apply (case_tac "m = 0", simp)
apply clarsimp
apply (subst diff_add_assoc, assumption)
apply (simp only: mod_add_self1)
apply (rule mod_less)
apply (simp add: less_imp_diff_less)
done
corollary divisor_add_diff_mod_eq1: "
  a mod m \<le> b mod m \<Longrightarrow>
  (m + b mod m - a mod m) mod (m::nat) = b mod m - a mod m"
by (simp add: divisor_add_diff_mod_if)
corollary divisor_add_diff_mod_eq2: "
  b mod m < a mod m \<Longrightarrow>
  (m + b mod m - a mod m) mod (m::nat) = m + b mod m - a mod m"
by (simp add: divisor_add_diff_mod_if)

lemma mod_add_mod_if: "
  (a mod m + b mod m) mod (m::nat)= (
  if a mod m + b mod m < m
  then a mod m + b mod m
  else a mod m + b mod m - m)"
apply (case_tac "m = 0", simp_all)
apply (clarsimp simp: linorder_not_less)
apply (simp add: mod_if[of "a mod m + b mod m"])
apply (rule mod_less)
apply (rule diff_less_conv[THEN iffD2], assumption)
apply (simp add: add_less_mono)
done
corollary mod_add_mod_eq1: "
  a mod m + b mod m < m \<Longrightarrow>
  (a mod m + b mod m) mod (m::nat) = a mod m + b mod m"
by (simp add: mod_add_mod_if)
corollary mod_add_mod_eq2: "
  m \<le> a mod m + b mod m\<Longrightarrow>
  (a mod m + b mod m) mod (m::nat) = a mod m + b mod m - m"
by (simp add: mod_add_mod_if)

lemma mod_add1_eq_if: "
  (a + b) mod (m::nat) = (
  if (a mod m + b mod m < m) then a mod m + b mod m
  else a mod m + b mod m - m)"
by (simp add: mod_add_eq[symmetric, of a b] mod_add_mod_if)

lemma mod_add_eq_mod_conv: "0 < (m::nat) \<Longrightarrow>
  ((x + a) mod m = b mod m ) =
  (x mod m = (m + b mod m - a mod m) mod m)"
apply (simp only: mod_add_eq[symmetric, of x a])
apply (rule iffI)
 apply (drule sym)
 apply (simp add: mod_add_mod_if)
apply (simp add: mod_add_left_eq le_add_diff_inverse2[OF trans_le_add1[OF mod_le_divisor]])
done




lemma mod_diff1_eq: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (m + b mod m - a mod m) mod m"
apply (case_tac "m = 0", simp)
apply simp
proof -
  assume a_as:"a \<le> b"
    and m_as: "0 < m"
  have a_mod_le_b_s: "a mod m \<le> b"
    by (rule le_trans[of _ a], simp only: mod_le_dividend, simp only: a_as)
  have "(b - a) mod m = (b - a mod m) mod m"
    using a_as by (simp only: mod_diff_right_eq)
  also have "\<dots> = (b - a mod m + m) mod m"
    by simp
  also have "\<dots> = (b + m - a mod m) mod m"
    using a_mod_le_b_s by simp
  also have "\<dots> = (b div m * m + b mod m + m - a mod m) mod m"
    by simp
  also have "\<dots> = (b div m * m + (b mod m + m - a mod m)) mod m"
    by (simp add: diff_add_assoc[OF mod_le_divisor, OF m_as])
  also have "\<dots> = ((b mod m + m - a mod m) + b div m * m) mod m"
    by simp
  also have "\<dots> = (b mod m + m - a mod m) mod m"
    by simp
  also have "\<dots> = (m + b mod m - a mod m) mod m"
    by (simp only: add.commute)
  finally show ?thesis .
qed
corollary mod_diff1_eq_if: "
  (a::nat) \<le> b \<Longrightarrow> (b - a) mod m = (
    if a mod m \<le> b mod m then b mod m - a mod m
    else m + b mod m - a mod m)"
by (simp only: mod_diff1_eq divisor_add_diff_mod_if)
corollary mod_diff1_eq1: "
  \<lbrakk> (a::nat) \<le> b; a mod m \<le> b mod m \<rbrakk>
  \<Longrightarrow> (b - a) mod m = b mod m - a mod m"
by (simp add: mod_diff1_eq_if)
corollary mod_diff1_eq2: "
  \<lbrakk> (a::nat) \<le> b; b mod m < a mod m\<rbrakk>
  \<Longrightarrow> (b - a) mod m = m + b mod m - a mod m"
by (simp add: mod_diff1_eq_if)


subsubsection \<open>Divisor subtraction with \<open>div\<close> and \<open>mod\<close>\<close>

lemma mod_diff_self1: "
  0 < (n::nat) \<Longrightarrow> (m - n) mod m = m - n"
by (case_tac "m = 0", simp_all)
lemma mod_diff_self2: "
  m \<le> (n::nat) \<Longrightarrow> (n - m) mod m = n mod m"
by (simp add: mod_diff_right_eq)
lemma mod_diff_mult_self1: "
  k * m \<le> (n::nat) \<Longrightarrow> (n - k * m) mod m = n mod m"
by (simp add: mod_diff_right_eq)
lemma mod_diff_mult_self2: "
  m * k \<le> (n::nat) \<Longrightarrow> (n - m * k) mod m = n mod m"
by (simp only: mult.commute[of m k] mod_diff_mult_self1)

lemma div_diff_self1: "0 < (n::nat) \<Longrightarrow> (m - n) div m = 0"
by (case_tac "m = 0", simp_all)
lemma div_diff_self2: "(n - m) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (case_tac "n < m", simp)
apply (case_tac "n = m", simp)
apply (simp add: div_if)
done

lemma div_diff_mult_self1: "
  (n - k * m) div m = n div m - (k::nat)"
apply (case_tac "m = 0", simp)
apply (case_tac "n < k * m")
 apply simp
 apply (drule div_le_mono[OF less_imp_le, of n _ m])
 apply simp
apply (simp add: linorder_not_less)
apply (rule iffD1[OF mult_cancel1_gr0[where k=m]], assumption)
apply (subst diff_mult_distrib2)
apply (simp only: minus_mod_eq_mult_div [symmetric])
apply (simp only: diff_commute[of _ "k*m"])
apply (simp only: mult.commute[of m])
apply (simp only: mod_diff_mult_self1)
done
lemma div_diff_mult_self2: "
  (n - m * k) div m = n div m - (k::nat)"
by (simp only: mult.commute div_diff_mult_self1)


subsubsection \<open>Modulo equality and modulo of difference\<close>

lemma mod_eq_imp_diff_mod_0:"
  (a::nat) mod m = b mod m \<Longrightarrow> (b - a) mod m = 0"
  (is "?P \<Longrightarrow> ?Q")
proof -
  assume as1: ?P
  have "b - a = b div m * m + b mod m - (a div m * m + a mod m)"
    by simp
  also have "\<dots> = b div m * m + b mod m - (a mod m + a div m * m)"
    by simp
  also have "\<dots> = b div m * m + b mod m - a mod m - a div m * m"
    by simp
  also have "\<dots> = b div m * m + b mod m - b mod m - a div m * m"
    using as1 by simp
  also have "\<dots> = b div m * m - a div m * m"
    by (simp only: diff_add_inverse2)
  also have "\<dots> = (b div m - a div m) * m"
    by (simp only: diff_mult_distrib)
  finally have "b - a = (b div m - a div m) * m" .
  hence "(b - a) mod m = (b div m - a div m) * m mod m"
    by (rule arg_cong)
  thus ?thesis by (simp only: mod_mult_self2_is_0)
qed
corollary mod_eq_imp_diff_dvd: "
  (a::nat) mod m = b mod m \<Longrightarrow> m dvd b - a"
by (rule dvd_eq_mod_eq_0[THEN iffD2, OF mod_eq_imp_diff_mod_0])

lemma mod_neq_imp_diff_mod_neq0:"
  \<lbrakk> (a::nat) mod m \<noteq> b mod m; a \<le> b \<rbrakk> \<Longrightarrow> 0 < (b - a) mod m"
apply (case_tac "m = 0", simp)
apply (drule le_imp_less_or_eq, erule disjE)
 prefer 2
 apply simp
apply (drule neq_iff[THEN iffD1], erule disjE)
 apply (simp add: mod_diff1_eq1)
apply (simp add: mod_diff1_eq2[OF less_imp_le] trans_less_add1[OF mod_less_divisor])
done
corollary mod_neq_imp_diff_not_dvd:"
  \<lbrakk> (a::nat) mod m \<noteq> b mod m; a \<le> b \<rbrakk> \<Longrightarrow> \<not> m dvd b - a"
by (simp add: dvd_eq_mod_eq_0 mod_neq_imp_diff_mod_neq0)

lemma diff_mod_0_imp_mod_eq:"
  \<lbrakk> (b - a) mod m = 0; a \<le> b \<rbrakk> \<Longrightarrow> (a::nat) mod m = b mod m"
apply (rule ccontr)
apply (drule mod_neq_imp_diff_mod_neq0)
apply simp_all
done
corollary diff_dvd_imp_mod_eq:"
  \<lbrakk> m dvd b - a; a \<le> b \<rbrakk> \<Longrightarrow> (a::nat) mod m = b mod m"
by (rule dvd_eq_mod_eq_0[THEN iffD1, THEN diff_mod_0_imp_mod_eq])



lemma mod_eq_diff_mod_0_conv: "
  a \<le> (b::nat) \<Longrightarrow> (a mod m = b mod m) = ((b - a) mod m = 0)"
apply (rule iffI)
apply (rule mod_eq_imp_diff_mod_0, assumption)
apply (rule diff_mod_0_imp_mod_eq, assumption+)
done
corollary mod_eq_diff_dvd_conv: "
  a \<le> (b::nat) \<Longrightarrow> (a mod m = b mod m) = (m dvd b - a)"
by (rule dvd_eq_mod_eq_0[symmetric, THEN subst], rule mod_eq_diff_mod_0_conv)


subsection \<open>Some additional lemmata about integer \<open>div\<close> and \<open>mod\<close>\<close>

lemma zmod_eq_imp_diff_mod_0:
  "a mod m = b mod m \<Longrightarrow> (b - a) mod m = 0" for a b m :: int
  by (simp add: mod_diff_cong)
  
(*lemma int_mod_distrib: "int (n mod m) = int n mod int m"*)
lemmas int_mod_distrib = zmod_int

lemma zdiff_mod_0_imp_mod_eq__pos:"
  \<lbrakk> (b - a) mod m = 0; 0 < (m::int) \<rbrakk> \<Longrightarrow> a mod m = b mod m"
  (is "\<lbrakk> ?P; ?Pm \<rbrakk> \<Longrightarrow> ?Q")
proof -
  assume as1: ?P
    and as2: "0 < m"

  obtain r1 where a_r1:"r1 = a mod m" by blast
  obtain r2 where b_r2:"r2 = b mod m" by blast

  obtain q1 where a_q1: "q1 = a div m" by blast
  obtain q2 where b_q2: "q2 = b div m" by blast

  have a_r1_q1: "a = m * q1 + r1"
    using a_r1 a_q1 by simp
  have b_r2_q2: "b = m * q2 + r2"
    using b_r2 b_q2 by simp

  have "b - a = m * q2 + r2 - (m * q1 + r1)"
    using a_r1_q1 b_r2_q2 by simp
  also have "\<dots> = m * q2 + r2 - m * q1 - r1"
    by simp
  also have "\<dots> = m * q2 - m * q1 + r2 - r1"
    by simp
  finally have "b - a = m * (q2 - q1) + (r2 - r1)"
    by (simp add: right_diff_distrib)
  hence "(b - a) mod m = (r2 - r1) mod m"
    by (simp add: mod_add_eq)
  hence r2_r1_mod_m_0:"(r2 - r1) mod m = 0" (is "?R1")
    by (simp only: as1)

  have "r1 = r2"
  proof (rule notI[of "r1 \<noteq> r2", simplified])
    assume as1': "r1 \<noteq> r2"
    have diff_le_s: "\<And>a b (m::int). \<lbrakk> 0 \<le> a; b < m \<rbrakk> \<Longrightarrow> b - a < m"
      by simp
    have s_r1:"0 \<le> r1 \<and> r1 < m" and s_r2:"0 \<le> r2 \<and> r2 < m"
      by (simp add: as2 a_r1 b_r2 pos_mod_conj)+
    have mr2r1:"-m < r2 - r1" and r2r1m:"r2 - r1 < m"
      by (simp add: minus_less_iff[of m] s_r1 s_r2 diff_le_s)+
    have "0 \<le> r2 - r1 \<Longrightarrow> (r2 - r1) mod m = (r2 - r1)"
      using r2r1m by (blast intro: mod_pos_pos_trivial)
    hence s1_pos: "0 \<le> r2 - r1 \<Longrightarrow> r2 - r1 = 0"
      using r2_r1_mod_m_0 by simp

    have "(r2-r1) mod -m = 0"
      by (simp add: zmod_zminus2_eq_if[of "r2-r1" m, simplified] r2_r1_mod_m_0)
    moreover
    have "r2 - r1 \<le> 0 \<Longrightarrow> (r2 - r1) mod -m = r2 - r1"
      using mr2r1
      by (simp add: mod_neg_neg_trivial)
    ultimately have s1_neg:"r2 - r1 \<le> 0 \<Longrightarrow> r2 - r1 = 0"
      by simp

    have "r2 - r1 = 0"
      using s1_pos s1_neg linorder_linear by blast
    hence "r1 = r2" by simp
    thus False
      using as1' by blast
  qed
  thus ?thesis
    using a_r1 b_r2 by blast
qed

lemma zmod_zminus_eq_conv_pos: "
  0 < (m::int) \<Longrightarrow> (a mod - m = b mod - m) = (a mod m = b mod m)"
apply (simp only: mod_minus_right neg_equal_iff_equal)
apply (simp only: zmod_zminus1_eq_if)
apply (split if_split)+
apply (safe, simp_all)
apply (insert pos_mod_bound[of m a] pos_mod_bound[of m b], simp_all)
done
lemma zmod_zminus_eq_conv: "
  ((a::int) mod - m = b mod - m) = (a mod m = b mod m)"
apply (insert linorder_less_linear[of 0 m], elim disjE)
apply (blast dest: zmod_zminus_eq_conv_pos)
apply simp
apply (simp add: zmod_zminus_eq_conv_pos[of "-m", symmetric])
done

lemma zdiff_mod_0_imp_mod_eq:"
  (b - a) mod m = 0 \<Longrightarrow> (a::int) mod m = b mod m"
by (metis dvd_eq_mod_eq_0 mod_eq_dvd_iff)

lemma zmod_eq_diff_mod_0_conv: "
  ((a::int) mod m = b mod m) = ((b - a) mod m = 0)"
apply (rule iffI)
apply (rule zmod_eq_imp_diff_mod_0, assumption)
apply (rule zdiff_mod_0_imp_mod_eq, assumption)
done

lemma "\<not>(\<exists>(a::int) b m. (b - a) mod m = 0 \<and> a mod m \<noteq> b mod m)"
by (simp add: zmod_eq_diff_mod_0_conv)
lemma "\<exists>(a::nat) b m. (b - a) mod m = 0 \<and> a mod m \<noteq> b mod m"
apply (rule_tac x=1 in exI)
apply (rule_tac x=0 in exI)
apply (rule_tac x=2 in exI)
apply simp
done



lemma zmult_div_leq_mono:"
  \<lbrakk> (0::int) \<le> x; a \<le> b; 0 < d \<rbrakk> \<Longrightarrow> x * a div d \<le> x * b div d"
by (metis mult_right_mono zdiv_mono1 mult.commute)

lemma zmult_div_leq_mono_neg:"
  \<lbrakk> x \<le> (0::int); a \<le> b; 0 < d \<rbrakk> \<Longrightarrow> x * b div d \<le> x * a div d"
by (metis mult_left_mono_neg zdiv_mono1)

lemma zmult_div_pos_le:"
  \<lbrakk> (0::int) \<le> a; 0 \<le> b; b \<le> c \<rbrakk> \<Longrightarrow> a * b div c \<le> a"
apply (case_tac "b = 0", simp)
apply (subgoal_tac "b * a \<le> c * a")
 prefer 2
 apply (simp only: mult_right_mono)
apply (simp only: mult.commute)
apply (subgoal_tac "a * b div c \<le> a * c div c")
 prefer 2
 apply (simp only: zdiv_mono1)
apply simp
done

lemma zmult_div_neg_le:"
  \<lbrakk> a \<le> (0::int); 0 < c; c \<le> b \<rbrakk> \<Longrightarrow> a * b div c \<le> a"
apply (subgoal_tac "b * a \<le> c * a")
 prefer 2
 apply (simp only: mult_right_mono_neg)
apply (simp only: mult.commute)
apply (subgoal_tac "a * b div c \<le> a * c div c")
 prefer 2
 apply (simp only: zdiv_mono1)
apply simp
done

lemma zmult_div_ge_0:"\<lbrakk> (0::int) \<le> x; 0 \<le> a; 0 < c \<rbrakk> \<Longrightarrow> 0 \<le> a * x div c"
by (metis pos_imp_zdiv_nonneg_iff split_mult_pos_le)

corollary zmult_div_plus_ge_0: "
  \<lbrakk> (0::int) \<le> x; 0 \<le> a; 0 \<le> b; 0 < c\<rbrakk> \<Longrightarrow> 0 \<le> a * x div c + b"
by (insert zmult_div_ge_0[of x a c], simp)


lemma zmult_div_abs_ge: "
  \<lbrakk> (0::int) \<le> b; b \<le> b'; 0 \<le> a; 0 < c\<rbrakk> \<Longrightarrow>
  \<bar>a * b div c\<bar> \<le> \<bar>a * b' div c\<bar>"
apply (insert zmult_div_ge_0[of b a c] zmult_div_ge_0[of "b'" a c], simp)
by (metis zmult_div_leq_mono)

lemma zmult_div_plus_abs_ge: "
  \<lbrakk> (0::int) \<le> b; b \<le> b'; 0 \<le> a; 0 < c \<rbrakk> \<Longrightarrow>
  \<bar>a * b div c + a\<bar> \<le> \<bar>a * b' div c + a\<bar>"
apply (insert zmult_div_plus_ge_0[of b a a c] zmult_div_plus_ge_0[of "b'" a a c], simp)
by (metis zmult_div_leq_mono)


subsection \<open>Some further (in-)equality results for \<open>div\<close> and \<open>mod\<close>\<close>

lemma less_mod_eq_imp_add_divisor_le: "
  \<lbrakk> (x::nat) < y; x mod m = y mod m \<rbrakk> \<Longrightarrow> x + m \<le> y"
apply (case_tac "m = 0")
 apply simp
apply (rule contrapos_pp[of "x mod m = y mod m"])
 apply blast
apply (rule ccontr, simp only: not_not, clarify)
proof -
  assume m_greater_0: "0 < m"
  assume x_less_y:"x < y"
  hence y_x_greater_0:"0 < y - x"
    by simp
  assume "x mod m = y mod m"
  hence y_x_mod_m: "(y - x) mod m = 0"
    by (simp only: mod_eq_imp_diff_mod_0)
  assume "\<not> x + m \<le> y"
  hence "y < x + m" by simp
  hence "y - x < x + m - x"
    by (simp add: diff_add_inverse diff_less_conv m_greater_0)
  hence y_x_less_m: "y - x < m"
    by simp
  have "(y - x) mod m = y - x"
    using y_x_less_m by simp
  hence "y - x = 0"
    using y_x_mod_m by simp
  thus False
    using y_x_greater_0 by simp
qed


lemma less_div_imp_mult_add_divisor_le: "
  (x::nat) < n div m \<Longrightarrow> x * m + m \<le> n"
apply (case_tac "m = 0", simp)
apply (case_tac "n < m", simp)
apply (simp add: linorder_not_less)
apply (subgoal_tac "m \<le> n - n mod m")
 prefer 2
 apply (drule div_le_mono[of m _ m])
 apply (simp only: div_self)
 apply (drule mult_le_mono2[of 1 _ m])
 apply (simp only: mult_1_right minus_mod_eq_mult_div [symmetric])
apply (drule less_imp_le_pred[of x])
apply (drule mult_le_mono2[of x _ m])
apply (simp add: diff_mult_distrib2 minus_mod_eq_mult_div [symmetric] del: diff_diff_left)
apply (simp only: le_diff_conv2[of m])
apply (drule le_diff_imp_le[of "m * x + m"])
apply (simp only: mult.commute[of _ m])
done

lemma mod_add_eq_imp_mod_0: "
  ((n + k) mod (m::nat) = n mod m) = (k mod m = 0)"
by (metis add_eq_if mod_add mod_add_self1 mod_self add.commute)

lemma between_imp_mod_between: "
  \<lbrakk> b < (m::nat); m * k + a \<le> n; n \<le> m * k + b \<rbrakk> \<Longrightarrow>
  a \<le> n mod m \<and> n mod m \<le> b"
  apply (case_tac "m = 0", simp_all)
  apply (frule gr_implies_gr0)
  apply (subgoal_tac "k = n div m")
   prefer 2
   apply (rule sym, rule div_nat_eqI) apply simp
   apply simp
  apply clarify
  apply (rule conjI)
   apply (rule add_le_imp_le_left[where c="m * (n div m)"], simp)+
  done

corollary between_imp_mod_le: "
  \<lbrakk> b < (m::nat); m * k \<le> n; n \<le> m * k + b \<rbrakk> \<Longrightarrow> n mod m \<le> b"
by (insert between_imp_mod_between[of b m k 0 n], simp)
corollary between_imp_mod_gr0: "
  \<lbrakk> (m::nat) * k < n; n < m * k + m \<rbrakk> \<Longrightarrow> 0 < n mod m"
apply (case_tac "m = 0", simp_all)
apply (rule Suc_le_lessD)
apply (rule between_imp_mod_between[THEN conjunct1, of "m - Suc 0" m k "Suc 0" n])
apply simp_all
done

corollary le_less_div_conv: "
  0 < m \<Longrightarrow> (k * m \<le> n \<and> n < Suc k * m) = (n div m = k)"
  by (auto simp add: ac_simps intro: div_nat_eqI dividend_less_times_div)

lemma le_less_imp_div: "
  \<lbrakk> k * m \<le> n; n < Suc k * m \<rbrakk> \<Longrightarrow> n div m = k"
  by (auto simp add: ac_simps intro: div_nat_eqI)  

lemma div_imp_le_less: "
  \<lbrakk> n div m = k; 0 < m \<rbrakk> \<Longrightarrow> k * m \<le> n \<and> n < Suc k * m"
  by (auto simp add: ac_simps intro: dividend_less_times_div)

lemma div_le_mod_le_imp_le: "
  \<lbrakk> (a::nat) div m \<le> b div m; a mod m \<le> b mod m \<rbrakk> \<Longrightarrow> a \<le> b"
apply (rule subst[OF mult_div_mod_eq[of m a]])
apply (rule subst[OF mult_div_mod_eq[of m b]])
apply (rule add_le_mono)
apply (rule mult_le_mono2)
apply assumption+
done

lemma le_mod_add_eq_imp_add_mod_le: "
  \<lbrakk> a \<le> b; (a + k) mod m = (b::nat) mod m \<rbrakk> \<Longrightarrow> a + k mod m \<le> b"
by (metis add_le_mono2 diff_add_inverse le_add1 le_add_diff_inverse mod_diff1_eq mod_less_eq_dividend)

corollary mult_divisor_le_mod_ge_imp_ge: "
  \<lbrakk> (m::nat) * k \<le> n; r \<le> n mod m \<rbrakk> \<Longrightarrow> m * k + r \<le> n"
apply (insert le_mod_add_eq_imp_add_mod_le[of "m * k" n "n mod m" m])
apply (simp add: add.commute[of "m * k"])
done


subsection \<open>Additional multiplication results for \<open>mod\<close> and \<open>div\<close>\<close>

lemma mod_0_imp_mod_mult_right_0: "
  n mod m = (0::nat) \<Longrightarrow> n * k mod m = 0"
by fastforce
lemma mod_0_imp_mod_mult_left_0: "
  n mod m = (0::nat) \<Longrightarrow> k * n mod m = 0"
by fastforce

lemma mod_0_imp_div_mult_left_eq: "
  n mod m = (0::nat) \<Longrightarrow> k * n div m = k * (n div m)"
by fastforce
lemma mod_0_imp_div_mult_right_eq: "
  n mod m = (0::nat) \<Longrightarrow> n * k div m = k * (n div m)"
by fastforce


lemma mod_0_imp_mod_factor_0_left: "
  n mod (m * m') = (0::nat) \<Longrightarrow> n mod m = 0"
by fastforce
lemma mod_0_imp_mod_factor_0_right: "
  n mod (m * m') = (0::nat) \<Longrightarrow> n mod m' = 0"
by fastforce


subsection \<open>Some factor distribution facts for \<open>mod\<close>\<close>

lemma mod_eq_mult_distrib: "
  (a::nat) mod m = b mod m \<Longrightarrow>
  a * k mod (m * k) = b * k mod (m * k)"
by simp

lemma mod_mult_eq_imp_mod_eq: "
  (a::nat) mod (m * k) = b mod (m * k) \<Longrightarrow> a mod m = b mod m"
apply (simp only: mod_mult2_eq)
apply (drule_tac arg_cong[where f="\<lambda>x. x mod m"])
apply (simp add: add.commute)
done
corollary mod_eq_mod_0_imp_mod_eq: "
  \<lbrakk> (a::nat) mod m' = b mod m'; m' mod m = 0 \<rbrakk>
  \<Longrightarrow> a mod m = b mod m"
  using mod_mod_cancel [of m m' a] mod_mod_cancel [of m m' b] by auto

lemma mod_factor_imp_mod_0: "
  \<lbrakk>(x::nat) mod (m * k) = y * k mod (m * k)\<rbrakk> \<Longrightarrow> x mod k = 0"
  (is "\<lbrakk> ?P1 \<rbrakk> \<Longrightarrow> ?Q")
proof -
  assume as1: ?P1
  have "y * k mod (m * k) = y mod m * k"
    by simp
  hence "x mod (m * k) = y mod m * k"
    using as1 by simp
  hence "y mod m * k = k * (x div k mod m) + x mod k" (is "?l1 = ?r1")
    by (simp only: ac_simps mod_mult2_eq)
  hence "(y mod m * k) mod k = ?r1 mod k"
    by simp
  hence "0 = ?r1 mod k"
    by simp
  thus "x mod k = 0"
    by (simp add: mod_add_eq)
qed
corollary mod_factor_div: "
  \<lbrakk>(x::nat) mod (m * k) = y * k mod (m * k)\<rbrakk> \<Longrightarrow> x div k * k = x"
by (blast intro: mod_factor_imp_mod_0[THEN mod_0_div_mult_cancel[THEN iffD1]])

lemma mod_factor_div_mod:"
  \<lbrakk> (x::nat) mod (m * k) = y * k mod (m * k); 0 < k \<rbrakk>
  \<Longrightarrow> x div k mod m = y mod m"
  (is "\<lbrakk> ?P1; ?P2 \<rbrakk> \<Longrightarrow> ?L = ?R")
proof -
  assume as1: ?P1
  assume as2: ?P2
  have x_mod_k_0: "x mod k = 0"
    using as1 by (blast intro: mod_factor_imp_mod_0)
  have "?L * k + x mod k = x mod (k * m)"
    by (simp only: mod_mult2_eq mult.commute[of _ k])
  hence "?L * k = x mod (k * m)"
    using x_mod_k_0 by simp
  hence "?L * k = y * k mod (m * k)"
    using as1 by (simp only: ac_simps)
  hence "?L * k = y mod m * k"
    by (simp only: mult_mod_left)
  thus ?thesis
    using as2 by simp
qed


subsection \<open>More results about quotient \<open>div\<close> with addition and subtraction\<close>

lemma div_add1_eq_if: "0 < m \<Longrightarrow>
  (a + b) div (m::nat) = a div m + b div m + (
    if a mod m + b mod m < m then 0 else Suc 0)"
apply (simp only: div_add1_eq[of a b])
apply (rule arg_cong[of "(a mod m + b mod m) div m"])
apply (clarsimp simp: linorder_not_less)
apply (rule le_less_imp_div[of "Suc 0" m "a mod m + b mod m"], simp)
apply simp
apply (simp only: add_less_mono[OF mod_less_divisor mod_less_divisor])
done
corollary div_add1_eq1: "
  a mod m + b mod m < (m::nat) \<Longrightarrow>
  (a + b) div (m::nat) = a div m + b div m"
apply (case_tac "m = 0", simp)
apply (simp add: div_add1_eq_if)
done
corollary div_add1_eq1_mod_0_left: "
  a mod m = 0 \<Longrightarrow> (a + b) div (m::nat) = a div m + b div m"
apply (case_tac "m = 0", simp)
apply (simp add: div_add1_eq1)
done
corollary div_add1_eq1_mod_0_right: "
  b mod m = 0 \<Longrightarrow> (a + b) div (m::nat) = a div m + b div m"
by (fastforce simp: div_add1_eq1_mod_0_left)
corollary div_add1_eq2: "
  \<lbrakk> 0 < m; (m::nat) \<le> a mod m + b mod m \<rbrakk> \<Longrightarrow>
  (a + b) div (m::nat) = Suc (a div m + b div m)"
by (simp add: div_add1_eq_if)

lemma div_Suc: "
  0 < n \<Longrightarrow> Suc m div n = (if Suc (m mod n) = n then Suc (m div n) else m div n)"
apply (drule Suc_leI, drule le_imp_less_or_eq)
apply (case_tac "n = Suc 0", simp)
apply (split if_split, intro conjI impI)
 apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
 apply (subst div_add1_eq2, simp+)
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
apply (subst div_add1_eq1, simp+)
done
lemma div_Suc': "
  0 < n \<Longrightarrow> Suc m div n = (if m mod n < n - Suc 0 then m div n else Suc (m div n))"
apply (simp add: div_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma div_diff1_eq_if: "
  (b - a) div (m::nat) =
  b div m - a div m - (if a mod m \<le> b mod m then 0 else Suc 0)"
apply (case_tac "m = 0", simp)
apply (case_tac "b < a")
 apply (frule less_imp_le[of b])
 apply (frule div_le_mono[of _ _ m])
 apply simp
apply (simp only: linorder_not_less neq0_conv)
proof -
  assume le_as: "a \<le> b"
    and m_as: "0 < m"
  have div_le:"a div m \<le> b div m"
    using le_as by (simp only: div_le_mono)
  have "b - a = b div m * m + b mod m - (a div m * m + a mod m)"
    by simp
  also have "\<dots> = b div m * m + b mod m - a div m * m - a mod m"
    by simp
  also have "\<dots> = b div m * m - a div m * m + b mod m - a mod m"
    by (simp only: diff_add_assoc2[OF mult_le_mono1[OF div_le]])
  finally have b_a_s1: "b - a = (b div m - a div m) * m + b mod m - a mod m"
    (is "?b_a = ?b_a1")
    by (simp only: diff_mult_distrib)
  hence b_a_div_s: "(b - a) div m =
    ((b div m - a div m) * m + b mod m - a mod m) div m"
    by (rule arg_cong)

  show ?thesis
  proof (cases "a mod m \<le> b mod m")
    case True
    hence as': "a mod m \<le> b mod m" .

    have "(b - a) div m = ?b_a1 div m"
      using b_a_div_s .
    also have "\<dots> = ((b div m - a div m) * m + (b mod m - a mod m)) div m"
      using as' by simp
    also have "\<dots> = b div m - a div m + (b mod m - a mod m) div m"
      apply (simp only: add.commute)
      by (simp only: div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]])
    finally have b_a_div_s': "(b - a) div m = \<dots>" .
    have "(b mod m - a mod m) div m = 0"
      by (rule div_less, rule less_imp_diff_less,
          rule mod_less_divisor, rule m_as)
    thus ?thesis
      using b_a_div_s' as'
      by simp
  next
    case False
    hence as1': "\<not> a mod m \<le> b mod m" .
    hence as': "b mod m < a mod m" by simp

    have a_div_less: "a div m < b div m"
      using le_as as'
      by (blast intro: le_mod_greater_imp_div_less)

    have "b div m - a div m = b div m - a div m - (Suc 0 - Suc 0)"
      by simp
    also have "\<dots> = b div m - a div m + Suc 0 - Suc 0"
      by simp
    also have "\<dots> = b div m - a div m - Suc 0 + Suc 0"
      by (simp only: diff_add_assoc2
        a_div_less[THEN zero_less_diff[THEN iffD2], THEN Suc_le_eq[THEN iffD2]])
    finally have b_a_div_s': "b div m - a div m = \<dots>" .

    have "(b - a) div m = ?b_a1 div m"
      using b_a_div_s .
    also have "\<dots> = ((b div m - a div m - Suc 0 + Suc 0) * m
      + b mod m - a mod m ) div m"
      using b_a_div_s' by (rule arg_cong)
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + Suc 0 * m + b mod m - a mod m ) div m"
      by (simp only: add_mult_distrib)
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + m + b mod m - a mod m ) div m"
      by simp
    also have "\<dots> = ((b div m - a div m - Suc 0) * m
      + (m + b mod m - a mod m) ) div m"
      by (simp only: add.assoc m_as
        diff_add_assoc[of "a mod m" "m + b mod m"]
        trans_le_add1[of "a mod m" m, OF mod_le_divisor])
    also have "\<dots> = b div m - a div m - Suc 0
      + (m + b mod m - a mod m) div m"
      by (simp only: add.commute div_mult_self1[OF less_imp_neq[OF m_as, THEN not_sym]])
    finally have b_a_div_s': "(b - a) div m = \<dots>" .

    have div_0_s: "(m + b mod m - a mod m) div m = 0"
      by (rule div_less, simp only: add_diff_less m_as as')
    show ?thesis
      by (simp add: as1' b_a_div_s' div_0_s)
  qed
qed

corollary div_diff1_eq: "
  (b - a) div (m::nat) =
  b div m - a div m - (m + a mod m - Suc (b mod m)) div m"
apply (case_tac "m = 0", simp)
apply (simp only: neq0_conv)
apply (rule subst[of
  "if a mod m \<le> b mod m then 0 else Suc 0"
  "(m + a mod m - Suc(b mod m)) div m"])
 prefer 2 apply (rule div_diff1_eq_if)
apply (split if_split, rule conjI)
 apply simp
apply (clarsimp simp: linorder_not_le)
apply (rule sym)
apply (drule Suc_le_eq[of "b mod m", THEN iffD2])
apply (simp only: diff_add_assoc)
apply (simp only: div_add_self1)
apply (simp add: less_imp_diff_less)
done

corollary div_diff1_eq1: "
  a mod m \<le> b mod m \<Longrightarrow>
  (b - a) div (m::nat) = b div m - a div m"
by (simp add: div_diff1_eq_if)
corollary div_diff1_eq1_mod_0: "
  a mod m = 0 \<Longrightarrow>
  (b - a) div (m::nat) = b div m - a div m"
by (simp add: div_diff1_eq1)
corollary div_diff1_eq2: "
  b mod m < a mod m \<Longrightarrow>
  (b - a) div (m::nat) = b div m - Suc (a div m)"
by (simp add: div_diff1_eq_if)


subsection \<open>Further results about \<open>div\<close> and \<open>mod\<close>\<close>

subsubsection \<open>Some auxiliary facts about \<open>mod\<close>\<close>

lemma diff_less_divisor_imp_sub_mod_eq: "
  \<lbrakk> (x::nat) \<le> y; y - x < m \<rbrakk> \<Longrightarrow> x = y - (y - x) mod m"
by simp
lemma diff_ge_divisor_imp_sub_mod_less: "
  \<lbrakk> (x::nat) \<le> y; m \<le> y - x; 0 < m \<rbrakk> \<Longrightarrow> x < y - (y - x) mod m"
apply (simp only: less_diff_conv)
apply (simp only: le_diff_conv2 add.commute[of m])
apply (rule less_le_trans[of _ "x + m"])
apply simp_all
done

lemma le_imp_sub_mod_le: "
  (x::nat) \<le> y \<Longrightarrow> x \<le> y - (y - x) mod m"
apply (case_tac "m = 0", simp_all)
apply (case_tac "m \<le> y - x")
apply (drule diff_ge_divisor_imp_sub_mod_less[of x y m])
apply simp_all
done

lemma mod_less_diff_mod: "
  \<lbrakk> n mod m < r; r \<le> m; r \<le> (n::nat) \<rbrakk> \<Longrightarrow>
  (n - r) mod m = m + n mod m - r"
apply (case_tac "r = m")
 apply (simp add: mod_diff_self2)
apply (simp add: mod_diff1_eq[of r n m])
done

lemma mod_0_imp_mod_pred: "
  \<lbrakk> 0 < (n::nat); n mod m = 0 \<rbrakk> \<Longrightarrow>
  (n - Suc 0) mod m = m - Suc 0"
apply (case_tac "m = 0", simp_all)
apply (simp only: Suc_le_eq[symmetric])
apply (simp only: mod_diff1_eq)
apply (case_tac "m = Suc 0")
apply simp_all
done

lemma mod_pred: "
  0 < n \<Longrightarrow>
  (n - Suc 0) mod m = (
    if n mod m = 0 then m - Suc 0 else n mod m - Suc 0)"
apply (split if_split, rule conjI)
 apply (simp add: mod_0_imp_mod_pred)
apply clarsimp
apply (case_tac "m = Suc 0", simp)
apply (frule subst[OF Suc0_mod[symmetric], where P="\<lambda>x. x \<le> n mod m"], simp)
apply (simp only: mod_diff1_eq1)
apply (simp add: Suc0_mod)
done
corollary mod_pred_Suc_mod: "
  0 < n \<Longrightarrow> Suc ((n - Suc 0) mod m) mod m = n mod m"
apply (case_tac "m = 0", simp)
apply (simp add: mod_pred)
done
corollary diff_mod_pred: "
  a < b \<Longrightarrow>
  (b - Suc a) mod m = (
    if a mod m = b mod m then m - Suc 0 else (b - a) mod m - Suc 0)"
apply (rule_tac t="b - Suc a" and s="b - a - Suc 0" in subst, simp)
apply (subst mod_pred, simp)
apply (simp add: mod_eq_diff_mod_0_conv)
done
corollary diff_mod_pred_Suc_mod: "
  a < b \<Longrightarrow> Suc ((b - Suc a) mod m) mod m = (b - a) mod m"
apply (case_tac "m = 0", simp)
apply (simp add: diff_mod_pred mod_eq_diff_mod_0_conv)
done

lemma mod_eq_imp_diff_mod_eq_divisor: "
  \<lbrakk> a < b; 0 < m; a mod m = b mod m \<rbrakk> \<Longrightarrow>
  Suc ((b - Suc a) mod m) = m"
apply (drule mod_eq_imp_diff_mod_0[of a])
apply (frule iffD2[OF zero_less_diff])
apply (drule mod_0_imp_mod_pred[of "b-a" m], assumption)
apply simp
done


lemma sub_diff_mod_eq: "
  r \<le> t \<Longrightarrow> (t - (t - r) mod m) mod (m::nat) = r mod m"
by (metis mod_diff_right_eq diff_diff_cancel diff_le_self)

lemma sub_diff_mod_eq': "
  r \<le> t \<Longrightarrow> (k * m + t - (t - r) mod m) mod (m::nat) = r mod m"
apply (simp only: diff_mod_le[of t r m, THEN add_diff_assoc, symmetric])
apply (simp add: sub_diff_mod_eq)
done

lemma mod_eq_Suc_0_conv: "Suc 0 < k \<Longrightarrow> ((x + k - Suc 0) mod k = 0) = (x mod k = Suc 0)"
apply (simp only: mod_pred)
apply (case_tac "x mod k = Suc 0")
apply simp_all
done

lemma mod_eq_divisor_minus_Suc_0_conv: "Suc 0 < k \<Longrightarrow> (x mod k = k - Suc 0) = (Suc x mod k = 0)"
by (simp only: mod_Suc, split if_split, fastforce)


subsubsection \<open>Some auxiliary facts about \<open>div\<close>\<close>

lemma sub_mod_div_eq_div: "((n::nat) - n mod m) div m = n div m"
apply (case_tac "m = 0", simp)
apply (simp add: minus_mod_eq_mult_div)
done

lemma mod_less_imp_diff_div_conv: "
  \<lbrakk> n mod m < r; r \<le> m + n mod m\<rbrakk> \<Longrightarrow> (n - r) div m = n div m - Suc 0"
  apply (case_tac "m = 0", simp)
  apply (simp only: neq0_conv)
  apply (case_tac "n < m", simp)
  apply (simp only: linorder_not_less)
  apply (rule div_nat_eqI)
   apply (simp_all add: algebra_simps minus_mod_eq_mult_div [symmetric])
  done

corollary mod_0_le_imp_diff_div_conv: "
  \<lbrakk> n mod m = 0; 0 < r; r \<le> m \<rbrakk> \<Longrightarrow> (n - r) div m = n div m - Suc 0"
by (simp add: mod_less_imp_diff_div_conv)
corollary mod_0_less_imp_diff_Suc_div_conv: "
  \<lbrakk> n mod m = 0; r < m \<rbrakk> \<Longrightarrow> (n - Suc r) div m = n div m - Suc 0"
by (drule mod_0_le_imp_diff_div_conv[where r="Suc r"], simp_all)
corollary mod_0_imp_diff_Suc_div_conv: "
  (n - r) mod m = 0 \<Longrightarrow> (n - Suc r) div m = (n - r) div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (rule_tac t="n - Suc r" and s="n - r - Suc 0" in subst, simp)
apply (rule mod_0_le_imp_diff_div_conv, simp+)
done
corollary mod_0_imp_sub_1_div_conv: "
  n mod m = 0 \<Longrightarrow> (n - Suc 0) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (simp add: mod_0_less_imp_diff_Suc_div_conv)
done
corollary sub_Suc_mod_div_conv: "
  (n - Suc (n mod m)) div m = n div m - Suc 0"
apply (case_tac "m = 0", simp)
apply (simp add: mod_less_imp_diff_div_conv)
done


lemma div_le_conv: "0 < m \<Longrightarrow> n div m \<le> k = (n \<le> Suc k * m - Suc 0)"
apply (rule iffI)
 apply (drule mult_le_mono1[of _ _ m])
 apply (simp only: mult.commute[of _ m] minus_mod_eq_mult_div [symmetric])
 apply (drule le_diff_conv[THEN iffD1])
 apply (rule le_trans[of _ "m * k + n mod m"], assumption)
 apply (simp add: add.commute[of m])
 apply (simp only: diff_add_assoc[OF Suc_leI])
 apply (rule add_le_mono[OF le_refl])
 apply (rule less_imp_le_pred)
 apply (rule mod_less_divisor, assumption)
apply (drule div_le_mono[of _ _ m])
apply (simp add: mod_0_imp_sub_1_div_conv)
done

lemma le_div_conv: "0 < (m::nat) \<Longrightarrow> (n \<le> k div m) = (n * m \<le> k)"
apply (rule iffI)
 apply (drule mult_le_mono1[of _ _ m])
 apply (simp add: div_mult_cancel)
apply (drule div_le_mono[of _ _ m])
apply simp
done

lemma less_mult_imp_div_less: "n < k * m \<Longrightarrow> n div m < (k::nat)"
apply (case_tac "k = 0", simp)
apply (case_tac "m = 0", simp)
apply simp
apply (drule less_imp_le_pred[of n])
apply (drule div_le_mono[of _ _ m])
apply (simp add: mod_0_imp_sub_1_div_conv)
done

lemma div_less_imp_less_mult: "\<lbrakk> 0 < (m::nat); n div m < k \<rbrakk> \<Longrightarrow> n < k * m"
apply (rule ccontr, simp only: linorder_not_less)
apply (drule div_le_mono[of _ _ m])
apply simp
done

lemma div_less_conv: "0 < (m::nat) \<Longrightarrow> (n div m < k) = (n < k * m)"
apply (rule iffI)
apply (rule div_less_imp_less_mult, assumption+)
apply (rule less_mult_imp_div_less, assumption)
done

lemma div_eq_0_conv: "(n div (m::nat) = 0) = (m = 0 \<or> n < m)"
apply (rule iffI)
 apply (case_tac "m = 0", simp)
 apply (rule ccontr)
 apply (simp add: linorder_not_less)
 apply (drule div_le_mono[of _ _ m])
 apply simp
apply fastforce
done
lemma div_eq_0_conv': "0 < m \<Longrightarrow> (n div (m::nat) = 0) = (n < m)"
by (simp add: div_eq_0_conv)
corollary div_gr_imp_gr_divisor: "x < n div (m::nat) \<Longrightarrow> m \<le> n"
apply (drule gr_implies_gr0, drule neq0_conv[THEN iffD2])
apply (simp add: div_eq_0_conv)
done

lemma mod_0_less_div_conv: "
  n mod (m::nat) = 0 \<Longrightarrow> (k * m < n) = (k < n div m)"
apply (case_tac "m = 0", simp)
apply fastforce
done

lemma add_le_divisor_imp_le_Suc_div: "
  \<lbrakk> x div m \<le> n; y \<le> m \<rbrakk> \<Longrightarrow> (x + y) div m \<le> Suc n"
apply (case_tac "m = 0", simp)
apply (simp only: div_add1_eq_if[of _ x])
apply (drule order_le_less[of y, THEN iffD1], fastforce)
done


text \<open>List of definitions and lemmas\<close>

thm
  minus_mod_eq_mult_div [symmetric]
  mod_0_div_mult_cancel
  div_mult_le
  less_div_Suc_mult
thm
  Suc0_mod
  Suc0_mod_subst
  Suc0_mod_cong

thm
  mod_Suc_conv

thm
  mod_add
  mod_sub_add

thm
  mod_sub_eq_mod_0_conv
  mod_sub_eq_mod_swap

thm
  le_mod_greater_imp_div_less
thm
  mod_diff_right_eq
  mod_eq_imp_diff_mod_eq

thm
  divisor_add_diff_mod_if
  divisor_add_diff_mod_eq1
  divisor_add_diff_mod_eq2

thm
  mod_add_eq
  mod_add1_eq_if
thm
  mod_diff1_eq_if
  mod_diff1_eq
  mod_diff1_eq1
  mod_diff1_eq2

thm
  Divides.nat_mod_distrib
  int_mod_distrib

thm
  zmod_zminus_eq_conv

thm
  mod_eq_imp_diff_mod_0
  zmod_eq_imp_diff_mod_0

thm
  mod_neq_imp_diff_mod_neq0
  diff_mod_0_imp_mod_eq
  zdiff_mod_0_imp_mod_eq

thm
  zmod_eq_diff_mod_0_conv
  mod_eq_diff_mod_0_conv

thm
  less_mod_eq_imp_add_divisor_le
thm
  mod_add_eq_imp_mod_0
thm
  mod_eq_mult_distrib
  mod_factor_imp_mod_0
  mod_factor_div
  mod_factor_div_mod


thm
  mod_diff_self1
  mod_diff_self2
  mod_diff_mult_self1
  mod_diff_mult_self2

thm
  div_diff_self1
  div_diff_self2
  div_diff_mult_self1
  div_diff_mult_self2

thm
  le_less_imp_div
  div_imp_le_less
thm
  le_less_div_conv

thm
  diff_less_divisor_imp_sub_mod_eq
  diff_ge_divisor_imp_sub_mod_less
  le_imp_sub_mod_le

thm
  sub_mod_div_eq_div

thm
  mod_less_imp_diff_div_conv
  mod_0_le_imp_diff_div_conv
  mod_0_less_imp_diff_Suc_div_conv
  mod_0_imp_sub_1_div_conv


thm
  sub_Suc_mod_div_conv

thm
  mod_less_diff_mod
  mod_0_imp_mod_pred

thm
  mod_pred
  mod_pred_Suc_mod

thm
  mod_eq_imp_diff_mod_eq_divisor

thm
  diff_mod_le
  sub_diff_mod_eq
  sub_diff_mod_eq'

thm
  div_diff1_eq_if
  div_diff1_eq
  div_diff1_eq1
  div_diff1_eq2


thm
  div_le_conv

end
