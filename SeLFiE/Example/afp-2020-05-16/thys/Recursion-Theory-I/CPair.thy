(*  Title:       Defintion and basics facts about Cantor pairing function
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Cantor pairing function\<close>

theory CPair
imports Main
begin

text \<open>
  We introduce a particular coding \<open>c_pair\<close> from ordered pairs
  of natural numbers to natural numbers.  See \cite{Rogers} and the
  Isabelle documentation for more information.
\<close>

subsection \<open>Pairing function\<close>

definition
  sf :: "nat \<Rightarrow> nat" where
  sf_def: "sf x = x * (x+1) div 2"

definition
  c_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_pair x y = sf (x+y) + x"

lemma sf_at_0: "sf 0 = 0" by (simp add: sf_def)

lemma sf_at_1: "sf 1 = 1" by (simp add: sf_def)

lemma sf_at_Suc: "sf (x+1) = sf x + x + 1"
proof -
  have S1: "sf(x+1) = ((x+1)*(x+2)) div 2" by (simp add: sf_def)
  have S2: "(x+1)*(x+2) = x*(x+1) + 2*(x+1)" by (auto)
  have S2_1: "\<And> x y. x=y \<Longrightarrow> x div 2 = y div 2" by auto
  from S2 have S3: "(x+1)*(x+2) div 2 = (x*(x+1) + 2*(x+1)) div 2" by (rule S2_1)
  have S4: "(0::nat) < 2" by (auto)
  from S4 have S5: "(x*(x+1) + 2*(x+1)) div 2 = (x+1) + x*(x+1) div 2" by simp
  from S1 S3 S5 show ?thesis by (simp add: sf_def)
qed

lemma arg_le_sf: "x \<le> sf x"
proof -
  have "x + x \<le> x*(x + 1)" by simp
  hence "(x + x) div 2 \<le> x*(x+1) div 2" by (rule div_le_mono)
  hence "x \<le> x*(x+1) div 2" by simp
  thus ?thesis by (simp add: sf_def)
qed

lemma sf_mono: "x \<le> y \<Longrightarrow> sf x \<le> sf y"
proof -
  assume A1: "x \<le> y"
  then have "x+1 \<le> y+1" by (auto)
  with A1 have "x*(x+1) \<le> y*(y+1)" by (rule mult_le_mono)
  then have "x*(x+1) div 2 \<le> y*(y+1) div 2" by (rule div_le_mono)
  thus ?thesis by (simp add: sf_def)
qed

lemma sf_strict_mono: "x < y \<Longrightarrow> sf x < sf y"
proof -
  assume A1: "x < y"
  from A1 have S1: "x+1 \<le> y" by simp
  from S1 sf_mono have S2: "sf (x+1) \<le> sf y" by (auto)
  from sf_at_Suc have S3: "sf x < sf (x+1)" by (auto)
  from S2 S3 show ?thesis by (auto)
qed

lemma sf_posI: "x > 0 \<Longrightarrow> sf(x) > 0"
proof -
  assume A1: "x > 0"
  then have "sf(0) < sf(x)" by (rule sf_strict_mono)
  then show ?thesis by simp
qed

lemma arg_less_sf: "x > 1 \<Longrightarrow> x < sf(x)"
proof -
  assume A1: "x > 1"
  let ?y = "x-(1::nat)"
  from A1 have S1: "x = ?y+1" by simp
  from A1 have "?y > 0" by simp
  then have S2: "sf(?y) > 0" by (rule sf_posI)
  have "sf(?y+1) = sf(?y) + ?y + 1" by (rule sf_at_Suc)
  with S1 have "sf(x) = sf(?y) + x" by simp
  with S2  show ?thesis by simp
qed

lemma sf_eq_arg: "sf x = x \<Longrightarrow> x \<le> 1"
proof -
  assume "sf(x) = x"
  then have "\<not> (x < sf(x))" by simp
  then have "(\<not> (x > 1))" by (auto simp add: arg_less_sf)
  then show ?thesis by simp
qed

lemma sf_le_sfD: "sf x \<le> sf y \<Longrightarrow> x \<le> y"
proof -
  assume A1: "sf x \<le> sf y"
  have S1: "y < x \<Longrightarrow> sf y < sf x" by (rule sf_strict_mono)
  have S2: "y < x \<or> x \<le> y" by (auto)
  from A1 S1 S2 show ?thesis by (auto)
qed

lemma sf_less_sfD: "sf x < sf y \<Longrightarrow> x < y"
proof -
  assume A1: "sf x < sf y"
  have S1: "y \<le> x \<Longrightarrow> sf y \<le> sf x" by (rule sf_mono)
  have S2: "y \<le> x \<or> x < y" by (auto)
  from A1 S1 S2 show ?thesis by (auto)
qed

lemma sf_inj: "sf x = sf y \<Longrightarrow> x = y"
proof -
  assume A1: "sf x = sf y"
  have S1: "sf x \<le> sf y \<Longrightarrow> x \<le> y" by (rule sf_le_sfD)
  have S2: "sf y \<le> sf x \<Longrightarrow> y \<le> x" by (rule sf_le_sfD)
  from A1 have S3: "sf x \<le> sf y \<and> sf y \<le> sf x" by (auto)
  from S3 S1 S2 have S4: "x \<le> y \<and> y \<le> x" by (auto)
  from S4 show ?thesis by (auto)
qed

text \<open>Auxiliary lemmas\<close>

lemma sf_aux1: "x + y < z \<Longrightarrow> sf(x+y) + x < sf(z)"
proof -
  assume A1: "x+y < z"
  from A1 have S1: "x+y+1 \<le> z" by (auto)
  from S1 have S2: "sf(x+y+1) \<le> sf(z)" by (rule sf_mono)
  have S3: "sf(x+y+1) = sf(x+y) + (x+y)+1" by (rule sf_at_Suc)
  from S3 S2 have S4: "sf(x+y) + (x+y) + 1 \<le> sf(z)" by (auto)
  from S4 show ?thesis by (auto)
qed

lemma sf_aux2: "sf(z) \<le> sf(x+y) + x \<Longrightarrow> z \<le> x+y"
proof -
  assume A1: "sf(z) \<le> sf(x+y) + x"
  from A1 have S1: "\<not> sf(x+y) +x < sf(z)" by (auto)
  from S1 sf_aux1 have S2: "\<not> x+y < z" by (auto)
  from S2 show ?thesis by (auto)
qed

lemma sf_aux3: "sf(z) + m < sf(z+1) \<Longrightarrow> m \<le> z"
proof -
  assume A1: "sf(z) + m < sf(z+1)"
  have S1: "sf(z+1) = sf(z) + z + 1" by (rule sf_at_Suc)
  from A1 S1 have S2: "sf(z) + m < sf(z) + z + 1" by (auto)
  from S2 have S3: "m < z + 1" by (auto)
  from S3 show ?thesis by (auto)
qed

lemma sf_aux4: "(s::nat) < t \<Longrightarrow> (sf s) + s < sf t"
proof -
  assume A1: "(s::nat) < t"
  have "s*(s + 1) + 2*(s+1) \<le> t*(t+1)"
  proof -
    from A1 have S1: "(s::nat) + 1 \<le> t" by (auto)
    from A1 have "(s::nat) + 2 \<le> t+1" by (auto)
    with S1 have "((s::nat)+1)*(s+2) \<le> t*(t+1)" by (rule mult_le_mono)
    thus ?thesis by (auto)
  qed
  then have S1: "(s*(s+1) + 2*(s+1)) div 2 \<le>  t*(t+1) div 2" by (rule div_le_mono)
  have "(0::nat) < 2" by (auto)
  then have "(s*(s+1) + 2*(s+1)) div 2 = (s+1) + (s*(s+1)) div 2" by simp
  with S1 have "(s*(s+1)) div 2 + (s+1) \<le> t*(t+1) div 2" by (auto)
  then have "(s*(s+1)) div 2 + s < t*(t+1) div 2" by (auto)
  thus ?thesis by (simp add: sf_def)  
qed

text \<open>Basic properties of c\_pair function\<close>

lemma sum_le_c_pair: "x + y \<le> c_pair x y"
proof -
  have "x+y \<le> sf(x+y)" by (rule arg_le_sf)
  thus ?thesis by (simp add: c_pair_def)
qed

lemma arg1_le_c_pair: "x \<le> c_pair x y"
proof -
  have "(x::nat) \<le> x + y" by (simp)
  moreover have "x + y \<le> c_pair x y" by (rule sum_le_c_pair)
  ultimately show ?thesis by (simp)
qed

lemma arg2_le_c_pair: "y \<le> c_pair x y"
proof -
  have "(y::nat) \<le> x + y" by (simp)
  moreover have "x + y \<le> c_pair x y" by (rule sum_le_c_pair)
  ultimately show ?thesis by (simp)
qed

lemma c_pair_sum_mono: "(x1::nat) + y1 < x2 + y2 \<Longrightarrow> c_pair x1 y1 < c_pair x2 y2"
proof -
  assume "(x1::nat) + y1 < x2 + y2"
  hence "sf (x1+y1) + (x1+y1) < sf(x2+y2)" by (rule sf_aux4)
  hence "sf (x1+y1) + x1 < sf(x2+y2) + x2" by (auto)
  thus ?thesis by (simp add: c_pair_def)
qed

lemma c_pair_sum_inj: "c_pair x1 y1 = c_pair x2 y2 \<Longrightarrow> x1 + y1 = x2 + y2"
proof -
  assume A1: "c_pair x1 y1 = c_pair x2 y2"
  have S1: "(x1::nat) + y1 < x2 + y2 \<Longrightarrow> c_pair x1 y1 \<noteq> c_pair x2 y2" by (rule less_not_refl3, rule c_pair_sum_mono, auto)
  have S2: "(x2::nat) + y2 < x1 + y1 \<Longrightarrow> c_pair x1 y1 \<noteq> c_pair x2 y2" by (rule less_not_refl2, rule c_pair_sum_mono, auto)
  from S1 S2 have "(x1::nat) + y1 \<noteq> x2 + y2 \<Longrightarrow> c_pair x1 y1 \<noteq> c_pair x2 y2" by (arith)
  with A1 show ?thesis by (auto)
qed

lemma c_pair_inj: "c_pair x1 y1 = c_pair x2 y2 \<Longrightarrow> x1 = x2 \<and> y1 = y2"
proof -
  assume A1: "c_pair x1 y1 = c_pair x2 y2"
  from A1 have S1: "x1 + y1 = x2 + y2" by (rule c_pair_sum_inj)
  from A1 have S2: "sf (x1+y1) + x1 = sf (x2+y2) + x2" by (unfold c_pair_def)
  from S1 S2 have S3: "x1 = x2" by (simp)
  from S1 S3 have S4: "y1 = y2" by (simp)
  from S3 S4 show ?thesis by (auto)
qed

lemma c_pair_inj1: "c_pair x1 y1 = c_pair x2 y2 \<Longrightarrow> x1 = x2" by (frule c_pair_inj, drule conjunct1)

lemma c_pair_inj2: "c_pair x1 y1 = c_pair x2 y2 \<Longrightarrow> y1 = y2" by (frule c_pair_inj, drule conjunct2)

lemma c_pair_strict_mono1: "x1 < x2 \<Longrightarrow> c_pair x1 y < c_pair x2 y"
proof -
  assume "x1 < x2"
  then have "x1 + y < x2 + y" by simp
  then show ?thesis by (rule c_pair_sum_mono)
qed

lemma c_pair_mono1: "x1 \<le> x2 \<Longrightarrow> c_pair x1 y \<le> c_pair x2 y"
proof -
  assume A1: "x1 \<le> x2"
  show ?thesis
  proof cases
    assume "x1 < x2"
    then have "c_pair x1 y < c_pair x2 y" by (rule c_pair_strict_mono1)
    then show ?thesis by simp
  next
    assume "\<not> x1 < x2"
    with A1 have "x1 = x2" by simp
    then show ?thesis by simp
  qed
qed

lemma c_pair_strict_mono2: "y1 < y2 \<Longrightarrow> c_pair x y1 < c_pair x y2"
proof -
  assume A1: "y1 < y2"
  from A1 have S1: "x + y1 < x + y2" by simp
  then show ?thesis by (rule c_pair_sum_mono)
qed

lemma c_pair_mono2: "y1 \<le> y2 \<Longrightarrow> c_pair x y1 \<le> c_pair x y2"
proof -
  assume A1: "y1 \<le> y2"
  show ?thesis
  proof cases
    assume "y1 < y2"
    then have "c_pair x y1 < c_pair x y2" by (rule c_pair_strict_mono2)
    then show ?thesis by simp
  next
    assume "\<not> y1 < y2"
    with A1 have "y1 = y2" by simp
    then show ?thesis by simp
  qed
qed

subsection \<open>Inverse mapping\<close>

text \<open>
  \<open>c_fst\<close> and \<open>c_snd\<close> are the functions which yield
  the inverse mapping to \<open>c_pair\<close>.
\<close>

definition
  c_sum :: "nat \<Rightarrow> nat" where
  "c_sum u = (LEAST z. u < sf (z+1))"

definition
  c_fst :: "nat \<Rightarrow> nat" where
  "c_fst u = u - sf (c_sum u)"

definition
  c_snd :: "nat \<Rightarrow> nat" where
  "c_snd u = c_sum u - c_fst u"

lemma arg_less_sf_at_Suc_of_c_sum: "u < sf ((c_sum u) + 1)"
proof -
  have "u+1 \<le> sf(u+1)" by (rule arg_le_sf)
  hence "u < sf(u+1)" by simp
  thus ?thesis by (unfold c_sum_def, rule LeastI)
qed

lemma arg_less_sf_imp_c_sum_less_arg: "u < sf(x) \<Longrightarrow> c_sum u < x"
proof -
  assume A1: "u < sf(x)"
  then show ?thesis
  proof (cases x)
    assume "x=0"
    with A1 show ?thesis by (simp add: sf_def)
  next
    fix y
    assume A2: "x = Suc y"
    show ?thesis
    proof -
      from A1 A2 have "u < sf(y+1)" by simp
      hence "(Least (%z. u < sf (z+1))) \<le> y" by (rule Least_le)
      hence "c_sum u \<le> y" by (fold c_sum_def)
      with A2 show ?thesis by simp
    qed
  qed
qed

lemma sf_c_sum_le_arg: "u \<ge> sf (c_sum u)"
proof -
  let ?z = "c_sum u"
  from arg_less_sf_at_Suc_of_c_sum have S1: "u < sf (?z+1)" by (auto)
  have S2: "\<not> c_sum u < c_sum u" by (auto)
  from arg_less_sf_imp_c_sum_less_arg S2 have S3: "\<not> u < sf (c_sum u) " by (auto)
  from S3 show ?thesis by (auto)
qed

lemma c_sum_le_arg: "c_sum u \<le> u"
proof -
  have "c_sum u \<le> sf (c_sum u)" by (rule arg_le_sf)
  moreover have "sf(c_sum u) \<le> u" by (rule sf_c_sum_le_arg)
  ultimately show ?thesis by simp
qed

lemma c_sum_of_c_pair [simp]: "c_sum (c_pair x y) = x + y"
proof -
  let ?u = "c_pair x y"
  let ?z = "c_sum ?u"
  have S1: "?u < sf(?z+1)" by (rule arg_less_sf_at_Suc_of_c_sum)
  have S2: "sf(?z) \<le> ?u" by (rule sf_c_sum_le_arg)
  from S1 have S3: "sf(x+y)+x < sf(?z+1)" by (simp add: c_pair_def)
  from S2 have S4: "sf(?z) \<le> sf(x+y) + x" by (simp add: c_pair_def)
  from S3 have S5: "sf(x+y) < sf(?z+1)" by (auto)
  from S5 have S6: "x+y < ?z+1" by (rule sf_less_sfD)
  from S6 have S7: "x+y \<le> ?z" by (auto)
  from S4 have S8: "?z \<le> x+y" by (rule sf_aux2)
  from S7 S8 have S9: "?z = x+y" by (auto)
  from S9 show ?thesis by (simp)
qed

lemma c_fst_of_c_pair[simp]: "c_fst (c_pair x y) = x"
proof -
  let ?u = "c_pair x y"
  have "c_sum ?u = x + y" by simp
  hence "c_fst ?u = ?u - sf(x+y)" by (simp add: c_fst_def)
  moreover have "?u = sf(x+y) + x" by (simp add: c_pair_def)
  ultimately show ?thesis by (simp)
qed

lemma c_snd_of_c_pair[simp]: "c_snd (c_pair x y) = y"
proof -
  let ?u = "c_pair x y"
  have "c_sum ?u = x + y" by simp
  moreover have "c_fst ?u = x" by simp
  ultimately show ?thesis by (simp add: c_snd_def)
qed

lemma c_pair_at_0: "c_pair 0 0 = 0" by (simp add: sf_def c_pair_def)

lemma c_fst_at_0: "c_fst 0 = 0"
proof -
  have "c_pair 0 0 = 0" by (rule c_pair_at_0)
  hence "c_fst 0 = c_fst (c_pair 0 0)" by simp
  thus ?thesis by simp
qed

lemma c_snd_at_0: "c_snd 0 = 0"
proof -
  have "c_pair 0 0 = 0" by (rule c_pair_at_0)
  hence "c_snd 0 = c_snd (c_pair 0 0)" by simp
  thus ?thesis by simp
qed

lemma sf_c_sum_plus_c_fst: "sf(c_sum u) + c_fst u = u"
proof -
  have S1: "sf(c_sum u) \<le> u" by (rule sf_c_sum_le_arg)
  have S2: "c_fst u = u - sf(c_sum u)" by (simp add: c_fst_def)
  from S1 S2 show ?thesis by (auto)
qed

lemma c_fst_le_c_sum: "c_fst u \<le> c_sum u"
proof -
  have S1: "sf(c_sum u) + c_fst u = u" by (rule sf_c_sum_plus_c_fst)
  have S2: "u < sf((c_sum u) + 1)" by (rule arg_less_sf_at_Suc_of_c_sum)
  from S1 S2 sf_aux3 show ?thesis by (auto)
qed

lemma c_snd_le_c_sum: "c_snd u \<le> c_sum u" by (simp add: c_snd_def)

lemma c_fst_le_arg: "c_fst u \<le> u"
proof -
  have "c_fst u \<le> c_sum u" by (rule c_fst_le_c_sum)
  moreover have "c_sum u \<le> u" by (rule c_sum_le_arg)
  ultimately show ?thesis by simp
qed

lemma c_snd_le_arg: "c_snd u \<le> u"
proof -
  have "c_snd u \<le> c_sum u" by (rule c_snd_le_c_sum)
  moreover have "c_sum u \<le> u" by (rule c_sum_le_arg)
  ultimately show ?thesis by simp
qed

lemma c_sum_is_sum: "c_sum u = c_fst u + c_snd u" by (simp add: c_snd_def c_fst_le_c_sum)
 
lemma proj_eq_imp_arg_eq: "\<lbrakk> c_fst u = c_fst v; c_snd u = c_snd v\<rbrakk> \<Longrightarrow> u = v"
proof -
  assume A1: "c_fst u = c_fst v"
  assume A2: "c_snd u = c_snd v"
  from A1 A2 c_sum_is_sum have S1: "c_sum u = c_sum v" by (auto)
  have S2: "sf(c_sum u) + c_fst u = u" by (rule sf_c_sum_plus_c_fst)
  from A1 S1 S2 have S3: "sf(c_sum v) + c_fst v = u" by (auto)
  from S3 sf_c_sum_plus_c_fst show ?thesis by (auto)
qed

lemma c_pair_of_c_fst_c_snd[simp]: "c_pair (c_fst u) (c_snd u) = u"
proof -
  let ?x = "c_fst u"
  let ?y = "c_snd u"
  have S1: "c_pair ?x ?y = sf(?x + ?y) + ?x" by (simp add: c_pair_def)
  have S2: "c_sum u = ?x + ?y" by (rule c_sum_is_sum)
  from S1 S2 have "c_pair ?x ?y = sf(c_sum u) + c_fst u" by (auto)
  thus ?thesis by (simp add: sf_c_sum_plus_c_fst)
qed

lemma c_sum_eq_arg: "c_sum x = x \<Longrightarrow> x \<le> 1"
proof -
  assume A1: "c_sum x = x"
  have S1: "sf(c_sum x) + c_fst x = x" by (rule sf_c_sum_plus_c_fst)
  from A1 S1 have S2: "sf x + c_fst x = x" by simp
  have S3: "x \<le> sf x" by (rule arg_le_sf)
  from S2 S3 have "sf(x)=x" by simp
  thus ?thesis by (rule sf_eq_arg)
qed

lemma c_sum_eq_arg_2: "c_sum x = x \<Longrightarrow> c_fst x = 0"
proof -
  assume A1: "c_sum x = x"
  have S1: "sf(c_sum x) + c_fst x = x" by (rule sf_c_sum_plus_c_fst)
  from A1 S1 have S2: "sf x + c_fst x = x" by simp
  have S3: "x \<le> sf x" by (rule arg_le_sf)
  from S2 S3 show ?thesis by simp
qed

lemma c_fst_eq_arg: "c_fst x = x \<Longrightarrow> x = 0"
proof -
  assume A1: "c_fst x = x"
  have S1: "c_fst x \<le> c_sum x" by (rule c_fst_le_c_sum)
  have S2: "c_sum x \<le> x" by (rule c_sum_le_arg)
  from A1 S1 S2 have "c_sum x = x" by simp
  then have "c_fst x = 0" by (rule c_sum_eq_arg_2)
  with A1 show ?thesis by simp
qed

lemma c_fst_less_arg: "x > 0 \<Longrightarrow> c_fst x < x"
proof -
  assume A1: "x > 0"
  show ?thesis
  proof cases
    assume "c_fst x < x"
    then show ?thesis by simp
  next
    assume "\<not> c_fst x < x"
    then have S1: "c_fst x \<ge> x" by simp
    have "c_fst x \<le> x" by (rule c_fst_le_arg)
    with S1 have "c_fst x = x" by simp
    then have "x = 0" by (rule c_fst_eq_arg)
    with A1 show ?thesis by simp
  qed
qed

lemma c_snd_eq_arg: "c_snd x = x \<Longrightarrow> x \<le> 1"
proof -
  assume A1: "c_snd x = x"
  have S1: "c_snd x \<le> c_sum x" by (rule c_snd_le_c_sum)
  have S2: "c_sum x \<le> x" by (rule c_sum_le_arg)
  from A1 S1 S2 have "c_sum x = x" by simp  
  then show ?thesis by (rule c_sum_eq_arg)
qed

lemma c_snd_less_arg: "x > 1 \<Longrightarrow> c_snd x < x"
proof -
  assume A1: "x > 1"
  show ?thesis
  proof cases
    assume "c_snd x < x"
    then show ?thesis .
  next
    assume "\<not> c_snd x < x"
    then have S1: "c_snd x \<ge> x" by auto
    have "c_snd x \<le> x" by (rule c_snd_le_arg)
    with S1 have "c_snd x = x" by simp
    then have "x \<le> 1" by (rule c_snd_eq_arg)
    with A1 show ?thesis by simp
  qed
qed

end
