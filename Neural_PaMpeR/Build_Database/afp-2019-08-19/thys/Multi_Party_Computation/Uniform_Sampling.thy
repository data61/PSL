section \<open>Uniform Sampling\<close>

text\<open>Here we prove different one time pad lemmas based on uniform sampling we require throughout our proofs.\<close>

theory Uniform_Sampling
  imports 
    CryptHOL.Cyclic_Group_SPMF 
    "HOL-Number_Theory.Cong"
    CryptHOL.List_Bits
begin 

text \<open>If q is a prime we can sample from the units.\<close>

definition sample_uniform_units :: "nat \<Rightarrow> nat spmf"
  where "sample_uniform_units q = spmf_of_set ({..< q} - {0})"

lemma set_spmf_sampl_uni_units [simp]: "set_spmf (sample_uniform_units q) = {..< q} - {0}" 
  by(simp add: sample_uniform_units_def)

lemma lossless_sample_uniform_units: 
  assumes "q > 1"
  shows "lossless_spmf (sample_uniform_units q)"
  apply(simp add: sample_uniform_units_def) 
  using assms by auto

text \<open>General lemma for mapping using uniform sampling from units.\<close>

lemma one_time_pad_units: 
  assumes inj_on: "inj_on f ({..<q} - {0})" 
    and sur: "f ` ({..<q} - {0}) = ({..<q} - {0})"  
  shows "map_spmf f (sample_uniform_units q) = (sample_uniform_units q)"
    (is "?lhs = ?rhs")
proof-
  have rhs: "?rhs = spmf_of_set (({..<q} - {0}))" 
    by(auto simp add: sample_uniform_units_def)
  also have "map_spmf(\<lambda>s. f s) (spmf_of_set ({..<q} - {0})) = spmf_of_set ((\<lambda>s. f s) ` ({..<q} - {0}))"
    by(simp add: inj_on)
  also have "f ` ({..<q} - {0}) = ({..<q} - {0})"
    apply(rule endo_inj_surj) by(simp, simp add: sur, simp add: inj_on)
  ultimately show ?thesis using rhs by simp
qed

text \<open>General lemma for mapping using uniform sampling.\<close>

lemma one_time_pad: 
  assumes inj_on: "inj_on f {..<q}" 
    and sur: "f ` {..<q} = {..<q}"  
  shows "map_spmf f (sample_uniform q) = (sample_uniform q)"
    (is "?lhs = ?rhs")
proof-
  have rhs: "?rhs = spmf_of_set ({..< q})" 
    by(auto simp add: sample_uniform_def)
  also have "map_spmf(\<lambda>s. f s) (spmf_of_set {..<q}) = spmf_of_set ((\<lambda>s. f s) ` {..<q})"
    by(simp add: inj_on)
  also have "f ` {..<q} = {..<q}"
    apply(rule endo_inj_surj) by(simp, simp add: sur, simp add: inj_on)
  ultimately show ?thesis using rhs by simp
qed

text \<open>The addition map case.\<close>

lemma inj_add: 
  assumes x:  "x < q" 
    and x': "x' < q" 
    and map: "((y :: nat) + x) mod q = (y + x') mod q"  
  shows "x = x'"
proof-
  have aa: "((y :: nat) + x) mod q = (y + x') mod q \<Longrightarrow> x mod q = x' mod q"
  proof-
    have 4: "((y:: nat) + x) mod q = (y + x') mod q \<Longrightarrow> [((y:: nat) + x) = (y + x')] (mod q)"
      by(simp add: cong_def)
    have 5: "[((y:: nat) + x) = (y + x')] (mod q) \<Longrightarrow> [x = x'] (mod q)"
      by (simp add: cong_add_lcancel_nat)
    have 6: "[x = x'] (mod q) \<Longrightarrow> x mod q = x' mod q"
      by(simp add: cong_def)
    then show ?thesis by(simp add: map 4 5 6)
  qed
  also have bb: "x mod q = x' mod q \<Longrightarrow> x = x'"
    by(simp add: x x')
  ultimately show ?thesis by(simp add: map) 
qed

lemma inj_uni_samp_add: "inj_on (\<lambda>(b :: nat). (y + b) mod q ) {..<q}"
  by(simp add: inj_on_def)(auto simp only: inj_add)

lemma surj_uni_samp: 
  assumes inj: "inj_on  (\<lambda>(b :: nat). (y + b) mod q ) {..<q}" 
  shows "(\<lambda>(b :: nat). (y + b) mod q) ` {..< q} =  {..< q}" 
  apply(rule endo_inj_surj) using inj by auto

lemma samp_uni_plus_one_time_pad: 
  shows "map_spmf (\<lambda>b. (y + b) mod q) (sample_uniform q) = (sample_uniform q)"
  using inj_uni_samp_add surj_uni_samp one_time_pad by simp

text \<open>The multiplicaton map case.\<close>

lemma inj_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and y: "y < q" 
    and y': "y' < q" 
  and map: "x * y mod q = x * y' mod q" 
shows "y = y'"
proof-
  have "x*y mod q = x*y' mod q \<Longrightarrow> y mod q = y' mod q"
  proof-
    have "x*y mod q = x*y' mod q \<Longrightarrow> [x*y = x*y'] (mod q)"
      by(simp add: cong_def)
    also have "[x*y = x*y'] (mod q) = [y = y'] (mod q)"
      by(simp add: cong_mult_lcancel_nat coprime)
    also have "[y = y'] (mod q) \<Longrightarrow> y mod q = y' mod q"
      by(simp add: cong_def)
    ultimately show ?thesis by(simp add: map)
  qed
  also have "y mod q = y' mod q \<Longrightarrow> y = y'"
    by(simp add: y y')
  ultimately show ?thesis by(simp add: map) 
qed

lemma inj_on_mult: 
  assumes coprime: "coprime x (q::nat)" 
  shows "inj_on (\<lambda> b. x*b mod q) {..<q}"
  apply(auto simp add: inj_on_def)
  using coprime by(simp only: inj_mult)

lemma surj_on_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and inj: "inj_on (\<lambda> b. x*b mod q) {..<q}"
  shows "(\<lambda> b. x*b mod q) ` {..< q} = {..< q}"
  apply(rule endo_inj_surj) using coprime inj by auto

lemma mult_one_time_pad: 
  assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. x*b mod q) (sample_uniform q) = (sample_uniform q)"
  using inj_on_mult surj_on_mult one_time_pad coprime by simp

text \<open>The multiplication map for sampling from units.\<close>

lemma inj_on_mult_units: 
  assumes 1: "coprime x (q::nat)" shows "inj_on (\<lambda> b. x*b mod q) ({..<q} - {0})"
  apply(auto simp add: inj_on_def)
  using 1 by(simp only: inj_mult)

lemma surj_on_mult_units: 
  assumes coprime: "coprime x (q::nat)" 
    and inj: "inj_on (\<lambda> b. x*b mod q) ({..<q} - {0})"
  shows "(\<lambda> b. x*b mod q) ` ({..<q} - {0}) = ({..<q} - {0})"
proof(rule endo_inj_surj)
  show "finite ({..<q} - {0})" using coprime inj by(simp)
  show "(\<lambda>b. x * b mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}" 
  proof -
    obtain n :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> nat" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> x1 v3 \<notin> x0) = (n x0 x1 x2 \<in> x2 \<and> x1 (n x0 x1 x2) \<notin> x0)"
      by moura
    then have subset: "\<forall>N f Na. n Na f N \<in> N \<and> f (n Na f N) \<notin> Na \<or> f ` N \<subseteq> Na"
      by (meson image_subsetI)
    have mem_insert: "x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<notin> {..<q} \<or> x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q}"
      by force
    have map_eq: "(x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q} - {0}) = (x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0})"
      by simp
    { assume "x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q = x * 0 mod q"
      then have "(0 \<le> q) = (0 = q) \<or> (n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} \<or> n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<in> {0}) \<or> n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} - {0} \<or> x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0}"
        by (metis antisym_conv1 insertCI lessThan_iff local.coprime inj_mult) }
    moreover
    { assume "0 \<noteq> x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q"
      moreover
      { assume "x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q} \<and> x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<notin> {0}"
        then have "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}"
          using map_eq subset by (meson Diff_iff) }
      ultimately have "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0} \<or> (0 \<le> q) = (0 = q)"
        using mem_insert by (metis antisym_conv1 lessThan_iff mod_less_divisor singletonD) }
    ultimately have "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0} \<or> n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} - {0} \<or> x * n ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0}"
      by force
    then show "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}"
      using subset by meson
  qed
  show "inj_on (\<lambda>b. x * b mod q) ({..<q} - {0})" using assms by(simp) 
qed

lemma mult_one_time_pad_units: 
  assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. x*b mod q) (sample_uniform_units q) = sample_uniform_units q"
  using inj_on_mult_units surj_on_mult_units one_time_pad_units coprime by simp

text \<open>Addition and multiplication map.\<close>

lemma samp_uni_add_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and xa: "xa < q" 
    and ya: "ya < q" 
    and map: "(y + x * xa) mod q = (y + x * ya) mod q" 
  shows "xa = ya"
proof-
  have "(y + x * xa) mod q = (y + x * ya) mod q \<Longrightarrow> xa mod q = ya mod q"
  proof-
    have "(y + x * xa) mod q = (y + x * ya) mod q \<Longrightarrow> [y + x*xa = y + x *ya] (mod q)"
      using cong_def by blast
    also have "[y + x*xa = y + x *ya] (mod q) \<Longrightarrow> [xa = ya] (mod q)"
      by(simp add: cong_add_lcancel_nat)(simp add: coprime cong_mult_lcancel_nat)
    ultimately show ?thesis by(simp add: cong_def map)
  qed
  also have "xa mod q = ya mod q \<Longrightarrow> xa = ya"
    by(simp add: xa ya)
  ultimately show ?thesis by(simp add: map)
qed

lemma inj_on_add_mult: 
  assumes coprime: "coprime x (q::nat)" 
  shows "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}"
  apply(auto simp add: inj_on_def)
  using coprime by(simp only: samp_uni_add_mult)

lemma surj_on_add_mult: assumes coprime: "coprime x (q::nat)" and inj: "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}" 
  shows "(\<lambda> b. (y + x*b) mod q) ` {..< q} = {..< q}" 
  apply(rule endo_inj_surj) using coprime inj by auto

lemma add_mult_one_time_pad: assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. (y + x*b) mod q) (sample_uniform q) = (sample_uniform q)"
  using inj_on_add_mult surj_on_add_mult one_time_pad coprime by simp

text \<open>Subtraction Map.\<close>

lemma inj_minus: 
  assumes x: "(x :: nat) < q" 
    and ya: "ya < q" 
    and map: "(y + q - x) mod q = (y + q - ya) mod q" 
  shows  "x = ya"
proof-
  have "(y + q - x) mod q = (y + q - ya) mod q \<Longrightarrow> x mod q = ya mod q"
  proof-
    have "(y + q - x) mod q = (y + q - ya) mod q \<Longrightarrow> [y + q - x = y + q - ya] (mod q)"
      using cong_def by blast
    moreover have "[y + q - x = y + q - ya] (mod q) \<Longrightarrow> [q - x = q - ya] (mod q)"
      using x ya cong_add_lcancel_nat by fastforce
    moreover have "[y + q - x = y + q - ya] (mod q) \<Longrightarrow> [q + x = q + ya] (mod q)" 
      by (metis add_diff_inverse_nat calculation(2) cong_add_lcancel_nat cong_add_rcancel_nat cong_sym less_imp_le_nat not_le x ya)
    ultimately show ?thesis 
      by (simp add: cong_def map)
  qed
  moreover have "x mod q = ya mod q \<Longrightarrow> x = ya"
    by(simp add: x ya)
  ultimately show ?thesis by(simp add: map)
qed

lemma inj_on_minus: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}"
  by(auto simp add: inj_on_def inj_minus) 

lemma surj_on_minus: 
  assumes inj: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}" 
  shows "(\<lambda>(b :: nat). (y + (q - b)) mod q) ` {..< q} = {..< q}"
  apply(rule endo_inj_surj) 
  using inj by auto

lemma samp_uni_minus_one_time_pad: 
  shows "map_spmf(\<lambda> b. (y + (q - b)) mod q) (sample_uniform q) = (sample_uniform q)"
  using inj_on_minus surj_on_minus one_time_pad by simp

lemma not_coin_flip: "map_spmf (\<lambda> a. \<not> a) coin_spmf = coin_spmf" 
proof-
  have "inj_on Not {True, False}" 
    by simp
  also have  "Not ` {True, False} = {True, False}" 
    by auto 
  ultimately show ?thesis using one_time_pad 
    by (simp add: UNIV_bool)
qed

lemma xor_uni_samp: "map_spmf(\<lambda> b. y \<oplus> b) (coin_spmf) = map_spmf(\<lambda> b. b) (coin_spmf)"
  (is "?lhs = ?rhs")
proof-
  have rhs: "?rhs = spmf_of_set {True, False}"
    by (simp add: UNIV_bool insert_commute)
  also have "map_spmf(\<lambda> b. y \<oplus> b) (spmf_of_set {True, False}) = spmf_of_set((\<lambda> b. y \<oplus> b) ` {True, False})"
    by (simp add: xor_def)
  also have "(\<lambda> b. xor y b) ` {True, False} = {True, False}"
    using xor_def by auto
  finally show ?thesis using rhs by(simp)
qed

end