theory Uniform_Sampling imports 
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
begin 

definition sample_uniform_units :: "nat \<Rightarrow> nat spmf"
  where "sample_uniform_units q = spmf_of_set ({..< q} - {0})"

lemma set_spmf_sample_uniform_units [simp]:
  "set_spmf (sample_uniform_units q) = {..< q} - {0}" 
  by(simp add: sample_uniform_units_def)

lemma lossless_sample_uniform_units:
  assumes "(p::nat) > 1" 
  shows "lossless_spmf (sample_uniform_units p)" 
  unfolding sample_uniform_units_def
  using assms by auto

lemma weight_sample_uniform_units:
  assumes "(p::nat) > 1" 
  shows "weight_spmf (sample_uniform_units p) = 1"
  using assms lossless_sample_uniform_units 
  by (simp add: lossless_weight_spmfD)

(*General lemma for mapping using sample_uniform*)

lemma one_time_pad': 
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

(*(y + b)*)

lemma plus_inj_eq: 
  assumes x: "x < q"
    and x': "x' < q" 
    and map: "((y :: nat) + x) mod q = (y + x') mod q"  
shows "x = x'"
proof-
  have "((y :: nat) + x) mod q = (y + x') mod q \<Longrightarrow> x mod q = x' mod q"
  proof-
    have "((y:: nat) + x) mod q = (y + x') mod q \<Longrightarrow> [((y:: nat) + x) = (y + x')] (mod q)"
      by(simp add: cong_def)
    moreover have "[((y:: nat) + x) = (y + x')] (mod q) \<Longrightarrow> [x = x'] (mod q)"
      by (simp add: cong_add_lcancel_nat)
    moreover have "[x = x'] (mod q) \<Longrightarrow> x mod q = x' mod q"
      by(simp add: cong_def)
    ultimately show ?thesis by(simp add: map)
  qed
  moreover have "x mod q = x' mod q \<Longrightarrow> x = x'"
    by(simp add: x x')
  ultimately show ?thesis by(simp add: map) 
qed

lemma inj_uni_samp_plus: "inj_on  (\<lambda>(b :: nat). (y + b) mod q ) {..<q}" 
  by(simp add: inj_on_def)(auto simp only: plus_inj_eq)

lemma surj_uni_samp_plus: 
  assumes inj: "inj_on  (\<lambda>(b :: nat). (y + b) mod q ) {..<q}" 
  shows "(\<lambda>(b :: nat). (y + b) mod q) ` {..< q} =  {..< q}" 
  apply(rule endo_inj_surj) using inj by auto

lemma samp_uni_plus_one_time_pad: 
shows "map_spmf (\<lambda>b. (y + b) mod q) (sample_uniform q) = sample_uniform q"
  using inj_uni_samp_plus surj_uni_samp_plus one_time_pad by simp

(*x*b*) 

lemma mult_inj_eq: 
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
    moreover have "[x*y = x*y'] (mod q) = [y = y'] (mod q)"
      by(simp add: cong_mult_lcancel_nat coprime)
    moreover have "[y = y'] (mod q) \<Longrightarrow> y mod q = y' mod q"
      by(simp add: cong_def)
    ultimately show ?thesis by(simp add: map)
  qed
  moreover have "y mod q = y' mod q \<Longrightarrow> y = y'"
    by(simp add: y y')
  ultimately show ?thesis by(simp add: map) 
qed

lemma inj_on_mult: 
  assumes coprime: "coprime x (q::nat)" 
  shows "inj_on (\<lambda> b. x*b mod q) {..<q}"
  apply(auto simp add: inj_on_def)
  using coprime by(simp only: mult_inj_eq)

lemma surj_on_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and inj: "inj_on (\<lambda> b. x*b mod q) {..<q}"
  shows "(\<lambda> b. x*b mod q) ` {..< q} = {..< q}"
  apply(rule endo_inj_surj) using coprime inj by auto

lemma mult_one_time_pad: 
  assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. x*b mod q) (sample_uniform q) = sample_uniform q"
  using inj_on_mult surj_on_mult one_time_pad coprime by simp


lemma inj_on_mult':
  assumes coprime: "coprime x (q::nat)" 
  shows "inj_on (\<lambda> b. x*b mod q) ({..<q} - {0})"
  apply(auto simp add: inj_on_def)
  using coprime by(simp only: mult_inj_eq)

lemma surj_on_mult': 
  assumes coprime: "coprime x (q::nat)" 
    and inj: "inj_on (\<lambda> b. x*b mod q) ({..<q} - {0})"
  shows "(\<lambda> b. x*b mod q) ` ({..<q} - {0}) = ({..<q} - {0})"
proof(rule endo_inj_surj) 
  show " finite ({..<q} - {0})" by auto
  show "(\<lambda>b. x * b mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}"  
  proof-
    obtain nn :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> nat" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> x1 v3 \<notin> x0) = (nn x0 x1 x2 \<in> x2 \<and> x1 (nn x0 x1 x2) \<notin> x0)"
        by moura
    hence 1: "\<forall>N f Na. nn Na f N \<in> N \<and> f (nn Na f N) \<notin> Na \<or> f ` N \<subseteq> Na"
      by (meson image_subsetI)
    have 2: "x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<notin> {..<q} \<or> x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q}"
      by force
    have 3: "(x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q} - {0}) = (x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0})"
      by simp 
    { assume "x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q = x * 0 mod q" 
      hence "(0 \<le> q) = (0 = q) \<or> (nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} \<or> nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<in> {0}) \<or> nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} - {0} \<or> x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0}"
        by (metis antisym_conv1 insertCI lessThan_iff local.coprime mult_inj_eq) } 
    moreover
    { assume "0 \<noteq> x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q"
      moreover 
      { assume "x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> insert 0 {..<q} \<and> x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<notin> {0}"
        hence "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}"
          using 3 1 by (meson Diff_iff) } 
      ultimately have "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0} \<or> (0 \<le> q) = (0 = q)"
        using 2 by (metis antisym_conv1 lessThan_iff mod_less_divisor singletonD) } 
    ultimately have "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0} \<or> nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) \<notin> {..<q} - {0} \<or> x * nn ({..<q} - {0}) (\<lambda>n. x * n mod q) ({..<q} - {0}) mod q \<in> {..<q} - {0}"
      by force 
    thus "(\<lambda>n. x * n mod q) ` ({..<q} - {0}) \<subseteq> {..<q} - {0}"
      using 1 by meson 
  qed
  show "inj_on (\<lambda>b. x * b mod q) ({..<q} - {0})" 
    using inj by blast
qed

lemma mult_one_time_pad':
  assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. x*b mod q) (sample_uniform_units q) = sample_uniform_units q"
  using inj_on_mult' surj_on_mult' one_time_pad' coprime by simp

(*y + x*b*)

lemma samp_uni_add_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and x': "x' < q" 
    and y': "y' < q" 
    and map: "(y + x * x') mod q = (y + x * y') mod q" 
  shows "x' = y'"
proof-
  have "(y + x * x') mod q = (y + x * y') mod q \<Longrightarrow> x' mod q = y' mod q"
  proof-
  have "(y + x * x') mod q = (y + x * y') mod q \<Longrightarrow> [y + x*x' = y + x *y'] (mod q)"
    using cong_def by blast
  moreover have "[y + x*x' = y + x *y'] (mod q) \<Longrightarrow> [x' = y'] (mod q)"
    by(simp add: cong_add_lcancel_nat)(simp add: coprime cong_mult_lcancel_nat)
  ultimately show ?thesis by(simp add: cong_def map)
  qed
  moreover have "x' mod q = y' mod q \<Longrightarrow> x' = y'"
    by(simp add: x' y')
  ultimately show ?thesis by(simp add: map)
qed

lemma inj_on_add_mult: 
  assumes coprime: "coprime x (q::nat)" 
  shows "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}"
  apply(auto simp add: inj_on_def)
  using coprime by(simp only: samp_uni_add_mult)

lemma surj_on_add_mult: 
  assumes coprime: "coprime x (q::nat)" 
    and inj: "inj_on (\<lambda> b. (y + x*b) mod q) {..<q}" 
  shows "(\<lambda> b. (y + x*b) mod q) ` {..< q} = {..< q}" 
  apply(rule endo_inj_surj) using coprime inj by auto

lemma add_mult_one_time_pad: 
  assumes coprime: "coprime x q" 
  shows "map_spmf (\<lambda> b. (y + x*b) mod q) (sample_uniform q) = (sample_uniform q)"
  using inj_on_add_mult surj_on_add_mult one_time_pad coprime by simp

(*(y - b) *)

lemma inj_on_minus: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}"
proof(unfold inj_on_def; auto)
  fix x :: nat and y' :: nat
  assume x: "x < q"
  assume y': "y' < q"
  assume map: "(y + q - x) mod q = (y + q - y') mod q"
  have "\<forall>n na p. \<exists>nb. \<forall>nc nd pa. (\<not> (nc::nat) < nd \<or> \<not> pa (nc - nd) \<or> pa 0) \<and> (\<not> p (0::nat) \<or> p (n - na) \<or> na + nb = n)"
    by (metis (no_types) nat_diff_split)
  hence "\<not> y < y' - q \<and> \<not> y < x - q"
    using y' x by (metis add.commute less_diff_conv not_add_less2)
  hence "\<exists>n. (y' + n) mod q = (n + x) mod q"
    using map by (metis add.commute add_diff_inverse_nat less_diff_conv mod_add_left_eq)
  thus "x = y'" 
    by (metis plus_inj_eq  x y' add.commute)
qed

lemma surj_on_minus: 
  assumes inj: "inj_on  (\<lambda>(b :: nat). (y + (q - b)) mod q ) {..<q}" 
  shows "(\<lambda>(b :: nat). (y + (q - b)) mod q) ` {..< q} = {..< q}"
  apply(rule endo_inj_surj) using inj by auto

lemma samp_uni_minus_one_time_pad: 
  shows "map_spmf(\<lambda> b. (y + (q - b)) mod q) (sample_uniform q) = sample_uniform q"
  using inj_on_minus surj_on_minus one_time_pad by simp

lemma not_coin_spmf: "map_spmf (\<lambda> a. \<not> a) coin_spmf = coin_spmf" 
proof-
  have "inj_on Not {True, False}" 
    by simp
  moreover have  "Not ` {True, False} = {True, False}" 
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

lemma ped_inv_mapping:
  assumes "(a::nat) < q"
    and "[m \<noteq> 0] (mod q)"
  shows "map_spmf (\<lambda> d. (d + a * (m::nat)) mod q) (sample_uniform q) = map_spmf (\<lambda> d. (d + q * m - a * m) mod q) (sample_uniform q)"
(is "?lhs = ?rhs")
proof-
  have ineq: "q * m - a * m > 0" 
    using assms gr0I by force
  have "?lhs = map_spmf (\<lambda> d. (a * m + d) mod q) (sample_uniform q)" 
    using add.commute by metis
  also have "... = sample_uniform q"
    using samp_uni_plus_one_time_pad by simp
  also have "... = map_spmf (\<lambda> d. ((q * m - a * m) + d) mod q) (sample_uniform q)"
    using ineq samp_uni_plus_one_time_pad by metis
  ultimately show ?thesis 
    using add.commute ineq  
    by (simp add: Groups.add_ac(2))
qed

end
