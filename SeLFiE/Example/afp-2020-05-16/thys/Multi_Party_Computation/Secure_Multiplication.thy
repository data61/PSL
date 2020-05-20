subsection \<open>Secure multiplication protocol\<close>

theory Secure_Multiplication imports
  CryptHOL.Cyclic_Group_SPMF   
  Uniform_Sampling 
  Semi_Honest_Def
begin

locale secure_mult =
  fixes q :: nat
  assumes q_gt_0: "q > 0"
    and "prime q"
begin

type_synonym real_view = "nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat \<times> nat \<times> nat) \<times> nat \<times> nat) spmf"
type_synonym sim = "nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat \<times> nat \<times> nat) \<times> nat \<times> nat) spmf"

lemma samp_uni_set_spmf [simp]: "set_spmf (sample_uniform q) = {..< q}" 
  by(simp add: sample_uniform_def)

definition funct :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) spmf"
  where "funct x y = do {
    s \<leftarrow> sample_uniform q;
    return_spmf (s, (x*y + (q - s)) mod q)}"

definition TI :: "((nat \<times> nat) \<times> (nat \<times> nat)) spmf"
  where "TI = do {
    a \<leftarrow> sample_uniform q;  
    b \<leftarrow> sample_uniform q;
    r \<leftarrow> sample_uniform q;
    return_spmf ((a, r), (b, ((a*b + (q - r)) mod q)))}"

definition out :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) spmf"
  where "out x y = do {
    ((c1,d1),(c2,d2)) \<leftarrow> TI;
    let e2 = (x + c1) mod q;
    let e1 = (y + (q - c2)) mod q;
    return_spmf (((x*e1 + (q - d1)) mod q), ((e2 * c2 + (q - d2)) mod q))}"

definition R1 :: "real_view"
  where "R1 x y = do {
    ((c1, d1), (c2, d2)) \<leftarrow> TI;
    let e2 = (x + c1) mod q;
    let e1 = (y + (q - c2)) mod q;
    let s1 = (x*e1 + (q - d1)) mod q;
    let s2 = (e2 * c2 + (q - d2)) mod q;
    return_spmf ((x, c1, d1, e1), s1, s2)}"

definition S1 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) spmf" 
  where "S1 x s1 = do {
    a :: nat \<leftarrow> sample_uniform q;  
    e1 \<leftarrow> sample_uniform q;
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf (x, a, d1, e1)}"

definition Out1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) spmf"
  where "Out1 x y s1 = do {
    let s2 = (x*y + (q - s1)) mod q;
    return_spmf (s1,s2)}"

definition R2 :: "real_view"
  where "R2 x y = do {
    ((c1, d1), (c2, d2)) \<leftarrow> TI;
    let e2 = (x + c1) mod q;
    let e1 = (y + (q - c2)) mod q;
    let s1 = (x*e1 + (q - d1)) mod q;
    let s2 = (e2 * c2 + (q - d2)) mod q;
    return_spmf ((y, c2, d2, e2), s1, s2)}"

definition S2 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat) spmf"
  where "S2 y s2 = do { 
    b \<leftarrow> sample_uniform q;
    e2 \<leftarrow> sample_uniform q;
    let d2 = (e2*b + (q - s2)) mod q;
    return_spmf (y, b, d2, e2)}"

definition Out2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) spmf"
  where "Out2 y x s2 = do {
    let s1 = (x*y + (q - s2)) mod q;
    return_spmf (s1,s2)}"

definition Ideal2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat \<times> nat \<times> nat) \<times> (nat \<times> nat)) spmf"
  where "Ideal2 y x out2 = do {
    view2 :: (nat \<times> nat \<times> nat \<times> nat) \<leftarrow> S2 y out2;
    out2 \<leftarrow> Out2 y x out2;
    return_spmf (view2, out2)}"

sublocale sim_non_det_def: sim_non_det_def R1 S1 Out1 R2 S2 Out2 funct .

lemma minus_mod:
  assumes "a > b"
  shows "[a - b mod q = a - b] (mod q)"
  by(metis cong_diff_nat  cong_def le_trans less_or_eq_imp_le assms mod_less_eq_dividend mod_mod_trivial)

lemma q_cong:"[a = q + a] (mod q)" 
  by (simp add: cong_def)

lemma q_cong_reverse: "[q + a = a] (mod q)" 
  by (simp add: cong_def)

lemma qq_cong: "[a = q*q + a] (mod q)" 
  by (simp add: cong_def)

lemma minus_q_mult_cancel: 
  assumes "[a = e + b - q * c - d] (mod q)" 
    and "e + b - d > 0" 
    and "e + b - q * c - d > 0"
  shows  "[a = e + b  - d] (mod q)" 
proof-
  have "a mod q = (e + b - q * c - d) mod q"
    using assms(1) cong_def by blast
  then have "a mod q = (e + b - d) mod q"
    by (metis (no_types) add_cancel_left_left assms(3) diff_commute diff_is_0_eq' linordered_semidom_class.add_diff_inverse mod_add_left_eq mod_mult_self1_is_0 nat_less_le)
  then show ?thesis
    using cong_def by blast
qed

lemma s1_s2:
  assumes "x < q" "a < q" "b < q" and r:"r < q" "y < q"
  shows "((x + a) mod q * b + q - (a * b + q - r) mod q) mod q =
          (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q"
proof-
  have s: "(x * y + (q - (x * ((y + (q - b)) mod q) + (q - r)) mod q)) mod q 
                 = ((x + a) mod q * b + (q - (a * b + (q - r)) mod q)) mod q"
  proof-
    have lhs: "(x * y + (q - (x * ((y + (q - b)) mod q) + (q - r)) mod q)) mod q = (x*b + r) mod q"
    proof-
      let ?h = "(x * y + (q - (x * ((y + (q - b)) mod q) + (q - r)) mod q)) mod q"
      have "[?h = x * y + q - (x * ((y + (q - b)) mod q) + (q - r)) mod q] (mod q)" 
        by(simp add: assms(1) cong_def q_gt_0)
      then have "[?h = x * y + q - (x * (y + (q - b)) + (q - r)) mod q] (mod q)" 
        by (metis mod_add_left_eq mod_mult_right_eq)
      then have no_qq: "[?h = x * y + q - (x * y + x * (q - b) + (q - r)) mod q] (mod q)" 
        by(metis distrib_left)
      then have "[?h = q*q + x * y + q - (x * y + x * (q - b) + (q - r)) mod q] (mod q)"  
      proof-
        have "[x * y + q - (x * y + x * (q - b) + (q - r)) mod q = q*q + x * y + q - (x * y + x * (q - b) + (q - r)) mod q] (mod q)"
          by (smt qq_cong  add.assoc cong_diff_nat cong_def le_add2 le_trans mod_le_divisor q_gt_0)
        then show ?thesis using cong_trans no_qq by blast
      qed
      then have mod: "[?h = q + q*q + x * y + q - (x * y + x * (q - b) + (q - r)) mod q] (mod q)"  
        by (smt Nat.add_diff_assoc cong_def add.assoc add.commute le_add2 le_trans mod_add_self2 mod_le_divisor q_gt_0)
      then have "[?h = q + q*q + x * y + q - (x * y + x * (q - b) + (q - r))] (mod q)"
      proof-
        have 1: "q \<ge> q - b" using assms by simp 
        then have  "q*q \<ge> x*(q-b)" "q \<ge> q - r" using 1  assms   
           apply (auto simp add: mult_strict_mono)  
          by (simp add: mult_le_mono)
        then have "q + q*q + x * y + q  > x * y + x * (q - b) + (q - r)" 
          using assms(5) by linarith
        then have "[q + q*q + x * y + q - (x * y + x * (q - b) + (q - r)) mod q = q + q*q + x * y + q - (x * y + x * (q - b) + (q - r))] (mod q)"
          using minus_mod by blast
        then show ?thesis using mod using cong_trans by blast  
      qed
      then have "[?h = q + q*q + x * y + q - (x * y + (x * q - x*b) + (q - r))] (mod q)"  
        by (simp add: right_diff_distrib')
      then have "[?h = q + q*q + x * y + q - x * y - (x * q - x*b) - (q - r)] (mod q)" 
        by simp
      then have mod': "[?h = q + q*q + q - (x * q - x*b) - (q - r)] (mod q)" 
        by(simp add: add.commute)
      then have neg: "[?h = q + q*q + q - x * q +  x*b - (q - r)] (mod q)" 
      proof-
        have "[q + q*q + q - (x * q - x*b) - (q - r) = q + q*q + q - x * q + x*b - (q - r)] (mod q)"
        proof(cases "x = 0")
          case True
          then show ?thesis by simp
        next
          case False
          have "x * q - x*b > 0" using False assms by simp
          also have "q + q*q + q - x * q > 0"  
            by (metis assms(1) add.commute diff_mult_distrib2 less_Suc_eq mult.commute mult_Suc_right nat_0_less_mult_iff q_gt_0 zero_less_diff)
          ultimately show ?thesis by simp
        qed
        then show ?thesis using mod' cong_trans by blast  
      qed
      then have "[?h = q + q*q + q +  x*b - (q - r)] (mod q)" 
      proof-
        have "[q + q*q + q - x * q +  x*b - (q - r) = q + q*q + q +  x*b - (q - r)] (mod q)"
        proof(cases "x = 0")
          case True
          then show ?thesis by simp
        next
          case False
          have "q*q > x*q" 
            using False assms 
            by (simp add: mult_strict_mono) 
          then have 1: "q + q*q + q - x * q +  x*b - (q - r) > 0" 
            by linarith
          then have 2: "q + q*q + q +  x*b - (q - r) > 0" by simp
          then show ?thesis 
            by (smt 1 2 Nat.add_diff_assoc2 \<open>x * q < q * q\<close> add_cancel_left_left add_diff_inverse_nat 
                le_add1 le_add2 le_trans less_imp_add_positive less_numeral_extra(3) minus_mod 
                minus_q_mult_cancel mod_if mult.commute q_gt_0)
        qed
        then show ?thesis using cong_trans neg by blast
      qed
      then have "[?h = q + q*q + q +  x*b - q + r] (mod q)" 
        by (metis r(1) Nat.add_diff_assoc2 Nat.diff_diff_right le_add2 less_imp_le_nat semiring_normalization_rules(23))   
      then have "[?h = q + q*q + q +  x*b + r] (mod q)" 
        apply(simp add: cong_def)  
        by (metis (no_types, lifting) add.assoc add.commute add_diff_cancel_right' diff_is_0_eq' mod_if mod_le_divisor q_gt_0)
      then have "[?h = x*b + r] (mod q)" 
        apply(simp add: cong_def) 
        by (metis mod_add_cong mod_add_self1 mod_mult_self1) 
      then show ?thesis by (simp add: cong_def assms)
    qed
    also have rhs: "((x + a) mod q * b + (q - (a * b + (q - r)) mod q)) mod q = (x*b + r) mod q"
    proof-
      let ?h = "((x + a) mod q * b + (q - (a * b + (q - r)) mod q)) mod q"
      have "[?h =  (x + a) mod q * b + q - (a * b + (q - r)) mod q] (mod q)" 
        by (simp add: q_gt_0  assms(1) cong_def)
      then have "[?h = (x + a) * b + q - (a * b + (q - r)) mod q] (mod q)" 
        by (smt Nat.add_diff_assoc cong_def mod_add_cong mod_le_divisor mod_mult_left_eq q_gt_0 assms)
      then have "[?h = x*b + a*b + q - (a * b + (q - r)) mod q] (mod q)" 
        by(metis distrib_right) 
      then have mod: "[?h = q + x*b + a*b + q - (a * b + (q - r)) mod q] (mod q)" 
        by (smt Nat.add_diff_assoc cong_def add.assoc add.commute le_add2 le_trans mod_add_self2 mod_le_divisor q_gt_0)
      then have "[?h =  q + x*b + a*b + q - (a * b + (q - r))] (mod q)" using  q_cong assms(1) 
      proof-
        have ge: "q + x*b + a*b + q  > (a * b + (q - r))" using assms by simp
        then have "[ q + x*b + a*b + q - (a * b + (q - r)) mod q =  q + x*b + a*b + q - (a * b + (q - r))] (mod q)"
          using Divides.mod_less_eq_dividend cong_diff_nat  cong_def le_trans less_not_refl2
                  less_or_eq_imp_le q_gt_0 minus_mod by presburger
        then show ?thesis using mod cong_trans by blast  
      qed
      then have "[?h =  q + x*b + q - (q - r)] (mod q)" 
        by (simp add: add.commute)
      then have "[?h =  q + x*b + q - q + r] (mod q)" 
        by (metis Nat.add_diff_assoc2 Nat.diff_diff_right r(1) le_add2 less_imp_le_nat)
      then have "[?h = q + x*b + r] (mod q)" by simp
      then have "[?h = q + (x*b + r)] (mod q)" 
        using add.assoc by metis
      then have "[?h = x*b + r] (mod q)" 
        using cong_def q_cong_reverse by metis 
      then show ?thesis by (simp add: cong_def assms(1))
    qed
    ultimately show ?thesis by simp
  qed
  have lhs:"((x + a) mod q * b + q - (a * b + q - r) mod q) mod q = ((x + a) mod q * b + (q - (a * b + (q - r)) mod q)) mod q"
    using assms by simp
  have rhs: "(x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q = (x * y + (q - (x * ((y + (q - b)) mod q) + (q - r)) mod q)) mod q " 
    using assms by simp
  have " ((x + a) mod q * b + (q - (a * b + (q - r)) mod q)) mod q = (x * y + (q - (x * ((y + (q - b)) mod q) + (q - r)) mod q)) mod q"
    using assms s[symmetric] by blast
  then show ?thesis using lhs rhs 
    by metis
qed

lemma s1_s2_P2:
  assumes "x < q" "xa < q" "xb < q" "xc < q" "y < q"
  shows "((y, xa, (xb * xa + q - xc) mod q, (x + xb) mod q), (x * ((y + q - xa) mod q) + q - xc) mod q, ((x + xb) mod q * xa + q - (xb * xa + q - xc) mod q) mod q) =
         ((y, xa, (xb * xa + q - xc) mod q, (x + xb) mod q), (x * ((y + q - xa) mod q) + q - xc) mod q, (x * y + q - (x * ((y + q - xa) mod q) + q - xc) mod q) mod q)"
  using assms s1_s2 by metis

lemma c1: 
  assumes "e2 = (x + c1) mod q" 
    and  "x < q" "c1 < q"
  shows "c1 = (e2 + q - x) mod q"
proof-
  have "[e2 + q = x + c1] (mod q)" by(simp add: assms cong_def)
  then have "[e2 + q - x  =  c1] (mod q)" 
  proof-
    have "e2 + q \<ge> x" using assms by simp
    then show ?thesis 
      by (metis \<open>[e2 + q = x + c1] (mod q)\<close> cong_add_lcancel_nat le_add_diff_inverse)
  qed
  then show ?thesis by(simp add: cong_def assms)
qed

lemma c1_P2:
  assumes "xb < q" "xa < q" "xc < q" "x < q" 
  shows "((y, xa, (xb * xa + q - xc) mod q, (x + xb) mod q), (x * ((y + q - xa) mod q) + q - xc) mod q, (x * y + q - (x * ((y + q - xa) mod q) + q - xc) mod q) mod q) = 
          ((y, xa, (((x + xb) mod q + q - x) mod q * xa + q - xc) mod q, (x + xb) mod q), (x * ((y + q - xa) mod q) + q - xc) mod q, (x * y + q - (x * ((y + q - xa) mod q) + q - xc) mod q) mod q)"
proof-
  have "(xb * xa + q - xc) mod q = (((x + xb) mod q + q - x) mod q * xa + q - xc) mod q"
    using assms c1 by simp
  then show ?thesis
    using assms by metis
qed

lemma minus_mod_cancel:
  assumes "a - b > 0" "a - b mod q > 0" 
  shows "[a - b + c = a - b mod q + c] (mod q)" 
proof-
  have "(b - b mod q + (a - b)) mod q = (0 + (a - b)) mod q"
    using  cong_def mod_add_cong neq0_conv q_gt_0 
    by (simp add: minus_mod_eq_mult_div)
  then show ?thesis
    by (metis (no_types) Divides.mod_less_eq_dividend Nat.add_diff_assoc2 add_diff_inverse_nat assms(1) cong_def diff_is_0_eq' less_or_eq_imp_le mod_add_cong neq0_conv)
qed

lemma d2: 
  assumes d2: "d2 = (((e2 + q - x) mod q)*b + (q - r)) mod q"
    and s1: "s1 = (x*((y + (q - b)) mod q) + (q - r)) mod q" 
    and s2: "s2 = (x*y + (q - s1)) mod q"
    and x: "x < q"
    and y: "y < q" 
    and r: "r < q" 
    and b: "b < q" 
    and e2: "e2 < q"
  shows "d2  = (e2*b + (q - s2)) mod q" 
proof-
  have s1_le_q: "s1 < q" 
    using s1 q_gt_0 by simp
  have s2_le_q: "s2 < q" 
    using s2 q_gt_0 by simp
  have xb: "(x*b) mod q = (s2  + (q - r)) mod q"
  proof-
    have "s1 = (x*(y + (q - b)) + (q - r)) mod q" using s1 b 
      by (metis mod_add_left_eq mod_mult_right_eq)
    then have s1_dist: "s1 = (x*y + x*(q - b) + (q - r)) mod q" 
      by(metis distrib_left)
    then have "s1 = (x*y + x*q - x*b + (q - r)) mod q" 
      using distrib_left b diff_mult_distrib2 by auto
    then have "[s1 = x*y + x*q - x*b + (q - r)] (mod q)" 
      by(simp add: cong_def)
    then have "[s1 + x * b = x*y + x*q - x*b + x*b + (q - r)] (mod q)" 
      by (metis add.commute add.left_commute cong_add_lcancel_nat)
    then have "[s1 + x*b = x*y + x*q + (q - r)] (mod q)" 
      using b by (simp add: algebra_simps)
        (metis add_diff_inverse_nat diff_diff_left diff_mult_distrib2 less_imp_add_positive mult.commute not_add_less1 zero_less_diff)
    then have s1_xb: "[s1 + x*b = q + x*y + x*q + (q - r)] (mod q)" 
      by (smt mod_add_cong mod_add_self1 cong_def)
    then have "[x*b = q + x*y + x*q + (q - r) - s1] (mod q)"
    proof-
      have "q + x*y + x*q + (q - r) - s1 > 0" using s1_le_q by simp
      then show ?thesis 
        by (metis add_diff_inverse_nat less_numeral_extra(3) s1_xb cong_add_lcancel_nat nat_diff_split)
    qed
    then have "[x*b = x*y + x*q + (q - r) + q - s1] (mod q)" 
      by (metis add.assoc add.commute)
    then have "[x*b = x*y + (q - r) + q - s1] (mod q)" 
      by (smt Nat.add_diff_assoc cong_def less_imp_le_nat mod_mult_self1 s1_le_q semiring_normalization_rules(23))
    then have "(x*b) mod q = (x*y  + (q - r) + q - s1) mod q" 
      by(simp add: cong_def) 
    then have "(x*b) mod q = (x*y  + (q - r) + (q - s1)) mod q" 
      using add.assoc s1_le_q by auto
    then have "(x*b) mod q = (x*y  + (q - s1) + (q - r)) mod q" 
      using add.commute by presburger
    then show ?thesis using s2 by presburger
  qed 
  have "d2 = (((e2 + q - x) mod q)*b + (q - r)) mod q" 
    using d2 by simp
  then have "d2 = (((e2 + q - x))*b + (q - r)) mod q" 
    using mod_add_cong mod_mult_left_eq by blast
  then have "d2 = (e2*b + q*b - x*b + (q - r)) mod q"  
    by (simp add: distrib_right diff_mult_distrib)
  then have a: "[d2 = e2*b + q*b - x*b + (q - r)] (mod q)" 
    by(simp add: cong_def)
  then have b:"[d2 = q + q + e2*b + q*b - x*b + (q - r)] (mod q)" 
  proof-
    have "[e2*b + q*b - x*b + (q - r) = q + q + e2*b + q*b - x*b + (q - r)] (mod q)"
      by (smt assms Nat.add_diff_assoc add.commute cong_def less_imp_le_nat mod_add_self2 
          mult.commute nat_mult_le_cancel_disj semiring_normalization_rules(23))
    then show ?thesis using cong_trans a by blast
  qed
  then have "[d2 = q + q + e2*b + q*b - (x*b) mod q + (q - r)] (mod q)" 
  proof-
    have "[q + q + e2*b + q*b - (x*b)  + (q - r) = q + q + e2*b + q*b - (x*b) mod q + (q - r)] (mod q)"
    proof(cases "b = 0")
      case True
      then show ?thesis by simp
    next
      case False
      have "q*b - (x*b) > 0"
        using False x by simp
      then have 1: "q + q + e2*b + q*b - (x*b) > 0" by linarith
      then have 2:"q + q + e2*b + q*b - (x*b) mod q > 0" 
        by (simp add: q_gt_0 trans_less_add1)
      then show ?thesis using 1 2 minus_mod_cancel by simp
    qed
    then show ?thesis using cong_trans b by blast
  qed
  then have c: "[d2 = q + q + e2*b + q*b - (s2  + (q - r)) mod q + (q - r)] (mod q)" 
    using xb by simp
  then have "[d2 = q + q + e2*b + q*b - (s2  + (q - r)) + (q - r)] (mod q)"
  proof-
    have "[q + q + e2*b + q*b - (s2  + (q - r)) mod q + (q - r) = q + q + e2*b + q*b - (s2  + (q - r)) + (q - r)] (mod q)"
    proof-
      have "q + q + e2*b + q*b - (s2  + (q - r)) mod q > 0"  
        by (metis diff_is_0_eq gr0I le_less_trans mod_less_divisor not_add_less1 q_gt_0 semiring_normalization_rules(23) trans_less_add2)
      moreover have"q + q + e2*b + q*b - (s2  + (q - r)) > 0" 
        using s2_le_q by simp
      ultimately show ?thesis 
        using minus_mod_cancel cong_sym by blast
    qed
    then show ?thesis using cong_trans c by blast
  qed
  then have d: "[d2 = q + q + e2*b + q*b - s2 - (q - r) + (q - r)] (mod q)" by simp
  then have "[d2 = q + q + e2*b + q*b - s2 ] (mod q)" 
  proof-
    have "q + q + e2*b + q*b - s2 - (q - r) > 0" 
      using s2_le_q by simp
    then show ?thesis using d cong_trans by simp
  qed
  then have "[d2 = q + q + e2*b - s2] (mod q)" 
    by (smt Nat.add_diff_assoc2 cong_def less_imp_le_nat mod_mult_self1 mult.commute s2_le_q semiring_normalization_rules(23) trans_less_add2)
  then have "[d2 = q + e2*b + q - s2] (mod q)" 
    by(simp add: add.commute add.assoc) 
  then have "[d2 = e2*b + q - s2] (mod q)" 
    by (smt Nat.add_diff_assoc2 add.commute cong_def less_imp_le_nat mod_add_self2 s2_le_q trans_less_add2)
  then have "[d2 = e2*b + (q - s2)] (mod q)"
    by (simp add: less_imp_le_nat s2_le_q) 
  then show ?thesis by(simp add: cong_def d2)
qed

lemma d2_P2:
  assumes x: "x < q" and y: "y < q" and r: "b < q" and b: "e2 < q" and e2: "r < q"
  shows "((y, b, ((e2 + q - x) mod q * b + q - r) mod q, e2), (x * ((y + q - b) mod q) + q - r) mod q, (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q) =
                ((y, b, (e2 * b + q - (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q) mod q, e2), (x * ((y + q - b) mod q) + q - r) mod q, 
                      (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q)"
proof-
  have "((e2 + q - x) mod q * b + q - r) mod q = (e2 * b + q - (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q) mod q"
    (is "?lhs = ?rhs")
  proof-
    have d2: "(((e2 + q - x) mod q)*b + (q - r)) mod q  = (e2*b + (q - ((x*y + (q - ((x*((y + (q - b)) mod q) + (q - r)) mod q))) mod q))) mod q" 
      using assms d2 by blast
    have "?lhs = (((e2 + q - x) mod q)*b + (q - r)) mod q" 
      using assms by simp
    also have "?rhs = (e2*b + (q - ((x*y + (q - ((x*((y + (q - b)) mod q) + (q - r)) mod q))) mod q))) mod q" 
      using assms by simp
    ultimately show ?thesis using assms d2 by metis
  qed 
  then show ?thesis using assms by metis
qed

lemma s1: 
  assumes s2: "s2 = (x*y + q - s1) mod q" 
    and x: "x < q" 
    and y: "y < q" 
    and s1: "s1 < q"
  shows "s1 = (x*y + q - s2) mod q"
proof-
  have s2_le_q:"s2 < q" using s2 q_gt_0 by simp
  have "[s2 = x*y + q - s1] (mod q)" by(simp add: cong_def s2)
  then have "[s2 = x*y + q - s1] (mod q)" using add.assoc 
    by (simp add: less_imp_le_nat s1)
  then have s1_s2: "[s2 + s1 = x*y + q] (mod q)" 
    by (metis (mono_tags, lifting) cong_def le_add2 le_add_diff_inverse2 le_trans mod_add_left_eq order.strict_implies_order s1)
  then have "[s1 = x*y + q - s2] (mod q)" 
  proof-
    have "x*y + q - s2 > 0" using s2_le_q by simp
    then show ?thesis 
      by (metis s1_s2 add_diff_cancel_left' cong_diff_nat cong_def le_add1 less_imp_le_nat zero_less_diff)
  qed
  then show ?thesis by(simp add: cong_def s1)
qed

lemma s1_P2: 
  assumes x: "x < q" 
    and y: "y < q" 
    and "b < q" 
    and "e2 < q" 
    and "r < q" 
    and "s1 < q"
  shows "((y, b, (e2 * b + q - (x * y + q - r) mod q) mod q, e2), r, (x * y + q - r) mod q) =
                ((y, b, (e2 * b + q - (x * y + q - r) mod q) mod q, e2), (x * y + q - (x * y + q - r) mod q) mod q, (x * y + q - r) mod q)"
proof-
  have "s1 = (x*y + q - ((x*y + q - s1) mod q)) mod q"
    using assms secure_mult.s1 secure_mult_axioms by blast
  then show ?thesis using assms s1 by blast 
qed

theorem P2_security:
  assumes "x < q" "y < q"
  shows "sim_non_det_def.perfect_sec_P2 x y"
  including monad_normalisation
proof-
  have "((funct x y) \<bind> (\<lambda> (s1',s2'). (sim_non_det_def.Ideal2 y x s2'))) = R2 x y"
  proof-
    have "R2 x y = do {
      a :: nat \<leftarrow> sample_uniform q;  
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      let c1 = a;
      let d1 = r;
      let c2 = b;
      let d2 = ((a*b + (q - r)) mod q);
      let e2 = (x + c1) mod q;
      let e1 = (y + (q - c2)) mod q;
      let s1 = (x*e1 + (q - r)) mod q;
      let s2 = (e2 * c2 + (q - d2)) mod q;
      return_spmf ((y, c2, d2, e2), s1, s2)}"
      by(simp add: R2_def TI_def Let_def)
    also have "... = do {
      a :: nat \<leftarrow> sample_uniform q;  
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      let c1 = a;
      let d1 = r;
      let c2 = b;
      let e2 = (x + c1) mod q;
      let d2 = ((((e2 + q - x) mod q)*b + (q - r)) mod q);
      let s1 = (x*((y + (q - c2)) mod q) + (q - r)) mod q;
      return_spmf ((y, c2, d2, e2), (s1, (x*y + (q - s1)) mod q))}"
      by(simp add: Let_def s1_s2_P2 assms c1_P2 cong: bind_spmf_cong_simp)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      let d1 = r;
      let c2 = b;
      e2 \<leftarrow> map_spmf (\<lambda> c1. (x + c1) mod q) (sample_uniform q);
      let d2 = ((((e2 + q - x) mod q)*b + (q - r)) mod q);
      let s1 = (x*((y + (q - c2)) mod q) + (q - r)) mod q;
      return_spmf ((y, c2, d2, e2), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: bind_map_spmf o_def Let_def)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      let d1 = r;
      let c2 = b;
      e2 \<leftarrow> sample_uniform q;
      let d2 = (((e2 + q - x) mod q)*b + (q - r)) mod q;
      let s1 = (x*((y + (q - c2)) mod q) + (q - r)) mod q;
      return_spmf ((y, c2, d2, e2), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: samp_uni_plus_one_time_pad)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      e2 \<leftarrow> sample_uniform q;
      let s1 = (x*((y + (q - b)) mod q) + (q - r)) mod q;
      let s2 = (x*y + (q - s1)) mod q;
      let d2 = (((e2 + q - x) mod q)*b + (q - r)) mod q;
      return_spmf ((y, b, d2, e2), s1, s2)}"
      by(simp)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      r :: nat \<leftarrow> sample_uniform q;
      e2 \<leftarrow> sample_uniform q;
      let s1 = (x*((y + (q - b)) mod q) + (q - r)) mod q;
      let s2 = (x*y + (q - s1)) mod q;
      let d2 = (e2*b + (q - s2)) mod q;
      return_spmf ((y, b, d2, e2), s1, s2)}"
      by(simp add: d2_P2 assms Let_def cong: bind_spmf_cong_simp)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      e2 \<leftarrow> sample_uniform q;
      s1 \<leftarrow> map_spmf (\<lambda> r. (x*((y + (q - b)) mod q) + (q - r)) mod q) (sample_uniform q);
      let s2 = (x*y + (q - s1)) mod q;
      let d2 = (e2*b + (q - s2)) mod q;
      return_spmf ((y, b, d2, e2), s1, s2)}"
      by(simp add: bind_map_spmf o_def Let_def)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      e2 \<leftarrow> sample_uniform q;
      s1 \<leftarrow> sample_uniform q;
      let s2 = (x*y + (q - s1)) mod q;
      let d2 = (e2*b + (q - s2)) mod q;
      return_spmf ((y, b, d2, e2), s1, s2)}"
      by(simp add: samp_uni_minus_one_time_pad)
    also have "... = do {
      b :: nat \<leftarrow> sample_uniform q;
      e2 \<leftarrow> sample_uniform q;
      s1 \<leftarrow> sample_uniform q;
      let s2 = (x*y + (q - s1)) mod q;
      let d2 = (e2*b + (q - s2)) mod q;
      return_spmf ((y, b, d2, e2), (x*y + (q - s2)) mod q, s2)}"
      by(simp add: s1_P2 assms Let_def cong: bind_spmf_cong_simp)
    ultimately show ?thesis by(simp add: funct_def Let_def sim_non_det_def.Ideal2_def Out2_def S2_def R2_def)
  qed
  then show ?thesis by(simp add: sim_non_det_def.perfect_sec_P2_def)
qed

lemma s1_s2_P1:  assumes "x < q" "xa < q" "xb < q" "xc < q" "y < q"
  shows "((x, xa, xb, (y + q - xc) mod q), (x * ((y + q - xc) mod q) + q - xb) mod q, ((x + xa) mod q * xc + q - (xa * xc + q - xb) mod q) mod q) = 
         ((x, xa, xb, (y + q - xc) mod q), (x * ((y + q - xc) mod q) + q - xb) mod q, (x * y + q - (x * ((y + q - xc) mod q) + q - xb) mod q) mod q)"
  using assms s1_s2 by metis

lemma mod_minus: assumes "a - b > 0" and "c - d > 0" 
  shows "(a - b + (c - d mod q)) mod q = (a - b + (c - d)) mod q"
  using assms
  by (metis cong_def minus_mod mod_add_right_eq zero_less_diff)

lemma r: 
  assumes e1: "e1 = (y + (q - b)) mod q" 
    and s1: "s1 = (x*((y + (q - b)) mod q) + (q - r)) mod q"
    and b: "b < q"
    and x: "x < q" 
    and y: "y < q" 
    and r: "r < q" 
  shows "r = (x*e1 + (q - s1)) mod q"
    (is "?lhs = ?rhs")
proof-
  have "s1 = (x*((y + (q - b))) + (q - r)) mod q" using s1 b 
    by (metis mod_add_left_eq mod_mult_right_eq)
  then have s1_dist: "s1 = (x*y + x*(q - b) + (q - r)) mod q" 
    by(metis distrib_left)
  then have "?rhs = (x*((y + (q - b)) mod q) + (q - (x*y + x*(q - b) + (q - r)) mod q)) mod q" 
    using e1  by simp
  then have "?rhs = (x*((y + (q - b))) + (q - (x*y + x*(q - b) + (q - r)) mod q)) mod q" 
    by (metis mod_add_left_eq mod_mult_right_eq)
  then have "?rhs = (x*y + x*(q - b) + (q - (x*y + x*(q - b) + (q - r)) mod q)) mod q" 
    by(metis distrib_left)
  then have a: "?rhs = (x*y + x*q - x*b + (q - (x*y + x*(q - b) + (q - r)) mod q)) mod q" 
    using distrib_left b diff_mult_distrib2 by auto
  then have b: "?rhs = (x*y + x*q - x*b + (q*q + q*q + q  - (x*y + x*(q - b) + (q - r)) mod q)) mod q" 
  proof -
    have "(x*y + x*q - x*b + (q - (x*y + x*(q - b) + (q - r)) mod q)) mod q = (x*y + x*q - x*b + (q*q + q*q + q - (x*y + x*(q - b) + (q - r)) mod q)) mod q"
    proof -
      have f1: "\<forall>n na nb nc nd. (n::nat) mod na \<noteq> nb mod na \<or> nc mod na \<noteq> nd mod na \<or> (n + nc) mod na = (nb + nd) mod na"
        by (meson mod_add_cong)
      then have "(q - (x * y + x*(q - b) + (q - r)) mod q) mod q = (q * q + q * q + q - (x * y + x*(q - b) + (q - r)) mod q) mod q"
        by (metis Nat.diff_add_assoc mod_le_divisor q_gt_0 mod_mult_self4)
      then show ?thesis
        using f1 by blast
    qed
    then show ?thesis using a by simp
  qed
  then have "?rhs = (x*y + x*q - x*b + (q*q + q*q + q  - (x*y + x*(q - b) + (q - r)))) mod q" 
  proof-
    have "(x*y + x*q - x*b + (q*q + q*q + q - (x*y + x*(q - b) + (q - r)) mod q)) mod q =
         (x*y + x*q - x*b + (q*q + q*q + q - (x*y + x*(q - b)+ (q - r)))) mod q" 
    proof(cases "x = 0")
      case True
      then show ?thesis  
        by (metis (no_types, lifting) assms(2) assms(4) True Nat.add_diff_assoc add.left_neutral 
            cong_def diff_le_self minus_mod mult_is_0 not_gr_zero zero_eq_add_iff_both_eq_0 zero_less_diff)
    next
      case False
      have qb: "q - b \<le> q" 
        using b by simp
      then have qb':"x*(q - b) < q*q" 
        using x by (metis mult_less_le_imp_less nat_0_less_mult_iff nat_less_le neq0_conv)   
      have a: "x*y + x*(q - b) > 0" 
        using False assms by simp
      have 1: "q*q > x*y" 
        using False by (simp add: mult_strict_mono q_gt_0 x y)
      have 2: "q*q > x*q" using False 
        by (simp add: mult_strict_mono q_gt_0 x y)
      have b: "(q*q + q*q + q - (x*y + x*(q - b) + (q - r))) > 0" 
        using 1 qb' by simp
      then show ?thesis using a b mod_minus[of "x*y + x*q" "x*b" "q*q + q*q + q" "x*y + x*(q - b) + (q - r)"]
        by (smt add.left_neutral cong_def gr0I minus_mod zero_less_diff)
    qed
    then show ?thesis using b by simp
  qed
  then have d: "?rhs = (x*y + x*q - x*b + (q*q + q*q + q - x*y - x*(q - b) - (q - r))) mod q" 
    by simp
  then have e: "?rhs = (x*y + x*q - x*b + q*q + q*q + q - x*y - x*(q - b) - (q - r)) mod q" 
  proof(cases "x = 0")
    case True
    then show ?thesis using True d by simp
  next
    case False
    have qb: "q - b \<le> q" using b by simp
    then have qb':"x*(q - b) < q*q"  
      using x by (metis mult_less_le_imp_less nat_0_less_mult_iff nat_less_le neq0_conv)   
    have a: "x*y + x*(q - b) > 0" using False assms by simp
    have 1: "q*q > x*y" using False 
      by (simp add: mult_strict_mono q_gt_0 x y)
    have 2: "q*q > x*q" using False 
      by (simp add: mult_strict_mono q_gt_0 x y)
    have b: "q*q + q*q + q  - x*y - x*(q - b) - (q - r) > 0" using 1 qb' by simp
    then show ?thesis using b d 
      by (smt Nat.add_diff_assoc add.assoc diff_diff_left less_imp_le_nat zero_less_diff)
  qed
  then have "?rhs = (x*q - x*b + q*q + q*q + q - x*(q - b) - (q - r)) mod q" 
  proof-
    have "(x*y + x*q - x*b + q*q + q*q + q - x*y - x*(q - b) - (q - r)) mod q = (x*q - x*b + q*q + q*q + q - x*(q - b) - (q - r)) mod q"
    proof -
      have 1: "q + n - b = q - b + n" for n 
        by (simp add: assms(3) less_imp_le)
      have 2: "(c::nat) * b + (c * a + n) = c * (b + a) + n" 
        for n a b c by (simp add: distrib_left)
      have "(c::nat) + (b + a) - (n + a) = c + b - n" for n a b c
        by auto
      then have "(q + (q * q + (q * q + x * (q + y - b))) - (q - r + x * (y + (q - b)))) mod q = (q + (q * q + (q * q + x * (q - b))) - (q - r + x * (q - b))) mod q"
        by (metis (no_types) add.commute 1 2)
      then show ?thesis
        by (simp add: add.commute diff_mult_distrib2 distrib_left)
    qed
    then show ?thesis using e by simp
  qed
  then have "?rhs = (x*(q - b) + q*q + q*q + q - x*(q - b) - (q - r)) mod q" 
    by(metis diff_mult_distrib2)
  then have "?rhs = (q*q + q*q + q - (q - r)) mod q" 
    using assms(6) by simp
  then have "?rhs = (q*q + q*q + q - q + r) mod q" 
    using assms(6) by(simp add: Nat.diff_add_assoc2 less_imp_le)
  then have "?rhs = (q*q + q*q  + r) mod q" 
    by simp
  then have "?rhs = r mod q" 
    by (metis add.commute distrib_right mod_mult_self1)
  then show ?thesis using assms(6) by simp
qed

lemma r_P2:
  assumes b: "b < q" and x: "x < q" and y: "y < q" and r: "r < q"
  shows 
    "((x, a, r, (y + q - b) mod q), (x * ((y + q - b) mod q) + q - r) mod q, (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q) =
              ((x, a, (x * ((y + q - b) mod q) + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q, (y + q - b) mod q), (x * ((y + q - b) mod q) + q - r) mod q,     
                      (x * y + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q)"
proof-
  have  "(x * ((y + q - b) mod q) + q - (x * ((y + q - b) mod q) + q - r) mod q) mod q = r" 
    (is "?lhs = ?rhs")
  proof-
    have 1:"r = (x*((y + (q - b)) mod q) + (q - ((x*((y + (q - b)) mod q) + (q - r)) mod q))) mod q"
      using assms secure_mult.r secure_mult_axioms by blast
    also have "?rhs = (x*((y + (q - b)) mod q) + (q - ((x*((y + (q - b)) mod q) + (q - r)) mod q))) mod q" using assms 1 by blast
    ultimately show ?thesis using assms 1 by simp
  qed
  then show ?thesis using assms by simp
qed

theorem P1_security:
  assumes "x < q" "y < q"
  shows "sim_non_det_def.perfect_sec_P1 x y"
  including monad_normalisation
proof-
  have "(funct x y) \<bind> (\<lambda> (s1',s2'). (sim_non_det_def.Ideal1 x y s1')) = R1 x y"
  proof-
    have "R1 x y = do {
    a :: nat \<leftarrow> sample_uniform q;  
    b :: nat \<leftarrow> sample_uniform q;
    r :: nat \<leftarrow> sample_uniform q;    
    let c1 = a;
    let d1 = r;
    let c2 = b;
    let d2 = ((a*b + (q - r)) mod q);
    let e2 = (x + c1) mod q;
    let e1 = (y + (q - c2)) mod q;
    let s1 = (x*e1 + (q - d1)) mod q;
    let s2 = (e2 * c2 + (q - d2)) mod q;
    return_spmf ((x, c1, d1, e1), s1, s2)}"
      by(simp add: R1_def TI_def Let_def)
    also have "... = do {
    a :: nat \<leftarrow> sample_uniform q;  
    b :: nat \<leftarrow> sample_uniform q;
    r :: nat \<leftarrow> sample_uniform q;    
    let c1 = a;
    let c2 = b;
    let e1 = (y + (q - b)) mod q;
    let s1 = (x*((y + (q - b)) mod q) + (q - r)) mod q;
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf ((x, c1, d1, e1), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: Let_def assms s1_s2_P1  r_P2 cong: bind_spmf_cong_simp)
    also have "... = do {
    a :: nat \<leftarrow> sample_uniform q;  
    b :: nat \<leftarrow> sample_uniform q;
    let c1 = a;
    let c2 = b;
    let e1 = (y + (q - b)) mod q;
    s1 \<leftarrow> map_spmf (\<lambda> r. (x*((y + (q - b)) mod q) + (q - r)) mod q) (sample_uniform q);
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf ((x, c1, d1, e1), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: bind_map_spmf Let_def o_def)
    also have "... = do {
    a :: nat \<leftarrow> sample_uniform q;  
    b :: nat \<leftarrow> sample_uniform q;
    let c1 = a;
    let c2 = b;
    let e1 = (y + (q - b)) mod q;
    s1 \<leftarrow> sample_uniform q;
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf ((x, c1, d1, e1), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: samp_uni_minus_one_time_pad)
    also have "... = do {
    a :: nat \<leftarrow> sample_uniform q;  
    let c1 = a;
    e1 \<leftarrow> map_spmf (\<lambda>b. (y + (q - b)) mod q) (sample_uniform q);
    s1 \<leftarrow> sample_uniform q;
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf ((x, c1, d1, e1), s1, (x*y + (q - s1)) mod q)}"
      by(simp add: bind_map_spmf Let_def o_def)
    also have "... = do {
    a :: nat \<leftarrow> sample_uniform q;  
    let c1 = a;
    e1 \<leftarrow> sample_uniform q;
    s1 \<leftarrow> sample_uniform q;
    let d1 = (x*e1 + (q - s1)) mod q;
    return_spmf ((x, c1, d1, e1), s1, (x*y + (q - s1)) mod q)}"      
      by(simp add: samp_uni_minus_one_time_pad)
    ultimately show ?thesis by(simp add: funct_def sim_non_det_def.Ideal1_def Let_def R1_def TI_def Out1_def S1_def)
  qed
  thus ?thesis by(simp add: sim_non_det_def.perfect_sec_P1_def)
qed

end

locale secure_mult_asymp = 
  fixes q :: "nat \<Rightarrow> nat"
  assumes "\<And> n. secure_mult (q n)"
begin

sublocale secure_mult "q n" for n 
  using secure_mult_asymp_axioms secure_mult_asymp_def by blast

theorem P1_secure:
  assumes "x < q n" "y < q n"
  shows "sim_non_det_def.perfect_sec_P1 n x y"
  by (metis P1_security assms)

theorem P2_secure:
  assumes "x < q n" "y < q n"
  shows "sim_non_det_def.perfect_sec_P2 n x y"
  by (metis P2_security assms)

end 

end