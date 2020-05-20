subsection \<open>Noar Pinkas OT\<close>

text\<open>Here we prove security for the Noar Pinkas OT from \cite{DBLP:conf/soda/NaorP01}.\<close>

theory Noar_Pinkas_OT imports
  Cyclic_Group_Ext 
  Game_Based_Crypto.Diffie_Hellman
  OT_Functionalities 
  Semi_Honest_Def
  Uniform_Sampling 
begin

locale np_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes finite_group: "finite (carrier \<G>)"
    and or_gt_0: "0 < order \<G>"
    and prime_order: "prime (order \<G>)"
begin

lemma prime_field: "a < (order \<G>) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a (order \<G>)"
  by(metis dvd_imp_le neq0_conv not_le prime_imp_coprime prime_order coprime_commute)

lemma weight_sample_uniform_units: "weight_spmf (sample_uniform_units (order \<G>)) = 1"
  using  lossless_spmf_def lossless_sample_uniform_units prime_order  prime_gt_1_nat by auto

definition protocol :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> (unit \<times> 'grp) spmf"
  where "protocol M v = do {
    let (m0,m1) = M;
    a :: nat \<leftarrow> sample_uniform (order \<G>);
    b :: nat \<leftarrow> sample_uniform (order \<G>);
    let c\<^sub>v = (a*b) mod (order \<G>);
    c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
    r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
    let z0' = ((\<^bold>g [^] (if v then c\<^sub>v' else c\<^sub>v)) [^] s0) \<otimes> ((\<^bold>g [^] b) [^] r0);
    r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
    let z1' = ((\<^bold>g [^] ((if v then c\<^sub>v else c\<^sub>v'))) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
    let enc_m0 = z0' \<otimes> m0;
    let enc_m1 = z1' \<otimes> m1;
    let out_2 = (if v then enc_m1 \<otimes> inv (w1 [^] b) else enc_m0 \<otimes> inv (w0 [^] b));
    return_spmf ((), out_2)}"

lemma lossless_protocol: "lossless_spmf (protocol M \<sigma>)"
  apply(auto simp add: protocol_def Let_def split_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

type_synonym 'grp' view1 = "(('grp' \<times> 'grp') \<times> ('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp')) spmf"

type_synonym 'grp' dist_adversary = "(('grp' \<times> 'grp') \<times> 'grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> bool spmf"

definition R1 :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'grp view1"
  where "R1 msgs \<sigma> = do {
    let (m0, m1) = msgs;
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);
    let c\<^sub>\<sigma> = a*b;
    c\<^sub>\<sigma>' \<leftarrow> sample_uniform (order \<G>);
    return_spmf (msgs, (\<^bold>g [^] a, \<^bold>g [^] b, (if \<sigma> then \<^bold>g [^] c\<^sub>\<sigma>' else \<^bold>g [^] c\<^sub>\<sigma>), (if \<sigma> then \<^bold>g [^] c\<^sub>\<sigma> else \<^bold>g [^] c\<^sub>\<sigma>')))}"  

lemma lossless_R1: "lossless_spmf (R1 M \<sigma>)"
  by(simp add: R1_def Let_def lossless_sample_uniform_units or_gt_0)

definition inter :: "('grp \<times> 'grp) \<Rightarrow> 'grp view1"
  where "inter msgs = do {
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);  
    c \<leftarrow> sample_uniform (order \<G>);
    d \<leftarrow> sample_uniform (order \<G>);
    return_spmf (msgs, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c, \<^bold>g [^] d)}"

definition S1 :: "('grp \<times> 'grp) \<Rightarrow> unit \<Rightarrow> 'grp view1"
  where "S1 msgs out1 = do {
    let (m0, m1) = msgs;
    a \<leftarrow> sample_uniform (order \<G>);
    b \<leftarrow> sample_uniform (order \<G>);
    c \<leftarrow> sample_uniform (order \<G>);
    return_spmf (msgs, (\<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c, \<^bold>g [^] (a*b)))}"  

lemma lossless_S1: "lossless_spmf (S1 M out1)"
  by(simp add: S1_def Let_def lossless_sample_uniform_units or_gt_0)

fun R1_inter_adversary :: "'grp dist_adversary \<Rightarrow> ('grp \<times> 'grp) \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where "R1_inter_adversary \<A> msgs \<alpha> \<beta> \<gamma> = do {
    c \<leftarrow> sample_uniform (order \<G>);
    \<A> (msgs, \<alpha>, \<beta>, \<gamma>, \<^bold>g [^] c)}"

fun inter_S1_adversary :: "'grp dist_adversary \<Rightarrow> ('grp \<times> 'grp) \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> 'grp \<Rightarrow> bool spmf"
  where "inter_S1_adversary \<A> msgs \<alpha> \<beta> \<gamma> = do {
    c \<leftarrow> sample_uniform (order \<G>);
    \<A> (msgs, \<alpha>, \<beta>, \<^bold>g [^] c, \<gamma>)}"

sublocale ddh: ddh \<G> .

definition R2 :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> (bool \<times> 'grp \<times> 'grp \<times>  'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
  where "R2 M v  = do {
  let (m0,m1) = M;
  a :: nat \<leftarrow> sample_uniform (order \<G>);
  b :: nat \<leftarrow> sample_uniform (order \<G>);
  let c\<^sub>v = (a*b) mod (order \<G>);
  c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
  r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
  let z = ((\<^bold>g [^] c\<^sub>v') [^] s0) \<otimes> ((\<^bold>g [^] b) [^] r0);
  r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
  let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
  let enc_m = z \<otimes> (if v then m0 else m1);
  let enc_m' = z' \<otimes> (if v then m1 else m0) ;
  return_spmf(v, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 

lemma lossless_R2: "lossless_spmf (R2 M \<sigma>)"
  apply(simp add: R2_def Let_def split_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

definition S2 :: "bool \<Rightarrow> 'grp \<Rightarrow> (bool \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) spmf" 
  where "S2 v m =  do {
  a :: nat \<leftarrow> sample_uniform (order \<G>);
  b :: nat \<leftarrow> sample_uniform (order \<G>);
  let c\<^sub>v = (a*b) mod (order \<G>);
  r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
  r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
  let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
  let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
  s' \<leftarrow> sample_uniform (order \<G>);
  let enc_m =  \<^bold>g [^] s';
  let enc_m' = z' \<otimes> m ;
  return_spmf(v, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"

lemma lossless_S2: "lossless_spmf (S2 \<sigma> out2)"
  apply(simp add: S2_def Let_def lossless_sample_uniform_units or_gt_0)
  using prime_order prime_gt_1_nat lossless_sample_uniform_units by simp

sublocale sim_def: sim_det_def R1 S1 R2 S2 funct_OT_12 protocol
  unfolding sim_det_def_def 
  by(auto simp add: lossless_R1 lossless_S1 lossless_R2 lossless_S2 lossless_protocol lossless_funct_OT_12)

end

locale np = np_base + cyclic_group \<G>
begin

lemma protocol_inverse: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>" 
  shows" ((\<^bold>g [^] ((a*b) mod (order \<G>))) [^] (s1 :: nat)) \<otimes> ((\<^bold>g [^] b) [^] (r1::nat)) \<otimes> (if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b) 
        = (if v then m0 else m1)"
(is "?lhs = ?rhs")
proof-
  have  1: "(a*b)*(s1) + b*r1 =((a::nat)*(s1) + r1)*b " using mult.commute mult.assoc  add_mult_distrib by auto
  have "?lhs = 
 ((\<^bold>g [^] (a*b)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1) \<otimes> (if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b)"
    by(simp add: pow_generator_mod)
  also have "... = (\<^bold>g [^] ((a*b)*(s1))) \<otimes> ((\<^bold>g [^] (b*r1))) \<otimes> ((if v then m0 else m1) \<otimes> inv (((\<^bold>g [^] ((a*(s1) + r1)*b)))))"
    by(auto simp add: nat_pow_pow nat_pow_mult assms cyclic_group_assoc)
  also have "... = \<^bold>g [^] ((a*b)*(s1)) \<otimes> \<^bold>g [^] (b*r1) \<otimes> ((inv (((\<^bold>g [^] ((a*(s1) + r1)*b))))) \<otimes> (if v then m0 else m1))"
    by(simp add: nat_pow_mult cyclic_group_commute assms)
  also have "... = (\<^bold>g [^] ((a*b)*(s1) + b*r1) \<otimes> inv (((\<^bold>g [^] ((a*(s1) + r1)*b))))) \<otimes> (if v then m0 else m1)"
    by(simp add: nat_pow_mult cyclic_group_assoc assms)
  also have "... = (\<^bold>g [^] ((a*b)*(s1) + b*r1) \<otimes> inv (((\<^bold>g [^] (((a*b)*(s1) + r1*b)))))) \<otimes> (if v then m0 else m1)"
    using 1 by (simp add: mult.commute)
  ultimately show ?thesis
    using l_cancel_inv assms  by (simp add: mult.commute)
qed

lemma correctness: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>" 
  shows "sim_def.correctness (m0,m1) \<sigma>"
proof-
  have "protocol (m0, m1) \<sigma> = funct_OT_12 (m0, m1) \<sigma>"
  proof-
    have "protocol (m0, m1) \<sigma> = do {
    a :: nat \<leftarrow> sample_uniform (order \<G>);
    b :: nat \<leftarrow> sample_uniform (order \<G>);
    r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
    let out_2 = ((\<^bold>g [^] ((a*b) mod (order \<G>))) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1) \<otimes> (if \<sigma> then m1 else m0) \<otimes> inv (((\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1) [^] b);
    return_spmf ((), out_2)}"
      by(simp add: protocol_def lossless_sample_uniform_units bind_spmf_const weight_sample_uniform_units or_gt_0)
    also have "... = do {   
    let out_2 = (if \<sigma> then m1 else m0);
    return_spmf ((), out_2)}"
      by(simp add: protocol_inverse assms lossless_sample_uniform_units bind_spmf_const weight_sample_uniform_units or_gt_0)
    ultimately show ?thesis by(simp add: Let_def funct_OT_12_def)
  qed
  thus ?thesis 
    by(simp add: sim_def.correctness_def)
qed

lemma security_P1: 
  shows "sim_def.adv_P1 msgs \<sigma> D \<le> ddh.advantage (R1_inter_adversary D msgs) + ddh.advantage (inter_S1_adversary D msgs)"
    (is "?lhs \<le> ?rhs")
proof(cases \<sigma>)
  case True
  have "R1 msgs \<sigma> = S1 msgs out1" for out1
    by(simp add: R1_def S1_def True)
  then have "sim_def.adv_P1 msgs \<sigma> D = 0"
    by(simp add: sim_def.adv_P1_def funct_OT_12_def) 
  also have "ddh.advantage A \<ge> 0" for A using ddh.advantage_def by simp 
  ultimately show ?thesis by simp 
next
  case False
  have bounded_advantage: "\<bar>(a :: real) - b\<bar> = e1 \<Longrightarrow> \<bar>b - c\<bar> = e2 \<Longrightarrow> \<bar>a - c\<bar> \<le> e1 + e2" 
    for a b e1 c e2 by simp
  also have R1_inter_dist: "\<bar>spmf (R1 msgs False \<bind> D) True - spmf ((inter msgs) \<bind> D) True\<bar> = ddh.advantage (R1_inter_adversary D msgs)"
    unfolding R1_def inter_def ddh.advantage_def ddh.ddh_0_def ddh.ddh_1_def Let_def split_def by(simp)
  also  have inter_S1_dist: "\<bar>spmf ((inter msgs) \<bind> D) True - spmf (S1 msgs out1 \<bind> D) True\<bar> = ddh.advantage (inter_S1_adversary D msgs)" 
    for out1 including monad_normalisation
    by(simp add: S1_def inter_def ddh.advantage_def ddh.ddh_0_def ddh.ddh_1_def) 
  ultimately have "\<bar>spmf (R1 msgs False \<bind> (\<lambda>view. D view)) True - spmf (S1 msgs out1 \<bind> (\<lambda>view. D view)) True\<bar> \<le> ?rhs"
    for out1 using R1_inter_dist by auto
  thus ?thesis by(simp add: sim_def.adv_P1_def funct_OT_12_def False) 
qed

lemma add_mult_one_time_pad: 
  assumes "s0 < order \<G>" 
    and "s0 \<noteq> 0"
  shows "map_spmf (\<lambda> c\<^sub>v'. (((b* r0) + (s0 * c\<^sub>v')) mod(order \<G>))) (sample_uniform (order \<G>)) = sample_uniform (order \<G>)"
proof-
  have "gcd s0 (order \<G>) = 1" 
    using assms prime_field by simp
  thus ?thesis 
    using add_mult_one_time_pad by force
qed

lemma security_P2: 
  assumes "m0 \<in> carrier \<G>" "m1 \<in> carrier \<G>"
  shows "sim_def.perfect_sec_P2 (m0,m1) \<sigma>"
proof-
  have "R2 (m0, m1) \<sigma> = S2 \<sigma> (if \<sigma> then m1 else m0)"
    including monad_normalisation
  proof-
    have "R2 (m0, m1) \<sigma> = do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      c\<^sub>v' :: nat \<leftarrow> sample_uniform (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      let s' = (((b* r0) + ((c\<^sub>v')*(s0))) mod(order \<G>));
      let z = \<^bold>g [^] s' ;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<sigma>, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 
      by(simp add: R2_def nat_pow_pow nat_pow_mult pow_generator_mod add.commute) 
    also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      s' \<leftarrow> map_spmf (\<lambda> c\<^sub>v'. (((b* r0) + ((c\<^sub>v')*(s0))) mod(order \<G>))) (sample_uniform (order \<G>));
      let z = \<^bold>g [^] s';
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<sigma>, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}" 
      by(simp add: bind_map_spmf o_def Let_def)
    also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      s' \<leftarrow>  (sample_uniform (order \<G>));
      let z = \<^bold>g [^] s';
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      let enc_m = z \<otimes> (if \<sigma> then m0 else m1); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<sigma>, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"  
      by(simp add: add_mult_one_time_pad Let_def mult.commute cong: bind_spmf_cong_simp)
    also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      enc_m \<leftarrow> map_spmf (\<lambda> s'.  \<^bold>g [^] s' \<otimes> (if \<sigma> then m0 else m1)) (sample_uniform (order \<G>)); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<sigma>, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"
      by(simp add: bind_map_spmf o_def Let_def)
    also have "... =  do {
      a :: nat \<leftarrow> sample_uniform (order \<G>);
      b :: nat \<leftarrow> sample_uniform (order \<G>);
      let c\<^sub>v = (a*b) mod (order \<G>);
      r0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s0 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w0 = (\<^bold>g [^] a) [^] s0 \<otimes> \<^bold>g [^] r0;
      r1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      s1 :: nat \<leftarrow> sample_uniform_units (order \<G>);
      let w1 = (\<^bold>g [^] a) [^] s1 \<otimes> \<^bold>g [^] r1;
      let z' = ((\<^bold>g [^] (c\<^sub>v)) [^] s1) \<otimes> ((\<^bold>g [^] b) [^] r1);
      enc_m \<leftarrow> map_spmf (\<lambda> s'.  \<^bold>g [^] s') (sample_uniform (order \<G>)); 
      let enc_m' = z' \<otimes> (if \<sigma> then m1 else m0) ;
      return_spmf(\<sigma>, \<^bold>g [^] a, \<^bold>g [^] b, \<^bold>g [^] c\<^sub>v, w0, enc_m, w1, enc_m')}"
      by(simp add: sample_uniform_one_time_pad assms)
    ultimately show ?thesis by(simp add: S2_def Let_def bind_map_spmf o_def)
  qed
  thus ?thesis 
    by(simp add: sim_def.perfect_sec_P2_def funct_OT_12_def)
qed

end 

locale np_asymp = 
  fixes \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  assumes np: "\<And>\<eta>. np (\<G> \<eta>)"
begin
  
sublocale np "\<G> \<eta>" for \<eta> by(simp add: np)

theorem correctness_asymp: 
  assumes "m0 \<in> carrier (\<G> \<eta>)" "m1 \<in> carrier (\<G> \<eta>)"
  shows "sim_def.correctness \<eta> (m0, m1) \<sigma>"
  by(simp add: correctness assms) 

theorem security_P1_asymp: 
  assumes "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (inter_S1_adversary \<eta> D msgs))"
    and "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (R1_inter_adversary \<eta>  D msgs))"
  shows "negligible (\<lambda> \<eta>. sim_def.adv_P1 \<eta> msgs \<sigma> D)"
proof-
  have "sim_def.adv_P1 \<eta> msgs \<sigma> D \<le> ddh.advantage \<eta> (R1_inter_adversary \<eta>  D msgs) + ddh.advantage \<eta> (inter_S1_adversary \<eta> D msgs)" 
    for \<eta>
    using security_P1 by simp
  moreover have "negligible (\<lambda> \<eta>. ddh.advantage \<eta> (R1_inter_adversary \<eta>  D msgs) + ddh.advantage \<eta> (inter_S1_adversary \<eta> D msgs))"
    using assms 
    by (simp add: negligible_plus)
  ultimately show ?thesis 
    using negligible_le sim_def.adv_P1_def by auto
qed

theorem security_P2_asymp: 
  assumes "m0 \<in> carrier (\<G> \<eta>)" "m1 \<in> carrier (\<G> \<eta>)"
  shows "sim_def.perfect_sec_P2 \<eta> (m0,m1) \<sigma>"
  by(simp add: security_P2 assms)

end

end