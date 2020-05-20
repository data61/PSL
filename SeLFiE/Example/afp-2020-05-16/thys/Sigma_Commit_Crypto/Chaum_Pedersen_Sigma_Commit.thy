subsection\<open>Chaum-Pedersen \<open>\<Sigma>\<close>-protocol\<close>

text\<open>The Chaum-Pedersen \<open>\<Sigma>\<close>-protocol \cite{DBLP:conf/crypto/ChaumP92} considers a relation of equality of discrete logs.\<close>

theory Chaum_Pedersen_Sigma_Commit imports
  Commitment_Schemes
  Sigma_Protocols
  Cyclic_Group_Ext
  Discrete_Log
  Number_Theory_Aux
  Uniform_Sampling 
begin 

locale chaum_ped_\<Sigma>_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
    and x :: nat
  assumes  prime_order: "prime (order \<G>)"
begin

definition "g' = \<^bold>g [^] x"

lemma or_gt_1: "order \<G> > 1" 
  using prime_order 
  using prime_gt_1_nat by blast

lemma or_gt_0 [simp]:"order \<G> > 0" 
  using or_gt_1 by simp

type_synonym witness = "nat"
type_synonym rand = nat 
type_synonym 'grp' msg = "'grp' \<times> 'grp'"
type_synonym response = nat
type_synonym challenge = nat
type_synonym 'grp' pub_in = "'grp' \<times> 'grp'"

definition "G = do {
    w \<leftarrow> sample_uniform (order \<G>);
    return_spmf ((\<^bold>g [^] w, g' [^] w), w)}"

lemma lossless_G: "lossless_spmf G"
  by(simp add: G_def)

definition "challenge_space = {..< order \<G>}" 

definition init :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> (rand \<times> 'grp msg) spmf"
  where "init h w = do {
    let (h, h') = h;  
    r \<leftarrow> sample_uniform (order \<G>);
    return_spmf (r, \<^bold>g [^] r, g' [^] r)}"

lemma lossless_init: "lossless_spmf (init h w)" 
  by(simp add:  init_def)

definition "response r w e = return_spmf ((w*e + r) mod (order \<G>))"

lemma lossless_response: "lossless_spmf (response r w  e)"
  by(simp add: response_def)

definition check :: "'grp pub_in \<Rightarrow> 'grp msg \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool"
  where "check h a e z =  (fst a \<otimes> (fst h [^] e) = \<^bold>g [^] z \<and> snd a \<otimes> (snd h [^] e) = g' [^] z \<and> fst a \<in> carrier \<G> \<and> snd a \<in> carrier \<G>)"

definition R :: "('grp pub_in \<times> witness) set"
  where "R = {(h, w). (fst h = \<^bold>g [^] w \<and> snd h = g' [^] w)}"

definition S2 :: "'grp pub_in \<Rightarrow> challenge \<Rightarrow> ('grp msg, response) sim_out spmf"
  where "S2 H c = do {
  let (h, h') = H;
  z \<leftarrow> (sample_uniform (order \<G>));
  let a = \<^bold>g [^] z \<otimes> inv (h [^] c); 
  let a' =  g' [^] z \<otimes> inv (h' [^] c);
  return_spmf ((a,a'), z)}"

definition ss_adversary :: "'grp pub_in \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> nat spmf"
  where "ss_adversary x' c1 c2 = do {
    let ((a,a'), e, z) = c1;
    let ((b,b'), e', z') = c2;
    return_spmf (if (e mod order \<G> > e' mod order \<G>) then (nat ((int z - int z') * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) mod order \<G>)) else 
(nat ((int z' - int z) * (fst (bezw ((e' mod order \<G> - e mod order \<G>) mod order \<G>) (order \<G>))) mod order \<G>)))}"

definition "valid_pub = carrier \<G> \<times> carrier \<G>"

end 

locale chaum_ped_\<Sigma> = chaum_ped_\<Sigma>_base + cyclic_group \<G>
begin

lemma g'_in_carrier [simp]: "g' \<in> carrier \<G>"
  by(simp add: g'_def) 

sublocale chaum_ped_sigma: \<Sigma>_protocols_base init response check R S2 ss_adversary challenge_space valid_pub 
  by unfold_locales (auto simp add: R_def valid_pub_def)

lemma completeness: 
  shows "chaum_ped_sigma.completeness"
proof-
  have "g' [^] y \<otimes> (g' [^] w') [^] e = g' [^] ((w' * e + y) mod order \<G>)" for y e w'
    by (simp add: Groups.add_ac(2) pow_carrier_mod nat_pow_pow nat_pow_mult)
  moreover have "\<^bold>g [^] y \<otimes> (\<^bold>g [^] w') [^] e = \<^bold>g [^] ((w' * e + y) mod order \<G>)" for y e w'
    by (metis add.commute nat_pow_pow nat_pow_mult pow_generator_mod generator_closed mod_mult_right_eq)  
  ultimately show ?thesis
    unfolding chaum_ped_sigma.completeness_def chaum_ped_sigma.completeness_game_def
    by(auto simp add: R_def challenge_space_def init_def check_def response_def split_def bind_spmf_const)
qed

lemma hvzk_xr'_rewrite:
  assumes r: "r < order \<G>"
  shows "((w*c + r) mod (order \<G>) mod (order \<G>) + (order \<G>) * w*c - w*c) mod (order \<G>) = r"
(is "?lhs = ?rhs")
proof-
  have "?lhs = (w*c + r  + (order \<G>) * w*c- w*c) mod (order \<G>)" 
    by (metis Nat.add_diff_assoc Num.of_nat_simps(1) One_nat_def add_less_same_cancel2 less_imp_le_nat 
        mod_add_left_eq mult.assoc mult_0_right n_less_m_mult_n nat_neq_iff not_add_less2 of_nat_0_le_iff prime_gt_1_nat prime_order) 
  thus ?thesis using r 
    by (metis ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) diff_add_inverse mod_if mod_mult_self2)
qed

lemma hvzk_h_sub_rewrite:
  assumes "h = \<^bold>g [^] w"  
    and z: "z < order \<G>" 
  shows "\<^bold>g [^] ((z + (order \<G>)* w * c - w*c)) = \<^bold>g [^] z \<otimes> inv (h [^] c)" 
    (is "?lhs = ?rhs")
proof(cases "w = 0")
  case True
  then show ?thesis using assms by simp
next
  case w_gt_0: False
  then show ?thesis 
  proof-
    have "(z + order \<G> * w * c - w * c) = (z + (order \<G> * w * c- w * c))"
      using z by (simp add: less_imp_le_nat mult_le_mono) 
    then have lhs: "?lhs = \<^bold>g [^] z \<otimes> \<^bold>g [^] ((order \<G>) * w *c - w*c)" 
      by(simp add: nat_pow_mult)
    have " \<^bold>g [^] ((order \<G>) * w *c - w*c) =  inv (h [^] c)"  
    proof(cases "c = 0")
      case True
      then show ?thesis using lhs by simp
    next
      case False
      hence *: "((order \<G>)*w *c - w*c) > 0" using assms w_gt_0 
        using gr0I mult_less_cancel2 n_less_m_mult_n numeral_nat(7) prime_gt_1_nat prime_order zero_less_diff by presburger
      then have " \<^bold>g [^] ((order \<G>)*w*c - w*c) =  \<^bold>g [^] int ((order \<G>)*w*c - w*c)"
        by (simp add: int_pow_int) 
      also have "... = \<^bold>g [^] int ((order \<G>)*w*c) \<otimes> inv (\<^bold>g [^] (w*c))" 
        using int_pow_diff[of "\<^bold>g" "order \<G> * w * c" "w * c"] * generator_closed int_ops(6) int_pow_neg int_pow_neg_int by presburger

      also have "... = \<^bold>g [^] ((order \<G>)*w*c) \<otimes> inv (\<^bold>g [^] (w*c))"
        by (metis int_pow_int) 
      also have "... = \<^bold>g [^] ((order \<G>)*w*c) \<otimes> inv ((\<^bold>g [^] w) [^] c)"
        by(simp add: nat_pow_pow)
      also have "... = \<^bold>g [^] ((order \<G>)*w*c) \<otimes> inv (h [^] c)"
        using assms by simp
      also have "... = \<one> \<otimes> inv (h [^] c)"
        using generator_pow_order
        by (metis generator_closed mult_is_0 nat_pow_0 nat_pow_pow)
      ultimately show ?thesis
        by (simp add: assms(1)) 
    qed
    then show ?thesis using lhs by simp
  qed
qed

lemma hvzk_h_sub2_rewrite:
  assumes  "h' = g' [^] w" 
    and z: "z < order \<G>" 
  shows "g' [^] ((z + (order \<G>)*w*c - w*c))  = g' [^] z \<otimes> inv (h' [^] c)" 
    (is "?lhs = ?rhs")
proof(cases "w = 0")
  case True
  then show ?thesis 
    using assms by (simp add: g'_def)
next
  case w_gt_0: False
  then show ?thesis 
  proof-
    have "g' = \<^bold>g [^] x" using g'_def by simp
    have g'_carrier: "g' \<in> carrier \<G>" using g'_def by simp
    have 1: "g' [^] ((order \<G>)*w*c- w*c) = inv (h' [^] c)"
    proof(cases "c = 0")
      case True
      then show ?thesis by simp
    next
      case False
      hence *: "((order \<G>)*w*c - w*c) > 0" 
        using assms mult_strict_mono w_gt_0 prime_gt_1_nat prime_order by auto 
      then have " g' [^] ((order \<G>)*w*c - w*c) =  g' [^] int ((order \<G>)*w*c - w*c)"
        by (simp add: int_pow_int) 
      also have "... = g' [^] int ((order \<G>)*w*c) \<otimes> inv (g' [^] (w*c))" 
        using int_pow_diff[of "g'" "order \<G> * w* c" "w * c"] g'_carrier 
        by (metis * chaum_ped_\<Sigma>_axioms chaum_ped_\<Sigma>_def cyclic_group_def group.int_pow_neg_int int_ops(6) int_pow_neg less_not_refl2 of_nat_eq_0_iff)
      also have "... = g' [^] ((order \<G>)*w*c) \<otimes> inv (g' [^] (w*c))" 
        by (metis int_pow_int) 
      also have "... = g' [^] ((order \<G>)*w*c) \<otimes> inv (h' [^] c)"
        by(simp add: nat_pow_pow assms)
      also have "... = \<one> \<otimes> inv (h' [^] c)" 
        by (metis g'_carrier nat_pow_one nat_pow_pow pow_order_eq_1)
      ultimately show ?thesis
        by (simp add: assms(1)) 
    qed
    have "(z + order \<G> * w * c - w * c) = (z + (order \<G> * w * c - w * c))"
      using z by (simp add: less_imp_le_nat mult_le_mono) 
    then have lhs: "?lhs = g' [^] z \<otimes> g' [^] ((order \<G>)*w*c - w*c)" 
      by(auto simp add: nat_pow_mult)
    then show ?thesis using 1 by simp
  qed
qed

lemma hv_zk2:
  assumes "(H, w) \<in> R" 
  shows "chaum_ped_sigma.R H w c = chaum_ped_sigma.S H c"
  including monad_normalisation
proof-
  have H: "H = (\<^bold>g [^] (w::nat), g' [^] w)" 
    using assms R_def  by(simp add: prod.expand)
  have g'_carrier: "g' \<in> carrier \<G>" using g'_def by simp
  have "chaum_ped_sigma.R H w c  = do {
    let (h, h') = H;
    r \<leftarrow> sample_uniform (order \<G>);
    let z = (w*c + r) mod (order \<G>);
    let a = \<^bold>g [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>)); 
    let a' = g' [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
    apply(simp add: chaum_ped_sigma.R_def Let_def response_def split_def init_def)
    using assms hvzk_xr'_rewrite 
    by(simp cong: bind_spmf_cong_simp)
  also have "... = do {
    let (h, h') = H;
    z \<leftarrow> map_spmf (\<lambda> r. (w*c + r) mod (order \<G>)) (sample_uniform (order \<G>));
    let a = \<^bold>g [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>)); 
    let a' = g' [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
    by(simp add: bind_map_spmf Let_def o_def)
  also have "... = do {
    let (h, h') = H;
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>)); 
    let a' = g' [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
    by(simp add: samp_uni_plus_one_time_pad)
  also have "... = do {
    let (h, h') = H;
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g [^] z \<otimes> inv (h [^] c); 
    let a' = g' [^] ((z + (order \<G>) * w*c - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
    using hvzk_h_sub_rewrite assms
    apply(simp add: Let_def H)
    apply(intro bind_spmf_cong[OF refl]; clarsimp?)
    by (simp add: pow_generator_mod)
  also have "... = do {
    let (h, h') = H;
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g [^] z \<otimes> inv (h [^] c); 
    let a' = g' [^] ((z + (order \<G>)*w*c - w*c));
    return_spmf ((a,a'),c, z)}"
     using g'_carrier pow_carrier_mod[of "g'"] by simp
   also have "... = do {
    let (h, h') = H;
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g [^] z \<otimes> inv (h [^] c); 
    let a' =  g' [^] z \<otimes> inv (h' [^] c);
    return_spmf ((a,a'),c, z)}"
     using hvzk_h_sub2_rewrite assms H
     by(simp cong: bind_spmf_cong_simp)
   ultimately show ?thesis 
     unfolding chaum_ped_sigma.S_def chaum_ped_sigma.R_def
     by(simp add: init_def S2_def split_def Let_def \<Sigma>_protocols_base.S_def bind_map_spmf map_spmf_conv_bind_spmf)
qed

lemma HVZK: 
  shows "chaum_ped_sigma.HVZK"
    unfolding chaum_ped_sigma.HVZK_def 
    by(auto simp add: hv_zk2 R_def valid_pub_def   S2_def check_def cyclic_group_assoc)

lemma ss_rewrite1:
  assumes "fst h \<in> carrier \<G>"
    and "a \<in> carrier \<G>" 
    and e: "e < order \<G>" 
    and "a \<otimes> fst h [^] e = \<^bold>g [^] z"  
    and e': "e' < e"
    and "a \<otimes> fst h [^] e' = \<^bold>g [^] z'"
  shows "fst h = \<^bold>g [^] ((int z - int z') * inverse (e - e') (order \<G>) mod int (order \<G>))"
proof-
  have gcd: "gcd (e - e') (order \<G>) = 1" 
    using e e' prime_field prime_order by simp
  have "a = \<^bold>g [^] z \<otimes> inv (fst h [^] e)" 
    using assms
    by (simp add: assms inv_solve_right)
  moreover have "a = \<^bold>g [^] z' \<otimes> inv (fst h [^] e')" 
    using assms
    by (simp add: assms inv_solve_right)
  ultimately have "\<^bold>g [^] z \<otimes> fst h [^] e' = \<^bold>g [^] z' \<otimes> fst h [^] e"
    by (metis (no_types, lifting) assms cyclic_group_assoc cyclic_group_commute nat_pow_closed)
  moreover obtain t :: nat where t: "fst h = \<^bold>g [^] t"
    using assms generatorE by blast
  ultimately have "\<^bold>g [^] (z + t * e') = \<^bold>g [^] (z' + t * e)" 
    using nat_pow_pow 
    by (simp add: nat_pow_mult)
  hence "[z + t * e' = z' + t * e] (mod order \<G>)"
    using group_eq_pow_eq_mod or_gt_0 by blast
  hence "[int z + int t * int e' = int z' + int t * int e] (mod order \<G>)"
    using cong_int_iff by force
  hence "[int z - int z' = int t * int e - int t * int e'] (mod order \<G>)"
    by (smt cong_diff_iff_cong_0)
  hence "[int z - int z' = int t * (int e - int e')] (mod order \<G>)"
    by (simp add: right_diff_distrib)
  hence "[int z - int z' = int t * (e - e')] (mod order \<G>)" 
    using assms by (simp add: of_nat_diff)
  hence "[(int z - int z') * fst (bezw (e - e') (order \<G>))  = int t * (e - e') * fst (bezw (e - e') (order \<G>))] (mod order \<G>)"
    using cong_scalar_right by blast
  hence "[(int z - int z') * fst (bezw (e - e') (order \<G>))  = int t * ((e - e') * fst (bezw (e - e') (order \<G>)))] (mod order \<G>)" 
    by (simp add: more_arith_simps(11))
  hence "[(int z - int z') * fst (bezw (e - e') (order \<G>))  = int t * 1] (mod order \<G>)" 
    by (metis (no_types, hide_lams) cong_scalar_left cong_trans inverse gcd)
  hence "[(int z - int z') * fst (bezw (e - e') (order \<G>)) mod order \<G>  = t] (mod order \<G>)" 
    by simp
  hence "[nat ((int z - int z') * fst (bezw (e - e') (order \<G>)) mod order \<G>)  = t] (mod order \<G>)" 
    by (metis cong_def int_ops(9) mod_mod_trivial nat_int)
  hence "\<^bold>g [^] (nat ((int z - int z') * fst (bezw (e - e') (order \<G>)) mod order \<G>))  = \<^bold>g [^] t" 
    using order_gt_0 order_gt_0_iff_finite pow_generator_eq_iff_cong by blast
  thus ?thesis using t by simp
qed

lemma ss_rewrite2:
  assumes "fst h \<in> carrier \<G>"
    and "snd h \<in> carrier \<G>" 
    and "a \<in> carrier \<G>" 
    and "b \<in> carrier \<G>"
    and "e < order \<G>" 
    and "a \<otimes> fst h [^] e = \<^bold>g [^] z" 
    and "b \<otimes> snd h [^] e = g' [^] z"
    and "e' < e" 
    and "a \<otimes> fst h [^] e' = \<^bold>g [^] z'"
    and "b \<otimes> snd h [^] e' = g' [^] z'"
  shows "snd h = g' [^] ((int z - int z') * inverse (e - e') (order \<G>) mod int (order \<G>))"
proof-
  have gcd: "gcd (e - e') (order \<G>) = 1" 
    using prime_field assms prime_order by simp
  have "b = g' [^] z \<otimes> inv (snd h [^] e)"
    by (simp add: assms inv_solve_right)
  moreover have "b = g' [^] z' \<otimes> inv (snd h [^] e')"
    by (metis assms(2) assms(4) assms(10) g'_def generator_closed group.inv_solve_right' group_l_invI l_inv_ex nat_pow_closed)
  ultimately have "g' [^] z \<otimes> snd h [^] e' = g' [^] z' \<otimes> snd h [^] e" 
    by (metis (no_types, lifting) assms cyclic_group_assoc cyclic_group_commute nat_pow_closed)
  moreover obtain t :: nat where t: "snd h = \<^bold>g [^] t"
    using assms(2) generatorE by blast
  ultimately have "\<^bold>g [^] (x * z + t * e') = \<^bold>g [^] (x * z' + t * e)"
    using g'_def nat_pow_pow
    by (simp add: nat_pow_mult) 
  hence "[x * z + t * e' = x * z' + t * e] (mod order \<G>)"
    using group_eq_pow_eq_mod order_gt_0 by blast
  hence "[int x * int z + int t * int e' = int x * int z' + int t * int e] (mod order \<G>)"
    by (metis Groups.add_ac(2) Groups.mult_ac(2) cong_int_iff int_ops(7) int_plus)
  hence "[int x * int z - int x * int z' = int t * int e - int t * int e'] (mod order \<G>)"
    by (smt cong_diff_iff_cong_0)
  hence "[int x * (int z - int z') = int t * (int e - int e')] (mod order \<G>)"
    by (simp add: int_distrib(4))
  hence "[int x * (int z - int z') = int t * (e - e')] (mod order \<G>)"
    using assms by (simp add: of_nat_diff)
  hence "[(int x * (int z - int z')) * fst (bezw (e - e') (order \<G>)) = int t * (e - e') * fst (bezw (e - e') (order \<G>))] (mod order \<G>)"
    using cong_scalar_right by blast
  hence "[(int x * (int z - int z')) * fst (bezw (e - e') (order \<G>)) = int t * ((e - e') * fst (bezw (e - e') (order \<G>)))] (mod order \<G>)"
    by (simp add: more_arith_simps(11))
  hence *: "[(int x * (int z - int z')) * fst (bezw (e - e') (order \<G>)) = int t * 1] (mod order \<G>)"
    by (metis (no_types, hide_lams) cong_scalar_left cong_trans gcd inverse)
  hence "[nat ((int x * (int z - int z')) * fst (bezw (e - e') (order \<G>)) mod order \<G>) = t] (mod order \<G>)"
    by (metis cong_def cong_mod_right more_arith_simps(6) nat_int zmod_int)
  hence "\<^bold>g [^] (nat ((int x * (int z - int z')) * fst (bezw (e - e') (order \<G>)) mod order \<G>)) = \<^bold>g [^] t"
    using order_gt_0 order_gt_0_iff_finite pow_generator_eq_iff_cong by blast
  thus ?thesis using t 
    by (metis (mono_tags, hide_lams) * cong_def g'_def generator_closed int_pow_int int_pow_pow mod_mult_right_eq more_arith_simps(11) more_arith_simps(6) pow_generator_mod_int)
qed

lemma ss_rewrite_snd_h:
  assumes e_e'_mod: "e' mod order \<G> < e mod order \<G>"
    and h_mem: "snd h \<in> carrier \<G>"
    and a_mem: "snd a \<in> carrier \<G>"
    and a1: "snd a \<otimes> snd h [^] e = g' [^] z" 
    and a2: "snd a \<otimes> snd h [^] e' = g' [^] z'" 
  shows "snd h = g' [^] ((int z - int z') * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>))"
proof-
  have gcd: "gcd ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>) = 1"
    using prime_field 
    by (simp add: assms less_imp_diff_less linorder_not_le prime_order)
  have "snd a = g' [^] z \<otimes> inv (snd h [^] e)"
    using a1 
    by (metis (no_types, lifting) Group.group.axioms(1) h_mem a_mem group.inv_closed group_l_invI l_inv_ex monoid.m_assoc nat_pow_closed r_inv r_one)
  moreover have "snd a = g' [^] z' \<otimes> inv (snd h [^] e')"
    by (metis a2 h_mem a_mem g'_def generator_closed group.inv_solve_right' group_l_invI l_inv_ex nat_pow_closed)
  ultimately have "g' [^] z \<otimes> snd h [^] e' = g' [^] z' \<otimes> snd h [^] e" 
    by (metis (no_types, lifting) a2 h_mem a_mem a1 cyclic_group_assoc cyclic_group_commute nat_pow_closed)
  moreover obtain t :: nat where t: "snd h = \<^bold>g [^] t"
    using assms(2) generatorE by blast
  ultimately have "\<^bold>g [^] (x * z + t * e') = \<^bold>g [^] (x * z' + t * e)"
    using g'_def nat_pow_pow
    by (simp add: nat_pow_mult) 
  hence "[x * z + t * e' = x * z' + t * e] (mod order \<G>)"
    using group_eq_pow_eq_mod order_gt_0 by blast
  hence "[int x * int z + int t * int e' = int x * int z' + int t * int e] (mod order \<G>)"
    by (metis Groups.add_ac(2) Groups.mult_ac(2) cong_int_iff int_ops(7) int_plus)
  hence "[int x * int z - int x * int z' = int t * int e - int t * int e'] (mod order \<G>)"
    by (smt cong_diff_iff_cong_0)
  hence "[int x * (int z - int z') = int t * (int e - int e')] (mod order \<G>)"
    by (simp add: int_distrib(4))
  hence "[int x * (int z - int z') = int t * (int e mod order \<G> - int e' mod order \<G>) mod order \<G>] (mod order \<G>)"
    by (metis (no_types, lifting) cong_def mod_diff_eq mod_mod_trivial mod_mult_right_eq)
  hence *: "[int x * (int z - int z') = int t * (e mod order \<G> - e' mod order \<G>) mod order \<G>] (mod order \<G>)"
    by (simp add: assms(1) int_ops(9) less_imp_le_nat of_nat_diff)
  hence "[int x * (int z - int z') * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) 
               = int t * ((e mod order \<G> - e' mod order \<G>) mod order \<G> 
                  * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)))] (mod order \<G>)"
    by (metis (no_types, lifting) cong_mod_right cong_scalar_right less_imp_diff_less mod_if more_arith_simps(11) or_gt_0 unique_euclidean_semiring_numeral_class.pos_mod_bound)
  hence "[int x * (int z - int z') * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) 
               = int t * 1] (mod order \<G>)"
    by (meson Number_Theory_Aux.inverse * gcd cong_scalar_left cong_trans)
  hence "\<^bold>g [^] (int x * (int z - int z') * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) = \<^bold>g [^] t"
    by (metis cong_def int_pow_int more_arith_simps(6) pow_generator_mod_int)
  thus ?thesis using t 
    by (metis (mono_tags, hide_lams) g'_def generator_closed int_pow_int int_pow_pow mod_mult_right_eq more_arith_simps(11) pow_generator_mod_int)
qed

lemma special_soundness:
  shows "chaum_ped_sigma.special_soundness"
  unfolding chaum_ped_sigma.special_soundness_def 
  apply(auto simp add: challenge_space_def check_def ss_adversary_def R_def valid_pub_def)
  using ss_rewrite2 ss_rewrite1 by auto

theorem \<Sigma>_protocol:  "chaum_ped_sigma.\<Sigma>_protocol"
  by(simp add: chaum_ped_sigma.\<Sigma>_protocol_def completeness HVZK special_soundness)

sublocale chaum_ped_\<Sigma>_commit: \<Sigma>_protocols_to_commitments init response check R S2 ss_adversary challenge_space valid_pub G
  apply unfold_locales
      apply(auto simp add: \<Sigma>_protocol lossless_init lossless_response lossless_G)
  by(simp add: R_def G_def)

sublocale dis_log: dis_log \<G> 
  unfolding dis_log_def by simp

sublocale dis_log_alt: dis_log_alt \<G> x 
  unfolding dis_log_alt_def by simp

lemma reduction_to_dis_log: 
  shows "chaum_ped_\<Sigma>_commit.rel_advantage \<A> = dis_log.advantage (dis_log_alt.adversary3 \<A>)"
proof-
  have "chaum_ped_\<Sigma>_commit.rel_game \<A> = TRY do {
    w \<leftarrow> sample_uniform (order \<G>);
    let (h,w) = ((\<^bold>g [^] w, g' [^] w), w);
    w' \<leftarrow> \<A> h;
    return_spmf ((fst h = \<^bold>g [^] w' \<and> snd h = g' [^] w'))} ELSE return_spmf False"
    unfolding chaum_ped_\<Sigma>_commit.rel_game_def 
    by(simp add:  G_def R_def)
  also have "... = TRY do {    
    w \<leftarrow> sample_uniform (order \<G>);
    let (h,w) = ((\<^bold>g [^] w, g' [^] w), w);
    w' \<leftarrow> \<A> h;
    return_spmf ([w = w'] (mod (order \<G>)) \<and> [x*w = x*w'] (mod order \<G>))} ELSE return_spmf False"
    apply(intro try_spmf_cong bind_spmf_cong[OF refl]; simp add: dis_log_alt.dis_log3_def dis_log_alt.g'_def g'_def)
    by (simp add: finite_carrier nat_pow_pow pow_generator_eq_iff_cong)
  also have "... = dis_log_alt.dis_log3 \<A>"
    apply(auto simp add:  dis_log_alt.dis_log3_def dis_log_alt.g'_def g'_def)
    by(intro try_spmf_cong  bind_spmf_cong[OF refl]; clarsimp?; auto simp add: cong_scalar_left)
  ultimately have "chaum_ped_\<Sigma>_commit.rel_advantage \<A> = dis_log_alt.advantage3 \<A>"
    by(simp add: chaum_ped_\<Sigma>_commit.rel_advantage_def dis_log_alt.advantage3_def)
  thus ?thesis
    by (simp add: dis_log_alt_reductions.dis_log_adv3 cyclic_group_axioms dis_log_alt.dis_log_alt_axioms dis_log_alt_reductions.intro)
qed

lemma commitment_correct: "chaum_ped_\<Sigma>_commit.abstract_com.correct"
  by(simp add: chaum_ped_\<Sigma>_commit.commit_correct)

lemma  "chaum_ped_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa \<A>"
  using chaum_ped_\<Sigma>_commit.perfect_hiding by blast

lemma binding: "chaum_ped_\<Sigma>_commit.abstract_com.bind_advantage \<A> \<le> dis_log.advantage (dis_log_alt.adversary3 ((chaum_ped_\<Sigma>_commit.adversary \<A>)))"
  using chaum_ped_\<Sigma>_commit.bind_advantage reduction_to_dis_log by simp

end

locale chaum_ped_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
    and x :: nat
  assumes cp_\<Sigma>: "\<And>\<eta>. chaum_ped_\<Sigma> (\<G> \<eta>)"
begin

sublocale chaum_ped_\<Sigma> "\<G> \<eta>" for \<eta> 
  by(simp add: cp_\<Sigma>)

text\<open>The \<open>\<Sigma>\<close>-protocol statement comes easily in the asympotic setting.\<close>

theorem sigma_protocol:
  shows "chaum_ped_sigma.\<Sigma>_protocol n"
  by(simp add: \<Sigma>_protocol)

text\<open>We now show the statements of security for the commitment scheme in the asymptotic setting, the main difference is that
we are able to show the binding advantage is negligible in the security parameter.\<close>

lemma asymp_correct: "chaum_ped_\<Sigma>_commit.abstract_com.correct n" 
  using  chaum_ped_\<Sigma>_commit.commit_correct by simp

lemma asymp_perfect_hiding: "chaum_ped_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa n (\<A> n)"
  using chaum_ped_\<Sigma>_commit.perfect_hiding by blast

lemma asymp_computational_binding: 
  assumes "negligible (\<lambda> n. dis_log.advantage n (dis_log_alt.adversary3 n ((chaum_ped_\<Sigma>_commit.adversary n (\<A> n)))))"
  shows "negligible (\<lambda> n. chaum_ped_\<Sigma>_commit.abstract_com.bind_advantage n (\<A> n))"
  using chaum_ped_\<Sigma>_commit.bind_advantage assms chaum_ped_\<Sigma>_commit.abstract_com.bind_advantage_def negligible_le binding by auto

end

end
