(* Title: Elgamal.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Cryptographic constructions and their security\<close>

theory Elgamal imports
  CryptHOL.Cyclic_Group_SPMF
  CryptHOL.Computational_Model
  Diffie_Hellman
  IND_CPA_PK_Single
  CryptHOL.Negligible
begin

subsection \<open>Elgamal encryption scheme\<close>

locale elgamal_base =
  fixes \<G> :: "'grp cyclic_group" (structure)
begin

type_synonym 'grp' pub_key = "'grp'"
type_synonym 'grp' priv_key = nat
type_synonym 'grp' plain = 'grp'
type_synonym 'grp' cipher = "'grp' \<times> 'grp'"

definition key_gen :: "('grp pub_key \<times> 'grp priv_key) spmf"
where 
  "key_gen = do {
     x \<leftarrow> sample_uniform (order \<G>);
     return_spmf (\<^bold>g [^] x, x)
  }"

lemma key_gen_alt:
  "key_gen = map_spmf (\<lambda>x. (\<^bold>g [^] x, x)) (sample_uniform (order \<G>))"
by(simp add: map_spmf_conv_bind_spmf key_gen_def)

definition aencrypt :: "'grp pub_key \<Rightarrow> 'grp \<Rightarrow> 'grp cipher spmf"
where
  "aencrypt \<alpha> msg = do {
    y \<leftarrow> sample_uniform (order \<G>);
    return_spmf (\<^bold>g [^] y, (\<alpha> [^] y) \<otimes> msg)
  }"

lemma aencrypt_alt:
  "aencrypt \<alpha> msg = map_spmf (\<lambda>y. (\<^bold>g [^] y, (\<alpha> [^] y) \<otimes> msg)) (sample_uniform (order \<G>))"
by(simp add: map_spmf_conv_bind_spmf aencrypt_def)

definition adecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher \<Rightarrow> 'grp option"
where
  "adecrypt x = (\<lambda>(\<beta>, \<zeta>). Some (\<zeta> \<otimes> (inv (\<beta> [^] x))))"

abbreviation valid_plains :: "'grp \<Rightarrow> 'grp \<Rightarrow> bool"
where "valid_plains msg1 msg2 \<equiv> msg1 \<in> carrier \<G> \<and> msg2 \<in> carrier \<G>"

sublocale ind_cpa: ind_cpa key_gen aencrypt adecrypt valid_plains .
sublocale ddh: ddh \<G> .

fun elgamal_adversary :: "('grp pub_key, 'grp plain, 'grp cipher, 'state) ind_cpa.adversary \<Rightarrow> 'grp ddh.adversary"
where
  "elgamal_adversary (\<A>1, \<A>2) \<alpha> \<beta> \<gamma> = TRY do {
    b \<leftarrow> coin_spmf;
    ((msg1, msg2), \<sigma>) \<leftarrow> \<A>1 \<alpha>;
    \<comment> \<open>have to check that the attacker actually sends two elements from the group; otherwise flip a coin\<close>
    _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
    guess \<leftarrow> \<A>2 (\<beta>, \<gamma> \<otimes> (if b then msg1 else msg2)) \<sigma>;
    return_spmf (guess = b)
  } ELSE coin_spmf"

end

locale elgamal = elgamal_base + cyclic_group \<G>
begin 

theorem advantage_elgamal: "ind_cpa.advantage \<A> = ddh.advantage (elgamal_adversary \<A>)"
  including monad_normalisation
proof -
  obtain \<A>1 and \<A>2 where "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  note [simp] = this order_gt_0_iff_finite finite_carrier try_spmf_bind_out split_def o_def spmf_of_set bind_map_spmf weight_spmf_le_1 scale_bind_spmf bind_spmf_const
    and [cong] = bind_spmf_cong_simp
  have "ddh.ddh_1 (elgamal_adversary \<A>) = TRY do {
       x \<leftarrow> sample_uniform (order \<G>);
       y \<leftarrow> sample_uniform (order \<G>);
       ((msg1, msg2), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g [^] x);
       _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
       b \<leftarrow> coin_spmf;
       z \<leftarrow> map_spmf (\<lambda>z. \<^bold>g [^] z \<otimes> (if b then msg1 else msg2)) (sample_uniform (order \<G>));
       guess \<leftarrow> \<A>2 (\<^bold>g [^] y, z) \<sigma>;
       return_spmf (guess \<longleftrightarrow> b)
     } ELSE coin_spmf"
    by(simp add: ddh.ddh_1_def)
  also have "\<dots> = TRY do {
       x \<leftarrow> sample_uniform (order \<G>);
       y \<leftarrow> sample_uniform (order \<G>);
       ((msg1, msg2), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g [^] x);
       _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
       z \<leftarrow> map_spmf (\<lambda>z. \<^bold>g [^] z) (sample_uniform (order \<G>));
       guess \<leftarrow> \<A>2 (\<^bold>g [^] y, z) \<sigma>;
       map_spmf ((=) guess) coin_spmf
     } ELSE coin_spmf"
    by(simp add: sample_uniform_one_time_pad map_spmf_conv_bind_spmf[where p=coin_spmf])
  also have "\<dots> = coin_spmf"
    by(simp add: map_eq_const_coin_spmf try_bind_spmf_lossless2')
  also have "ddh.ddh_0 (elgamal_adversary \<A>) = ind_cpa.ind_cpa \<A>"
    by(simp add: ddh.ddh_0_def IND_CPA_PK_Single.ind_cpa.ind_cpa_def key_gen_def aencrypt_def nat_pow_pow eq_commute)
  ultimately show ?thesis by(simp add: ddh.advantage_def ind_cpa.advantage_def)
qed

end
  
locale elgamal_asymp = 
  fixes \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  assumes elgamal: "\<And>\<eta>. elgamal (\<G> \<eta>)"
begin
  
sublocale elgamal "\<G> \<eta>" for \<eta> by(simp add: elgamal)
    
theorem elgamal_secure:
  "negligible (\<lambda>\<eta>. ind_cpa.advantage \<eta> (\<A> \<eta>))" if "negligible (\<lambda>\<eta>. ddh.advantage \<eta> (elgamal_adversary \<eta> (\<A> \<eta>)))"
  by(simp add: advantage_elgamal that)

end

context elgamal_base begin

lemma lossless_key_gen [simp]: "lossless_spmf (key_gen) \<longleftrightarrow> 0 < order \<G>"
by(simp add: key_gen_def Let_def)

lemma lossless_aencrypt [simp]:
  "lossless_spmf (aencrypt key plain) \<longleftrightarrow> 0 < order \<G>"
by(simp add: aencrypt_def Let_def)

lemma lossless_elgamal_adversary:
  "\<lbrakk> ind_cpa.lossless \<A>; 0 < order \<G> \<rbrakk>
  \<Longrightarrow> ddh.lossless (elgamal_adversary \<A>)"
by(cases \<A>)(simp add: ddh.lossless_def ind_cpa.lossless_def Let_def split_def)

end

end
