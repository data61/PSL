(* Title: IND_CPA_PK_Single.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory IND_CPA_PK_Single imports
  CryptHOL.Computational_Model
begin

subsection \<open>The IND-CPA game (public key, single instance)\<close>

locale ind_cpa = 
  fixes key_gen :: "('pub_key \<times> 'priv_key) spmf" \<comment> \<open>probabilistic\<close>
  and aencrypt :: "'pub_key \<Rightarrow> 'plain \<Rightarrow> 'cipher spmf"  \<comment> \<open>probabilistic\<close>
  and adecrypt :: "'priv_key \<Rightarrow> 'cipher \<Rightarrow> 'plain option" \<comment> \<open>deterministic, but not used\<close>
  and valid_plains :: "'plain \<Rightarrow> 'plain \<Rightarrow> bool" \<comment> \<open>checks whether a pair of plaintexts is valid, i.e., they both have the right format\<close>
begin

text \<open>
  We cannot incorporate the predicate @{term valid_plain} in the type @{typ "'plain"} of plaintexts,
  because the single @{typ "'plain"} must contain plaintexts for all values of the security parameter,
  as HOL does not have dependent types.  Consequently, the oracle has to ensure that the received
  plaintexts are valid.
\<close>

type_synonym ('pub_key', 'plain', 'cipher', 'state) adversary = 
  "('pub_key' \<Rightarrow> (('plain' \<times> 'plain') \<times> 'state) spmf)
   \<times> ('cipher' \<Rightarrow> 'state \<Rightarrow> bool spmf)"

primrec ind_cpa :: "('pub_key, 'plain, 'cipher, 'state) adversary \<Rightarrow> bool spmf"
where
  "ind_cpa (\<A>1, \<A>2) = TRY do {
     (pk, sk) \<leftarrow> key_gen;
     ((m0, m1), \<sigma>) \<leftarrow> \<A>1 pk;
     _ :: unit \<leftarrow> assert_spmf (valid_plains m0 m1);
     b \<leftarrow> coin_spmf;
     cipher \<leftarrow> aencrypt pk (if b then m0 else m1);
     b' \<leftarrow> \<A>2 cipher \<sigma>;
     return_spmf (b = b')
  } ELSE coin_spmf"

declare ind_cpa.simps [simp del]

definition advantage :: "('pub_key, 'plain, 'cipher, 'state) adversary \<Rightarrow> real"
where "advantage \<A> = \<bar>spmf (ind_cpa \<A>) True - 1/2\<bar>"

definition lossless :: "('pub_key, 'plain, 'cipher, 'state) adversary \<Rightarrow> bool"
where
  "lossless \<A> \<longleftrightarrow>
   ((\<forall>pk. lossless_spmf (fst \<A> pk)) \<and>
        (\<forall>cipher \<sigma>. lossless_spmf (snd \<A> cipher \<sigma>)))"

lemma lossless_ind_cpa:
  "\<lbrakk> lossless \<A>; lossless_spmf (key_gen) \<rbrakk> \<Longrightarrow> lossless_spmf (ind_cpa \<A>)"
by(auto simp add: lossless_def ind_cpa_def split_def Let_def)

end

end
