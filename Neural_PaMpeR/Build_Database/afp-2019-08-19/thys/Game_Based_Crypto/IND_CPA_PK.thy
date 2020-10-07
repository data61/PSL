(* Title: IND_CPA_PK.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory IND_CPA_PK imports
  CryptHOL.Computational_Model
  CryptHOL.Negligible
begin

subsection \<open>The IND-CPA game for public-key encryption with oracle access\<close>

locale ind_cpa_pk = 
  fixes key_gen :: "('pubkey \<times> 'privkey, 'call, 'ret) gpv" \<comment> \<open>probabilistic\<close>
  and aencrypt :: "'pubkey \<Rightarrow> 'plain \<Rightarrow> ('cipher, 'call, 'ret) gpv"  \<comment> \<open>probabilistic w/ access to an oracle\<close>
  and adecrypt :: "'privkey \<Rightarrow> 'cipher \<Rightarrow> ('plain, 'call, 'ret) gpv" \<comment> \<open>not used\<close>
  and valid_plains :: "'plain \<Rightarrow> 'plain \<Rightarrow> bool" \<comment> \<open>checks whether a pair of plaintexts is valid, i.e., they have the right format\<close>
begin

text \<open>
  We cannot incorporate the predicate @{term valid_plain} in the type @{typ "'plain"} of plaintexts,
  because the single @{typ "'plain"} must contain plaintexts for all values of the security parameter,
  as HOL does not have dependent types.  Consequently, the game has to ensure that the received
  plaintexts are valid.
\<close>

type_synonym ('pubkey', 'plain', 'cipher', 'call', 'ret', 'state) adversary = 
  "('pubkey' \<Rightarrow> (('plain' \<times> 'plain') \<times> 'state, 'call', 'ret') gpv)
   \<times> ('cipher' \<Rightarrow> 'state \<Rightarrow> (bool, 'call', 'ret') gpv)"

fun ind_cpa :: "('pubkey, 'plain, 'cipher, 'call, 'ret, 'state) adversary \<Rightarrow> (bool, 'call, 'ret) gpv"
where
  "ind_cpa (\<A>1, \<A>2) = TRY do {
     (pk, sk) \<leftarrow> key_gen;
     b \<leftarrow> lift_spmf coin_spmf;
     ((m0, m1), \<sigma>) \<leftarrow> (\<A>1 pk);
     assert_gpv (valid_plains m0 m1);
     cipher \<leftarrow> aencrypt pk (if b then m0 else m1);
     guess \<leftarrow> \<A>2 cipher \<sigma>; 
     Done (guess = b)
   } ELSE lift_spmf coin_spmf"

definition advantage :: "('\<sigma> \<Rightarrow> 'call \<Rightarrow> ('ret \<times> '\<sigma>) spmf) \<Rightarrow> '\<sigma> \<Rightarrow> ('pubkey, 'plain, 'cipher, 'call, 'ret, 'state) adversary \<Rightarrow> real"
where "advantage oracle \<sigma> \<A> = \<bar>spmf (run_gpv oracle (ind_cpa \<A>) \<sigma>) True - 1/2\<bar>"

lemma advantage_nonneg: "advantage oracle \<sigma> \<A> \<ge> 0" by(simp add: advantage_def)

definition ibounded_by :: "('call \<Rightarrow> bool) \<Rightarrow> ('pubkey, 'plain, 'cipher, 'call, 'ret, 'state) adversary \<Rightarrow> enat \<Rightarrow> bool"
where 
  "ibounded_by consider = (\<lambda>(\<A>1, \<A>2) q. 
  (\<exists>q1 q2. (\<forall>pk. interaction_bounded_by consider (\<A>1 pk) q1) \<and> (\<forall>cipher \<sigma>. interaction_bounded_by consider (\<A>2 cipher \<sigma>) q2) \<and> q1 + q2 \<le> q))"

lemma ibounded_by'E [consumes 1, case_names ibounded_by', elim?]:
  assumes "ibounded_by consider (\<A>1, \<A>2) q"
  obtains q1 q2
  where "q1 + q2 \<le> q"
  and "\<And>pk. interaction_bounded_by consider (\<A>1 pk) q1"
  and "\<And>cipher \<sigma>. interaction_bounded_by consider (\<A>2 cipher \<sigma>) q2"
using assms by(auto simp add: ibounded_by_def)

lemma ibounded_byI [intro?]:
  "\<lbrakk> \<And>pk. interaction_bounded_by consider (\<A>1 pk) q1; \<And>cipher \<sigma>. interaction_bounded_by consider (\<A>2 cipher \<sigma>) q2; q1 + q2 \<le> q \<rbrakk>
  \<Longrightarrow> ibounded_by consider (\<A>1, \<A>2) q"
by(auto simp add: ibounded_by_def)

definition lossless :: "('pubkey, 'plain, 'cipher, 'call, 'ret, 'state) adversary \<Rightarrow> bool"
where "lossless = (\<lambda>(\<A>1, \<A>2). (\<forall>pk. lossless_gpv \<I>_full (\<A>1 pk)) \<and> (\<forall>cipher \<sigma>. lossless_gpv \<I>_full (\<A>2 cipher \<sigma>)))"

end

end
