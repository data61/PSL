(* Title: IND_CPA.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory IND_CPA imports
  CryptHOL.Generative_Probabilistic_Value
  CryptHOL.Computational_Model
  CryptHOL.Negligible
begin

subsection \<open>The IND-CPA game for symmetric encryption schemes\<close>

locale ind_cpa = 
  fixes key_gen :: "'key spmf" \<comment> \<open>probabilistic\<close>
  and encrypt :: "'key \<Rightarrow> 'plain \<Rightarrow> 'cipher spmf"  \<comment> \<open>probabilistic\<close>
  and decrypt :: "'key \<Rightarrow> 'cipher \<Rightarrow> 'plain option" \<comment> \<open>deterministic, but not used\<close>
  and valid_plain :: "'plain \<Rightarrow> bool" \<comment> \<open>checks whether a plain text is valid, i.e., has the right format\<close>
begin

text \<open>
  We cannot incorporate the predicate @{term valid_plain} in the type @{typ "'plain"} of plaintexts,
  because the single @{typ "'plain"} must contain plaintexts for all values of the security parameter,
  as HOL does not have dependent types.  Consequently, the oracle has to ensure that the received
  plaintexts are valid.
\<close>

type_synonym ('plain', 'cipher', 'state) adversary = 
  "(('plain' \<times> 'plain') \<times> 'state, 'plain', 'cipher') gpv
   \<times> ('cipher' \<Rightarrow> 'state \<Rightarrow> (bool, 'plain', 'cipher') gpv)"

definition encrypt_oracle :: "'key \<Rightarrow> unit \<Rightarrow> 'plain \<Rightarrow> ('cipher \<times> unit) spmf"
where
  "encrypt_oracle key \<sigma> plain = do {
     cipher \<leftarrow> encrypt key plain;
     return_spmf (cipher, ())
  }"

definition ind_cpa :: "('plain, 'cipher, 'state) adversary \<Rightarrow> bool spmf"
where
  "ind_cpa \<A> = do {
     let (\<A>1, \<A>2) = \<A>;
     key \<leftarrow> key_gen;
     b \<leftarrow> coin_spmf;
     (guess, _) \<leftarrow> exec_gpv (encrypt_oracle key) (do {
         ((m0, m1), \<sigma>) \<leftarrow> \<A>1;
         if valid_plain m0 \<and> valid_plain m1 then do {
           cipher \<leftarrow> lift_spmf (encrypt key (if b then m0 else m1));
           \<A>2 cipher \<sigma>
         } else lift_spmf coin_spmf
       }) ();
     return_spmf (guess = b)
  }"

definition advantage :: "('plain, 'cipher, 'state) adversary \<Rightarrow> real"
where "advantage \<A> = \<bar>spmf (ind_cpa \<A>) True - 1/2\<bar>"

lemma advantage_nonneg: "advantage \<A> \<ge> 0" by(simp add: advantage_def)

definition ibounded_by :: "('plain, 'cipher, 'state) adversary \<Rightarrow> enat \<Rightarrow> bool"
where 
  "ibounded_by = (\<lambda>(\<A>1, \<A>2) q. 
  (\<exists>q1 q2. interaction_any_bounded_by \<A>1 q1 \<and> (\<forall>cipher \<sigma>. interaction_any_bounded_by (\<A>2 cipher \<sigma>) q2) \<and> q1 + q2 \<le> q))"

lemma ibounded_byE [consumes 1, case_names ibounded_by, elim?]:
  assumes "ibounded_by (\<A>1, \<A>2) q"
  obtains q1 q2
  where "q1 + q2 \<le> q"
  and "interaction_any_bounded_by \<A>1 q1"
  and "\<And>cipher \<sigma>. interaction_any_bounded_by (\<A>2 cipher \<sigma>) q2"
using assms by(auto simp add: ibounded_by_def)

lemma ibounded_byI [intro?]:
  "\<lbrakk> interaction_any_bounded_by \<A>1 q1; \<And>cipher \<sigma>. interaction_any_bounded_by (\<A>2 cipher \<sigma>) q2; q1 + q2 \<le> q \<rbrakk>
  \<Longrightarrow> ibounded_by (\<A>1, \<A>2) q"
by(auto simp add: ibounded_by_def)

definition lossless :: "('plain, 'cipher, 'state) adversary \<Rightarrow> bool"
where "lossless = (\<lambda>(\<A>1, \<A>2). lossless_gpv \<I>_full \<A>1 \<and> (\<forall>cipher \<sigma>. lossless_gpv \<I>_full (\<A>2 cipher \<sigma>)))"

end

end
