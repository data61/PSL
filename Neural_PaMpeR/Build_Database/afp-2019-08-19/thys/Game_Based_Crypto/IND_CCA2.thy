(* Title: IND_CCA2.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory IND_CCA2 imports
  CryptHOL.Computational_Model
  CryptHOL.Negligible
  CryptHOL.Environment_Functor
begin

locale pk_enc = 
  fixes key_gen :: "security \<Rightarrow> ('ekey \<times> 'dkey) spmf" \<comment> \<open>probabilistic\<close>
  and encrypt :: "security \<Rightarrow> 'ekey \<Rightarrow> 'plain \<Rightarrow> 'cipher spmf"  \<comment> \<open>probabilistic\<close>
  and decrypt :: "security \<Rightarrow> 'dkey \<Rightarrow> 'cipher \<Rightarrow> 'plain option" \<comment> \<open>deterministic, but not used\<close>
  and valid_plain :: "security \<Rightarrow> 'plain \<Rightarrow> bool" \<comment> \<open>checks whether a plain text is valid, i.e., has the right format\<close>

subsection \<open>The IND-CCA2 game for public-key encryption\<close>

text \<open>
  We model an IND-CCA2 security game in the multi-user setting as described in
  \cite{BellareBoldyrevaMicali2000EUROCRYPT}.
\<close>

locale ind_cca2 = pk_enc +
  constrains key_gen :: "security \<Rightarrow> ('ekey \<times> 'dkey) spmf"
  and encrypt :: "security \<Rightarrow> 'ekey \<Rightarrow> 'plain \<Rightarrow> 'cipher spmf"
  and decrypt :: "security \<Rightarrow> 'dkey \<Rightarrow> 'cipher \<Rightarrow> 'plain option"
  and valid_plain :: "security \<Rightarrow> 'plain \<Rightarrow> bool"
begin

type_synonym ('ekey', 'dkey', 'cipher') state_oracle = "('ekey' \<times> 'dkey' \<times> 'cipher' list) option"

fun decrypt_oracle
  :: "security \<Rightarrow> ('ekey, 'dkey, 'cipher) state_oracle \<Rightarrow> 'cipher
  \<Rightarrow> ('plain option \<times> ('ekey, 'dkey, 'cipher) state_oracle) spmf"
where
  "decrypt_oracle \<eta> None cipher = return_spmf (None, None)"
| "decrypt_oracle \<eta> (Some (ekey, dkey, cstars)) cipher = return_spmf
   (if cipher \<in> set cstars then None else decrypt \<eta> dkey cipher, Some (ekey, dkey, cstars))"

fun ekey_oracle
  :: "security \<Rightarrow> ('ekey, 'dkey, 'cipher) state_oracle \<Rightarrow> unit \<Rightarrow> ('ekey \<times> ('ekey, 'dkey, 'cipher) state_oracle) spmf"
where
  "ekey_oracle \<eta> None _ = do {
      (ekey, dkey) \<leftarrow> key_gen \<eta>;
      return_spmf (ekey, Some (ekey, dkey, []))
    }"
| "ekey_oracle \<eta> (Some (ekey, rest)) _ = return_spmf (ekey, Some (ekey, rest))"

lemma ekey_oracle_conv:
  "ekey_oracle \<eta> \<sigma> x =
  (case \<sigma> of None \<Rightarrow> map_spmf (\<lambda>(ekey, dkey). (ekey, Some (ekey, dkey, []))) (key_gen \<eta>) 
   | Some (ekey, rest) \<Rightarrow> return_spmf (ekey, Some (ekey, rest)))"
by(cases \<sigma>)(auto simp add: map_spmf_conv_bind_spmf split_def)

context notes bind_spmf_cong[fundef_cong] begin
function encrypt_oracle
  :: "bool \<Rightarrow> security \<Rightarrow> ('ekey, 'dkey, 'cipher) state_oracle \<Rightarrow> 'plain \<times> 'plain
  \<Rightarrow> ('cipher \<times> ('ekey, 'dkey, 'cipher) state_oracle) spmf"
where
  "encrypt_oracle b \<eta> None m01 = do { (_, \<sigma>) \<leftarrow> ekey_oracle \<eta> None (); encrypt_oracle b \<eta> \<sigma> m01 }"
| "encrypt_oracle b \<eta> (Some (ekey, dkey, cstars)) (m0, m1) =
  (if valid_plain \<eta> m0 \<and> valid_plain \<eta> m1 then do {  
     let pb = (if b then m0 else m1);
     cstar \<leftarrow> encrypt \<eta> ekey pb;
     return_spmf (cstar, Some (ekey, dkey, cstar # cstars))
   } else return_pmf None)"
by pat_completeness auto
termination by(relation "Wellfounded.measure (\<lambda>(b, \<eta>, \<sigma>, m01). case \<sigma> of None \<Rightarrow> 1 | _ \<Rightarrow> 0)") auto
end

subsubsection \<open>Single-user setting\<close>

type_synonym ('plain', 'cipher') call\<^sub>1 = "unit + 'cipher' + 'plain' \<times> 'plain'"
type_synonym ('ekey', 'plain', 'cipher') ret\<^sub>1 = "'ekey' + 'plain' option + 'cipher'"

definition oracle\<^sub>1 :: "bool \<Rightarrow> security 
  \<Rightarrow> (('ekey, 'dkey, 'cipher) state_oracle, ('plain, 'cipher) call\<^sub>1, ('ekey, 'plain, 'cipher) ret\<^sub>1) oracle'"
where "oracle\<^sub>1 b \<eta> = ekey_oracle \<eta> \<oplus>\<^sub>O (decrypt_oracle \<eta> \<oplus>\<^sub>O encrypt_oracle b \<eta>)"

lemma oracle\<^sub>1_simps [simp]:
  "oracle\<^sub>1 b \<eta> s (Inl x) = map_spmf (apfst Inl) (ekey_oracle \<eta> s x)"
  "oracle\<^sub>1 b \<eta> s (Inr (Inl y)) = map_spmf (apfst (Inr \<circ> Inl)) (decrypt_oracle \<eta> s y)"
  "oracle\<^sub>1 b \<eta> s (Inr (Inr z)) = map_spmf (apfst (Inr \<circ> Inr)) (encrypt_oracle b \<eta> s z)"
by(simp_all add: oracle\<^sub>1_def spmf.map_comp apfst_compose o_def)

type_synonym ('ekey', 'plain', 'cipher') adversary\<^sub>1' = 
  "(bool, ('plain', 'cipher') call\<^sub>1, ('ekey', 'plain', 'cipher') ret\<^sub>1) gpv"
type_synonym ('ekey', 'plain', 'cipher') adversary\<^sub>1 =
  "security \<Rightarrow> ('ekey', 'plain', 'cipher') adversary\<^sub>1'"

definition ind_cca2\<^sub>1 :: "('ekey, 'plain, 'cipher) adversary\<^sub>1 \<Rightarrow> security \<Rightarrow> bool spmf"
where
  "ind_cca2\<^sub>1 \<A> \<eta> = TRY do {
    b \<leftarrow> coin_spmf;
    (guess, s) \<leftarrow> exec_gpv (oracle\<^sub>1 b \<eta>) (\<A> \<eta>) None;
    return_spmf (guess = b)
  } ELSE coin_spmf"

definition advantage\<^sub>1 :: "('ekey, 'plain, 'cipher) adversary\<^sub>1 \<Rightarrow> advantage"
where "advantage\<^sub>1 \<A> \<eta> = \<bar>spmf (ind_cca2\<^sub>1 \<A> \<eta>) True - 1/2\<bar>"

lemma advantage\<^sub>1_nonneg: "advantage\<^sub>1 \<A> \<eta> \<ge> 0" by(simp add: advantage\<^sub>1_def)

abbreviation secure_for\<^sub>1 :: "('ekey, 'plain, 'cipher) adversary\<^sub>1 \<Rightarrow> bool"
where "secure_for\<^sub>1 \<A> \<equiv> negligible (advantage\<^sub>1 \<A>)"

definition ibounded_by\<^sub>1' :: "('ekey, 'plain, 'cipher) adversary\<^sub>1' \<Rightarrow> nat \<Rightarrow> bool"
where "ibounded_by\<^sub>1' \<A> q = interaction_any_bounded_by \<A> q"

abbreviation ibounded_by\<^sub>1 :: "('ekey, 'plain, 'cipher) adversary\<^sub>1 \<Rightarrow> (security \<Rightarrow> nat) \<Rightarrow> bool"
where "ibounded_by\<^sub>1 \<equiv> rel_envir ibounded_by\<^sub>1'"

definition lossless\<^sub>1' :: "('ekey, 'plain, 'cipher) adversary\<^sub>1' \<Rightarrow> bool"
where "lossless\<^sub>1' \<A> = lossless_gpv \<I>_full \<A>"

abbreviation lossless\<^sub>1 :: "('ekey, 'plain, 'cipher) adversary\<^sub>1 \<Rightarrow> bool"
where "lossless\<^sub>1 \<equiv> pred_envir lossless\<^sub>1'"

lemma lossless_decrypt_oracle [simp]: "lossless_spmf (decrypt_oracle \<eta> \<sigma> cipher)"
by(cases "(\<eta>, \<sigma>, cipher)" rule: decrypt_oracle.cases) simp_all

lemma lossless_ekey_oracle [simp]:
  "lossless_spmf (ekey_oracle \<eta> \<sigma> x) \<longleftrightarrow> (\<sigma> = None \<longrightarrow> lossless_spmf (key_gen \<eta>))"
by(cases "(\<eta>, \<sigma>, x)" rule: ekey_oracle.cases)(auto)

lemma lossless_encrypt_oracle [simp]:
  "\<lbrakk> \<sigma> = None \<Longrightarrow> lossless_spmf (key_gen \<eta>);
    \<And>ekey m. valid_plain \<eta> m \<Longrightarrow> lossless_spmf (encrypt \<eta> ekey m) \<rbrakk>
  \<Longrightarrow> lossless_spmf (encrypt_oracle b \<eta> \<sigma> (m0, m1)) \<longleftrightarrow> valid_plain \<eta> m0 \<and> valid_plain \<eta> m1"
apply(cases "(b, \<eta>, \<sigma>, (m0, m1))" rule: encrypt_oracle.cases)
apply(auto simp add: split_beta dest: lossless_spmfD_set_spmf_nonempty split: if_split_asm)
done

subsubsection \<open>Multi-user setting\<close>

definition oracle\<^sub>n :: "bool \<Rightarrow> security
   \<Rightarrow> ('i \<Rightarrow> ('ekey, 'dkey, 'cipher) state_oracle, 'i \<times> ('plain, 'cipher) call\<^sub>1, ('ekey, 'plain, 'cipher) ret\<^sub>1) oracle'"
where "oracle\<^sub>n b \<eta> = family_oracle (\<lambda>_. oracle\<^sub>1 b \<eta>)"

lemma oracle\<^sub>n_apply [simp]:
  "oracle\<^sub>n b \<eta> s (i, x) = map_spmf (apsnd (fun_upd s i)) (oracle\<^sub>1 b \<eta> (s i) x)"
by(simp add: oracle\<^sub>n_def)

type_synonym ('i, 'ekey', 'plain', 'cipher') adversary\<^sub>n' = 
  "(bool, 'i \<times> ('plain', 'cipher') call\<^sub>1, ('ekey', 'plain', 'cipher') ret\<^sub>1) gpv"
type_synonym ('i, 'ekey', 'plain', 'cipher') adversary\<^sub>n =
  "security \<Rightarrow> ('i, 'ekey', 'plain', 'cipher') adversary\<^sub>n'"

definition ind_cca2\<^sub>n :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n \<Rightarrow> security \<Rightarrow> bool spmf"
where
  "ind_cca2\<^sub>n \<A> \<eta> = TRY do {
    b \<leftarrow> coin_spmf;
    (guess, \<sigma>) \<leftarrow> exec_gpv (oracle\<^sub>n b \<eta>) (\<A> \<eta>) (\<lambda>_. None);
    return_spmf (guess = b)
  } ELSE coin_spmf"

definition advantage\<^sub>n :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n \<Rightarrow> advantage"
where "advantage\<^sub>n \<A> \<eta> = \<bar>spmf (ind_cca2\<^sub>n \<A> \<eta>) True - 1/2\<bar>"

lemma advantage\<^sub>n_nonneg: "advantage\<^sub>n \<A> \<eta> \<ge> 0" by(simp add: advantage\<^sub>n_def)

abbreviation secure_for\<^sub>n :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n \<Rightarrow> bool"
where "secure_for\<^sub>n \<A> \<equiv> negligible (advantage\<^sub>n \<A>)"

definition ibounded_by\<^sub>n' :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n' \<Rightarrow> nat \<Rightarrow> bool"
where "ibounded_by\<^sub>n' \<A> q = interaction_any_bounded_by \<A> q"

abbreviation ibounded_by\<^sub>n :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n \<Rightarrow> (security \<Rightarrow> nat) \<Rightarrow> bool"
where "ibounded_by\<^sub>n \<equiv> rel_envir ibounded_by\<^sub>n'"

definition lossless\<^sub>n' :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n' \<Rightarrow> bool"
where "lossless\<^sub>n' \<A> = lossless_gpv \<I>_full \<A>"

abbreviation lossless\<^sub>n :: "('i, 'ekey, 'plain, 'cipher) adversary\<^sub>n \<Rightarrow> bool"
where "lossless\<^sub>n \<equiv> pred_envir lossless\<^sub>n'"


definition cipher_queries :: "('i \<Rightarrow> ('ekey, 'dkey, 'cipher) state_oracle) \<Rightarrow> 'cipher set"
where "cipher_queries ose = (\<Union>(_, _, ciphers)\<in>ran ose. set ciphers)"

lemma cipher_queriesI:
  "\<lbrakk> ose n = Some (ek, dk, ciphers); x \<in> set ciphers \<rbrakk> \<Longrightarrow> x \<in> cipher_queries ose"
by(auto simp add: cipher_queries_def ran_def)

lemma cipher_queriesE:
  assumes "x \<in> cipher_queries ose"
  obtains (cipher_queries) n ek dk ciphers where "ose n = Some (ek, dk, ciphers)" "x \<in> set ciphers"
using assms by(auto simp add: cipher_queries_def ran_def)

lemma cipher_queries_updE:
  assumes "x \<in> cipher_queries (ose(n \<mapsto> (ek, dk, ciphers)))"
  obtains (old) "x \<in> cipher_queries ose" "x \<notin> set ciphers" | (new) "x \<in> set ciphers"
using assms by(cases "x \<in> set ciphers")(fastforce elim!: cipher_queriesE split: if_split_asm intro: cipher_queriesI)+

lemma cipher_queries_empty [simp]: "cipher_queries Map.empty = {}"
by(simp add: cipher_queries_def)

end

end
