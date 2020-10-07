(* Title: SUF_CMA.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory SUF_CMA imports
  CryptHOL.Computational_Model
  CryptHOL.Negligible
  CryptHOL.Environment_Functor
begin

subsection \<open>Strongly existentially unforgeable signature scheme\<close>

locale sig_scheme =
  fixes key_gen :: "security \<Rightarrow> ('vkey \<times> 'sigkey) spmf"
  and sign :: "security \<Rightarrow> 'sigkey \<Rightarrow> 'message \<Rightarrow> 'signature spmf"
  and verify :: "security \<Rightarrow> 'vkey \<Rightarrow> 'message \<Rightarrow> 'signature \<Rightarrow> bool" \<comment> \<open>verification is deterministic\<close>
  and valid_message :: "security \<Rightarrow> 'message \<Rightarrow> bool"

locale suf_cma = sig_scheme +
  constrains key_gen :: "security \<Rightarrow> ('vkey \<times> 'sigkey) spmf"
  and sign :: "security \<Rightarrow> 'sigkey \<Rightarrow> 'message \<Rightarrow> 'signature spmf"
  and verify :: "security \<Rightarrow> 'vkey \<Rightarrow> 'message \<Rightarrow> 'signature \<Rightarrow> bool"
  and valid_message :: "security \<Rightarrow> 'message \<Rightarrow> bool"
begin

type_synonym ('vkey', 'sigkey', 'message', 'signature') state_oracle 
  = "('vkey' \<times> 'sigkey' \<times> ('message' \<times> 'signature') list) option"

fun vkey_oracle :: "security \<Rightarrow> (('vkey, 'sigkey, 'message, 'signature) state_oracle, unit, 'vkey) oracle'"
where
  "vkey_oracle \<eta> None _ = do {
     (vkey, sigkey) \<leftarrow> key_gen \<eta>;
     return_spmf (vkey, Some (vkey, sigkey, []))
   }"
| "\<And>log. vkey_oracle \<eta> (Some (vkey, sigkey, log)) _ = return_spmf (vkey, Some (vkey, sigkey, log))"

context notes bind_spmf_cong[fundef_cong] begin
function sign_oracle
  :: "security \<Rightarrow> (('vkey, 'sigkey, 'message, 'signature) state_oracle, 'message, 'signature) oracle'"
where
  "sign_oracle \<eta> None m = do { (_, \<sigma>) \<leftarrow> vkey_oracle \<eta> None (); sign_oracle \<eta> \<sigma> m }"
| "\<And>log. sign_oracle \<eta> (Some (vkey, skey, log)) m =
  (if valid_message \<eta> m then do {
    sig \<leftarrow> sign \<eta> skey m;
    return_spmf (sig, Some (vkey, skey, (m, sig) # log)) 
  } else return_pmf None)"
by pat_completeness auto
termination by(relation "Wellfounded.measure (\<lambda>(\<eta>, \<sigma>, m). case \<sigma> of None \<Rightarrow> 1 | _ \<Rightarrow> 0)") auto
end

lemma lossless_vkey_oracle [simp]:
  "lossless_spmf (vkey_oracle \<eta> \<sigma> x) \<longleftrightarrow> (\<sigma> = None \<longrightarrow> lossless_spmf (key_gen \<eta>))"
by(cases "(\<eta>, \<sigma>, x)" rule: vkey_oracle.cases) auto

lemma lossless_sign_oracle [simp]:
  "\<lbrakk> \<sigma> = None \<Longrightarrow> lossless_spmf (key_gen \<eta>);
    \<And>skey m. valid_message \<eta> m \<Longrightarrow> lossless_spmf (sign \<eta> skey m) \<rbrakk>
  \<Longrightarrow> lossless_spmf (sign_oracle \<eta> \<sigma> m) \<longleftrightarrow> valid_message \<eta> m"
apply(cases "(\<eta>, \<sigma>, m)" rule: sign_oracle.cases)
apply(auto simp add: split_beta dest: lossless_spmfD_set_spmf_nonempty)
done

lemma lossless_sign_oracle_Some: fixes log shows
  "lossless_spmf (sign_oracle \<eta> (Some (vkey, skey, log)) m) \<longleftrightarrow> lossless_spmf (sign \<eta> skey m) \<and> valid_message \<eta> m"
by(simp)

subsubsection \<open>Single-user setting\<close>

type_synonym 'message' call\<^sub>1 = "unit + 'message'"
type_synonym ('vkey', 'signature') ret\<^sub>1 = "'vkey' + 'signature'"

definition oracle\<^sub>1 :: "security
  \<Rightarrow> (('vkey, 'sigkey, 'message, 'signature) state_oracle, 'message call\<^sub>1, ('vkey, 'signature) ret\<^sub>1) oracle'"
where "oracle\<^sub>1 \<eta> = vkey_oracle \<eta> \<oplus>\<^sub>O sign_oracle \<eta>"

lemma oracle\<^sub>1_simps [simp]:
  "oracle\<^sub>1 \<eta> s (Inl x) = map_spmf (apfst Inl) (vkey_oracle \<eta> s x)"
  "oracle\<^sub>1 \<eta> s (Inr y) = map_spmf (apfst Inr) (sign_oracle \<eta> s y)"
by(simp_all add: oracle\<^sub>1_def)

type_synonym ('vkey', 'message', 'signature') adversary\<^sub>1' = 
  "(('message' \<times> 'signature'), 'message' call\<^sub>1, ('vkey', 'signature') ret\<^sub>1) gpv"
type_synonym ('vkey', 'message', 'signature') adversary\<^sub>1 =
  "security \<Rightarrow> ('vkey', 'message', 'signature') adversary\<^sub>1'"

definition suf_cma\<^sub>1 :: "('vkey, 'message, 'signature) adversary\<^sub>1 \<Rightarrow> security \<Rightarrow> bool spmf"
where
  "\<And>log. suf_cma\<^sub>1 \<A> \<eta> = do {
    ((m, sig), \<sigma>) \<leftarrow> exec_gpv (oracle\<^sub>1 \<eta>) (\<A> \<eta>) None;
    return_spmf (
      case \<sigma> of None \<Rightarrow> False
      | Some (vkey, skey, log) \<Rightarrow> verify \<eta> vkey m sig \<and> (m, sig) \<notin> set log)
  }"

definition advantage\<^sub>1 :: "('vkey, 'message, 'signature) adversary\<^sub>1 \<Rightarrow> advantage"
where "advantage\<^sub>1 \<A> \<eta> = spmf (suf_cma\<^sub>1 \<A> \<eta>) True"

lemma advantage\<^sub>1_nonneg: "advantage\<^sub>1 \<A> \<eta> \<ge> 0" by(simp add: advantage\<^sub>1_def pmf_nonneg)

abbreviation secure_for\<^sub>1 :: "('vkey, 'message, 'signature) adversary\<^sub>1 \<Rightarrow> bool"
where "secure_for\<^sub>1 \<A> \<equiv> negligible (advantage\<^sub>1 \<A>)"

definition ibounded_by\<^sub>1' :: "('vkey, 'message, 'signature) adversary\<^sub>1' \<Rightarrow> nat \<Rightarrow> bool"
where "ibounded_by\<^sub>1' \<A> q = (interaction_any_bounded_by \<A> q)"

abbreviation ibounded_by\<^sub>1 :: "('vkey, 'message, 'signature) adversary\<^sub>1 \<Rightarrow> (security \<Rightarrow> nat) \<Rightarrow> bool"
where "ibounded_by\<^sub>1 \<equiv> rel_envir ibounded_by\<^sub>1'"

definition lossless\<^sub>1' :: "('vkey, 'message, 'signature) adversary\<^sub>1' \<Rightarrow> bool"
where "lossless\<^sub>1' \<A> = (lossless_gpv \<I>_full \<A>)"

abbreviation lossless\<^sub>1 :: "('vkey, 'message, 'signature) adversary\<^sub>1 \<Rightarrow> bool"
where "lossless\<^sub>1 \<equiv> pred_envir lossless\<^sub>1'"

subsubsection \<open>Multi-user setting\<close>

definition oracle\<^sub>n :: "security
  \<Rightarrow> ('i \<Rightarrow> ('vkey, 'sigkey, 'message, 'signature) state_oracle, 'i \<times> 'message call\<^sub>1, ('vkey, 'signature) ret\<^sub>1) oracle'"
where "oracle\<^sub>n \<eta> = family_oracle (\<lambda>_. oracle\<^sub>1 \<eta>)"

lemma oracle\<^sub>n_apply [simp]:
  "oracle\<^sub>n \<eta> s (i, x) = map_spmf (apsnd (fun_upd s i)) (oracle\<^sub>1 \<eta> (s i) x)"
by(simp add: oracle\<^sub>n_def)

type_synonym ('i, 'vkey', 'message', 'signature') adversary\<^sub>n' = 
  "(('i \<times> 'message' \<times> 'signature'), 'i \<times> 'message' call\<^sub>1, ('vkey', 'signature') ret\<^sub>1) gpv"
type_synonym ('i, 'vkey', 'message', 'signature') adversary\<^sub>n =
  "security \<Rightarrow> ('i, 'vkey', 'message', 'signature') adversary\<^sub>n'"

definition suf_cma\<^sub>n :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n \<Rightarrow> security \<Rightarrow> bool spmf"
where
  "\<And>log. suf_cma\<^sub>n \<A> \<eta> = do {
    ((i, m, sig), \<sigma>) \<leftarrow> exec_gpv (oracle\<^sub>n \<eta>) (\<A> \<eta>) (\<lambda>_. None);
    return_spmf (
      case \<sigma> i of None \<Rightarrow> False
      | Some (vkey, skey, log) \<Rightarrow> verify \<eta> vkey m sig \<and> (m, sig) \<notin> set log)
  }"

definition advantage\<^sub>n :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n \<Rightarrow> advantage"
where "advantage\<^sub>n \<A> \<eta> = spmf (suf_cma\<^sub>n \<A> \<eta>) True"

lemma advantage\<^sub>n_nonneg: "advantage\<^sub>n \<A> \<eta> \<ge> 0" by(simp add: advantage\<^sub>n_def pmf_nonneg)

abbreviation secure_for\<^sub>n :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n \<Rightarrow> bool"
where "secure_for\<^sub>n \<A> \<equiv> negligible (advantage\<^sub>n \<A>)"

definition ibounded_by\<^sub>n' :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n' \<Rightarrow> nat \<Rightarrow> bool"
where "ibounded_by\<^sub>n' \<A> q = (interaction_any_bounded_by \<A> q)"

abbreviation ibounded_by\<^sub>n :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n \<Rightarrow> (security \<Rightarrow> nat) \<Rightarrow> bool"
where "ibounded_by\<^sub>n \<equiv> rel_envir ibounded_by\<^sub>n'"

definition lossless\<^sub>n' :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n' \<Rightarrow> bool"
where "lossless\<^sub>n' \<A> = (lossless_gpv \<I>_full \<A>)"

abbreviation lossless\<^sub>n :: "('i, 'vkey, 'message, 'signature) adversary\<^sub>n \<Rightarrow> bool"
where "lossless\<^sub>n \<equiv> pred_envir lossless\<^sub>n'"

end

end
