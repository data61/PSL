(* Title: IND_CCA2_sym.thy
  Author: Andreas Lochbihler, ETH Zurich 
  Author: S. Reza Sefidgar, ETH Zurich *)

subsection \<open>The IND-CCA2 security for symmetric encryption schemes\<close>

theory IND_CCA2_sym imports
  CryptHOL.Computational_Model
begin

locale ind_cca =
  fixes key_gen :: "'key spmf"
  and encrypt :: "'key \<Rightarrow> 'message \<Rightarrow> 'cipher spmf"
  and decrypt :: "'key \<Rightarrow> 'cipher \<Rightarrow> 'message option"
  and msg_predicate :: "'message \<Rightarrow> bool"
begin

type_synonym ('message', 'cipher') adversary = 
  "(bool, 'message' \<times> 'message' + 'cipher', 'cipher' option + 'message' option) gpv"

definition oracle_encrypt :: "'key \<Rightarrow> bool \<Rightarrow> ('message \<times> 'message, 'cipher option, 'cipher set) callee"
where
  "oracle_encrypt k b L = (\<lambda>(msg1, msg0).
     (case msg_predicate msg1 \<and> msg_predicate msg0 of
        True \<Rightarrow> do {
         c \<leftarrow> encrypt k (if b then msg1 else msg0);
         return_spmf (Some c, {c} \<union> L)
        }
     | False \<Rightarrow> return_spmf (None, L)))"

lemma lossless_oracle_encrypt [simp]:
  assumes "lossless_spmf (encrypt k m1)" and "lossless_spmf (encrypt k m0)"
  shows "lossless_spmf (oracle_encrypt k b L (m1, m0))"
using assms by (simp add: oracle_encrypt_def split: bool.split)

definition oracle_decrypt :: "'key \<Rightarrow> ('cipher, 'message option, 'cipher set) callee"
where "oracle_decrypt k L c = return_spmf (if c \<in> L then None else decrypt k c, L)"

lemma lossless_oracle_decrypt [simp]: "lossless_spmf (oracle_decrypt k L c)"
by(simp add: oracle_decrypt_def)

definition game :: "('message, 'cipher) adversary \<Rightarrow> bool spmf"
where
  "game \<A> = do {
    key \<leftarrow> key_gen;
    b \<leftarrow> coin_spmf;
    (b', L') \<leftarrow> exec_gpv (oracle_encrypt key b \<oplus>\<^sub>O oracle_decrypt key) \<A> {};
    return_spmf (b = b')
  }"

definition advantage :: "('message, 'cipher) adversary \<Rightarrow> real"
where "advantage \<A> = \<bar>spmf (game \<A>) True - 1 / 2\<bar>"

lemma advantage_nonneg: "0 \<le> advantage \<A>" by(simp add: advantage_def)

end

end
