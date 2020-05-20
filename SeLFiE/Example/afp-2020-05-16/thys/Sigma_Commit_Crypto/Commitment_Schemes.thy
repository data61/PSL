section\<open>Commitment Schemes\<close>

text\<open>A commitment scheme is a two party Cryptographic protocol run between a committer and a verifier.
They allow the committer to commit to a chosen value while at a later time reveal the value. A commitment
scheme is composed of three algorithms, the key generation, the commitment and the verification algorithms.
 
The two main properties of commitment schemes are hiding and binding.\<close>


text\<open>Hiding is the property that the commitment leaks no information about the committed value, and 
binding is the property that the committer cannot reveal their a different message to the one they
committed to; that is they are bound to their commitment. We follow the game based approach \cite{DBLP:journals/iacr/Shoup04} to
define security. A game is played between an adversary and a challenger.\<close>

theory Commitment_Schemes imports
  CryptHOL.CryptHOL
begin

subsection\<open>Defining security\<close>
text\<open>Here we define the hiding, binding and correctness properties of commitment schemes.\<close> 

text\<open>We provide the types of the adversaries that take part in the hiding and binding games. We consider 
two variants of the hiding property, one stronger than the other --- thus we provide two hiding adversaries.
The first hiding property we consider is analogous to the IND-CPA property for encryption schemes, the second, 
weaker notion, does not allow the adversary to choose the messages used in the game, instead they are sampled 
from a set distribution.\<close>

type_synonym ('vk', 'plain', 'commit', 'state) hid_adv = 
  "('vk' \<Rightarrow> (('plain' \<times> 'plain') \<times> 'state) spmf)
   \<times> ('commit' \<Rightarrow> 'state \<Rightarrow> bool spmf)"

type_synonym 'commit' hid = "'commit' \<Rightarrow> bool spmf"

type_synonym ('ck', 'plain', 'commit', 'opening')  bind_adversary = 
  "'ck' \<Rightarrow> ('commit' \<times> 'plain' \<times> 'opening' \<times> 'plain' \<times> 'opening') spmf"

text\<open>We fix the algorithms that make up a commitment scheme in the locale.\<close>

locale abstract_commitment =
  fixes key_gen :: "('ck \<times> 'vk) spmf" \<comment> \<open>outputs the keys received by the two parties\<close>
    and commit :: "'ck \<Rightarrow> 'plain \<Rightarrow> ('commit \<times> 'opening) spmf" \<comment> \<open>outputs the commitment as well as the opening values sent by the committer in the reveal phase\<close>
    and verify :: "'vk \<Rightarrow> 'plain \<Rightarrow> 'commit \<Rightarrow> 'opening \<Rightarrow> bool" 
    and valid_msg :: "'plain \<Rightarrow> bool" \<comment> \<open>checks whether a message is valid, used in the hiding game\<close>
begin

definition "valid_msg_set = {m. valid_msg m}"

definition lossless :: "('pub_key, 'plain, 'commit, 'state) hid_adv \<Rightarrow> bool"
  where "lossless \<A> \<longleftrightarrow>
   ((\<forall>pk. lossless_spmf (fst \<A> pk)) \<and>
        (\<forall>commit \<sigma>. lossless_spmf (snd \<A> commit \<sigma>)))"

text\<open>The correct game runs the three algorithms that make up commitment schemes and outputs the output
of the verification algorithm.\<close>

definition correct_game :: "'plain \<Rightarrow> bool spmf"
  where "correct_game m = do {
  (ck, vk) \<leftarrow> key_gen;
  (c,d) \<leftarrow> commit ck m;
  return_spmf (verify vk m c d)}"

lemma   "\<lbrakk> lossless_spmf key_gen; lossless_spmf TI;
          \<And>pk m. valid_msg m \<Longrightarrow> lossless_spmf (commit pk m) \<rbrakk>
              \<Longrightarrow> valid_msg m \<Longrightarrow> lossless_spmf (correct_game m)"
  by(simp add: lossless_def correct_game_def split_def Let_def)

definition correct where "correct \<equiv> (\<forall>m. valid_msg m \<longrightarrow> spmf (correct_game m) True = 1)"

text\<open>The hiding property is defined using the hiding game. Here the adversary is asked to output two
messages, the challenger flips a coin to decide which message to commit and hand to the adversary.
The adversary's challenge is to guess which commitment it was handed. Note we must check the two 
messages outputted by the adversary are valid.\<close>

primrec hiding_game_ind_cpa :: "('vk, 'plain, 'commit, 'state) hid_adv \<Rightarrow> bool spmf"
  where "hiding_game_ind_cpa (\<A>1, \<A>2) = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  b \<leftarrow> coin_spmf; 
  (c,d) \<leftarrow> commit ck (if b then m0 else m1);
  b' :: bool \<leftarrow> \<A>2 c \<sigma>;
  return_spmf (b' = b)} ELSE coin_spmf"

text\<open>The adversary wins the game if \<open>b = b'\<close>.\<close>

lemma lossless_hiding_game:
  "\<lbrakk> lossless \<A>; lossless_spmf key_gen;
     \<And>pk plain. valid_msg plain \<Longrightarrow> lossless_spmf (commit pk plain) \<rbrakk>
  \<Longrightarrow> lossless_spmf (hiding_game_ind_cpa \<A>)"
  by(auto simp add: lossless_def hiding_game_ind_cpa_def split_def Let_def)

text\<open>To define security we consider the advantage an adversary has of winning the game over a tossing 
a coin to determine their output.\<close>

definition hiding_advantage_ind_cpa :: "('vk, 'plain, 'commit, 'state) hid_adv \<Rightarrow> real"
  where "hiding_advantage_ind_cpa \<A> \<equiv> \<bar>spmf (hiding_game_ind_cpa \<A>) True - 1/2\<bar>"

definition perfect_hiding_ind_cpa :: "('vk, 'plain, 'commit, 'state) hid_adv \<Rightarrow> bool"
  where "perfect_hiding_ind_cpa \<A> \<equiv> (hiding_advantage_ind_cpa \<A> = 0)"

  text\<open>The binding game challenges an adversary to bind two messages to the same committed value. Both
opening values and messages are verified with respect to the same committed value, the adversary wins
if the game outputs true. We must check some conditions of the adversaries output are met;
we will always require that \<open>m \<noteq> m'\<close>, other conditions will be dependent on the protocol for example 
we may require group or field membership.\<close>

definition bind_game :: "('ck, 'plain, 'commit, 'opening) bind_adversary \<Rightarrow> bool spmf"
  where "bind_game \<A> = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (c, m, d, m', d') \<leftarrow> \<A> ck;
  _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
  let b = verify vk m c d;
  let b' = verify vk m' c d';
  return_spmf (b \<and> b')} ELSE return_spmf False"

text\<open>We proof the binding game is equivalent to the following game which is easier to work with. In particular 
we assert b and b' in the game and return True.\<close>

lemma bind_game_alt_def:
  "bind_game \<A> = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (c, m, d, m', d') \<leftarrow> \<A> ck;
  _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
  let b = verify vk m c d;
  let b' = verify vk m' c d';
  _ :: unit \<leftarrow> assert_spmf (b \<and> b'); 
  return_spmf True} ELSE return_spmf False"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = TRY do {
      (ck, vk) \<leftarrow> key_gen;
      TRY do {
        (c, m, d, m', d') \<leftarrow> \<A> ck;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
          TRY return_spmf (verify vk m c d \<and> verify vk m' c d') ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    unfolding split_def bind_game_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  also have "\<dots> = TRY do {
      (ck, vk) \<leftarrow> key_gen;
      TRY do {
        (c, m, d, m', d') \<leftarrow> \<A> ck;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');
          TRY do {
            _ :: unit \<leftarrow> assert_spmf (verify vk m c d \<and> verify vk m' c d');
            return_spmf True
          } ELSE return_spmf False
        } ELSE return_spmf False
      } ELSE return_spmf False
    } ELSE return_spmf False"
    by(auto simp add: try_bind_assert_spmf try_spmf_return_spmf1 intro!: try_spmf_cong bind_spmf_cong)
  also have "\<dots> = ?rhs"
    unfolding split_def Let_def
    by(fold try_bind_spmf_lossless2[OF lossless_return_spmf]) simp
  finally show ?thesis .
qed

lemma lossless_binding_game: "lossless_spmf (bind_game \<A>)" 
  by (simp add: bind_game_def)

definition bind_advantage :: "('ck, 'plain, 'commit, 'opening) bind_adversary \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"

end

end