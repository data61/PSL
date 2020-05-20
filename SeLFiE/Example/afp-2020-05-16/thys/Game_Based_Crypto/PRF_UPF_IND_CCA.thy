(* Title: PRF_UPF_IND_CCA.thy
  Author: Andreas Lochbihler, ETH Zurich 
  Author: S. Reza Sefidgar, ETH Zurich *)

subsection \<open>IND-CCA from a PRF and an unpredictable function\<close>

theory PRF_UPF_IND_CCA
imports
  Pseudo_Random_Function
  CryptHOL.List_Bits
  Unpredictable_Function
  IND_CCA2_sym
  CryptHOL.Negligible
begin

text \<open>Formalisation of Shoup's construction of an IND-CCA secure cipher from a PRF and an unpredictable function \cite[\S 7]{Shoup2004IACR}.\<close>

type_synonym bitstring = "bool list"

locale simple_cipher = 
  PRF: "prf" prf_key_gen prf_fun "spmf_of_set (nlists UNIV prf_clen)" +
  UPF: upf upf_key_gen upf_fun
  for prf_key_gen :: "'prf_key spmf"
  and prf_fun :: "'prf_key \<Rightarrow> bitstring \<Rightarrow> bitstring"
  and prf_domain :: "bitstring set"
  and prf_range :: "bitstring set"
  and prf_dlen :: nat
  and prf_clen :: nat
  and upf_key_gen :: "'upf_key spmf"
  and upf_fun :: "'upf_key \<Rightarrow> bitstring \<Rightarrow> 'hash"
  +
  assumes prf_domain_finite: "finite prf_domain"
  assumes prf_domain_nonempty: "prf_domain \<noteq> {}"
  assumes prf_domain_length:  "x \<in> prf_domain \<Longrightarrow> length x = prf_dlen"
  assumes prf_codomain_length: 
    "\<lbrakk> key_prf \<in> set_spmf prf_key_gen; m \<in> prf_domain \<rbrakk> \<Longrightarrow> length (prf_fun key_prf m) = prf_clen"
  assumes prf_key_gen_lossless: "lossless_spmf prf_key_gen"
  assumes upf_key_gen_lossless: "lossless_spmf upf_key_gen"
begin

type_synonym 'hash' cipher_text = "bitstring \<times> bitstring \<times> 'hash'"

definition key_gen :: "('prf_key \<times> 'upf_key) spmf" where
 "key_gen = do {
   k_prf \<leftarrow> prf_key_gen;
   k_upf :: 'upf_key \<leftarrow> upf_key_gen;
   return_spmf (k_prf, k_upf)
 }"

lemma lossless_key_gen [simp]: "lossless_spmf key_gen"
  by(simp add: key_gen_def prf_key_gen_lossless upf_key_gen_lossless)

fun encrypt :: "('prf_key \<times> 'upf_key) \<Rightarrow> bitstring \<Rightarrow> 'hash cipher_text spmf"
where
  "encrypt (k_prf, k_upf) m = do {
    x \<leftarrow> spmf_of_set prf_domain;
    let c = prf_fun k_prf x [\<oplus>] m;
    let t = upf_fun k_upf (x @ c);
    return_spmf ((x, c, t))
  }"

lemma lossless_encrypt [simp]: "lossless_spmf (encrypt k m)"
  by (cases k) (simp add: Let_def prf_domain_nonempty prf_domain_finite split: bool.split)

fun decrypt :: "('prf_key \<times> 'upf_key) \<Rightarrow> 'hash cipher_text \<Rightarrow> bitstring option"
where
  "decrypt (k_prf, k_upf) (x, c, t) = (
    if upf_fun k_upf (x @ c) = t \<and> length x = prf_dlen then
      Some (prf_fun k_prf x [\<oplus>] c)
    else
      None
  )"

lemma cipher_correct:
  "\<lbrakk> k \<in> set_spmf key_gen; length m = prf_clen \<rbrakk>
  \<Longrightarrow> encrypt k m \<bind> (\<lambda>c. return_spmf (decrypt k c)) = return_spmf (Some m)"
by (cases k) (simp add: prf_domain_nonempty prf_domain_finite prf_domain_length
  prf_codomain_length key_gen_def bind_eq_return_spmf Let_def)

declare encrypt.simps[simp del]

sublocale ind_cca: ind_cca key_gen encrypt decrypt "\<lambda>m. length m = prf_clen" .
interpretation ind_cca': ind_cca key_gen encrypt "\<lambda> _ _. None" "\<lambda>m. length m = prf_clen" .

definition intercept_upf_enc
  :: "'prf_key \<Rightarrow> bool \<Rightarrow> 'hash cipher_text set \<times> 'hash cipher_text set \<Rightarrow> bitstring \<times> bitstring
  \<Rightarrow> ('hash cipher_text option \<times> ('hash cipher_text set \<times> 'hash cipher_text set),
     bitstring + (bitstring \<times> 'hash), 'hash + unit) gpv" 
where 
  "intercept_upf_enc k b = (\<lambda>(L, D) (m1, m0).
    (case (length m1 = prf_clen \<and> length m0 = prf_clen) of
      False \<Rightarrow> Done (None, L, D)
    | True \<Rightarrow> do {
        x \<leftarrow> lift_spmf (spmf_of_set prf_domain);
        let c = prf_fun k x [\<oplus>] (if b then m1 else m0);
        t \<leftarrow> Pause (Inl (x @ c)) Done;
        Done ((Some (x, c, projl t)), (insert (x, c, projl t) L, D))
      }))"

definition intercept_upf_dec
  :: "'hash cipher_text set \<times> 'hash cipher_text set \<Rightarrow> 'hash cipher_text
  \<Rightarrow> (bitstring option \<times> ('hash cipher_text set \<times> 'hash cipher_text set),
     bitstring + (bitstring \<times> 'hash), 'hash + unit) gpv" 
where
  "intercept_upf_dec = (\<lambda>(L, D) (x, c, t).
    if (x, c, t) \<in> L \<or> length x \<noteq> prf_dlen then Done (None, (L, D)) else do {
      Pause (Inr (x @ c, t)) Done;
      Done (None, (L, insert (x, c, t) D))
    })"

definition intercept_upf :: 
  "'prf_key \<Rightarrow> bool \<Rightarrow> 'hash cipher_text set \<times> 'hash cipher_text set \<Rightarrow> bitstring \<times> bitstring + 'hash cipher_text
  \<Rightarrow> (('hash cipher_text option + bitstring option) \<times> ('hash cipher_text set \<times> 'hash cipher_text set),
     bitstring + (bitstring \<times> 'hash), 'hash + unit) gpv" 
where
  "intercept_upf k b = plus_intercept (intercept_upf_enc k b) intercept_upf_dec"

lemma intercept_upf_simps [simp]:
  "intercept_upf k b (L, D) (Inr (x, c, t)) =
    (if (x, c, t) \<in> L \<or> length x \<noteq> prf_dlen then Done (Inr None, (L, D)) else do {
      Pause (Inr (x @ c, t)) Done;
      Done (Inr None, (L, insert (x, c, t) D))
    })"
  "intercept_upf k b (L, D) (Inl (m1, m0)) = 
    (case (length m1 = prf_clen \<and> length m0 = prf_clen) of
      False \<Rightarrow> Done (Inl None, L, D)
    | True \<Rightarrow> do {
        x \<leftarrow> lift_spmf (spmf_of_set prf_domain);
        let c = prf_fun k x [\<oplus>] (if b then m1 else m0);
        t \<leftarrow> Pause (Inl (x @ c)) Done;
        Done (Inl (Some (x, c, projl t)), (insert (x, c, projl t) L, D))
      })"
   by(simp_all add: intercept_upf_def intercept_upf_dec_def intercept_upf_enc_def o_def map_gpv_bind_gpv gpv.map_id Let_def split!: bool.split)


lemma interaction_bounded_by_upf_enc_Inr [interaction_bound]:
  "interaction_bounded_by (Not \<circ> isl) (intercept_upf_enc k b LD mm) 0"
unfolding intercept_upf_enc_def case_prod_app
by(interaction_bound, clarsimp simp add: SUP_constant bot_enat_def split: prod.split)

lemma interaction_bounded_by_upf_dec_Inr [interaction_bound]:
  "interaction_bounded_by (Not \<circ> isl) (intercept_upf_dec LD c) 1"
unfolding intercept_upf_dec_def case_prod_app
by(interaction_bound, clarsimp simp add: SUP_constant split: prod.split)

lemma interaction_bounded_by_intercept_upf_Inr [interaction_bound]:
  "interaction_bounded_by (Not \<circ> isl) (intercept_upf k b LD x) 1"
unfolding intercept_upf_def 
by interaction_bound(simp add: split_def one_enat_def SUP_le_iff split: sum.split)

lemma interaction_bounded_by_intercept_upf_Inl [interaction_bound]:
  "isl x \<Longrightarrow> interaction_bounded_by (Not \<circ> isl) (intercept_upf k b LD x) 0"
unfolding intercept_upf_def case_prod_app
by interaction_bound(auto split: sum.split)

lemma lossless_intercept_upf_enc [simp]: "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (intercept_upf_enc k b LD mm)"
by(simp add: intercept_upf_enc_def split_beta prf_domain_finite prf_domain_nonempty Let_def split: bool.split)

lemma lossless_intercept_upf_dec [simp]: "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (intercept_upf_dec LD mm)"
by(simp add: intercept_upf_dec_def split_beta)

lemma lossless_intercept_upf [simp]: "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (intercept_upf k b LD x)"
by(cases x)(simp_all add: intercept_upf_def)

lemma results_gpv_intercept_upf [simp]: "results_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (intercept_upf k b LD x) \<subseteq> responses_\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) x \<times> UNIV"
by(cases x)(auto simp add: intercept_upf_def)

definition reduction_upf :: "(bitstring, 'hash cipher_text) ind_cca.adversary
  \<Rightarrow> (bitstring, 'hash) UPF.adversary"
where "reduction_upf \<A> = do {
    k \<leftarrow> lift_spmf prf_key_gen;
    b \<leftarrow> lift_spmf coin_spmf;
    (_, (L, D)) \<leftarrow> inline (intercept_upf k b) \<A> ({}, {});
    Done () }"

lemma lossless_reduction_upf [simp]: 
  "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A> \<Longrightarrow> lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (reduction_upf \<A>)"
by(auto simp add: reduction_upf_def prf_key_gen_lossless intro: lossless_inline del: subsetI)

context includes lifting_syntax begin

lemma round_1:
  assumes "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A>"
  shows "\<bar>spmf (ind_cca.game \<A>) True - spmf (ind_cca'.game \<A>) True\<bar> \<le> UPF.advantage (reduction_upf \<A>)" 
proof -
  define oracle_decrypt0' where "oracle_decrypt0' \<equiv> (\<lambda>key (bad, L) (x', c', t'). return_spmf (
      if (x', c', t') \<in> L \<or> length x' \<noteq> prf_dlen then (None, (bad, L))
      else (decrypt key (x', c', t'), (bad \<or> upf_fun (snd key) (x' @ c') = t', L))))"
  have oracle_decrypt0'_simps:
    "oracle_decrypt0' key (bad, L) (x', c', t') = return_spmf (
       if (x', c', t') \<in> L \<or> length x' \<noteq> prf_dlen then (None, (bad, L))
       else (decrypt key (x', c', t'), (bad \<or> upf_fun (snd key) (x' @ c') = t', L)))"
    for key L bad x' c' t' by(simp add: oracle_decrypt0'_def)
  have lossless_oracle_decrypt0' [simp]: "lossless_spmf (oracle_decrypt0' k Lbad c)" for k Lbad c
    by(simp add: oracle_decrypt0'_def split_def)
  have callee_invariant_oracle_decrypt0' [simp]: "callee_invariant (oracle_decrypt0' k) fst" for k
    by (unfold_locales) (auto simp add: oracle_decrypt0'_def split: if_split_asm)

  define oracle_decrypt1'
    where "oracle_decrypt1' = (\<lambda>(key :: 'prf_key \<times> 'upf_key) (bad, L) (x', c', t'). 
      return_spmf (None :: bitstring option,
        (bad \<or> upf_fun (snd key) (x' @ c') = t' \<and> (x', c', t') \<notin> L \<and> length x' = prf_dlen), L))"
  have oracle_decrypt1'_simps:
    "oracle_decrypt1' key (bad, L) (x', c', t') = 
    return_spmf (None, 
      (bad \<or> upf_fun (snd key) (x' @ c') = t' \<and> (x', c', t') \<notin> L \<and> length x' = prf_dlen, L))"
    for key L bad x' c' t' by(simp add: oracle_decrypt1'_def)
  have lossless_oracle_decrypt1' [simp]: "lossless_spmf (oracle_decrypt1' k Lbad c)" for k Lbad c
    by(simp add: oracle_decrypt1'_def split_def)
  have callee_invariant_oracle_decrypt1' [simp]: "callee_invariant (oracle_decrypt1' k) fst" for k
    by (unfold_locales) (auto simp add: oracle_decrypt1'_def)

  define game01'
    where "game01' = (\<lambda>(decrypt :: 'prf_key \<times> 'upf_key \<Rightarrow> (bitstring \<times> bitstring \<times> 'hash, bitstring option, bool \<times> (bitstring \<times> bitstring \<times> 'hash) set) callee) \<A>. do {
    key \<leftarrow> key_gen;
    b \<leftarrow> coin_spmf;
    (b', (bad', L')) \<leftarrow> exec_gpv (\<dagger>(ind_cca.oracle_encrypt key b) \<oplus>\<^sub>O decrypt key) \<A> (False, {});
    return_spmf (b = b', bad') })"
  let ?game0' = "game01' oracle_decrypt0'"
  let ?game1' = "game01' oracle_decrypt1'"

  have game0'_eq: "ind_cca.game \<A> = map_spmf fst (?game0' \<A>)" (is ?game0)
    and game1'_eq: "ind_cca'.game \<A> = map_spmf fst (?game1' \<A>)" (is ?game1)
  proof -
    let ?S = "rel_prod2 (=)"
    define initial where "initial = (False, {} :: 'hash cipher_text set)"
    have [transfer_rule]: "?S {} initial" by(simp add: initial_def)

    have [transfer_rule]: 
      "((=) ===> ?S ===> (=) ===> rel_spmf (rel_prod (=) ?S))
       ind_cca.oracle_decrypt oracle_decrypt0'"
      unfolding ind_cca.oracle_decrypt_def[abs_def] oracle_decrypt0'_def[abs_def]
      by(simp add: rel_spmf_return_spmf1 rel_fun_def)

    have [transfer_rule]: 
      "((=) ===> ?S ===> (=) ===> rel_spmf (rel_prod (=) ?S))
       ind_cca'.oracle_decrypt oracle_decrypt1'"
      unfolding ind_cca'.oracle_decrypt_def[abs_def] oracle_decrypt1'_def[abs_def]
      by (simp add: rel_spmf_return_spmf1 rel_fun_def)

    note [transfer_rule] = extend_state_oracle_transfer
    show ?game0 ?game1 unfolding game01'_def ind_cca.game_def ind_cca'.game_def initial_def[symmetric]
      by (simp_all add: map_spmf_bind_spmf o_def split_def) transfer_prover+
  qed

  have *: "rel_spmf (\<lambda>(b'1, (bad1, L1)) (b'2, (bad2, L2)). bad1 = bad2 \<and> (\<not> bad2 \<longrightarrow> b'1 = b'2))
         (exec_gpv (\<dagger>(ind_cca.oracle_encrypt k b) \<oplus>\<^sub>O oracle_decrypt1' k) \<A> (False, {}))
         (exec_gpv (\<dagger>(ind_cca.oracle_encrypt k b) \<oplus>\<^sub>O oracle_decrypt0' k) \<A> (False, {}))"
    for k b
    by (cases k; rule exec_gpv_oracle_bisim_bad[where X="(=)" and ?bad1.0=fst and ?bad2.0=fst and \<I> = "\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
       (auto intro: rel_spmf_reflI callee_invariant_extend_state_oracle_const' simp add: spmf_rel_map1 spmf_rel_map2 oracle_decrypt0'_simps oracle_decrypt1'_simps assms split: plus_oracle_split)
    \<comment> \<open>We cannot get rid of the losslessness assumption on @{term \<A>} in this step, because if it 
      were not, then the bad event might still occur, but the adversary does not terminate in
      the case of @{term "?game1'"}. Thus, the reduction does not terminate either, but it cannot
      detect whether the bad event has happened. So the advantage in the UPF game could be lower than
      the probability of the bad event, if the adversary is not lossless.\<close>
  have "\<bar>measure (measure_spmf (?game1' \<A>)) {(b, bad). b} - measure (measure_spmf (?game0' \<A>)) {(b, bad). b}\<bar> 
     \<le> measure (measure_spmf (?game1' \<A>)) {(b, bad). bad}"
    by (rule fundamental_lemma[where ?bad2.0=snd])(auto intro!: rel_spmf_bind_reflI rel_spmf_bindI[OF *] simp add: game01'_def)
  also have "\<dots> = spmf (map_spmf snd (?game1' \<A>)) True"
    by (simp add: spmf_conv_measure_spmf measure_map_spmf split_def vimage_def)
  also have "map_spmf snd (?game1' \<A>) = UPF.game (reduction_upf \<A>)"
  proof -
    note [split del] = if_split
    have "map_spmf (\<lambda>x. fst (snd x)) (exec_gpv (\<dagger>(ind_cca.oracle_encrypt (k_prf, k_upf) b) \<oplus>\<^sub>O oracle_decrypt1' (k_prf, k_upf)) \<A> (False, {})) = 
        map_spmf (\<lambda>x. fst (snd x)) (exec_gpv (UPF.oracle k_upf) (inline (intercept_upf k_prf b) \<A> ({}, {})) (False, {}))"
      (is "map_spmf ?fl ?lhs = map_spmf ?fr ?rhs" is "map_spmf _ (exec_gpv ?oracle_normal _ ?init_normal) = _")
      for k_prf k_upf b
    proof(rule map_spmf_eq_map_spmfI)
      define oracle_intercept
        where [simp]: "oracle_intercept = (\<lambda>(s', s) y. map_spmf (\<lambda>((x, s'), s). (x, s', s))
         (exec_gpv (UPF.oracle k_upf) (intercept_upf k_prf b s' y) s))"
      let ?I = "(\<lambda>((L, D), (flg, Li)).
          (\<forall>(x, c, t) \<in> L. upf_fun k_upf (x @ c) = t \<and> length x = prf_dlen) \<and>
          (\<forall>e\<in>Li. \<exists>(x,c,_) \<in> L. e = x @ c) \<and>
          ((\<exists>(x, c, t) \<in> D. upf_fun k_upf (x @ c) = t) \<longleftrightarrow> flg))"
      interpret callee_invariant_on oracle_intercept "?I" \<I>_full
        apply(unfold_locales)
        subgoal for s x y s'
          apply(cases s; cases s'; cases x)
           apply(clarsimp simp add: set_spmf_of_set_finite[OF prf_domain_finite]
                UPF.oracle_hash_def prf_domain_length exec_gpv_bind Let_def split: bool.splits)
          apply(force simp add: exec_gpv_bind UPF.oracle_flag_def split: if_split_asm)
          done
        subgoal by simp
        done
      
      define S :: "bool \<times> 'hash cipher_text set \<Rightarrow> ('hash cipher_text set \<times> 'hash cipher_text set) \<times>  bool \<times> bitstring set \<Rightarrow> bool"
        where "S = (\<lambda>(bad, L1) ((L2, D), _). bad = (\<exists>(x, c, t)\<in>D. upf_fun k_upf (x @ c) = t) \<and> L1 = L2) \<upharpoonleft> (\<lambda>_. True) \<otimes> ?I"
      define initial :: "('hash cipher_text set \<times> 'hash cipher_text set) \<times>  bool \<times> bitstring set"
        where "initial = (({}, {}), (False, {}))"
      have [transfer_rule]: "S ?init_normal initial" by(simp add: S_def initial_def)
      have [transfer_rule]: "(S ===> (=) ===> rel_spmf (rel_prod (=) S)) ?oracle_normal oracle_intercept"
        unfolding S_def
        by(rule callee_invariant_restrict_relp, unfold_locales)
          (auto simp add: rel_fun_def bind_spmf_of_set prf_domain_finite prf_domain_nonempty bind_spmf_pmf_assoc bind_assoc_pmf bind_return_pmf spmf_rel_map exec_gpv_bind Let_def ind_cca.oracle_encrypt_def oracle_decrypt1'_def encrypt.simps UPF.oracle_hash_def UPF.oracle_flag_def bind_map_spmf o_def split: plus_oracle_split bool.split if_split intro!: rel_spmf_bind_reflI rel_pmf_bind_reflI)
      have "rel_spmf (rel_prod (=) S) ?lhs (exec_gpv oracle_intercept \<A> initial)"
        by(transfer_prover)
      then show "rel_spmf (\<lambda>x y. ?fl x = ?fr y) ?lhs ?rhs"
        by(auto simp add: S_def exec_gpv_inline spmf_rel_map initial_def elim: rel_spmf_mono)
    qed
    then show ?thesis including monad_normalisation
      by(auto simp add: reduction_upf_def UPF.game_def game01'_def key_gen_def map_spmf_conv_bind_spmf split_def exec_gpv_bind intro!: bind_spmf_cong[OF refl])
  qed
  finally show ?thesis using game0'_eq game1'_eq 
    by (auto simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def fst_def UPF.advantage_def)
qed


definition oracle_encrypt2 :: 
  "('prf_key \<times> 'upf_key) \<Rightarrow> bool \<Rightarrow> (bitstring, bitstring) PRF.dict \<Rightarrow> bitstring \<times> bitstring 
    \<Rightarrow> ('hash cipher_text option \<times> (bitstring, bitstring) PRF.dict) spmf"
where
  "oracle_encrypt2 = (\<lambda>(k_prf, k_upf) b D (msg1, msg0). (case (length msg1 = prf_clen \<and> length msg0 = prf_clen) of
      False \<Rightarrow> return_spmf (None, D)
    | True \<Rightarrow> do {
        x \<leftarrow> spmf_of_set prf_domain;
        P \<leftarrow> spmf_of_set (nlists UNIV prf_clen);
        let p = (case D x of Some r \<Rightarrow> r | None \<Rightarrow> P);
        let c = p [\<oplus>] (if b then msg1 else msg0);
        let t = upf_fun k_upf (x @ c);
        return_spmf (Some (x, c, t), D(x \<mapsto> p)) 
      }))"

definition oracle_decrypt2:: "('prf_key \<times> 'upf_key) \<Rightarrow> ('hash cipher_text, bitstring option, 'state) callee"
where "oracle_decrypt2 = (\<lambda>key D cipher. return_spmf (None, D))"

lemma lossless_oracle_decrypt2 [simp]: "lossless_spmf (oracle_decrypt2 k Dbad c)"
  by(simp add: oracle_decrypt2_def split_def)

lemma callee_invariant_oracle_decrypt2 [simp]: "callee_invariant (oracle_decrypt2 key) fst"
  by (unfold_locales) (auto simp add: oracle_decrypt2_def split: if_split_asm)

lemma oracle_decrypt2_parametric [transfer_rule]:
  "(rel_prod P U ===> S ===> rel_prod (=) (rel_prod (=) H) ===> rel_spmf (rel_prod (=) S))
   oracle_decrypt2 oracle_decrypt2"
  unfolding oracle_decrypt2_def split_def relator_eq[symmetric] by transfer_prover

definition game2 :: "(bitstring, 'hash cipher_text) ind_cca.adversary \<Rightarrow> bool spmf" 
where 
  "game2 \<A> \<equiv> do {
    key \<leftarrow> key_gen;
    b \<leftarrow> coin_spmf;
    (b', D) \<leftarrow> exec_gpv 
      (oracle_encrypt2 key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> Map_empty;
    return_spmf (b = b')
  }"

fun intercept_prf :: 
  "'upf_key \<Rightarrow> bool \<Rightarrow> unit \<Rightarrow> (bitstring \<times> bitstring) + 'hash cipher_text
  \<Rightarrow> (('hash cipher_text option + bitstring option) \<times> unit, bitstring, bitstring) gpv" 
where
  "intercept_prf _ _ _ (Inr _) = Done (Inr None, ())"
| "intercept_prf k b _ (Inl (m1, m0)) = (case (length m1) = prf_clen \<and> (length m0) = prf_clen of
      False \<Rightarrow> Done (Inl None, ())
    | True \<Rightarrow> do {
        x \<leftarrow> lift_spmf (spmf_of_set prf_domain);
        p \<leftarrow> Pause x Done;
        let c = p [\<oplus>] (if b then m1 else m0);
        let t = upf_fun k (x @ c);
        Done (Inl (Some (x, c, t)), ())
      })"

definition reduction_prf
  :: "(bitstring, 'hash cipher_text) ind_cca.adversary \<Rightarrow> (bitstring, bitstring) PRF.adversary"
where 
 "reduction_prf \<A> = do {
   k \<leftarrow> lift_spmf upf_key_gen;
   b \<leftarrow> lift_spmf coin_spmf;
   (b', _) \<leftarrow> inline (intercept_prf k b) \<A> ();
   Done (b' = b)
 }"

lemma round_2: "\<bar>spmf (ind_cca'.game \<A>) True - spmf (game2 \<A>) True\<bar> = PRF.advantage (reduction_prf \<A>)" 
proof -
  define oracle_encrypt1''
    where "oracle_encrypt1'' = (\<lambda>(k_prf, k_upf) b (_ :: unit) (msg1, msg0). 
      case length msg1 = prf_clen \<and> length msg0 = prf_clen of
        False \<Rightarrow> return_spmf (None, ())
      | True \<Rightarrow> do {
          x \<leftarrow> spmf_of_set prf_domain;
          let p = prf_fun k_prf x;
          let c = p [\<oplus>] (if b then msg1 else msg0);
          let t = upf_fun k_upf (x @ c);
          return_spmf (Some (x, c, t), ())})"
  define game1'' where "game1'' = do {
    key \<leftarrow> key_gen;
    b \<leftarrow> coin_spmf;
    (b', D) \<leftarrow> exec_gpv (oracle_encrypt1'' key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> ();
    return_spmf (b = b')}"

  have "ind_cca'.game \<A> = game1''"
  proof -
    define S where "S = (\<lambda>(L :: 'hash cipher_text set) (D :: unit). True)"
    have [transfer_rule]: "S {} ()" by (simp add: S_def)
    have [transfer_rule]: 
      "((=) ===> (=) ===> S ===> (=) ===> rel_spmf (rel_prod (=) S))
       ind_cca'.oracle_encrypt oracle_encrypt1''"
      unfolding ind_cca'.oracle_encrypt_def[abs_def] oracle_encrypt1''_def[abs_def]
      by (auto simp add: rel_fun_def Let_def S_def encrypt.simps prf_domain_finite prf_domain_nonempty intro: rel_spmf_bind_reflI rel_pmf_bind_reflI split: bool.split)
    have [transfer_rule]:
      "((=) ===> S ===> (=) ===> rel_spmf (rel_prod (=) S)) 
       ind_cca'.oracle_decrypt oracle_decrypt2"
      unfolding ind_cca'.oracle_decrypt_def[abs_def] oracle_decrypt2_def[abs_def]
      by(auto simp add: rel_fun_def)
    show ?thesis unfolding ind_cca'.game_def game1''_def by transfer_prover
  qed

  also have "\<dots> = PRF.game_0 (reduction_prf \<A>)"
  proof -
    { fix k_prf k_upf b
      define oracle_normal
        where "oracle_normal = oracle_encrypt1'' (k_prf, k_upf) b \<oplus>\<^sub>O oracle_decrypt2 (k_prf, k_upf)"
      define oracle_intercept
        where "oracle_intercept = (\<lambda>(s', s :: unit) y. map_spmf (\<lambda>((x, s'), s). (x, s', s)) (exec_gpv (PRF.prf_oracle k_prf) (intercept_prf k_upf b s' y) ()))"
      define initial where "initial = ()"
      define S where "S = (\<lambda>(s2 :: unit, _ :: unit) (s1 :: unit). True)"
      have [transfer_rule]: "S ((), ()) initial" by(simp add: S_def initial_def)
      have [transfer_rule]: "(S ===> (=) ===> rel_spmf (rel_prod (=) S)) oracle_intercept oracle_normal"
        unfolding oracle_normal_def oracle_intercept_def
        by(auto split: bool.split plus_oracle_split simp add: S_def rel_fun_def exec_gpv_bind PRF.prf_oracle_def oracle_encrypt1''_def Let_def map_spmf_conv_bind_spmf oracle_decrypt2_def intro!: rel_spmf_bind_reflI rel_spmf_reflI)
      have "map_spmf (\<lambda>x. b = fst x) (exec_gpv oracle_normal \<A> initial) =
        map_spmf (\<lambda>x. b = fst (fst x)) (exec_gpv (PRF.prf_oracle k_prf) (inline (intercept_prf k_upf b) \<A> ()) ())"
        by(transfer fixing: b \<A> prf_fun k_prf prf_domain prf_clen upf_fun k_upf)
          (auto simp add: map_spmf_eq_map_spmf_iff exec_gpv_inline spmf_rel_map oracle_intercept_def split_def intro: rel_spmf_reflI) }
    then show ?thesis unfolding game1''_def PRF.game_0_def key_gen_def reduction_prf_def
      by (auto simp add: exec_gpv_bind_lift_spmf exec_gpv_bind map_spmf_conv_bind_spmf split_def eq_commute intro!: bind_spmf_cong[OF refl])
  qed
  also have "game2 \<A> = PRF.game_1 (reduction_prf \<A>)"
  proof -
    note [split del] = if_split
    { fix k_upf b k_prf
      define oracle2
        where "oracle2 = oracle_encrypt2 (k_prf, k_upf) b \<oplus>\<^sub>O oracle_decrypt2 (k_prf, k_upf)"
      define oracle_intercept
        where "oracle_intercept = (\<lambda>(s', s) y. map_spmf (\<lambda>((x, s'), s). (x, s', s)) (exec_gpv PRF.random_oracle (intercept_prf k_upf b s' y) s))"
      define S
        where "S = (\<lambda>(s2 :: unit, s2') (s1 :: (bitstring, bitstring) PRF.dict). s2' = s1)"

      have [transfer_rule]: "S ((), Map_empty) Map_empty" by(simp add: S_def)
      have [transfer_rule]: "(S ===> (=) ===> rel_spmf (rel_prod (=) S)) oracle_intercept oracle2"
        unfolding oracle2_def oracle_intercept_def
        by(auto split: bool.split plus_oracle_split option.split simp add: S_def rel_fun_def exec_gpv_bind PRF.random_oracle_def oracle_encrypt2_def Let_def map_spmf_conv_bind_spmf oracle_decrypt2_def rel_spmf_return_spmf1 fun_upd_idem intro!: rel_spmf_bind_reflI rel_spmf_reflI)

      have [symmetric]: "map_spmf (\<lambda>x. b = fst (fst x)) (exec_gpv (PRF.random_oracle) (inline (intercept_prf k_upf b) \<A> ()) Map.empty) = 
        map_spmf (\<lambda>x. b = fst x) (exec_gpv oracle2 \<A> Map_empty)"
        by(transfer fixing: b prf_clen prf_domain upf_fun k_upf \<A> k_prf)
          (simp add: exec_gpv_inline map_spmf_conv_bind_spmf[symmetric] spmf.map_comp o_def split_def oracle_intercept_def) }
    then show ?thesis
      unfolding game2_def PRF.game_1_def key_gen_def reduction_prf_def
      by (clarsimp simp add: exec_gpv_bind_lift_spmf exec_gpv_bind map_spmf_conv_bind_spmf split_def bind_spmf_const prf_key_gen_lossless lossless_weight_spmfD eq_commute)
  qed
  ultimately show ?thesis by(simp add: PRF.advantage_def)
qed


definition oracle_encrypt3 :: 
   "('prf_key \<times> 'upf_key) \<Rightarrow> bool \<Rightarrow> (bool \<times> (bitstring, bitstring) PRF.dict) \<Rightarrow>
    bitstring \<times> bitstring \<Rightarrow> ('hash cipher_text option \<times> (bool \<times> (bitstring, bitstring) PRF.dict)) spmf"
where
  "oracle_encrypt3 = (\<lambda>(k_prf, k_upf) b (bad, D) (msg1, msg0). 
    (case (length msg1 = prf_clen \<and> length msg0 = prf_clen) of
      False \<Rightarrow> return_spmf (None, (bad, D))
    | True \<Rightarrow> do {
        x \<leftarrow> spmf_of_set prf_domain;
        P \<leftarrow> spmf_of_set (nlists UNIV prf_clen);
        let (p, F) = (case D x of Some r \<Rightarrow> (P, True) | None \<Rightarrow> (P, False));
        let c = p [\<oplus>] (if b then msg1 else msg0);
        let t = upf_fun k_upf (x @ c);
        return_spmf (Some (x, c, t), (bad \<or> F, D(x \<mapsto> p))) 
      }))"

lemma lossless_oracle_encrypt3 [simp]:
  "lossless_spmf (oracle_encrypt3 k b D m10) "
  by (cases m10) (simp add: oracle_encrypt3_def prf_domain_nonempty prf_domain_finite
    split_def Let_def split: bool.splits)

lemma callee_invariant_oracle_encrypt3 [simp]: "callee_invariant (oracle_encrypt3 key b) fst"
  by (unfold_locales) (auto simp add: oracle_encrypt3_def split_def Let_def split: bool.splits)

definition game3 :: "(bitstring, 'hash cipher_text) ind_cca.adversary \<Rightarrow> (bool \<times> bool) spmf" 
where 
  "game3 \<A> \<equiv> do {
    key \<leftarrow> key_gen;
    b \<leftarrow> coin_spmf;
    (b', (bad, D)) \<leftarrow> exec_gpv (oracle_encrypt3 key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> (False, Map_empty);
    return_spmf (b = b', bad)
  }"

lemma round_3:
  assumes "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A>"
  shows "\<bar>measure (measure_spmf (game3 \<A>)) {(b, bad). b} - spmf (game2 \<A>) True\<bar> 
          \<le> measure (measure_spmf (game3 \<A>)) {(b, bad). bad}" 
proof -
  define oracle_encrypt2'
    where "oracle_encrypt2' = (\<lambda>(k_prf :: 'prf_key, k_upf) b (bad, D) (msg1, msg0). 
      case length msg1 = prf_clen \<and> length msg0 = prf_clen of
        False \<Rightarrow> return_spmf (None, (bad, D))
      | True \<Rightarrow> do {
          x \<leftarrow> spmf_of_set prf_domain;
          P \<leftarrow> spmf_of_set (nlists UNIV prf_clen);
          let (p, F) = (case D x of Some r \<Rightarrow> (r, True) | None \<Rightarrow> (P, False));
          let c = p [\<oplus>] (if b then msg1 else msg0);
          let t = upf_fun k_upf (x @ c);
          return_spmf (Some (x, c, t), (bad \<or> F, D(x \<mapsto> p))) 
        })"

  have [simp]: "lossless_spmf (oracle_encrypt2' key b D msg10) " for key b D msg10
    by (cases msg10) (simp add: oracle_encrypt2'_def prf_domain_nonempty prf_domain_finite
      split_def Let_def split: bool.split)
  have [simp]: "callee_invariant (oracle_encrypt2' key b) fst" for key b
    by (unfold_locales) (auto simp add: oracle_encrypt2'_def split_def Let_def split: bool.splits)

  define game2'
    where "game2' = (\<lambda>\<A>. do {
      key \<leftarrow> key_gen;
      b \<leftarrow> coin_spmf;
      (b', (bad, D)) \<leftarrow> exec_gpv (oracle_encrypt2' key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> (False, Map_empty);
      return_spmf (b = b', bad)})"

  have game2'_eq: "game2 \<A> = map_spmf fst (game2' \<A>)"
  proof -
    define S where "S = (\<lambda>(D1 :: (bitstring, bitstring) PRF.dict) (bad :: bool, D2). D1 = D2)"
    have [transfer_rule, simp]: "S Map_empty (b, Map_empty)" for b by (simp add: S_def)
  
    have [transfer_rule]: "((=) ===> (=) ===> S ===> (=) ===> rel_spmf (rel_prod (=) S))
      oracle_encrypt2 oracle_encrypt2'"
      unfolding oracle_encrypt2_def[abs_def] oracle_encrypt2'_def[abs_def]
      by (auto simp add: rel_fun_def Let_def split_def S_def
           intro!: rel_spmf_bind_reflI split: bool.split option.split)
    have [transfer_rule]: "((=) ===> S ===> (=) ===> rel_spmf (rel_prod (=) S)) 
      oracle_decrypt2 oracle_decrypt2"
      by(auto simp add: rel_fun_def oracle_decrypt2_def)

    show ?thesis unfolding game2_def game2'_def
      by (simp add: map_spmf_bind_spmf o_def split_def Map_empty_def[symmetric] del: Map_empty_def)
         transfer_prover
  qed
  moreover have *: "rel_spmf (\<lambda>(b'1, bad1, L1) (b'2, bad2, L2). (bad1 \<longleftrightarrow> bad2) \<and> (\<not> bad2 \<longrightarrow> b'1 \<longleftrightarrow> b'2))
    (exec_gpv (oracle_encrypt3 key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> (False, Map_empty))
    (exec_gpv (oracle_encrypt2' key b \<oplus>\<^sub>O oracle_decrypt2 key) \<A> (False, Map_empty))"
    for key b
    apply(rule exec_gpv_oracle_bisim_bad[where X="(=)" and X_bad = "\<lambda>_ _. True" and ?bad1.0=fst and ?bad2.0=fst and \<I>="\<I>_full \<oplus>\<^sub>\<I> \<I>_full"])
    apply(simp_all add: assms)
    apply(auto simp add: assms spmf_rel_map Let_def oracle_encrypt2'_def oracle_encrypt3_def split: plus_oracle_split prod.split bool.split option.split intro!: rel_spmf_bind_reflI rel_spmf_reflI)
    done
  have "\<bar>measure (measure_spmf (game3 \<A>)) {(b, bad). b} - measure (measure_spmf (game2' \<A>)) {(b, bad). b}\<bar> \<le>
    measure (measure_spmf (game3 \<A>)) {(b, bad). bad}"
    unfolding game2'_def game3_def
    by(rule fundamental_lemma[where ?bad2.0=snd])(intro rel_spmf_bind_reflI rel_spmf_bindI[OF *]; clarsimp)
  ultimately show ?thesis by(simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def fst_def)
qed

lemma round_4:
  assumes "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A>"
  shows "map_spmf fst (game3 \<A>) = coin_spmf" 
proof -
  define oracle_encrypt4
    where "oracle_encrypt4 = (\<lambda>(k_prf :: 'prf_key, k_upf) (s :: unit) (msg1 :: bitstring, msg0 :: bitstring).
      case length msg1 = prf_clen \<and> length msg0 = prf_clen of
        False \<Rightarrow> return_spmf (None, s)
      | True \<Rightarrow> do {
          x \<leftarrow> spmf_of_set prf_domain;
          P \<leftarrow> spmf_of_set (nlists UNIV prf_clen);
          let c = P;
          let t = upf_fun k_upf (x @ c);
          return_spmf (Some (x, c, t), s) })"

  have [simp]: "lossless_spmf (oracle_encrypt4 k s msg10)" for k s msg10 
    by (cases msg10) (simp add: oracle_encrypt4_def prf_domain_finite prf_domain_nonempty
      split_def Let_def split: bool.splits)

  define game4 where "game4 = (\<lambda>\<A>. do {
    key \<leftarrow> key_gen;
    (b', _) \<leftarrow> exec_gpv (oracle_encrypt4 key \<oplus>\<^sub>O oracle_decrypt2 key) \<A> ();
    map_spmf ((=) b') coin_spmf})"

  have "map_spmf fst (game3 \<A>) = game4 \<A>"
  proof -
    note [split del] = if_split
    define S where "S = (\<lambda>(_ :: unit) (_ :: bool \<times> (bitstring, bitstring) PRF.dict). True)"
    define initial3 where "initial3 = (False, Map.empty :: (bitstring, bitstring) PRF.dict)"
    have [transfer_rule]: "S () initial3" by(simp add: S_def)
    have [transfer_rule]: "((=) ===> (=) ===> S ===> (=) ===> rel_spmf (rel_prod (=) S))
       (\<lambda>key b. oracle_encrypt4 key) oracle_encrypt3"
    proof(intro rel_funI; hypsubst)
      fix key unit msg10 b Dbad
      have "map_spmf fst (oracle_encrypt4 key () msg10) = map_spmf fst (oracle_encrypt3 key b Dbad msg10)"
        unfolding oracle_encrypt3_def oracle_encrypt4_def
        apply (clarsimp simp add: map_spmf_conv_bind_spmf Let_def split: bool.split prod.split; rule conjI; clarsimp)
        apply (rewrite in "\<hole> = _" one_time_pad[symmetric, where xs="if b then fst msg10 else snd msg10"])
         apply(simp split: if_split)
        apply(simp add: bind_map_spmf o_def option.case_distrib case_option_collapse xor_list_commute split_def cong del: option.case_cong_weak if_weak_cong)
        done
      then show "rel_spmf (rel_prod (=) S) (oracle_encrypt4 key unit msg10) (oracle_encrypt3 key b Dbad msg10)"
        by(auto simp add: spmf_rel_eq[symmetric] spmf_rel_map S_def elim: rel_spmf_mono)
    qed

    show ?thesis
      unfolding game3_def game4_def including monad_normalisation
      by (simp add: map_spmf_bind_spmf o_def split_def map_spmf_conv_bind_spmf initial3_def[symmetric] eq_commute)
         transfer_prover
  qed
  also have "\<dots> = coin_spmf"
    by(simp add: map_eq_const_coin_spmf game4_def bind_spmf_const split_def lossless_exec_gpv[OF assms] lossless_weight_spmfD)
  finally  show ?thesis .
qed

lemma game3_bad:
  assumes "interaction_bounded_by isl \<A> q"
  shows "measure (measure_spmf (game3 \<A>)) {(b, bad). bad} \<le> q / card prf_domain * q"
proof -
  have "measure (measure_spmf (game3 \<A>)) {(b, bad). bad} = spmf (map_spmf snd (game3 \<A>)) True"
    by (simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def snd_def)
  also
  have "spmf (map_spmf (fst \<circ> snd) (exec_gpv (oracle_encrypt3 k b \<oplus>\<^sub>O oracle_decrypt2 k) \<A> (False, Map.empty))) True \<le> q / card prf_domain * q"
    (is "spmf (map_spmf _ (exec_gpv ?oracle _ _)) _ \<le>  _")
    if k: "k \<in> set_spmf key_gen" for k b
  proof(rule callee_invariant_on.interaction_bounded_by'_exec_gpv_bad_count)
    obtain k_prf k_upf where k: "k = (k_prf, k_upf)" by(cases k)
    let ?I = "\<lambda>(bad, D). finite (dom D) \<and> dom D \<subseteq> prf_domain"
    have "callee_invariant (oracle_encrypt3 k b) ?I"
      by unfold_locales(clarsimp simp add: prf_domain_finite oracle_encrypt3_def Let_def split_def split: bool.splits)+
    moreover have "callee_invariant (oracle_decrypt2 k) ?I"
      by unfold_locales (clarsimp simp add: prf_domain_finite oracle_decrypt2_def)+
    ultimately show "callee_invariant ?oracle ?I" by simp

    let ?count = "\<lambda>(bad, D). card (dom D)"
    show "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (?oracle s x); ?I s; isl x \<rbrakk> \<Longrightarrow> ?count s' \<le> Suc (?count s)"
      by(clarsimp simp add: isl_def oracle_encrypt3_def split_def Let_def card_insert_if split: bool.splits)
    show "\<lbrakk> (y, s') \<in> set_spmf (?oracle s x); ?I s; \<not> isl x \<rbrakk> \<Longrightarrow> ?count s' \<le> ?count s" for s x y s'
      by(cases x)(simp_all add: oracle_decrypt2_def)
    show "spmf (map_spmf (fst \<circ> snd) (?oracle s' x)) True \<le> q / card prf_domain"
      if I: "?I s'" and bad: "\<not> fst s'" and count: "?count s' < q + ?count (False, Map.empty)" 
      and x: "isl x"
      for s' x
    proof -
      obtain bad D where s' [simp]: "s' = (bad, D)" by(cases s')
      from x obtain m1 m0 where x [simp]: "x = Inl (m1, m0)" by(auto elim: islE)
      have *: "(case D x of None \<Rightarrow> False | Some x \<Rightarrow> True) \<longleftrightarrow> x \<in> dom D" for x
        by(auto split: option.split)
      show ?thesis
      proof(cases "length m1 = prf_clen \<and> length m0 = prf_clen")
        case True
        with bad
        have "spmf (map_spmf (fst \<circ> snd) (?oracle s' x)) True = pmf (bernoulli_pmf (card (dom D \<inter> prf_domain) / card prf_domain)) True"
          by(simp add: spmf.map_comp o_def oracle_encrypt3_def k * bool.case_distrib[where h="\<lambda>p. spmf (map_spmf _ p) _"] option.case_distrib[where h=snd] map_spmf_bind_spmf Let_def split_beta bind_spmf_const cong: bool.case_cong option.case_cong split del: if_split split: bool.split)
            (simp add: map_spmf_conv_bind_spmf[symmetric] map_mem_spmf_of_set prf_domain_finite prf_domain_nonempty)
        also have "\<dots> = card (dom D \<inter> prf_domain) / card prf_domain"
          by(rule pmf_bernoulli_True)(auto simp add: field_simps prf_domain_finite prf_domain_nonempty card_gt_0_iff card_mono)
        also have "dom D \<inter> prf_domain = dom D" using I by auto
        also have "card (dom D) \<le> q" using count by simp
        finally show ?thesis by(simp add: divide_right_mono o_def)
      next
        case False
        thus ?thesis using bad 
          by(auto simp add: spmf.map_comp o_def oracle_encrypt3_def k split: bool.split)
      qed
    qed
  qed(auto split: plus_oracle_split_asm simp add: oracle_decrypt2_def assms)
  then have "spmf (map_spmf snd (game3 \<A>)) True \<le> q / card prf_domain * q"
    by(auto 4 3 simp add: game3_def map_spmf_bind_spmf o_def split_def map_spmf_conv_bind_spmf intro: spmf_bind_leI)
  finally show ?thesis .
qed


theorem security:
  assumes lossless: "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A>"
  and bound: "interaction_bounded_by isl \<A> q"
  shows "ind_cca.advantage \<A> \<le> 
    PRF.advantage (reduction_prf \<A>) + UPF.advantage (reduction_upf \<A>) +
    real q / real (card prf_domain) * real q" (is "?LHS \<le> _")
proof -
  have "?LHS \<le> \<bar>spmf (ind_cca.game \<A>) True - spmf (ind_cca'.game \<A>) True\<bar> + \<bar>spmf (ind_cca'.game \<A>) True - 1 / 2\<bar>"
    (is "_ \<le> ?round1 + ?rest") using abs_triangle_ineq by(simp add: ind_cca.advantage_def)
  also have "?round1 \<le> UPF.advantage (reduction_upf \<A>)"
    using lossless by(rule round_1)
  also have "?rest \<le> \<bar>spmf (ind_cca'.game \<A>) True - spmf (game2 \<A>) True\<bar> + \<bar>spmf (game2 \<A>) True - 1 / 2\<bar>"
    (is "_ \<le> ?round2 + ?rest") using abs_triangle_ineq by simp
  also have "?round2 = PRF.advantage (reduction_prf \<A>)" by(rule round_2)
  also have "?rest \<le> \<bar>measure (measure_spmf (game3 \<A>)) {(b, bad). b} - spmf (game2 \<A>) True\<bar> +
       \<bar>measure (measure_spmf (game3 \<A>)) {(b, bad). b} - 1 / 2\<bar>" 
    (is "_ \<le> ?round3 + _") using abs_triangle_ineq by simp
  also have "?round3 \<le> measure (measure_spmf (game3 \<A>)) {(b, bad). bad}"
    using round_3[OF lossless] .
  also have "\<dots> \<le> q / card prf_domain * q" using bound by(rule game3_bad)
  also have "measure (measure_spmf (game3 \<A>)) {(b, bad). b} = spmf coin_spmf True"
    using round_4[OF lossless, symmetric]
    by(simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def fst_def)
  also have "\<bar>\<dots> - 1 / 2\<bar> = 0" by(simp add: spmf_of_set)
  finally show ?thesis by(simp)
qed

theorem security1:
  assumes lossless: "lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<A>"
  assumes q: "interaction_bounded_by isl \<A> q"
  and q': "interaction_bounded_by (Not \<circ> isl) \<A> q'"
  shows "ind_cca.advantage \<A> \<le> 
    PRF.advantage (reduction_prf \<A>) +
    UPF.advantage1 (guessing_many_one.reduction q' (\<lambda>_. reduction_upf \<A>) ()) * q' +
    real q * real q / real (card prf_domain)"
proof -
  have "ind_cca.advantage \<A> \<le> 
    PRF.advantage (reduction_prf \<A>) + UPF.advantage (reduction_upf \<A>) +
    real q / real (card prf_domain) * real q"
    using lossless q by(rule security)
  also note q'[interaction_bound]
  have "interaction_bounded_by (Not \<circ> isl) (reduction_upf \<A>) q'"
    unfolding reduction_upf_def by(interaction_bound)(simp_all add: SUP_le_iff)
  then have "UPF.advantage (reduction_upf \<A>) \<le> UPF.advantage1 (guessing_many_one.reduction q' (\<lambda>_. reduction_upf \<A>) ()) * q'"
    by(rule UPF.advantage_advantage1)
  finally show ?thesis by(simp)
qed

end

end

locale simple_cipher' = 
  fixes prf_key_gen :: "security \<Rightarrow> 'prf_key spmf"
  and prf_fun :: "security \<Rightarrow> 'prf_key \<Rightarrow> bitstring \<Rightarrow> bitstring"
  and prf_domain :: "security \<Rightarrow> bitstring set"
  and prf_range :: "security \<Rightarrow> bitstring set"
  and prf_dlen :: "security \<Rightarrow> nat"
  and prf_clen :: "security \<Rightarrow> nat"
  and upf_key_gen :: "security \<Rightarrow> 'upf_key spmf"
  and upf_fun :: "security \<Rightarrow> 'upf_key \<Rightarrow> bitstring \<Rightarrow> 'hash"
  assumes simple_cipher: "\<And>\<eta>. simple_cipher (prf_key_gen \<eta>) (prf_fun \<eta>) (prf_domain \<eta>) (prf_dlen \<eta>) (prf_clen \<eta>) (upf_key_gen \<eta>)"
begin

sublocale simple_cipher 
  "prf_key_gen \<eta>" "prf_fun \<eta>" "prf_domain \<eta>" "prf_range \<eta>" "prf_dlen \<eta>" "prf_clen \<eta>" "upf_key_gen \<eta>" "upf_fun \<eta>"
  for \<eta>
by(rule simple_cipher)

theorem security_asymptotic:
  fixes q q' :: "security \<Rightarrow> nat"
  assumes lossless: "\<And>\<eta>. lossless_gpv (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) (\<A> \<eta>)"
  and bound: "\<And>\<eta>. interaction_bounded_by isl (\<A> \<eta>) (q \<eta>)"
  and bound': "\<And>\<eta>. interaction_bounded_by (Not \<circ> isl) (\<A> \<eta>) (q' \<eta>)"
  and [negligible_intros]:
    "polynomial q'" "polynomial q"
    "negligible (\<lambda>\<eta>. PRF.advantage \<eta> (reduction_prf \<eta> (\<A> \<eta>)))"
    "negligible (\<lambda>\<eta>. UPF.advantage1 \<eta> (guessing_many_one.reduction (q' \<eta>) (\<lambda>_. reduction_upf \<eta> (\<A> \<eta>)) ()))"
    "negligible (\<lambda>\<eta>. 1 / card (prf_domain \<eta>))"
  shows "negligible (\<lambda>\<eta>. ind_cca.advantage \<eta> (\<A> \<eta>))"
proof -
  have "negligible (\<lambda>\<eta>. PRF.advantage \<eta> (reduction_prf \<eta> (\<A> \<eta>)) +
    UPF.advantage1 \<eta> (guessing_many_one.reduction (q' \<eta>) (\<lambda>_. reduction_upf \<eta> (\<A> \<eta>)) ()) * q' \<eta> +
    real (q \<eta>) / real (card (prf_domain \<eta>)) * real (q \<eta>))"
    by(rule negligible_intros)+
  thus ?thesis by(rule negligible_le)(simp add: security1[OF lossless bound bound'] ind_cca.advantage_nonneg)
qed

end

end
