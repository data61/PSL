(* Title: Hashed_Elgamal.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Hashed Elgamal in the Random Oracle Model\<close>

theory Hashed_Elgamal imports
  CryptHOL.GPV_Bisim
  CryptHOL.Cyclic_Group_SPMF
  CryptHOL.List_Bits
  IND_CPA_PK
  Diffie_Hellman
begin

type_synonym bitstring = "bool list"

locale hash_oracle = fixes len :: "nat" begin

type_synonym 'a state = "'a \<rightharpoonup> bitstring"

definition "oracle" :: "'a state \<Rightarrow> 'a \<Rightarrow> (bitstring \<times> 'a state) spmf"
where
  "oracle \<sigma> x = 
  (case \<sigma> x of None \<Rightarrow> do {
     bs \<leftarrow> spmf_of_set (nlists UNIV len);
     return_spmf (bs, \<sigma>(x \<mapsto> bs))
   } | Some bs \<Rightarrow> return_spmf (bs, \<sigma>))"

abbreviation (input) initial :: "'a state" where "initial \<equiv> Map.empty"

inductive invariant :: "'a state \<Rightarrow> bool"
where
  invariant: "\<lbrakk> finite (dom \<sigma>); length ` ran \<sigma> \<subseteq> {len} \<rbrakk> \<Longrightarrow> invariant \<sigma>"

lemma invariant_initial [simp]: "invariant initial"
by(rule invariant.intros) auto

lemma invariant_update [simp]: "\<lbrakk> invariant \<sigma>; length bs = len \<rbrakk> \<Longrightarrow> invariant (\<sigma>(x \<mapsto> bs))"
by(auto simp add: invariant.simps ran_def)
                           
lemma invariant [intro!, simp]: "callee_invariant oracle invariant"
by unfold_locales(simp_all add: oracle_def in_nlists_UNIV split: option.split_asm)

lemma invariant_in_dom [simp]: "callee_invariant oracle (\<lambda>\<sigma>. x \<in> dom \<sigma>)"
by unfold_locales(simp_all add: oracle_def split: option.split_asm)

lemma lossless_oracle [simp]: "lossless_spmf (oracle \<sigma> x)"
by(simp add: oracle_def split: option.split)

lemma card_dom_state:
  assumes \<sigma>': "(x, \<sigma>') \<in> set_spmf (exec_gpv oracle gpv \<sigma>)"
  and ibound: "interaction_any_bounded_by gpv n"
  shows "card (dom \<sigma>') \<le> n + card (dom \<sigma>)"
proof(cases "finite (dom \<sigma>)")
  case True
  interpret callee_invariant_on "oracle" "\<lambda>\<sigma>. finite (dom \<sigma>)" \<I>_full
    by unfold_locales(auto simp add: oracle_def split: option.split_asm)
  from ibound \<sigma>' _ _ _ True show ?thesis
    by(rule interaction_bounded_by'_exec_gpv_count)(auto simp add: oracle_def card_insert_if simp del: fun_upd_apply split: option.split_asm)
next
  case False
  interpret callee_invariant_on "oracle" "\<lambda>\<sigma>'. dom \<sigma> \<subseteq> dom \<sigma>'" \<I>_full
    by unfold_locales(auto simp add: oracle_def split: option.split_asm)
  from \<sigma>' have "dom \<sigma> \<subseteq> dom \<sigma>'" by(rule exec_gpv_invariant) simp_all
  with False have "infinite (dom \<sigma>')" by(auto intro: finite_subset)
  with False show ?thesis by simp
qed

end

locale elgamal_base =
  fixes \<G> :: "'grp cyclic_group" (structure)
  and len_plain :: "nat"
begin

sublocale hash: hash_oracle "len_plain" .
abbreviation hash :: "'grp \<Rightarrow> (bitstring, 'grp, bitstring) gpv"
where "hash x \<equiv> Pause x Done"

type_synonym 'grp' pub_key = "'grp'"
type_synonym 'grp' priv_key = nat
type_synonym plain = bitstring
type_synonym 'grp' cipher = "'grp' \<times> bitstring"

definition key_gen :: "('grp pub_key \<times> 'grp priv_key) spmf"
where 
  "key_gen = do {
     x \<leftarrow> sample_uniform (order \<G>);
     return_spmf (\<^bold>g [^] x, x)
  }"

definition aencrypt :: "'grp pub_key \<Rightarrow> plain \<Rightarrow> ('grp cipher, 'grp, bitstring) gpv"
where
  "aencrypt \<alpha> msg = do {
    y \<leftarrow> lift_spmf (sample_uniform (order \<G>));
    h \<leftarrow> hash (\<alpha> [^] y);
    Done (\<^bold>g [^] y, h [\<oplus>] msg)
  }"

definition adecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher \<Rightarrow> (plain, 'grp, bitstring) gpv"
where
  "adecrypt x = (\<lambda>(\<beta>, \<zeta>). do {
    h \<leftarrow> hash (\<beta> [^] x);
    Done (\<zeta> [\<oplus>] h)
  })"

definition valid_plains :: "plain \<Rightarrow> plain \<Rightarrow> bool"
where "valid_plains msg1 msg2 \<longleftrightarrow> length msg1 = len_plain \<and> length msg2 = len_plain"

lemma lossless_aencrypt [simp]: "lossless_gpv \<I> (aencrypt \<alpha> msg) \<longleftrightarrow> 0 < order \<G>"
by(simp add: aencrypt_def Let_def)

lemma interaction_bounded_by_aencrypt [interaction_bound, simp]:
  "interaction_bounded_by (\<lambda>_. True) (aencrypt \<alpha> msg) 1"
unfolding aencrypt_def by interaction_bound(simp add: one_enat_def SUP_le_iff)

sublocale ind_cpa: ind_cpa_pk "lift_spmf key_gen" aencrypt adecrypt valid_plains .
sublocale lcdh: lcdh \<G> .

fun elgamal_adversary
   :: "('grp pub_key, plain, 'grp cipher, 'grp, bitstring, 'state) ind_cpa.adversary
   \<Rightarrow> 'grp lcdh.adversary"                     
where
  "elgamal_adversary (\<A>1, \<A>2) \<alpha> \<beta> = do {
    (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv hash.oracle (\<A>1 \<alpha>) hash.initial;
    \<comment> \<open>have to check that the attacker actually sends an element from the group; otherwise stop early\<close>
    TRY do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      h' \<leftarrow> spmf_of_set (nlists UNIV len_plain);
      (guess, s') \<leftarrow> exec_gpv hash.oracle (\<A>2 (\<beta>, h') \<sigma>) s;
      return_spmf (dom s')
    } ELSE return_spmf (dom s)
  }"

end

locale elgamal = elgamal_base +
  assumes cyclic_group: "cyclic_group \<G>"
begin

interpretation cyclic_group \<G> by(fact cyclic_group)

lemma advantage_elgamal: 
  includes lifting_syntax
  assumes lossless: "ind_cpa.lossless \<A>"
  shows "ind_cpa.advantage hash.oracle hash.initial \<A> \<le> lcdh.advantage (elgamal_adversary \<A>)"
proof -
  note [cong del] = if_weak_cong and [split del] = if_split
    and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const
  obtain \<A>1 \<A>2 where \<A> [simp]: "\<A> = (\<A>1, \<A>2)" by(cases "\<A>")

  interpret cyclic_group: cyclic_group \<G> by(rule cyclic_group)
  from finite_carrier have [simp]: "order \<G> > 0" using order_gt_0_iff_finite by(simp)

  from lossless have lossless1 [simp]: "\<And>pk. lossless_gpv \<I>_full (\<A>1 pk)"
    and lossless2 [simp]: "\<And>\<sigma> cipher. lossless_gpv \<I>_full (\<A>2 \<sigma> cipher)"
    by(auto simp add: ind_cpa.lossless_def)

  text \<open>We change the adversary's oracle to record the queries made by the adversary\<close>
  define hash_oracle' where "hash_oracle' = (\<lambda>\<sigma> x. do {
      h \<leftarrow> hash x;
      Done (h, insert x \<sigma>)
    })"
  have [simp]: "lossless_gpv \<I>_full (hash_oracle' \<sigma> x)" for \<sigma> x by(simp add: hash_oracle'_def)
  have [simp]: "lossless_gpv \<I>_full (inline hash_oracle' (\<A>1 \<alpha>) s)" for \<alpha> s
    by(rule lossless_inline[where \<I>=\<I>_full]) simp_all
  define game0 where "game0 = TRY do {
      (pk, _) \<leftarrow> lift_spmf key_gen;
      b \<leftarrow> lift_spmf coin_spmf;
      (((msg1, msg2), \<sigma>), s) \<leftarrow> inline hash_oracle' (\<A>1 pk) {};
      assert_gpv (valid_plains msg1 msg2);
      cipher \<leftarrow> aencrypt pk (if b then msg1 else msg2);
      (guess, s') \<leftarrow> inline hash_oracle' (\<A>2 cipher \<sigma>) s;
      Done (guess = b)
    } ELSE lift_spmf coin_spmf"
  { define cr where "cr = (\<lambda>_ :: unit. \<lambda>_ :: 'a set. True)"
    have [transfer_rule]: "cr () {}" by(simp add: cr_def)
    have [transfer_rule]: "((=) ===> cr ===> cr) (\<lambda>_ \<sigma>. \<sigma>) insert" by(simp add: rel_fun_def cr_def)
    have [transfer_rule]: "(cr ===> (=) ===> rel_gpv (rel_prod (=) cr) (=)) id_oracle hash_oracle'"
      unfolding hash_oracle'_def id_oracle_def[abs_def] bind_gpv_Pause bind_rpv_Done by transfer_prover
    have "ind_cpa.ind_cpa \<A> = game0" unfolding game0_def \<A> ind_cpa_pk.ind_cpa.simps
      by(transfer fixing: \<G> len_plain \<A>1 \<A>2)(simp add: bind_map_gpv o_def ind_cpa_pk.ind_cpa.simps split_def) }
  note game0 = this
  have game0_alt_def: "game0 = do {
      x \<leftarrow> lift_spmf (sample_uniform (order \<G>));
      b \<leftarrow> lift_spmf coin_spmf;
      (((msg1, msg2), \<sigma>), s) \<leftarrow> inline hash_oracle' (\<A>1 (\<^bold>g [^] x)) {};
      TRY do {
        _ :: unit \<leftarrow> assert_gpv (valid_plains msg1 msg2);
        cipher \<leftarrow> aencrypt (\<^bold>g [^] x) (if b then msg1 else msg2);
        (guess, s') \<leftarrow> inline hash_oracle' (\<A>2 cipher \<sigma>) s;
        Done (guess = b)
      } ELSE lift_spmf coin_spmf
    }"
    by(simp add: split_def game0_def key_gen_def lift_spmf_bind_spmf bind_gpv_assoc try_gpv_bind_lossless[symmetric])

  define hash_oracle'' where "hash_oracle'' = (\<lambda>(s, \<sigma>) (x :: 'a). do {
      (h, \<sigma>') \<leftarrow> case \<sigma> x of
          None \<Rightarrow> bind_spmf (spmf_of_set (nlists UNIV len_plain)) (\<lambda>bs. return_spmf (bs, \<sigma>(x \<mapsto> bs)))
        | Some (bs :: bitstring) \<Rightarrow> return_spmf (bs, \<sigma>);
      return_spmf (h, insert x s, \<sigma>')
    })"
  have *: "exec_gpv hash.oracle (inline hash_oracle' \<A> s) \<sigma> = 
    map_spmf (\<lambda>(a, b, c). ((a, b), c)) (exec_gpv hash_oracle'' \<A> (s, \<sigma>))" for \<A> \<sigma> s
    by(simp add: hash_oracle'_def hash_oracle''_def hash.oracle_def Let_def exec_gpv_inline exec_gpv_bind o_def split_def cong del: option.case_cong_weak)
  have [simp]: "lossless_spmf (hash_oracle'' s plain)" for s plain
    by(simp add: hash_oracle''_def Let_def split: prod.split option.split)
  have [simp]: "lossless_spmf (exec_gpv hash_oracle'' (\<A>1 \<alpha>) s)" for s \<alpha>
    by(rule lossless_exec_gpv[where \<I>=\<I>_full]) simp_all
  have [simp]: "lossless_spmf (exec_gpv hash_oracle'' (\<A>2 \<sigma> cipher) s)" for \<sigma> cipher s
    by(rule lossless_exec_gpv[where \<I>=\<I>_full]) simp_all

  let ?sample = "\<lambda>f. bind_spmf (sample_uniform (order \<G>)) (\<lambda>x. bind_spmf (sample_uniform (order \<G>)) (f x))"
  define game1 where "game1 = (\<lambda>(x :: nat) (y :: nat). do {
      b \<leftarrow> coin_spmf;
      (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv hash_oracle'' (\<A>1 (\<^bold>g [^] x)) ({}, hash.initial);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
        (h, s_h') \<leftarrow> hash.oracle s_h (\<^bold>g [^] (x * y));
        let cipher = (\<^bold>g [^] y, h [\<oplus>] (if b then msg1 else msg2));
        (guess, (s', s_h'')) \<leftarrow> exec_gpv hash_oracle'' (\<A>2 cipher \<sigma>) (s, s_h');
        return_spmf (guess = b, \<^bold>g [^] (x * y) \<in> s')
      } ELSE do {
        b \<leftarrow> coin_spmf;
        return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
      }
    })"
  have game01: "run_gpv hash.oracle game0 hash.initial = map_spmf fst (?sample game1)"
    apply(simp add: exec_gpv_bind split_def bind_gpv_assoc aencrypt_def game0_alt_def game1_def o_def bind_map_spmf if_distribs * try_bind_assert_gpv try_bind_assert_spmf lossless_inline[where \<I>=\<I>_full] bind_rpv_def nat_pow_pow del: bind_spmf_const)
    including monad_normalisation by(simp add: bind_rpv_def nat_pow_pow)
  
  define game2 where "game2 = (\<lambda>(x :: nat) (y :: nat). do {
    b \<leftarrow> coin_spmf;
    (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv hash_oracle'' (\<A>1 (\<^bold>g [^] x)) ({}, hash.initial);
    TRY do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      h \<leftarrow> spmf_of_set (nlists UNIV len_plain);
      \<comment> \<open>We do not do the lookup in \<open>s_h\<close> here, so the rest differs only if the adversary guessed \<open>y\<close>\<close>
      let cipher = (\<^bold>g [^] y, h [\<oplus>] (if b then msg1 else msg2));
      (guess, (s', s_h')) \<leftarrow> exec_gpv hash_oracle'' (\<A>2 cipher \<sigma>) (s, s_h);
      return_spmf (guess = b, \<^bold>g [^] (x * y) \<in> s')
    } ELSE do {
      b \<leftarrow> coin_spmf;
      return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
    }
  })"
  interpret inv'': callee_invariant_on "hash_oracle''" "\<lambda>(s, s_h). s = dom s_h" \<I>_full
    by unfold_locales(auto simp add: hash_oracle''_def split: option.split_asm if_split)
  have in_encrypt_oracle: "callee_invariant hash_oracle'' (\<lambda>(s, _). x \<in> s)" for x
    by unfold_locales(auto simp add: hash_oracle''_def)

  { fix x y :: nat
    let ?bad = "\<lambda>(s, s_h). \<^bold>g [^] (x * y) \<in> s"
    let ?X = "\<lambda>(s, s_h) (s', s_h'). s = dom s_h \<and> s' = s \<and> s_h = s_h'(\<^bold>g [^] (x * y) := None)"
    have bisim:
      "rel_spmf (\<lambda>(a, s1') (b, s2'). ?bad s1' = ?bad s2' \<and> (\<not> ?bad s2' \<longrightarrow> a = b \<and> ?X s1' s2'))
             (hash_oracle'' s1 plain) (hash_oracle'' s2 plain)"
      if "?X s1 s2" for s1 s2 plain using that
      by(auto split: prod.splits intro!: rel_spmf_bind_reflI simp add: hash_oracle''_def rel_spmf_return_spmf2 fun_upd_twist split: option.split dest!: fun_upd_eqD)
    have inv: "callee_invariant hash_oracle'' ?bad"
      by(unfold_locales)(auto simp add: hash_oracle''_def split: option.split_asm)
    have "rel_spmf (\<lambda>(win, bad) (win', bad'). bad = bad' \<and> (\<not> bad' \<longrightarrow> win = win')) (game2 x y) (game1 x y)"
      unfolding game1_def game2_def
      apply(clarsimp simp add: split_def o_def hash.oracle_def rel_spmf_bind_reflI if_distribs intro!: rel_spmf_bind_reflI simp del: bind_spmf_const)
      apply(rule rel_spmf_try_spmf)
      subgoal for b msg1 msg2 \<sigma> s s_h
        apply(rule rel_spmf_bind_reflI)
        apply(drule inv''.exec_gpv_invariant; clarsimp)
        apply(cases "s_h (\<^bold>g [^] (x * y))")
        subgoal \<comment> \<open>case @{const None}\<close>
          apply(clarsimp intro!: rel_spmf_bind_reflI)
          apply(rule rel_spmf_bindI)
           apply(rule exec_gpv_oracle_bisim_bad_full[OF _ _ bisim inv inv, where R="\<lambda>(x, s1) (y, s2). ?bad s1 = ?bad s2 \<and> (\<not> ?bad s2 \<longrightarrow> x = y)"]; clarsimp simp add: fun_upd_idem; fail)
          apply clarsimp
          done
        subgoal by(auto intro!: rel_spmf_bindI1 rel_spmf_bindI2 lossless_exec_gpv[where \<I>=\<I>_full] dest!: callee_invariant_on.exec_gpv_invariant[OF in_encrypt_oracle])
        done
      subgoal by(rule rel_spmf_reflI) simp
      done }
  hence "rel_spmf (\<lambda>(win, bad) (win', bad'). (bad \<longleftrightarrow> bad') \<and> (\<not> bad' \<longrightarrow> win \<longleftrightarrow> win')) (?sample game2) (?sample game1)"
    by(intro rel_spmf_bind_reflI)
  hence "\<bar>measure (measure_spmf (?sample game2)) {(x, _). x} - measure (measure_spmf (?sample game1)) {(y, _). y}\<bar>
        \<le> measure (measure_spmf (?sample game2)) {(_, bad). bad}"
    unfolding split_def by(rule fundamental_lemma)
  moreover have "measure (measure_spmf (?sample game2)) {(x, _). x} = spmf (map_spmf fst (?sample game2)) True"
    and "measure (measure_spmf (?sample game1)) {(y, _). y} = spmf (map_spmf fst (?sample game1)) True"
    and "measure (measure_spmf (?sample game2)) {(_, bad). bad} = spmf (map_spmf snd (?sample game2)) True"
    unfolding spmf_conv_measure_spmf measure_map_spmf by(rule arg_cong2[where f=measure]; fastforce)+
  ultimately have hop23: "\<bar>spmf (map_spmf fst (?sample game2)) True - spmf (map_spmf fst (?sample game1)) True\<bar> \<le> spmf (map_spmf snd (?sample game2)) True" by simp

  define game3
    where "game3 = (\<lambda>f :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bitstring spmf \<Rightarrow> _ spmf. \<lambda>(x :: nat) (y :: nat). do {
      b \<leftarrow> coin_spmf;
      (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv hash_oracle'' (\<A>1 (\<^bold>g [^] x)) ({}, hash.initial);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
        h' \<leftarrow> f b msg1 msg2 (spmf_of_set (nlists UNIV len_plain));
        let cipher = (\<^bold>g [^] y, h');
        (guess, (s', s_h')) \<leftarrow> exec_gpv hash_oracle'' (\<A>2 cipher \<sigma>) (s, s_h);
        return_spmf (guess = b, \<^bold>g [^] (x * y) \<in> s')
      } ELSE do {
        b \<leftarrow> coin_spmf;
        return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
      }
    })"
  let ?f = "\<lambda>b msg1 msg2. map_spmf (\<lambda>h. (if b then msg1 else msg2) [\<oplus>] h)"
  have "game2 x y = game3 ?f x y" for x y
    unfolding game2_def game3_def by(simp add: Let_def bind_map_spmf xor_list_commute o_def nat_pow_pow)
  also have "game3 ?f x y = game3 (\<lambda>_ _ _ x. x) x y" for x y (* optimistic sampling *)
    unfolding game3_def
    by(auto intro!: try_spmf_cong bind_spmf_cong[OF refl] if_cong[OF refl] simp add: split_def one_time_pad valid_plains_def simp del: map_spmf_of_set_inj_on bind_spmf_const split: if_split)
  finally have game23: "game2 x y = game3 (\<lambda>_ _ _ x. x) x y" for x y .

  define hash_oracle''' where "hash_oracle''' = (\<lambda>(\<sigma> :: 'a \<Rightarrow> _). hash.oracle \<sigma>)"
  { define bisim where "bisim = (\<lambda>\<sigma> (s :: 'a set, \<sigma>' :: 'a \<rightharpoonup> bitstring). s = dom \<sigma> \<and> \<sigma> = \<sigma>')"
    have [transfer_rule]: "bisim Map_empty ({}, Map_empty)" by(simp add: bisim_def)
    have [transfer_rule]: "(bisim ===> (=) ===> rel_spmf (rel_prod (=) bisim)) hash_oracle''' hash_oracle''"
      by(auto simp add: hash_oracle''_def split_def hash_oracle'''_def spmf_rel_map hash.oracle_def rel_fun_def bisim_def split: option.split intro!: rel_spmf_bind_reflI)
    have * [transfer_rule]: "(bisim ===> (=)) dom fst" by(simp add: bisim_def rel_fun_def)
    have * [transfer_rule]: "(bisim ===> (=)) (\<lambda>x. x) snd" by(simp add: rel_fun_def bisim_def)
    have "game3 (\<lambda>_ _ _ x. x) x y = do {
        b \<leftarrow> coin_spmf;
        (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv hash_oracle''' (\<A>1 (\<^bold>g [^] x)) hash.initial;
        TRY do {
          _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
          h' \<leftarrow> spmf_of_set (nlists UNIV len_plain);
          let cipher = (\<^bold>g [^] y, h');
          (guess, s') \<leftarrow> exec_gpv hash_oracle''' (\<A>2 cipher \<sigma>) s;
          return_spmf (guess = b, \<^bold>g [^] (x * y) \<in> dom s')
        } ELSE do {
          b \<leftarrow> coin_spmf;
          return_spmf (b, \<^bold>g [^] (x * y) \<in> dom s)
        }
      }" for x y
      unfolding game3_def Map_empty_def[symmetric] split_def fst_conv snd_conv prod.collapse
      by(transfer fixing: \<A>1 \<G> len_plain x y \<A>2) simp
    moreover have "map_spmf snd (\<dots> x y) = do {
        zs \<leftarrow> elgamal_adversary \<A> (\<^bold>g [^] x) (\<^bold>g [^] y);
        return_spmf (\<^bold>g [^] (x * y) \<in> zs)
      }" for x y
      by(simp add: o_def split_def hash_oracle'''_def map_try_spmf map_scale_spmf)
        (simp add: o_def map_try_spmf map_scale_spmf map_spmf_conv_bind_spmf[symmetric] spmf.map_comp map_const_spmf_of_set)
    ultimately have "map_spmf snd (?sample (game3 (\<lambda>_ _ _ x. x))) = lcdh.lcdh (elgamal_adversary \<A>)"
      by(simp add: o_def lcdh.lcdh_def Let_def nat_pow_pow) }
  then have game2_snd: "map_spmf snd (?sample game2) = lcdh.lcdh (elgamal_adversary \<A>)"
    using game23 by(simp add: o_def)

  have "map_spmf fst (game3 (\<lambda>_ _ _ x. x) x y) = do {
      (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv hash_oracle'' (\<A>1 (\<^bold>g [^] x)) ({}, hash.initial);
      TRY do {
        _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
        h' \<leftarrow> spmf_of_set (nlists UNIV len_plain);
        (guess, (s', s_h')) \<leftarrow> exec_gpv hash_oracle'' (\<A>2 (\<^bold>g [^] y, h') \<sigma>) (s, s_h);
        map_spmf ((=) guess) coin_spmf
      } ELSE coin_spmf
    }" for x y 
    including monad_normalisation
    by(simp add: game3_def o_def split_def map_spmf_conv_bind_spmf try_spmf_bind_out weight_spmf_le_1 scale_bind_spmf try_spmf_bind_out1 bind_scale_spmf)
  then have game3_fst: "map_spmf fst (game3 (\<lambda>_ _ _ x. x) x y) = coin_spmf" for x y
    by(simp add: o_def if_distribs spmf.map_comp map_eq_const_coin_spmf split_def)

  have "ind_cpa.advantage hash.oracle hash.initial \<A> = \<bar>spmf (map_spmf fst (?sample game1)) True - 1 / 2\<bar>"
    using game0 by(simp add: ind_cpa_pk.advantage_def game01 o_def)
  also have "\<dots> = \<bar>1 / 2 - spmf (map_spmf fst (?sample game1)) True\<bar>"
    by(simp add: abs_minus_commute)
  also have "1 / 2 = spmf (map_spmf fst (?sample game2)) True"
    by(simp add: game23 o_def game3_fst spmf_of_set)
  also note hop23 also note game2_snd
  finally show ?thesis by(simp add: lcdh.advantage_def)
qed

end

context elgamal_base begin

lemma lossless_key_gen [simp]: "lossless_spmf key_gen \<longleftrightarrow> 0 < order \<G>"
by(simp add: key_gen_def Let_def)

lemma lossless_elgamal_adversary:
  "\<lbrakk> ind_cpa.lossless \<A>; \<And>\<eta>. 0 < order \<G> \<rbrakk>
  \<Longrightarrow> lcdh.lossless (elgamal_adversary \<A>)"
by(cases \<A>)(auto simp add: lcdh.lossless_def ind_cpa.lossless_def split_def Let_def intro!: lossless_exec_gpv[where \<I>=\<I>_full] lossless_inline)

end

end
