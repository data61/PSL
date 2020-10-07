(* Title: Guessing_Many_One.thy
  Author: Andreas Lochbihler, ETH Zurich 
  Author: S. Reza Sefidgar, ETH Zurich *)

subsection \<open>Reducing games with many adversary guesses to games with single guesses\<close>

theory Guessing_Many_One imports
  CryptHOL.Computational_Model
  CryptHOL.GPV_Bisim
begin

locale guessing_many_one =
  fixes init :: "('c_o \<times> 'c_a \<times> 's) spmf"
  and "oracle" :: "'c_o \<Rightarrow> 's \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's) spmf"
  and "eval" :: "'c_o \<Rightarrow> 'c_a \<Rightarrow> 's \<Rightarrow> 'guess \<Rightarrow> bool spmf"
begin

type_synonym ('c_a', 'guess', 'call', 'ret') adversary_single = "'c_a' \<Rightarrow> ('guess', 'call', 'ret') gpv"

definition game_single :: "('c_a, 'guess, 'call, 'ret) adversary_single \<Rightarrow> bool spmf"
where
  "game_single \<A> = do {
    (c_o, c_a, s) \<leftarrow> init;
    (guess, s') \<leftarrow> exec_gpv (oracle c_o) (\<A> c_a) s;
    eval c_o c_a s' guess
  }"

definition advantage_single :: "('c_a, 'guess, 'call, 'ret) adversary_single \<Rightarrow> real"
where "advantage_single \<A> = spmf (game_single \<A>) True"


type_synonym ('c_a', 'guess', 'call', 'ret') adversary_many = "'c_a' \<Rightarrow> (unit, 'call' + 'guess', 'ret' + unit) gpv"

definition eval_oracle :: "'c_o \<Rightarrow> 'c_a \<Rightarrow> bool \<times> 's \<Rightarrow> 'guess \<Rightarrow> (unit \<times> (bool \<times> 's)) spmf"
where
  "eval_oracle c_o c_a = (\<lambda>(b, s') guess. map_spmf (\<lambda>b'. ((), (b \<or> b', s'))) (eval c_o c_a s' guess))"

definition game_multi :: "('c_a, 'guess, 'call, 'ret) adversary_many \<Rightarrow> bool spmf"
where
  "game_multi \<A> = do {
     (c_o, c_a, s) \<leftarrow> init;
     (_, (b, _)) \<leftarrow> exec_gpv
       (\<dagger>(oracle c_o) \<oplus>\<^sub>O eval_oracle c_o c_a)
       (\<A> c_a)
       (False, s);
     return_spmf b
  }"

definition advantage_multi :: "('c_a, 'guess, 'call, 'ret) adversary_many \<Rightarrow> real"
where "advantage_multi \<A> = spmf (game_multi \<A>) True"


type_synonym 'guess' reduction_state = "'guess' + nat"

primrec process_call :: "'guess reduction_state \<Rightarrow> 'call \<Rightarrow> ('ret option \<times> 'guess reduction_state, 'call, 'ret) gpv"
where
  "process_call (Inr j) x = do {
    ret \<leftarrow> Pause x Done;
    Done (Some ret, Inr j)
  }"
| "process_call (Inl guess) x = Done (None, Inl guess)"

primrec process_guess :: "'guess reduction_state \<Rightarrow> 'guess \<Rightarrow> (unit option \<times> 'guess reduction_state, 'call, 'ret) gpv"
where
  "process_guess (Inr j) guess = Done (if j > 0 then (Some (), Inr (j - 1)) else (None, Inl guess))"
| "process_guess (Inl guess) _ = Done (None, Inl guess)"

abbreviation reduction_oracle :: "'guess + nat \<Rightarrow> 'call + 'guess \<Rightarrow> (('ret + unit) option \<times> ('guess + nat), 'call, 'ret) gpv"
where "reduction_oracle \<equiv> plus_intercept_stop process_call process_guess"

definition reduction :: "nat \<Rightarrow> ('c_a, 'guess, 'call, 'ret) adversary_many \<Rightarrow> ('c_a, 'guess, 'call, 'ret) adversary_single"
where
  "reduction q \<A> c_a = do {
    j_star \<leftarrow> lift_spmf (spmf_of_set {..<q});
    (_, s) \<leftarrow> inline_stop reduction_oracle (\<A> c_a) (Inr j_star);
    Done (projl s)
  }"

lemma many_single_reduction:
  assumes bound: "\<And>c_a c_o s. (c_o, c_a, s) \<in> set_spmf init \<Longrightarrow> interaction_bounded_by (Not \<circ> isl) (\<A> c_a) q"
  and lossless_oracle: "\<And>c_a c_o s s' x. (c_o, c_a, s) \<in> set_spmf init \<Longrightarrow> lossless_spmf (oracle c_o s' x)"
  and lossless_eval: "\<And>c_a c_o s s' guess. (c_o, c_a, s) \<in> set_spmf init \<Longrightarrow> lossless_spmf (eval c_o c_a s' guess)"
  shows "advantage_multi \<A> \<le> advantage_single (reduction q \<A>) * q"
  including lifting_syntax
proof -
  define eval_oracle'
    where "eval_oracle' = (\<lambda>c_o c_a ((id, occ :: nat option), s') guess. 
    map_spmf (\<lambda>b'. case occ of Some j\<^sub>0 \<Rightarrow> ((), (Suc id, Some j\<^sub>0), s')
                                | None \<Rightarrow> ((), (Suc id, (if b' then Some id else None)), s'))
      (eval c_o c_a s' guess))"
  let ?multi'_body = "\<lambda>c_o c_a s. exec_gpv (\<dagger>(oracle c_o) \<oplus>\<^sub>O eval_oracle' c_o c_a) (\<A> c_a) ((0, None), s)"
  define game_multi' where "game_multi' = (\<lambda>c_o c_a s. do {
    (_, ((id, j\<^sub>0), s' :: 's)) \<leftarrow> ?multi'_body c_o c_a s;
    return_spmf (j\<^sub>0 \<noteq> None) })"

  define initialize :: "('c_o \<Rightarrow> 'c_a \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> bool spmf) \<Rightarrow> bool spmf" where
    "initialize body = do {
      (c_o, c_a, s) \<leftarrow> init;
      j\<^sub>s \<leftarrow> spmf_of_set {..<q};
      body c_o c_a s j\<^sub>s }" for body
  define body2 where "body2 c_o c_a s j\<^sub>s = do {
    (_, (id, j\<^sub>0), s') \<leftarrow> ?multi'_body c_o c_a s;
    return_spmf (j\<^sub>0 = Some j\<^sub>s) }" for c_o c_a s j\<^sub>s
  let ?game2 = "initialize body2"

  define stop_oracle where "stop_oracle = (\<lambda>c_o. 
     (\<lambda>(idgs, s) x. case idgs of Inr _ \<Rightarrow> map_spmf (\<lambda>(y, s). (Some y, (idgs, s))) (oracle c_o s x) | Inl _ \<Rightarrow> return_spmf (None, (idgs, s)))
     \<oplus>\<^sub>O\<^sup>S
     (\<lambda>(idgs, s) guess :: 'guess. return_spmf (case idgs of Inr 0 \<Rightarrow> (None, Inl (guess, s), s) | Inr (Suc i) \<Rightarrow> (Some (), Inr i, s) | Inl _ \<Rightarrow> (None, idgs, s))))"
  define body3 where "body3 c_o c_a s j\<^sub>s = do {
    (_ :: unit option, idgs, _) \<leftarrow> exec_gpv_stop (stop_oracle c_o) (\<A> c_a) (Inr j\<^sub>s, s);
    (b' :: bool) \<leftarrow> case idgs of Inr _ \<Rightarrow> return_spmf False | Inl (g, s') \<Rightarrow> eval c_o c_a s' g;
    return_spmf b' }" for c_o c_a s j\<^sub>s
  let ?game3 = "initialize body3"

  { define S :: "bool \<Rightarrow> nat \<times> nat option \<Rightarrow> bool" where "S \<equiv> \<lambda>b' (id, occ). b' \<longleftrightarrow> (\<exists>j\<^sub>0. occ = Some j\<^sub>0)"
    let ?S = "rel_prod S (=)"

    define initial :: "nat \<times> nat option" where "initial = (0, None)"
    define result :: "nat \<times> nat option \<Rightarrow> bool" where "result p = (snd p \<noteq> None)" for p
    have [transfer_rule]: "(S ===> (=)) (\<lambda>b. b) result" by(simp add: rel_fun_def result_def S_def)
    have [transfer_rule]: "S False initial" by (simp add: S_def initial_def)

    have eval_oracle'[transfer_rule]: 
      "((=) ===> (=) ===> ?S ===> (=) ===> rel_spmf (rel_prod (=) ?S))
       eval_oracle eval_oracle'"
      unfolding eval_oracle_def[abs_def] eval_oracle'_def[abs_def]
      by (auto simp add: rel_fun_def S_def map_spmf_conv_bind_spmf intro!: rel_spmf_bind_reflI split: option.split)
    
    have game_multi': "game_multi \<A> = bind_spmf init (\<lambda>(c_o, c_a, s). game_multi' c_o c_a s)"
      unfolding game_multi_def game_multi'_def initial_def[symmetric]
      by (rewrite in "case_prod \<hole>" in "bind_spmf _ (case_prod \<hole>)" in "_ = bind_spmf _ \<hole>" split_def)
         (fold result_def; transfer_prover) }
  moreover
  have "spmf (game_multi' c_o c_a s) True = spmf (bind_spmf (spmf_of_set {..<q}) (body2 c_o c_a s)) True * q"
    if "(c_o, c_a, s) \<in> set_spmf init" for c_o c_a s
  proof -
    have bnd: "interaction_bounded_by (Not \<circ> isl) (\<A> c_a) q" using bound that by blast

    have bound_occ: "j\<^sub>s < q" if that: "((), (id, Some j\<^sub>s), s') \<in> set_spmf (?multi'_body c_o c_a s)" 
      for s' id j\<^sub>s
    proof -
      have "id \<le> q" 
        by(rule oi_True.interaction_bounded_by'_exec_gpv_count[OF bnd that, where count="fst \<circ> fst", simplified])
          (auto simp add: eval_oracle'_def split: plus_oracle_split_asm option.split_asm)
      moreover let ?I = "\<lambda>((id, occ), s'). case occ of None \<Rightarrow> True | Some j\<^sub>s \<Rightarrow> j\<^sub>s < id"
      have "callee_invariant (\<dagger>(oracle c_o) \<oplus>\<^sub>O eval_oracle' c_o c_a) ?I"
        by(clarsimp simp add: split_def intro!: conjI[OF callee_invariant_extend_state_oracle_const'])
          (unfold_locales; auto simp add: eval_oracle'_def split: option.split_asm)
      from callee_invariant_on.exec_gpv_invariant[OF this that] have "j\<^sub>s < id" by simp
      ultimately show ?thesis by simp
    qed

    let ?M = "measure (measure_spmf (?multi'_body c_o c_a s))"
    have "spmf (game_multi' c_o c_a s) True = ?M {(u, (id, j\<^sub>0), s'). j\<^sub>0 \<noteq> None}"
      by(auto simp add: game_multi'_def map_spmf_conv_bind_spmf[symmetric] split_def spmf_conv_measure_spmf measure_map_spmf vimage_def)
    also have "{(u, (id, j\<^sub>0), s'). j\<^sub>0 \<noteq> None} =
      {((), (id, Some j\<^sub>s), s') |j\<^sub>s s' id. j\<^sub>s < q} \<union> {((), (id, Some j\<^sub>s), s') |j\<^sub>s s' id. j\<^sub>s \<ge> q}"
      (is "_ = ?A \<union> _") by auto
    also have "?M \<dots> = ?M ?A"
      by (rule measure_spmf.measure_zero_union)(auto simp add: measure_spmf_zero_iff dest: bound_occ)
    also have "\<dots> = measure (measure_spmf (pair_spmf (spmf_of_set {..< q}) (?multi'_body c_o c_a s)))
         {(j\<^sub>s, (), (id, j\<^sub>0), s') |j\<^sub>s j\<^sub>0 s' id. j\<^sub>0 = Some j\<^sub>s } * q"
      (is "_ = measure ?M' ?B * _")
    proof - 
      have "?B = {(j\<^sub>s, (), (id, j\<^sub>0), s') |j\<^sub>s j\<^sub>0 s' id. j\<^sub>0 = Some j\<^sub>s \<and> j\<^sub>s < q} \<union>
        {(j\<^sub>s, (), (id, j\<^sub>0), s') |j\<^sub>s j\<^sub>0 s' id. j\<^sub>0 = Some j\<^sub>s \<and> j\<^sub>s \<ge> q}" (is "_ = ?Set1 \<union> ?Set2")
        by auto
      then have "measure ?M' ?B = measure ?M' (?Set1 \<union> ?Set2)" by simp
      also have "\<dots> = measure ?M' ?Set1"
        by (rule measure_spmf.measure_zero_union) (auto simp add: measure_spmf_zero_iff)
      also have "\<dots> = (\<Sum>j\<in>{0..<q}. measure ?M' ({j} \<times> {((), (id, Some j), s')|s' id. True}))"
        by(subst measure_spmf.finite_measure_finite_Union[symmetric])
          (auto intro!: arg_cong2[where f=measure] simp add: disjoint_family_on_def)
      also have "\<dots> = (\<Sum>j\<in>{0..<q}. 1 / q * measure (measure_spmf (?multi'_body c_o c_a s)) {((), (id, Some j), s')|s' id. True})"
        by(simp add: measure_pair_spmf_times spmf_conv_measure_spmf[symmetric] spmf_of_set)
      also have "\<dots> = 1 / q * measure (measure_spmf (?multi'_body c_o c_a s)) {((), (id, Some j\<^sub>s), s')|j\<^sub>s s' id. j\<^sub>s < q}"
        unfolding sum_distrib_left[symmetric]
        by(subst measure_spmf.finite_measure_finite_Union[symmetric])
          (auto intro!: arg_cong2[where f=measure] simp add: disjoint_family_on_def)
      finally show ?thesis by simp
    qed
    also have "?B = (\<lambda>(j\<^sub>s, _, (_, j\<^sub>0), _). j\<^sub>0 = Some j\<^sub>s) -` {True}"
      by (auto simp add: vimage_def)
    also have rw2: "measure ?M' \<dots> = spmf (bind_spmf (spmf_of_set {..<q}) (body2 c_o c_a s)) True"
      by (simp add: body2_def[abs_def] measure_map_spmf[symmetric] map_spmf_conv_bind_spmf
        split_def pair_spmf_alt_def spmf_conv_measure_spmf[symmetric])
    finally show ?thesis .
  qed
  hence "spmf (bind_spmf init (\<lambda>(c_a, c_o, s). game_multi' c_a c_o s)) True = spmf ?game2 True * q"
    unfolding initialize_def spmf_bind[where p=init]
    by (auto intro!: integral_cong_AE simp del: integral_mult_left_zero simp add: integral_mult_left_zero[symmetric])

  moreover
  have "ord_spmf (\<longrightarrow>) (body2 c_o c_a s j\<^sub>s) (body3 c_o c_a s j\<^sub>s)"
    if init: "(c_o, c_a, s) \<in> set_spmf init" and j\<^sub>s: "j\<^sub>s < Suc q" for c_o c_a s j\<^sub>s
  proof -
    define oracle2' where "oracle2' \<equiv> \<lambda>(b, (id, gs), s) guess. if id = j\<^sub>s then do {
        b' :: bool \<leftarrow> eval c_o c_a s guess;
        return_spmf ((), (Some b', (Suc id, Some (guess, s)), s))
      } else return_spmf ((), (b, (Suc id, gs), s))"

    let ?R = "\<lambda>((id1, j\<^sub>0), s1) (b', (id2, gs), s2). s1 = s2 \<and> id1 = id2 \<and> (j\<^sub>0 = Some j\<^sub>s \<longrightarrow> b' = Some True) \<and> (id2 \<le> j\<^sub>s \<longrightarrow> b' = None)"
    from init have "rel_spmf (rel_prod (=) ?R)
      (exec_gpv (extend_state_oracle (oracle c_o) \<oplus>\<^sub>O eval_oracle' c_o c_a) (\<A> c_a) ((0, None), s))
      (exec_gpv (extend_state_oracle (extend_state_oracle (oracle c_o)) \<oplus>\<^sub>O oracle2') (\<A> c_a) (None, (0, None), s))"
      by(intro exec_gpv_oracle_bisim[where X="?R"])(auto simp add: oracle2'_def eval_oracle'_def spmf_rel_map map_spmf_conv_bind_spmf[symmetric] rel_spmf_return_spmf2 lossless_eval o_def intro!: rel_spmf_reflI split: option.split_asm plus_oracle_split if_split_asm)
    then have "rel_spmf (\<longrightarrow>) (body2 c_o c_a s j\<^sub>s) 
      (do {
        (_, b', _, _) \<leftarrow> exec_gpv (\<dagger>\<dagger>(oracle c_o) \<oplus>\<^sub>O oracle2') (\<A> c_a) (None, (0, None), s);
        return_spmf (b' = Some True) })"
      (is "rel_spmf _ _ ?body2'")
      \<comment> \<open>We do not get equality here because the right hand side may return @{const True} even
        when the bad event has happened before the @{text j\<^sub>s}-th iteration.\<close>
      unfolding body2_def by(rule rel_spmf_bindI) clarsimp
    also
    let ?guess_oracle = "\<lambda>((id, gs), s) guess. return_spmf ((), (Suc id, if id = j\<^sub>s then Some (guess, s) else gs), s)"
    let ?I = "\<lambda>(idgs, s). case idgs of (_, None) \<Rightarrow> False | (i, Some _) \<Rightarrow> j\<^sub>s < i"
    interpret I: callee_invariant_on "\<dagger>(oracle c_o) \<oplus>\<^sub>O ?guess_oracle" "?I" \<I>_full
      by(simp)(unfold_locales; auto split: option.split)

    let ?f = "\<lambda>s. case snd (fst s) of None \<Rightarrow> return_spmf False | Some a \<Rightarrow> eval c_o c_a (snd a) (fst a)"
    let ?X = "\<lambda>j\<^sub>s (b1, (id1, gs1), s1) (b2, (id2, gs2), s2). b1 = b2 \<and> id1 = id2 \<and> gs1 = gs2 \<and> s1 = s2 \<and> (b2 = None \<longleftrightarrow> gs2 = None) \<and> (id2 \<le> j\<^sub>s \<longrightarrow> b2 = None)"
    have "?body2' = do {
      (a, r, s) \<leftarrow> exec_gpv (\<lambda>(r, s) x. do {
               (y, s') \<leftarrow> (\<dagger>(oracle c_o) \<oplus>\<^sub>O ?guess_oracle) s x;
               if ?I s' \<and> r = None then map_spmf (\<lambda>r. (y, Some r, s')) (?f s') else return_spmf (y, r, s')
             })
         (\<A> c_a) (None, (0, None), s);
      case r of None \<Rightarrow> ?f s \<bind> return_spmf | Some r' \<Rightarrow> return_spmf r' }"
      unfolding oracle2'_def spmf_rel_eq[symmetric]
      by(rule rel_spmf_bindI[OF exec_gpv_oracle_bisim'[where X="?X j\<^sub>s"]])
        (auto simp add: bind_map_spmf o_def spmf.map_comp split_beta conj_comms map_spmf_conv_bind_spmf[symmetric] spmf_rel_map rel_spmf_reflI cong: conj_cong split: plus_oracle_split)
    also have "\<dots> = do {
        us' \<leftarrow> exec_gpv (\<dagger>(oracle c_o) \<oplus>\<^sub>O ?guess_oracle) (\<A> c_a) ((0, None), s);
        (b' :: bool) \<leftarrow> ?f (snd us');
        return_spmf b' }"
      (is "_ = ?body2''")
      by(rule I.exec_gpv_bind_materialize[symmetric])(auto split: plus_oracle_split_asm option.split_asm)
    also have "\<dots> = do {
        us' \<leftarrow> exec_gpv_stop (lift_stop_oracle (\<dagger>(oracle c_o) \<oplus>\<^sub>O ?guess_oracle)) (\<A> c_a) ((0, None), s);
        (b' :: bool) \<leftarrow> ?f (snd us');
        return_spmf b' }"
      supply lift_stop_oracle_transfer[transfer_rule] gpv_stop_transfer[transfer_rule] exec_gpv_parametric'[transfer_rule]
      by transfer simp
    also let ?S = "\<lambda>((id1, gs1), s1) ((id2, gs2), s2). gs1 = gs2 \<and> (gs2 = None \<longrightarrow> s1 = s2 \<and> id1 = id2) \<and> (gs1 = None \<longleftrightarrow> id1 \<le> j\<^sub>s)"
    have "ord_spmf (\<longrightarrow>) \<dots> (exec_gpv_stop ((\<lambda>((id, gs), s) x. case gs of None \<Rightarrow> lift_stop_oracle (\<dagger>(oracle c_o)) ((id, gs), s) x | Some _ \<Rightarrow> return_spmf (None, ((id, gs), s))) \<oplus>\<^sub>O\<^sup>S
            (\<lambda>((id, gs), s) guess. return_spmf (if id \<ge> j\<^sub>s then None else Some (), (Suc id, if id = j\<^sub>s then Some (guess, s) else gs), s)))
           (\<A> c_a) ((0, None), s) \<bind>
          (\<lambda>us'. case snd (fst (snd us')) of None \<Rightarrow> return_spmf False | Some a \<Rightarrow> eval c_o c_a (snd a) (fst a)))"
      unfolding body3_def stop_oracle_def
      by(rule ord_spmf_exec_gpv_stop[where stop = "\<lambda>((id, guess), _). guess \<noteq> None" and S="?S", THEN ord_spmf_bindI])
        (auto split: prod.split_asm plus_oracle_split_asm split!: plus_oracle_stop_split simp del: not_None_eq simp add: spmf.map_comp o_def apfst_compose ord_spmf_map_spmf1 ord_spmf_map_spmf2 split_beta ord_spmf_return_spmf2 intro!: ord_spmf_reflI)
    also let ?X = "\<lambda>((id, gs), s1) (idgs, s2). s1 = s2 \<and> (case (gs, idgs) of (None, Inr id') \<Rightarrow> id' = j\<^sub>s - id \<and> id \<le> j\<^sub>s | (Some gs, Inl gs') \<Rightarrow> gs = gs' \<and> id > j\<^sub>s | _ \<Rightarrow> False)"
    have "\<dots> = body3 c_o c_a s j\<^sub>s" unfolding body3_def spmf_rel_eq[symmetric] stop_oracle_def
      by(rule exec_gpv_oracle_bisim'[where X="?X", THEN rel_spmf_bindI])
        (auto split: option.split_asm plus_oracle_stop_split nat.splits split!: sum.split simp add: spmf_rel_map intro!: rel_spmf_reflI)
    finally show ?thesis by(rule pmf.rel_mono_strong)(auto elim!: option.rel_cases ord_option.cases)
  qed
  { then have "ord_spmf (\<longrightarrow>) ?game2 ?game3"
      by(clarsimp simp add: initialize_def intro!: ord_spmf_bind_reflI)
    also
    let ?X = "\<lambda>(gsid, s) (gid, s'). s = s' \<and> rel_sum (\<lambda>(g, s1) g'. g = g' \<and> s1 = s') (=) gsid gid"
    have "rel_spmf (\<longrightarrow>) ?game3 (game_single (reduction q \<A>))"
      unfolding body3_def stop_oracle_def game_single_def reduction_def split_def initialize_def
      apply(clarsimp simp add: bind_map_spmf exec_gpv_bind exec_gpv_inline intro!: rel_spmf_bind_reflI)
      apply(rule rel_spmf_bindI[OF exec_gpv_oracle_bisim'[where X="?X"]])
      apply(auto split: plus_oracle_stop_split elim!: rel_sum.cases simp add: map_spmf_conv_bind_spmf[symmetric] split_def spmf_rel_map rel_spmf_reflI rel_spmf_return_spmf1 lossless_eval split: nat.split)
      done
    finally have "ord_spmf (\<longrightarrow>) ?game2 (game_single (reduction q \<A>))"
      by(rule pmf.rel_mono_strong)(auto elim!: option.rel_cases ord_option.cases)
    from this[THEN ord_spmf_measureD, of "{True}"]
    have "spmf ?game2 True \<le> spmf (game_single (reduction q \<A>)) True" unfolding spmf_conv_measure_spmf
      by(rule ord_le_eq_trans)(auto intro: arg_cong2[where f=measure]) }
  ultimately show ?thesis unfolding advantage_multi_def advantage_single_def 
    by(simp add: mult_right_mono)
qed

end

end
