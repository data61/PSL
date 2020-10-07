subsection \<open>Pair Memory\<close>

theory Pair_Memory
  imports "../state_monad/Memory"
begin

(* XXX Move *)
lemma map_add_mono:
  "(m1 ++ m2) \<subseteq>\<^sub>m (m1' ++ m2')" if "m1 \<subseteq>\<^sub>m m1'" "m2 \<subseteq>\<^sub>m m2'" "dom m1 \<inter> dom m2' = {}"
  using that unfolding map_le_def map_add_def dom_def by (auto split: option.splits)

lemma map_add_upd2:
  "f(x \<mapsto> y) ++ g = (f ++ g)(x \<mapsto> y)" if "dom f \<inter> dom g = {}" "x \<notin> dom g"
  apply (subst map_add_comm)
   defer
   apply simp
   apply (subst map_add_comm)
  using that
  by auto

locale pair_mem_defs =
  fixes lookup1 lookup2 :: "'a \<Rightarrow> ('mem, 'v option) state"
    and update1 update2 :: "'a \<Rightarrow> 'v \<Rightarrow> ('mem, unit) state"
    and move12 :: "'k1 \<Rightarrow> ('mem, unit) state"
    and get_k1 get_k2 :: "('mem, 'k1) state"
    and P :: "'mem \<Rightarrow> bool"
  fixes key1 :: "'k \<Rightarrow> 'k1" and key2 :: "'k \<Rightarrow> 'a"
begin

text \<open>We assume that look-ups happen on the older row, so it is biased towards the second entry.\<close>
definition
  "lookup_pair k = do {
     let k' = key1 k;
     k2 \<leftarrow> get_k2;
     if k' = k2
     then lookup2 (key2 k)
     else do {
       k1 \<leftarrow> get_k1;
       if k' = k1
       then lookup1 (key2 k)
       else State_Monad.return None
     }
   }
   "

text \<open>We assume that updates happen on the newer row, so it is biased towards the first entry.\<close>
definition
  "update_pair k v = do {
    let k' = key1 k;
    k1 \<leftarrow> get_k1;
    if k' = k1
    then update1 (key2 k) v
    else do {
      k2 \<leftarrow> get_k2;
      if k' = k2
      then update2 (key2 k) v
      else (move12 k' \<then> update1 (key2 k) v)
    }
  }
  "

sublocale pair: state_mem_defs lookup_pair update_pair .

sublocale mem1: state_mem_defs lookup1 update1 .

sublocale mem2: state_mem_defs lookup2 update2 .

definition
  "inv_pair heap \<equiv>
    let
      k1 = fst (State_Monad.run_state get_k1 heap);
      k2 = fst (State_Monad.run_state get_k2 heap)
    in
    (\<forall> k \<in> dom (mem1.map_of heap). \<exists> k'. key1 k' = k1 \<and> key2 k' = k) \<and>
    (\<forall> k \<in> dom (mem2.map_of heap). \<exists> k'. key1 k' = k2 \<and> key2 k' = k) \<and>
    k1 \<noteq> k2 \<and> P heap
  "

definition
  "map_of1 m k = (if key1 k = fst (State_Monad.run_state get_k1 m) then mem1.map_of m (key2 k) else None)"

definition
  "map_of2 m k = (if key1 k = fst (State_Monad.run_state get_k2 m) then mem2.map_of m (key2 k) else None)"

end (* Pair Mem Defs *)

locale pair_mem = pair_mem_defs +
  assumes get_state:
    "State_Monad.run_state get_k1 m = (k, m') \<Longrightarrow> m' = m"
    "State_Monad.run_state get_k2 m = (k, m') \<Longrightarrow> m' = m"
  assumes move12_correct:
    "P m \<Longrightarrow> State_Monad.run_state (move12 k1) m = (x, m') \<Longrightarrow> mem1.map_of m' \<subseteq>\<^sub>m Map.empty"
    "P m \<Longrightarrow> State_Monad.run_state (move12 k1) m = (x, m') \<Longrightarrow> mem2.map_of m' \<subseteq>\<^sub>m mem1.map_of m"
  assumes move12_keys:
    "State_Monad.run_state (move12 k1) m = (x, m') \<Longrightarrow> fst (State_Monad.run_state get_k1 m') = k1"
    "State_Monad.run_state (move12 k1) m = (x, m') \<Longrightarrow> fst (State_Monad.run_state get_k2 m') = fst (State_Monad.run_state get_k1 m)"
  assumes move12_inv:
    "lift_p P (move12 k1)"
  assumes lookup_inv:
    "lift_p P (lookup1 k')" "lift_p P (lookup2 k')"
  assumes update_inv:
    "lift_p P (update1 k' v)" "lift_p P (update2 k' v)"
  assumes lookup_keys:
    "P m \<Longrightarrow> State_Monad.run_state (lookup1 k') m = (v', m') \<Longrightarrow>
     fst (State_Monad.run_state get_k1 m') = fst (State_Monad.run_state get_k1 m)"
    "P m \<Longrightarrow> State_Monad.run_state (lookup1 k') m = (v', m') \<Longrightarrow>
     fst (State_Monad.run_state get_k2 m') = fst (State_Monad.run_state get_k2 m)"
    "P m \<Longrightarrow> State_Monad.run_state (lookup2 k') m = (v', m') \<Longrightarrow>
     fst (State_Monad.run_state get_k1 m') = fst (State_Monad.run_state get_k1 m)"
    "P m \<Longrightarrow> State_Monad.run_state (lookup2 k') m = (v', m') \<Longrightarrow>
     fst (State_Monad.run_state get_k2 m') = fst (State_Monad.run_state get_k2 m)"
  assumes update_keys:
    "P m \<Longrightarrow> State_Monad.run_state (update1 k' v) m = (x, m') \<Longrightarrow>
     fst (State_Monad.run_state get_k1 m') = fst (State_Monad.run_state get_k1 m)"
    "P m \<Longrightarrow> State_Monad.run_state (update1 k' v) m = (x, m') \<Longrightarrow>
     fst (State_Monad.run_state get_k2 m') = fst (State_Monad.run_state get_k2 m)"
    "P m \<Longrightarrow> State_Monad.run_state (update2 k' v) m = (x, m') \<Longrightarrow>
     fst (State_Monad.run_state get_k1 m') = fst (State_Monad.run_state get_k1 m)"
    "P m \<Longrightarrow> State_Monad.run_state (update2 k' v) m = (x, m') \<Longrightarrow>
     fst (State_Monad.run_state get_k2 m') = fst (State_Monad.run_state get_k2 m)"
  assumes
    lookup_correct:
      "P m \<Longrightarrow> mem1.map_of (snd (State_Monad.run_state (lookup1 k') m)) \<subseteq>\<^sub>m (mem1.map_of m)"
      "P m \<Longrightarrow> mem2.map_of (snd (State_Monad.run_state (lookup1 k') m)) \<subseteq>\<^sub>m (mem2.map_of m)"
      "P m \<Longrightarrow> mem1.map_of (snd (State_Monad.run_state (lookup2 k') m)) \<subseteq>\<^sub>m (mem1.map_of m)"
      "P m \<Longrightarrow> mem2.map_of (snd (State_Monad.run_state (lookup2 k') m)) \<subseteq>\<^sub>m (mem2.map_of m)"
  assumes
    update_correct:
      "P m \<Longrightarrow> mem1.map_of (snd (State_Monad.run_state (update1 k' v) m)) \<subseteq>\<^sub>m (mem1.map_of m)(k' \<mapsto> v)"
      "P m \<Longrightarrow> mem2.map_of (snd (State_Monad.run_state (update2 k' v) m)) \<subseteq>\<^sub>m (mem2.map_of m)(k' \<mapsto> v)"
      "P m \<Longrightarrow> mem2.map_of (snd (State_Monad.run_state (update1 k' v) m)) \<subseteq>\<^sub>m mem2.map_of m"
      "P m \<Longrightarrow> mem1.map_of (snd (State_Monad.run_state (update2 k' v) m)) \<subseteq>\<^sub>m mem1.map_of m"
begin

lemma map_of_le_pair:
  "pair.map_of m \<subseteq>\<^sub>m map_of1 m ++ map_of2 m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding State_Monad.bind_def
  by (auto 4 4
        simp: mem2.map_of_def mem1.map_of_def Let_def
        dest: get_state split: prod.split_asm if_split_asm
     )

lemma pair_le_map_of:
  "map_of1 m ++ map_of2 m \<subseteq>\<^sub>m pair.map_of m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding State_Monad.bind_def
  by (auto
        simp: mem2.map_of_def mem1.map_of_def State_Monad.run_state_return Let_def
        dest: get_state split: prod.splits if_split_asm option.split
     )

lemma map_of_eq_pair:
  "map_of1 m ++ map_of2 m = pair.map_of m"
  if "inv_pair m"
  using that
  unfolding pair.map_of_def map_of1_def map_of2_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  unfolding State_Monad.bind_def
  by (auto 4 4
        simp: mem2.map_of_def mem1.map_of_def State_Monad.run_state_return Let_def
        dest: get_state split: prod.splits option.split
     )

lemma inv_pair_neq[simp]:
  False if "inv_pair m" "fst (State_Monad.run_state get_k1 m) = fst (State_Monad.run_state get_k2 m)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D:
  "P m" if "inv_pair m"
  using that unfolding inv_pair_def by (auto simp: Let_def)

lemma inv_pair_domD[intro]:
  "dom (map_of1 m) \<inter> dom (map_of2 m) = {}" if "inv_pair m"
  using that unfolding inv_pair_def map_of1_def map_of2_def by (auto split: if_split_asm)

lemma move12_correct1:
  "map_of1 heap' \<subseteq>\<^sub>m Map.empty" if "State_Monad.run_state (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct[OF that(2,1)] unfolding map_of1_def by (auto simp: move12_keys map_le_def)

lemma move12_correct2:
  "map_of2 heap' \<subseteq>\<^sub>m map_of1 heap" if "State_Monad.run_state (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct(2)[OF that(2,1)] that unfolding map_of1_def map_of2_def
  by (auto simp: move12_keys map_le_def)

lemma dom_empty[simp]:
  "dom (map_of1 heap') = {}" if "State_Monad.run_state (move12 k1) heap = (x, heap')" "P heap"
  using move12_correct1[OF that] by (auto dest: map_le_implies_dom_le)

lemma inv_pair_lookup1:
  "inv_pair m'" if "State_Monad.run_state (lookup1 k) m = (v, m')" "inv_pair m"
  using that lookup_inv[of k] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  by (auto 4 4
        simp: Let_def lookup_keys
        dest: lift_p_P lookup_correct[of _ k, THEN map_le_implies_dom_le]
     )

lemma inv_pair_lookup2:
  "inv_pair m'" if "State_Monad.run_state (lookup2 k) m = (v, m')" "inv_pair m"
  using that lookup_inv[of k] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  by (auto 4 4
        simp: Let_def lookup_keys
        dest: lift_p_P lookup_correct[of _ k, THEN map_le_implies_dom_le]
     )

lemma inv_pair_update1:
  "inv_pair m'"
  if "State_Monad.run_state (update1 (key2 k) v) m = (v', m')" "inv_pair m" "fst (State_Monad.run_state get_k1 m) = key1 k"
  using that update_inv[of "key2 k" v] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def update_keys
        dest: lift_p_P update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]
     )
   apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  done

lemma inv_pair_update2:
  "inv_pair m'"
  if "State_Monad.run_state (update2 (key2 k) v) m = (v', m')" "inv_pair m" "fst (State_Monad.run_state get_k2 m) = key1 k"
  using that update_inv[of "key2 k" v] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def update_keys
        dest: lift_p_P update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]
     )
   apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  apply (frule update_correct[of _ "key2 k" v, THEN map_le_implies_dom_le]; auto 13 2; fail)
  done

lemma inv_pair_move12:
  "inv_pair m'"
  if "State_Monad.run_state (move12 k) m = (v', m')" "inv_pair m" "fst (State_Monad.run_state get_k1 m) \<noteq> k"
  using that move12_inv[of "k"] inv_pair_P_D[OF \<open>inv_pair m\<close>] unfolding inv_pair_def
  apply (auto
        simp: Let_def move12_keys
        dest: lift_p_P move12_correct[of _ "k", THEN map_le_implies_dom_le]
     )
  apply (blast dest: move12_correct[of _ "k", THEN map_le_implies_dom_le])
  done

lemma mem_correct_pair:
  "mem_correct lookup_pair update_pair inv_pair"
  if injective: "\<forall> k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
proof (standard, goal_cases)
  case (1 k) \<comment> \<open>Lookup invariant\<close>
  show ?case
    unfolding lookup_pair_def Let_def
    by (auto 4 4
        intro!: lift_pI
        dest: get_state inv_pair_lookup1 inv_pair_lookup2
        simp: State_Monad.bind_def State_Monad.run_state_return
        split: if_split_asm prod.split_asm
        )
next
  case (2 k v) \<comment> \<open>Update invariant\<close>
  show ?case
    unfolding update_pair_def Let_def
    apply (auto 4 4
        intro!: lift_pI intro: inv_pair_update1 inv_pair_update2
        dest: get_state
        simp: State_Monad.bind_def get_state State_Monad.run_state_return
        split: if_split_asm prod.split_asm
        )+
    apply (elim inv_pair_update1 inv_pair_move12)
      apply (((subst get_state, assumption)+)?, auto intro: move12_keys dest: get_state; fail)+
    done
next
  case (3 m k)
  {
    let ?m = "snd (State_Monad.run_state (lookup2 (key2 k)) m)"
    have "map_of1 ?m \<subseteq>\<^sub>m map_of1 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of1_def surjective_pairing)
    moreover have "map_of2 ?m \<subseteq>\<^sub>m map_of2 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of2_def surjective_pairing)
    moreover have "dom (map_of1 ?m) \<inter> dom (map_of2 m) = {}"
      using 3 \<open>map_of1 ?m \<subseteq>\<^sub>m map_of1 m\<close> inv_pair_domD map_le_implies_dom_le by fastforce
    moreover have "inv_pair ?m"
      using 3 inv_pair_lookup2 surjective_pairing by metis
    ultimately have "pair.map_of ?m \<subseteq>\<^sub>m pair.map_of m"
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
      by (auto intro: 3 map_add_mono)
  }
  moreover
  {
    let ?m = "snd (State_Monad.run_state (lookup1 (key2 k)) m)"
    have "map_of1 ?m \<subseteq>\<^sub>m map_of1 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of1_def surjective_pairing)
    moreover have "map_of2 ?m \<subseteq>\<^sub>m map_of2 m"
      by (smt 3 domIff inv_pair_P_D local.lookup_keys lookup_correct map_le_def map_of2_def surjective_pairing)
    moreover have "dom (map_of1 ?m) \<inter> dom (map_of2 m) = {}"
      using 3 \<open>map_of1 ?m \<subseteq>\<^sub>m map_of1 m\<close> inv_pair_domD map_le_implies_dom_le by fastforce
    moreover have "inv_pair ?m"
      using 3 inv_pair_lookup1 surjective_pairing by metis
    ultimately have "pair.map_of ?m \<subseteq>\<^sub>m pair.map_of m"
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
      by (auto intro: 3 map_add_mono)
  }
  ultimately show ?case
    by (auto
        split:if_split prod.split
        simp: Let_def lookup_pair_def State_Monad.bind_def State_Monad.run_state_return dest: get_state intro: map_le_refl
        )
next
  case prems: (4 m k v)
  let ?m1 = "snd (State_Monad.run_state (update1 (key2 k) v) m)"
  let ?m2 = "snd (State_Monad.run_state (update2 (key2 k) v) m)"
  from prems have disjoint: "dom (map_of1 m) \<inter> dom (map_of2 m) = {}"
    by (simp add: inv_pair_domD)
  show ?case
    apply (auto
        intro: map_le_refl dest: get_state
        split: prod.split
        simp: Let_def update_pair_def State_Monad.bind_def State_Monad.run_state_return
        )
  proof goal_cases
    case (1 m')
    then have "m' = m"
      by (rule get_state)
    from 1 prems have "map_of1 ?m1 \<subseteq>\<^sub>m map_of1 m(k \<mapsto> v)"
      by (smt inv_pair_P_D map_le_def map_of1_def surjective_pairing domIff
          fst_conv fun_upd_apply injective update_correct update_keys
          )
    moreover from prems have "map_of2 ?m1 \<subseteq>\<^sub>m map_of2 m"
      by (smt domIff inv_pair_P_D update_correct update_keys map_le_def map_of2_def surjective_pairing)
    moreover from prems have "dom (map_of1 ?m1) \<inter> dom (map_of2 m) = {}"
      by (smt inv_pair_P_D[OF \<open>inv_pair m\<close>] domIff Int_emptyI eq_snd_iff inv_pair_neq 
          map_of1_def map_of2_def update_keys(1)
          )
    moreover from 1 prems have "k \<notin> dom (map_of2 m)"
      using inv_pair_neq map_of2_def by fastforce
    moreover from 1 prems have "inv_pair ?m1"
      using inv_pair_update1 fst_conv surjective_pairing by metis
    ultimately show "pair.map_of (snd (State_Monad.run_state (update1 (key2 k) v) m')) \<subseteq>\<^sub>m pair.map_of m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> using disjoint
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric], rule prems)
       apply (subst map_add_upd2[symmetric])
      by (auto intro: map_add_mono)
  next
    case (2 k1 m' m'')
    then have "m' = m" "m'' = m"
      by (auto dest: get_state)
    from 2 prems have "map_of2 ?m2 \<subseteq>\<^sub>m map_of2 m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> \<open>m'' = m\<close>
      by (smt inv_pair_P_D map_le_def map_of2_def surjective_pairing domIff
          fst_conv fun_upd_apply injective update_correct update_keys
          )
    moreover from prems have "map_of1 ?m2 \<subseteq>\<^sub>m map_of1 m"
      by (smt domIff inv_pair_P_D update_correct update_keys map_le_def map_of1_def surjective_pairing)
    moreover from 2 have "dom (map_of1 ?m2) \<inter> dom (map_of2 m(k \<mapsto> v)) = {}"
      unfolding \<open>m' = m\<close>
      by (smt domIff \<open>map_of1 ?m2 \<subseteq>\<^sub>m map_of1 m\<close> disjoint_iff_not_equal fst_conv fun_upd_apply
          map_le_def map_of1_def map_of2_def
          )
    moreover from 2 prems have "inv_pair ?m2"
      unfolding \<open>m' = m\<close>
      using inv_pair_update2 fst_conv surjective_pairing by metis
    ultimately show "pair.map_of (snd (State_Monad.run_state (update2 (key2 k) v) m'')) \<subseteq>\<^sub>m pair.map_of m(k \<mapsto> v)"
      unfolding \<open>m' = m\<close> \<open>m'' = m\<close>
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric], rule prems)
       apply (subst map_add_upd[symmetric])
      by (rule map_add_mono)
  next
    case (3 k1 m1 k2 m2 m3)
    then have "m1 = m" "m2 = m"
      by (auto dest: get_state)
    let ?m3 = "snd (State_Monad.run_state (update1 (key2 k) v) m3)"
    from 3 prems have "map_of1 ?m3 \<subseteq>\<^sub>m map_of2 m(k \<mapsto> v)"
      unfolding \<open>m2 = m\<close>
      by (smt inv_pair_P_D map_le_def map_of1_def surjective_pairing domIff
          fst_conv fun_upd_apply injective
          inv_pair_move12 move12_correct move12_keys update_correct update_keys
          )
    moreover have "map_of2 ?m3 \<subseteq>\<^sub>m map_of1 m"
    proof -
      from prems 3 have "P m" "P m3"
        unfolding \<open>m1 = m\<close> \<open>m2 = m\<close>
        using inv_pair_P_D[OF prems] by (auto elim: lift_p_P[OF move12_inv])
      from 3(3)[unfolded \<open>m2 = m\<close>] have "mem2.map_of ?m3 \<subseteq>\<^sub>m mem1.map_of m"
        by - (erule map_le_trans[OF update_correct(3)[OF \<open>P m3\<close>] move12_correct(2)[OF \<open>P m\<close>]])
      with 3 prems show ?thesis
        unfolding \<open>m1 = m\<close> \<open>m2 = m\<close> map_le_def map_of2_def
        apply auto
        apply (frule move12_keys(2), simp)
        by (metis
            domI inv_pair_def map_of1_def surjective_pairing
            inv_pair_move12 move12_keys(2) update_keys(2)
            )
    qed
    moreover from prems 3 have "dom (map_of1 ?m3) \<inter> dom (map_of1 m) = {}"
      unfolding \<open>m1 = m\<close> \<open>m2 = m\<close>
      by (smt inv_pair_P_D disjoint_iff_not_equal map_of1_def surjective_pairing domIff
          fst_conv inv_pair_move12 move12_keys update_keys
          )
    moreover from 3 have "k \<notin> dom (map_of1 m)"
      by (simp add: domIff map_of1_def)
    moreover from 3 prems have "inv_pair ?m3"
      unfolding \<open>m2 = m\<close>
      by (metis inv_pair_move12 inv_pair_update1 move12_keys(1) fst_conv surjective_pairing)
    ultimately show ?case
      unfolding \<open>m1 = m\<close> \<open>m2 = m\<close> using disjoint
      apply (subst map_of_eq_pair[symmetric])
       defer
       apply (subst map_of_eq_pair[symmetric])
        apply (rule prems)
       apply (subst (2) map_add_comm)
        defer
        apply (subst map_add_upd2[symmetric])
          apply (auto intro: map_add_mono)
      done
  qed
qed

lemma emptyI:
  assumes "inv_pair m" "mem1.map_of m \<subseteq>\<^sub>m Map.empty" "mem2.map_of m \<subseteq>\<^sub>m Map.empty"
  shows "pair.map_of m \<subseteq>\<^sub>m Map.empty"
  using assms by (auto simp: map_of1_def map_of2_def map_le_def map_of_eq_pair[symmetric])

end (* Pair Mem *)


datatype ('k, 'v) pair_storage = Pair_Storage 'k 'k 'v 'v

context mem_correct_empty
begin

context
  fixes key :: "'a \<Rightarrow> 'k"
begin

text \<open>We assume that look-ups happen on the older row, so it is biased towards the second entry.\<close>
definition
  "lookup_pair k =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key k in
        if k' = k2 then case State_Monad.run_state (lookup k) m2 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m1 m)
        else if k' = k1 then case State_Monad.run_state (lookup k) m1 of (v, m) \<Rightarrow> (v, Pair_Storage k1 k2 m m2)
        else (None, mem)
    )
    )
  "

text \<open>We assume that updates happen on the newer row, so it is biased towards the first entry.\<close>
definition
  "update_pair k v =
    State (\<lambda> mem.
    (
      case mem of Pair_Storage k1 k2 m1 m2 \<Rightarrow> let k' = key k in
        if k' = k1 then case State_Monad.run_state (update k v) m1 of (_, m) \<Rightarrow> ((), Pair_Storage k1 k2 m m2)
        else if k' = k2 then case State_Monad.run_state (update k v) m2 of (_, m) \<Rightarrow> ((),Pair_Storage k1 k2 m1 m)
        else case State_Monad.run_state (update k v) empty of (_, m) \<Rightarrow> ((), Pair_Storage k' k1 m m1)
    )
    )
  "

interpretation pair: state_mem_defs lookup_pair update_pair .

definition
  "inv_pair p = (case p of Pair_Storage k1 k2 m1 m2 \<Rightarrow>
    key ` dom (map_of m1) \<subseteq> {k1} \<and> key ` dom (map_of m2) \<subseteq> {k2} \<and> k1 \<noteq> k2 \<and> P m1 \<and> P m2
  )"

lemma map_of_le_pair:
  "pair.map_of (Pair_Storage k1 k2 m1 m2) \<subseteq>\<^sub>m (map_of m1 ++ map_of m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 6 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma pair_le_map_of:
  "map_of m1 ++ map_of m2 \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 5 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma map_of_eq_pair:
  "map_of m1 ++ map_of m2 = pair.map_of (Pair_Storage k1 k2 m1 m2)"
  if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that
  unfolding pair.map_of_def
  unfolding lookup_pair_def inv_pair_def map_of_def map_le_def dom_def map_add_def
  by (auto 4 7 split: prod.split_asm if_split_asm option.split simp: Let_def)

lemma inv_pair_neq[simp, dest]:
  False if "inv_pair (Pair_Storage k k x y)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D1:
  "P m1" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_P_D2:
  "P m2" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by auto

lemma inv_pair_domD[intro]:
  "dom (map_of m1) \<inter> dom (map_of m2) = {}" if "inv_pair (Pair_Storage k1 k2 m1 m2)"
  using that unfolding inv_pair_def by fastforce

lemma mem_correct_pair:
  "mem_correct lookup_pair update_pair inv_pair"
proof (standard, goal_cases)
  case (1 k) \<comment> \<open>Lookup invariant\<close>
  with lookup_inv[of k] show ?case
    unfolding lookup_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
         (force dest!: lookup_correct[of _ k] map_le_implies_dom_le)+
       )
next
  case (2 k v) \<comment> \<open>Update invariant\<close>
  with update_inv[of k v] update_correct[OF P_empty, of k v] P_empty show ?case
    unfolding update_pair_def Let_def
    by (auto intro!: lift_pI split: pair_storage.split_asm if_split_asm prod.split_asm)
       (auto dest: lift_p_P simp: inv_pair_def,
         (force dest: lift_p_P dest!: update_correct[of _ k v] map_le_implies_dom_le)+
       )
next
  case (3 m k)
  {
    fix m1 v1 m1' m2 v2 m2' k1 k2
    assume assms:
      "State_Monad.run_state (lookup k) m1 = (v1, m1')" "State_Monad.run_state (lookup k) m2 = (v2, m2')"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    have [intro]: "map_of m1' \<subseteq>\<^sub>m map_of m1" "map_of m2' \<subseteq>\<^sub>m map_of m2"
      using lookup_correct[OF \<open>P m1\<close>, of k] lookup_correct[OF \<open>P m2\<close>, of k] assms by auto
    from inv_pair_domD[OF assms(3)] have 1: "dom (map_of m1') \<inter> dom (map_of m2) = {}"
      by (metis (no_types) \<open>map_of m1' \<subseteq>\<^sub>m map_of m1\<close> disjoint_iff_not_equal domIff map_le_def)
    have inv1: "inv_pair (Pair_Storage (key k) k2 m1' m2)" if "k2 \<noteq> key k" "k1 = key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,3) lookup_correct[OF \<open>P m1\<close>, of k, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      using lookup_inv[of k] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key k) m1 m2')" if "k2 = key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(3) unfolding inv_pair_def by fastforce
      subgoal for x x' y
        using assms(2,3) lookup_correct[OF \<open>P m2\<close>, of k, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by fastforce
      using lookup_inv[of k] assms unfolding lift_p_def by force
    have A:
      "pair.map_of (Pair_Storage (key k) k2 m1' m2) \<subseteq>\<^sub>m pair.map_of (Pair_Storage (key k) k2 m1 m2)"
      if "k2 \<noteq> key k" "k1 = key k"
      using inv1 assms(3) 1
      by (auto intro: map_add_mono map_le_refl simp: that map_of_eq_pair[symmetric])
    have B:
      "pair.map_of (Pair_Storage k1 (key k) m1 m2') \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 (key k) m1 m2)"
      if "k2 = key k" "k1 \<noteq> key k"
      using inv2 assms(3) that
      by (auto intro: map_add_mono map_le_refl simp: map_of_eq_pair[symmetric] dest: inv_pair_domD)
    note A B
  }
  with \<open>inv_pair m\<close> show ?case
    by (auto split: pair_storage.split if_split prod.split simp: Let_def lookup_pair_def)
next
  case (4 m k v)
  {
    fix m1 v1 m1' m2 v2 m2' m3 k1 k2
    assume assms:
      "State_Monad.run_state (update k v) m1 = ((), m1')" "State_Monad.run_state (update k v) m2 = ((), m2')"
      "State_Monad.run_state (update k v) empty = ((), m3)"
      "inv_pair (Pair_Storage k1 k2 m1 m2)"
    from assms have "P m1" "P m2"
      by (auto intro: inv_pair_P_D1 inv_pair_P_D2)
    from assms(3) P_empty update_inv[of k v] have "P m3"
      unfolding lift_p_def by auto
    have [intro]: "map_of m1' \<subseteq>\<^sub>m map_of m1(k \<mapsto> v)" "map_of m2' \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)"
      using update_correct[OF \<open>P m1\<close>, of k v] update_correct[OF \<open>P m2\<close>, of k v] assms by auto
    have "map_of m3 \<subseteq>\<^sub>m map_of empty(k \<mapsto> v)"
      using assms(3) update_correct[OF P_empty, of k v] by auto
    also have "\<dots> \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)"
      using empty_correct by (auto elim: map_le_trans intro!: map_le_upd)
    finally have "map_of m3 \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)" .
    have 1: "dom (map_of m1) \<inter> dom (map_of m2(k \<mapsto> v)) = {}" if "k1 \<noteq> key k"
      using assms(4) that by (force simp: inv_pair_def)
    have 2: "dom (map_of m3) \<inter> dom (map_of m1) = {}" if "k1 \<noteq> key k"
      using \<open>local.map_of m3 \<subseteq>\<^sub>m local.map_of empty(k \<mapsto> v)\<close> assms(4) that
      by (fastforce dest!: map_le_implies_dom_le simp: inv_pair_def)
    have inv: "inv_pair (Pair_Storage (key k) k1 m3 m1)" if "k2 \<noteq> key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> \<open>P m3\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x x' y
        using assms(3) update_correct[OF P_empty, of k v, THEN map_le_implies_dom_le]
          empty_correct
        by (auto dest: map_le_implies_dom_le)
      subgoal for x x' y
        using assms(4) unfolding inv_pair_def by fastforce
      done
    have A:
      "pair.map_of (Pair_Storage (key k) k1 m3 m1) \<subseteq>\<^sub>m pair.map_of (Pair_Storage k1 k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key k" "k1 \<noteq> key k"
      using inv assms(4) \<open>map_of m3 \<subseteq>\<^sub>m map_of m2(k \<mapsto> v)\<close> 1
      apply (simp add: that map_of_eq_pair[symmetric])
      apply (subst map_add_upd[symmetric], subst Map.map_add_comm, rule 2, rule that)
      by (rule map_add_mono; auto)
    have inv1: "inv_pair (Pair_Storage (key k) k2 m1' m2)" if "k2 \<noteq> key k" "k1 = key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(1,4) update_correct[OF \<open>P m1\<close>, of k v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by auto
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      using update_inv[of k v] assms unfolding lift_p_def by force
    have inv2: "inv_pair (Pair_Storage k1 (key k) m1 m2')" if "k2 = key k" "k1 \<noteq> key k"
      using that \<open>P m1\<close> \<open>P m2\<close> unfolding inv_pair_def
      apply clarsimp
      apply safe
      subgoal for x' y
        using assms(4) unfolding inv_pair_def by fastforce
      subgoal for x x' y
        using assms(2,4) update_correct[OF \<open>P m2\<close>, of k v, THEN map_le_implies_dom_le]
        unfolding inv_pair_def by fastforce
      using update_inv[of k v] assms unfolding lift_p_def by force
    have C:
      "pair.map_of (Pair_Storage (key k) k2 m1' m2) \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage (key k) k2 m1 m2)(k \<mapsto> v)"
      if "k2 \<noteq> key k" "k1 = key k"
      using inv1[OF that] assms(4) \<open>inv_pair m\<close>
      by (simp add: that map_of_eq_pair[symmetric])
         (subst map_add_upd2[symmetric]; force simp: inv_pair_def intro: map_add_mono map_le_refl)
    have B:
      "pair.map_of (Pair_Storage k1 (key k) m1 m2') \<subseteq>\<^sub>m
       pair.map_of (Pair_Storage k1 (key k) m1 m2)(k \<mapsto> v)"
      if "k2 = key k" "k1 \<noteq> key k"
      using inv2[OF that] assms(4)
      by (simp add: that map_of_eq_pair[symmetric])
         (subst map_add_upd[symmetric]; rule map_add_mono; force simp: inv_pair_def)
    note A B C
  }
  with \<open>inv_pair m\<close> show ?case
    by (auto split: pair_storage.split if_split prod.split simp: Let_def update_pair_def)
qed

end (* Key function *)

end (* Lookup & Update w/ Empty *)

end (* Theory *)
