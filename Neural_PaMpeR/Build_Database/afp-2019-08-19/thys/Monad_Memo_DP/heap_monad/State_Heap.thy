subsection \<open>Relation Between the State and the Heap Monad\<close>

theory State_Heap
  imports
    "../state_monad/DP_CRelVS"
    "HOL-Imperative_HOL.Imperative_HOL"
    State_Heap_Misc
    Heap_Monad_Ext
begin

definition lift_p :: "(heap \<Rightarrow> bool) \<Rightarrow> 'a Heap \<Rightarrow> bool" where
  "lift_p P f =
    (\<forall> heap. P heap \<longrightarrow> (case execute f heap of None \<Rightarrow> False | Some (_, heap) \<Rightarrow> P heap))"

context
  fixes P f heap
  assumes lift: "lift_p P f" and P: "P heap"
begin

lemma execute_cases:
  "case execute f heap of None \<Rightarrow> False | Some (_, heap) \<Rightarrow> P heap"
  using lift P unfolding lift_p_def by auto

lemma execute_cases':
  "case execute f heap of Some (_, heap) \<Rightarrow> P heap"
  using execute_cases by (auto split: option.split)

lemma lift_p_None[simp, dest]:
  False if "execute f heap = None"
  using that execute_cases by auto

lemma lift_p_P:
  "case the (execute f heap) of (_, heap) \<Rightarrow> P heap"
  using execute_cases by (auto split: option.split_asm)

lemma lift_p_P':
  "P heap'" if "the (execute f heap) = (v, heap')"
  using that lift_p_P by auto

lemma lift_p_P'':
  "P heap'" if "execute f heap = Some (v, heap')"
  using that lift_p_P by auto

lemma lift_p_the_Some[simp]:
  "execute f heap = Some (v, heap')" if "the (execute f heap) = (v, heap')"
  using that execute_cases by (auto split: option.split_asm)

lemma lift_p_E:
  obtains v heap' where "execute f heap = Some (v, heap')" "P heap'"
  using execute_cases by (cases "execute f heap") auto

end

definition "state_of s \<equiv> State (\<lambda> heap. the (execute s heap))"

locale heap_mem_defs =
  fixes P :: "heap \<Rightarrow> bool"
    and lookup :: "'k \<Rightarrow> 'v option Heap"
    and update :: "'k \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition rel_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (heap, 'a) state \<Rightarrow> 'b Heap \<Rightarrow> bool" where
  "rel_state R f g \<equiv>
    \<forall> heap. P heap \<longrightarrow>
      (case State_Monad.run_state f heap of (v1, heap1) \<Rightarrow> case execute g heap of
        Some (v2, heap2) \<Rightarrow> R v1 v2 \<and> heap1 = heap2 \<and> P heap2 | None \<Rightarrow> False)"

definition "lookup' k \<equiv> State (\<lambda> heap. the (execute (lookup k) heap))"

definition "update' k v \<equiv> State (\<lambda> heap. the (execute (update k v) heap))"

definition "heap_get = Heap_Monad.Heap (\<lambda> heap. Some (heap, heap))"

definition checkmem :: "'k \<Rightarrow> 'v Heap \<Rightarrow> 'v Heap" where
  "checkmem param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> return x
    | None \<Rightarrow> Heap_Monad.bind calc (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

definition checkmem' :: "'k \<Rightarrow> (unit \<Rightarrow> 'v Heap) \<Rightarrow> 'v Heap" where
  "checkmem' param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> return x
    | None \<Rightarrow> Heap_Monad.bind (calc ()) (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

lemma checkmem_checkmem':
  "checkmem' param (\<lambda>_. calc) = checkmem param calc"
  unfolding checkmem'_def checkmem_def ..

definition map_of_heap where
  "map_of_heap heap k = fst (the (execute (lookup k) heap))"

lemma rel_state_elim:
  assumes "rel_state R f g" "P heap"
  obtains heap' v v' where
    "State_Monad.run_state f heap = (v, heap')" "execute g heap = Some (v', heap')" "R v v'" "P heap'"
  apply atomize_elim
  using assms unfolding rel_state_def
  apply auto
  apply (cases "State_Monad.run_state f heap")
  apply auto
  apply (auto split: option.split_asm)
  done

lemma rel_state_intro:
  assumes
    "\<And> heap v heap'. P heap \<Longrightarrow> State_Monad.run_state f heap = (v, heap')
      \<Longrightarrow> \<exists> v'. R v v' \<and> execute g heap = Some (v', heap')"
    "\<And> heap v heap'. P heap \<Longrightarrow> State_Monad.run_state f heap = (v, heap') \<Longrightarrow> P heap'"
  shows "rel_state R f g"
  unfolding rel_state_def
  apply auto
  apply (frule assms(1)[rotated])
   apply (auto intro: assms(2))
  done

context
  includes lifting_syntax state_monad_syntax
begin

lemma transfer_bind[transfer_rule]:
  "(rel_state R ===> (R ===> rel_state Q) ===> rel_state Q) State_Monad.bind Heap_Monad.bind"
  unfolding rel_fun_def State_Monad.bind_def Heap_Monad.bind_def
  by (force elim!: rel_state_elim intro!: rel_state_intro)

lemma transfer_return[transfer_rule]:
  "(R ===> rel_state R) State_Monad.return Heap_Monad.return"
  unfolding rel_fun_def State_Monad.return_def Heap_Monad.return_def
  by (fastforce intro: rel_state_intro elim: rel_state_elim simp: execute_heap)

lemma fun_app_lifted_transfer:
  "(rel_state (R ===> rel_state Q) ===> rel_state R ===> rel_state Q)
      State_Monad_Ext.fun_app_lifted Heap_Monad_Ext.fun_app_lifted"
  unfolding State_Monad_Ext.fun_app_lifted_def Heap_Monad_Ext.fun_app_lifted_def by transfer_prover

lemma transfer_get[transfer_rule]:
  "rel_state (=) State_Monad.get heap_get"
  unfolding State_Monad.get_def heap_get_def by (auto intro: rel_state_intro)

end (* Lifting Syntax *)

end (* Heap Mem Defs *)

locale heap_inv = heap_mem_defs _ lookup for lookup :: "'k \<Rightarrow> 'v option Heap"  +
  assumes lookup_inv: "lift_p P (lookup k)"
  assumes update_inv: "lift_p P (update k v)"
begin

lemma rel_state_lookup:
  "rel_state (=) (lookup' k) (lookup k)"
  unfolding rel_state_def lookup'_def using lookup_inv[of k] by (auto intro: lift_p_P')

lemma rel_state_update:
  "rel_state (=) (update' k v) (update k v)"
  unfolding rel_state_def update'_def using update_inv[of k v] by (auto intro: lift_p_P')

context
  includes lifting_syntax
begin

lemma transfer_lookup:
  "((=) ===> rel_state (=)) lookup' lookup"
  unfolding rel_fun_def by (auto intro: rel_state_lookup)

lemma transfer_update:
  "((=) ===> (=) ===> rel_state (=)) update' update"
  unfolding rel_fun_def by (auto intro: rel_state_update)

lemma transfer_checkmem:
  "((=) ===> rel_state (=) ===> rel_state (=))
    (state_mem_defs.checkmem lookup' update') checkmem"
  supply [transfer_rule] = transfer_lookup transfer_update
  unfolding state_mem_defs.checkmem_def checkmem_def by transfer_prover

end (* Lifting Syntax *)

end (* Heap Invariant *)

locale heap_correct =
  heap_inv +
  assumes lookup_correct:
      "P m \<Longrightarrow> map_of_heap (snd (the (execute (lookup k) m))) \<subseteq>\<^sub>m (map_of_heap m)"
  and update_correct:
      "P m \<Longrightarrow> map_of_heap (snd (the (execute (update k v) m))) \<subseteq>\<^sub>m (map_of_heap m)(k \<mapsto> v)"
begin

lemma lookup'_correct:
  "state_mem_defs.map_of lookup' (snd (State_Monad.run_state (lookup' k) m)) \<subseteq>\<^sub>m (state_mem_defs.map_of lookup' m)" if "P m"
  using \<open>P m\<close> unfolding state_mem_defs.map_of_def map_le_def lookup'_def
  by simp (metis (mono_tags, lifting) domIff lookup_correct map_le_def map_of_heap_def)

lemma update'_correct:
  "state_mem_defs.map_of lookup' (snd (State_Monad.run_state (update' k v) m)) \<subseteq>\<^sub>m state_mem_defs.map_of lookup' m(k \<mapsto> v)"
  if "P m"
  unfolding state_mem_defs.map_of_def map_le_def lookup'_def update'_def
  using update_correct[of m k v] that by (auto split: if_split_asm simp: map_le_def map_of_heap_def)

lemma lookup'_inv:
  "DP_CRelVS.lift_p P (lookup' k)"
  unfolding DP_CRelVS.lift_p_def lookup'_def by (auto elim: lift_p_P'[OF lookup_inv])

lemma update'_inv:
  "DP_CRelVS.lift_p P (update' k v)"
  unfolding DP_CRelVS.lift_p_def update'_def by (auto elim: lift_p_P'[OF update_inv])

lemma mem_correct_heap: "mem_correct lookup' update' P"
  by (intro mem_correct.intro lookup'_correct update'_correct lookup'_inv update'_inv)

end (* Heap correct *)

context heap_mem_defs
begin

context
  includes lifting_syntax
begin

lemma mem_correct_heap_correct:
  assumes correct: "mem_correct lookup\<^sub>s update\<^sub>s P"
    and lookup: "((=) ===> rel_state (=)) lookup\<^sub>s lookup"
    and update: "((=) ===> (=) ===> rel_state (=)) update\<^sub>s update"
  shows "heap_correct P update lookup"
proof -
  interpret mem: mem_correct lookup\<^sub>s update\<^sub>s P
    by (rule correct)
  have [simp]: "the (execute (lookup k) m) = run_state (lookup\<^sub>s k) m" if "P m" for k m
    using lookup[THEN rel_funD, OF HOL.refl, of k] \<open>P m\<close> by (auto elim: rel_state_elim)
  have [simp]: "the (execute (update k v) m) = run_state (update\<^sub>s k v) m" if "P m" for k v m
    using update[THEN rel_funD, THEN rel_funD, OF HOL.refl HOL.refl, of k v] \<open>P m\<close>
    by (auto elim: rel_state_elim)
  have [simp]: "map_of_heap m = mem.map_of m" if "P m" for m
    unfolding map_of_heap_def mem.map_of_def using \<open>P m\<close> by simp
  show ?thesis
  apply standard
    subgoal for k
      using mem.lookup_inv[of k] lookup[THEN rel_funD, OF HOL.refl, of k]
      unfolding lift_p_def DP_CRelVS.lift_p_def
      by (auto split: option.splits elim: rel_state_elim)
    subgoal for k v
      using mem.update_inv[of k] update[THEN rel_funD, THEN rel_funD, OF HOL.refl HOL.refl, of k v]
      unfolding lift_p_def DP_CRelVS.lift_p_def
      by (auto split: option.splits elim: rel_state_elim)
    subgoal premises prems for m k
    proof -
      have "P (snd (run_state (lookup\<^sub>s k) m))"
        by (meson DP_CRelVS.lift_p_P mem.lookup_inv prems prod.exhaust_sel)
      with mem.lookup_correct[OF \<open>P m\<close>, of k] \<open>P m\<close> show ?thesis
        by (simp add: prems)
    qed
    subgoal premises prems for m k v
    proof -
      have "P (snd (run_state (update\<^sub>s k v) m))"
        by (meson DP_CRelVS.lift_p_P mem.update_inv prems prod.exhaust_sel)
      with mem.update_correct[OF \<open>P m\<close>, of k] \<open>P m\<close> show ?thesis
        by (simp add: prems)
    qed
    done
qed

end

end

end (* Theory *)
