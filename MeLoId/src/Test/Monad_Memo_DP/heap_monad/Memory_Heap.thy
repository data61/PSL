subsection \<open>Heap Memory Implementations\<close>

theory Memory_Heap
  imports State_Heap DP_CRelVH Pair_Memory "HOL-Eisbach.Eisbach" "../Index"
begin

text \<open>Move\<close>
abbreviation "result_of c h \<equiv> fst (the (execute c h))"
abbreviation "heap_of   c h \<equiv> snd (the (execute c h))"

lemma map_emptyI:
  "m \<subseteq>\<^sub>m Map.empty" if "\<And> x. m x = None"
  using that unfolding map_le_def by auto

lemma result_of_return[simp]:
  "result_of (Heap_Monad.return x) h = x"
  by (simp add: execute_simps)

lemma get_result_of_lookup:
  "result_of (!r) heap = x" if "Ref.get heap r = x"
  using that by (auto simp: execute_simps)

context
  fixes size :: nat
    and to_index :: "('k2 :: heap) \<Rightarrow> nat"
begin

definition
  "mem_empty = (Array.new size (None :: ('v :: heap) option))"

lemma success_empty[intro]:
  "success mem_empty heap"
  unfolding mem_empty_def by (auto intro: success_intros)

lemma length_mem_empty:
  "Array.length
    (heap_of (mem_empty:: (('b :: heap) option array) Heap) h)
    (result_of (mem_empty :: ('b option array) Heap) h) = size"
  unfolding mem_empty_def by (auto simp: execute_simps Array.length_alloc)

lemma nth_mem_empty:
  "result_of
    (Array.nth (result_of (mem_empty :: ('b option array) Heap) h) i)
    (heap_of (mem_empty :: (('b :: heap) option array) Heap) h) = None" if "i < size"
  apply (subst execute_nth(1))
  apply (simp add: length_mem_empty that)
  apply (simp add: execute_simps mem_empty_def Array.get_alloc that)
  done

context
  fixes mem :: "('v :: heap) option array"
begin

definition
  "mem_lookup k = (let i = to_index k in
    if i < size then Array.nth mem i else return None
  )"

definition
  "mem_update k v = (let i = to_index k in
    if i < size then (Array.upd i (Some v) mem \<bind> (\<lambda> _. return ()))
    else return ()
  )
  "

context assumes injective: "injective size to_index"
begin

interpretation heap_correct "\<lambda>heap. Array.length heap mem = size" mem_update mem_lookup
  apply standard
  subgoal lookup_inv
    unfolding State_Heap.lift_p_def mem_lookup_def by (simp add: Let_def execute_simps)
  subgoal update_inv
    unfolding State_Heap.lift_p_def mem_update_def by (simp add: Let_def execute_simps)
  subgoal for k heap
    unfolding heap_mem_defs.map_of_heap_def map_le_def mem_lookup_def
    by (auto simp: execute_simps Let_def split: if_split_asm)
  subgoal for heap k
    unfolding heap_mem_defs.map_of_heap_def map_le_def mem_lookup_def mem_update_def
    apply (auto simp: execute_simps Let_def length_def split: if_split_asm)
    apply (subst (asm) nth_list_update_neq)
    using injective[unfolded injective_def] apply auto
    done
  done

lemmas mem_heap_correct = heap_correct_axioms

context
  assumes [simp]: "mem = result_of mem_empty Heap.empty"
begin

interpretation heap_correct_empty
  "\<lambda>heap. Array.length heap mem = size" mem_update mem_lookup
  "heap_of (mem_empty :: 'v option array Heap) Heap.empty"
  apply standard
  subgoal
    apply (rule map_emptyI)
    unfolding map_of_heap_def mem_lookup_def by (auto simp: Let_def nth_mem_empty)
  subgoal
    by (simp add: length_mem_empty)
  done

lemmas array_heap_emptyI = heap_correct_empty_axioms

context
  fixes dp :: "'k2 \<Rightarrow> 'v"
begin

interpretation dp_consistency_heap_empty
  "\<lambda>heap. Array.length heap mem = size" mem_update mem_lookup dp
  "heap_of (mem_empty :: 'v option array Heap) Heap.empty"
  by standard

lemmas array_consistentI = dp_consistency_heap_empty_axioms

end

end (* Empty Memory *)

end (* Injectivity *)

end (* Fixed array *)

lemma execute_bind_success':
  assumes "success f h" "execute (f \<bind> g) h = Some (y, h'')"
  obtains x h' where "execute f h = Some (x, h')" "execute (g x) h' = Some (y, h'')"
  using assms by (auto simp: execute_simps elim: successE)

lemma success_bind_I:
  assumes "success f h"
    and "\<And> x h'. execute f h = Some (x, h') \<Longrightarrow> success (g x) h'"
  shows "success (f \<bind> g) h"
  by (rule successE[OF assms(1)]) (auto elim: assms(2) intro: success_bind_executeI)

definition
  "alloc_pair a b \<equiv> do {
    r1 \<leftarrow> ref a;
    r2 \<leftarrow> ref b;
    return (r1, r2)
  }"

lemma alloc_pair_alloc:
  "Ref.get heap' r1 = a" "Ref.get heap' r2 = b"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis Ref.get_alloc fst_conv get_alloc_neq next_present present_alloc_neq snd_conv)+

lemma alloc_pairD1:
  "r =!= r1 \<and> r =!= r2 \<and> Ref.present heap' r"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')" "Ref.present heap r"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis next_fresh noteq_I Ref.present_alloc snd_conv)+

lemma alloc_pairD2:
  "r1 =!= r2 \<and> Ref.present heap' r2 \<and> Ref.present heap' r1"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis next_fresh next_present noteq_I Ref.present_alloc snd_conv)+

lemma alloc_pairD3:
  "Array.present heap' r"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')" "Array.present heap r"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis array_present_alloc snd_conv)

lemma alloc_pairD4:
  "Ref.get heap' r = x"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')"
     "Ref.get heap r = x" "Ref.present heap r"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis Ref.not_present_alloc Ref.present_alloc get_alloc_neq noteq_I snd_conv)

lemma alloc_pair_array_get:
  "Array.get heap' r = x"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')" "Array.get heap r = x"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
 (metis array_get_alloc snd_conv)

lemma alloc_pair_array_length:
  "Array.length heap' r = Array.length heap r"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')"
  using that unfolding alloc_pair_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF success_refI])
     (metis Ref.length_alloc snd_conv)

lemma alloc_pair_nth:
  "result_of (Array.nth r i) heap' = result_of (Array.nth r i) heap"
  if "execute (alloc_pair a b) heap = Some ((r1, r2), heap')"
  using alloc_pair_array_get[OF that(1) HOL.refl, of r] alloc_pair_array_length[OF that(1), of r]
  by (cases "(\<lambda>h. i < Array.length h r) heap"; simp add: execute_simps Array.nth_def)

lemma succes_alloc_pair[intro]:
  "success (alloc_pair a b) heap"
  unfolding alloc_pair_def by (auto intro: success_intros success_bind_I)

definition
  "init_state_inner k1 k2 m1 m2 \<equiv>  do {
    (k_ref1, k_ref2) \<leftarrow> alloc_pair k1 k2;
    (m_ref1, m_ref2) \<leftarrow> alloc_pair m1 m2;
    return (k_ref1, k_ref2, m_ref1, m_ref2)
  }
  "

lemma init_state_inner_alloc:
  assumes
    "execute (init_state_inner k1 k2 m1 m2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Ref.get heap' k_ref1 = k1" "Ref.get heap' k_ref2 = k2"
    "Ref.get heap' m_ref1 = m1" "Ref.get heap' m_ref2 = m2"
  using assms unfolding init_state_inner_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF succes_alloc_pair])
     (auto intro: alloc_pair_alloc dest: alloc_pairD2 elim: alloc_pairD4)

lemma init_state_inner_distinct:
  assumes
    "execute (init_state_inner k1 k2 m1 m2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "m_ref1 =!= m_ref2 \<and> m_ref1 =!= k_ref1 \<and> m_ref1 =!= k_ref2 \<and> m_ref2 =!= k_ref1
   \<and> m_ref2 =!= k_ref2 \<and> k_ref1 =!= k_ref2"
  using assms unfolding init_state_inner_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF succes_alloc_pair])
     (blast dest: alloc_pairD1 alloc_pairD2 intro: noteq_sym)+

lemma init_state_inner_present:
  assumes
    "execute (init_state_inner k1 k2 m1 m2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Ref.present heap' k_ref1" "Ref.present heap' k_ref2"
    "Ref.present heap' m_ref1" "Ref.present heap' m_ref2"
  using assms unfolding init_state_inner_def
  by (auto simp: execute_simps elim!: execute_bind_success'[OF succes_alloc_pair])
     (blast dest: alloc_pairD1 alloc_pairD2)+

lemma inite_state_inner_present':
  assumes
    "execute (init_state_inner k1 k2 m1 m2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
    "Array.present heap a"
  shows
    "Array.present heap' a"
    using assms unfolding init_state_inner_def
    by (auto simp: execute_simps elim!: execute_bind_success'[OF succes_alloc_pair] alloc_pairD3)

lemma succes_init_state_inner[intro]:
  "success (init_state_inner k1 k2 m1 m2) heap"
  unfolding init_state_inner_def by (auto 4 3 intro: success_intros success_bind_I)

lemma init_state_inner_nth:
  "result_of (Array.nth r i) heap' = result_of (Array.nth r i) heap"
  if "execute (init_state_inner k1 k2 m1 m2) heap = Some ((r1, r2), heap')"
  using that unfolding init_state_inner_def
  by (auto simp: execute_simps alloc_pair_nth elim!: execute_bind_success'[OF succes_alloc_pair])

definition
  "init_state k1 k2 \<equiv> do {
    m1 \<leftarrow> mem_empty;
    m2 \<leftarrow> mem_empty;
    init_state_inner k1 k2 m1 m2
  }"

lemma succes_init_state[intro]:
  "success (init_state k1 k2) heap"
  unfolding init_state_def by (auto intro: success_intros success_bind_I)

definition
  "inv_distinct k_ref1 k_ref2 m_ref1 m_ref2 \<equiv>
     m_ref1 =!= m_ref2 \<and> m_ref1 =!= k_ref1 \<and> m_ref1 =!= k_ref2 \<and> m_ref2 =!= k_ref1
   \<and> m_ref2 =!= k_ref2 \<and> k_ref1 =!= k_ref2
  "

lemma init_state_distinct:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "inv_distinct k_ref1 k_ref2 m_ref1 m_ref2"
  using assms unfolding init_state_def inv_distinct_def
  by (elim execute_bind_success'[OF success_empty] init_state_inner_distinct)

lemma init_state_present:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Ref.present heap' k_ref1" "Ref.present heap' k_ref2"
    "Ref.present heap' m_ref1" "Ref.present heap' m_ref2"
  using assms unfolding init_state_def
  by (auto
        simp: execute_simps elim!: execute_bind_success'[OF success_empty]
        dest: init_state_inner_present
     )

lemma empty_present:
  "Array.present h' x" if "execute mem_empty heap = Some (x, h')"
  using that unfolding mem_empty_def
  by (auto simp: execute_simps) (metis Array.present_alloc fst_conv snd_conv)

lemma empty_present':
  "Array.present h' a" if "execute mem_empty heap = Some (x, h')" "Array.present heap a"
  using that unfolding mem_empty_def
  by (auto simp: execute_simps Array.present_def Array.alloc_def Array.set_def Let_def)

lemma init_state_present2:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Array.present heap' (Ref.get heap' m_ref1)" "Array.present heap' (Ref.get heap' m_ref2)"
  using assms unfolding init_state_def
  by (auto 4 3
        simp: execute_simps init_state_inner_alloc elim!: execute_bind_success'[OF success_empty]
        dest: inite_state_inner_present' empty_present empty_present'
     )

lemma init_state_neq:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Ref.get heap' m_ref1 =!!= Ref.get heap' m_ref2"
  using assms unfolding init_state_def
  by (auto 4 3
        simp: execute_simps init_state_inner_alloc elim!: execute_bind_success'[OF success_empty]
        dest: inite_state_inner_present' empty_present empty_present'
     )
    (metis empty_present execute_new fst_conv mem_empty_def option.inject present_alloc_noteq)

lemma present_alloc_get:
  "Array.get heap' a = Array.get heap a"
  if "Array.alloc xs heap = (a', heap')" "Array.present heap a"
  using that by (auto simp: Array.alloc_def Array.present_def Array.get_def Let_def Array.set_def)

lemma init_state_length:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows
    "Array.length heap' (Ref.get heap' m_ref1) = size"
    "Array.length heap' (Ref.get heap' m_ref2) = size"
  using assms unfolding init_state_def
  apply (auto
        simp: execute_simps init_state_inner_alloc elim!: execute_bind_success'[OF success_empty]
        dest: inite_state_inner_present' empty_present empty_present'
     )
   apply (auto
      simp: execute_simps init_state_inner_def alloc_pair_def mem_empty_def Array.length_def
      elim!: execute_bind_success'[OF success_refI]
     )
  apply (metis
      Array.alloc_def Array.get_set_eq Array.present_alloc array_get_alloc fst_conv length_replicate
      present_alloc_get snd_conv
     )+
  done

context
  fixes key1 :: "'k \<Rightarrow> ('k1 :: heap)" and key2 :: "'k \<Rightarrow> 'k2"
    and m_ref1 m_ref2 :: "('v :: heap) option array ref"
    and k_ref1 k_ref2 :: "('k1 :: heap) ref"
begin

text \<open>We assume that look-ups happen on the older row, so this is biased towards the second entry.\<close>
definition
  "lookup_pair k = do {
    let k' = key1 k;
    k2 \<leftarrow> !k_ref2;
    if k' = k2 then
      do {
        m2 \<leftarrow> !m_ref2;
        mem_lookup m2 (key2 k)
      }
    else
      do {
      k1 \<leftarrow> !k_ref1;
      if k' = k1 then
        do {
          m1 \<leftarrow> !m_ref1;
          mem_lookup m1 (key2 k)
        }
      else
        return None
    }
  }
   "

text \<open>We assume that updates happen on the newer row, so this is biased towards the first entry.\<close>
definition
  "update_pair k v = do {
    let k' = key1 k;
      k1 \<leftarrow> !k_ref1;
      if k' = k1 then do {
        m \<leftarrow> !m_ref1;
        mem_update m (key2 k) v
      }
      else do {
        k2 \<leftarrow> !k_ref2;
        if k' = k2 then do {
          m \<leftarrow> !m_ref2;
          mem_update m (key2 k) v
        }
        else do {
          do {
            k1 \<leftarrow> !k_ref1;
            m \<leftarrow> mem_empty;
            m1 \<leftarrow> !m_ref1;
            k_ref2 := k1;
            k_ref1 := k';
            m_ref2 := m1;
            m_ref1 := m
          }
        ;
        m \<leftarrow> !m_ref1;
        mem_update m (key2 k) v
      }
    }
   }
   "

definition
  "inv_pair_weak heap = (
    let
      m1 = Ref.get heap m_ref1;
      m2 = Ref.get heap m_ref2
    in Array.length heap m1 = size \<and> Array.length heap m2 = size
      \<and> Ref.present heap k_ref1 \<and> Ref.present heap k_ref2
      \<and> Ref.present heap m_ref1 \<and> Ref.present heap m_ref2
      \<and> Array.present heap m1 \<and> Array.present heap m2
      \<and> m1 =!!= m2
  )"

(* TODO: Remove? *)
definition
  "inv_pair heap \<equiv> inv_pair_weak heap \<and> inv_distinct k_ref1 k_ref2 m_ref1 m_ref2"

lemma init_state_inv:
  assumes
    "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
  shows "inv_pair_weak heap'"
  using assms unfolding inv_pair_weak_def Let_def
  by (auto intro:
      init_state_present init_state_present2 init_state_neq init_state_length
      init_state_distinct
     )

lemma inv_pair_lengthD1:
  "Array.length heap (Ref.get heap m_ref1) = size" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_lengthD2:
  "Array.length heap (Ref.get heap m_ref2) = size" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_presentD:
  "Array.present heap (Ref.get heap m_ref1)" "Array.present heap (Ref.get heap m_ref2)"
  if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_presentD2:
  "Ref.present heap m_ref1" "Ref.present heap m_ref2"
  "Ref.present heap k_ref1" "Ref.present heap k_ref2"
  if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

lemma inv_pair_not_eqD:
  "Ref.get heap m_ref1 =!!= Ref.get heap m_ref2" if "inv_pair_weak heap"
  using that unfolding inv_pair_weak_def by (auto simp: Let_def)

definition "lookup1 k \<equiv> state_of (do {m \<leftarrow> !m_ref1; mem_lookup m k})"

definition "lookup2 k \<equiv> state_of (do {m \<leftarrow> !m_ref2; mem_lookup m k})"

definition "update1 k v \<equiv> state_of (do {m \<leftarrow> !m_ref1; mem_update m k v})"

definition "update2 k v \<equiv> state_of (do {m \<leftarrow> !m_ref2; mem_update m k v})"

definition "move12 k \<equiv> state_of (do {
    k1 \<leftarrow> !k_ref1;
    m \<leftarrow> mem_empty;
    m1 \<leftarrow> !m_ref1;
    k_ref2 := k1;
    k_ref1 := k;
    m_ref2 := m1;
    m_ref1 := m
  })
  "

definition "get_k1 \<equiv> state_of (!k_ref1)"

definition "get_k2 \<equiv> state_of (!k_ref2)"

lemma run_state_state_of[simp]:
  "State_Monad.run_state (state_of p) m = the (execute p m)"
  unfolding state_of_def by simp

context assumes injective: "injective size to_index"
begin

context
  assumes inv_distinct: "inv_distinct k_ref1 k_ref2 m_ref1 m_ref2"
begin

lemma disjoint[simp]:
  "m_ref1 =!= m_ref2" "m_ref1 =!= k_ref1" "m_ref1 =!= k_ref2"
  "m_ref2 =!= k_ref1" "m_ref2 =!= k_ref2"
  "k_ref1 =!= k_ref2"
  using inv_distinct unfolding inv_distinct_def by auto

lemmas [simp] = disjoint[THEN noteq_sym]

lemma [simp]:
  "Array.get (snd (Array.alloc xs heap)) a = Array.get heap a" if "Array.present heap a"
  using that unfolding Array.alloc_def Array.present_def
  apply (simp add: Let_def)
  apply (subst Array.get_set_neq)
  subgoal
    by (simp add: Array.noteq_def)
  subgoal
    unfolding Array.get_def by simp
  done

lemma [simp]:
  "Ref.get (snd (Array.alloc xs heap)) r = Ref.get heap r" if "Ref.present heap r"
  using that unfolding Array.alloc_def Ref.present_def
  by (simp add: Let_def Ref.get_def Array.set_def)

lemma alloc_present:
  "Array.present (snd (Array.alloc xs heap)) a" if "Array.present heap a"
  using that unfolding Array.present_def Array.alloc_def by (simp add: Let_def Array.set_def)

lemma alloc_present':
  "Ref.present (snd (Array.alloc xs heap)) r" if "Ref.present heap r"
  using that unfolding Ref.present_def Array.alloc_def by (simp add: Let_def Array.set_def)

lemma length_get_upd[simp]:
  "length (Array.get (Array.update a i x heap) r) = length (Array.get heap r)"
  unfolding Array.get_def Array.update_def Array.set_def by simp

method solve1 =
  (frule inv_pair_lengthD1, frule inv_pair_lengthD2, frule inv_pair_not_eqD)?,
  auto split: if_split_asm dest: Array.noteq_sym

interpretation pair: pair_mem lookup1 lookup2 update1 update2 move12 get_k1 get_k2 inv_pair_weak
  supply [simp] =
    mem_empty_def state_mem_defs.map_of_def map_le_def
    move12_def update1_def update2_def lookup1_def lookup2_def get_k1_def get_k2_def
    mem_update_def mem_lookup_def
    execute_bind_success[OF success_newI] execute_simps Let_def Array.get_alloc length_def
    inv_pair_presentD inv_pair_presentD2
    Memory_Heap.lookup1_def Memory_Heap.lookup2_def Memory_Heap.mem_lookup_def
  apply standard
                      apply (solve1; fail)+
  subgoal
    apply (rule lift_pI)
    unfolding inv_pair_weak_def
    apply (auto simp:
        intro: alloc_present alloc_present'
        elim: present_alloc_noteq[THEN Array.noteq_sym]
        )
    done
                     apply (rule lift_pI, unfold inv_pair_weak_def, auto split: if_split_asm; fail)+
                 apply (solve1; fail)+
  subgoal
    using injective[unfolded injective_def] by - (solve1, subst (asm) nth_list_update_neq, auto)
  subgoal
    using injective[unfolded injective_def] by - (solve1, subst (asm) nth_list_update_neq, auto)
   apply (solve1; fail)+
  done

lemmas mem_correct_pair = pair.mem_correct_pair

definition
  "mem_lookup1 k = do {m \<leftarrow> !m_ref1; mem_lookup m k}"

definition
  "mem_lookup2 k = do {m \<leftarrow> !m_ref2; mem_lookup m k}"

definition "get_k1' \<equiv> !k_ref1"

definition "get_k2' \<equiv> !k_ref2"

definition "update1' k v \<equiv> do {m \<leftarrow> !m_ref1; mem_update m k v}"

definition "update2' k v \<equiv> do {m \<leftarrow> !m_ref2; mem_update m k v}"

definition "move12' k \<equiv> do {
    k1 \<leftarrow> !k_ref1;
    m \<leftarrow> mem_empty;
    m1 \<leftarrow> !m_ref1;
    k_ref2 := k1;
    k_ref1 := k;
    m_ref2 := m1;
    m_ref1 := m
  }"

interpretation heap_mem_defs inv_pair_weak lookup_pair update_pair .

lemma rel_state_ofI:
  "rel_state op = (state_of m) m" if
  "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  "lift_p inv_pair_weak m"
  using that unfolding rel_state_def
  by (auto split: option.split intro: lift_p_P'' simp: success_def)

lemma inv_pair_iff:
  "inv_pair_weak = inv_pair"
  unfolding inv_pair_def using inv_distinct by simp

lemma lift_p_inv_pairI:
  "State_Heap.lift_p inv_pair m" if "State_Heap.lift_p inv_pair_weak m"
  using that unfolding inv_pair_iff by simp

lemma lift_p_success:
  "State_Heap.lift_p inv_pair_weak m"
  if "DP_CRelVS.lift_p inv_pair_weak (state_of m)" "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  using that
  unfolding lift_p_def DP_CRelVS.lift_p_def
  by (auto simp: success_def split: option.split)

lemma rel_state_ofI2:
  "rel_state op = (state_of m) m" if
  "\<forall> heap. inv_pair_weak heap \<longrightarrow> success m heap"
  "DP_CRelVS.lift_p inv_pair_weak (state_of m)"
  using that by (blast intro: rel_state_ofI lift_p_success)

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  "(op = ===> rel_state op =) move12 move12'"
  unfolding move12_def move12'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto
        simp: mem_empty_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.move12_inv unfolding move12_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup1 mem_lookup1"
  unfolding lookup1_def mem_lookup1_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 4
        simp: mem_lookup_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_bind_executeI success_returnI Array.success_nthI
       )
  subgoal
    using pair.lookup_inv(1) unfolding lookup1_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup2 mem_lookup2"
  unfolding lookup2_def mem_lookup2_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_lookup_def inv_pair_lengthD2 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.lookup_inv(2) unfolding lookup2_def .
  done

lemma [transfer_rule]:
  "rel_state (op =) get_k1 get_k1'"
  unfolding get_k1_def get_k1'_def
  apply (rule rel_state_ofI2)
  subgoal
    by (auto intro: success_lookupI)
  subgoal
    unfolding get_k1_def[symmetric] by (auto dest: pair.get_state(1) intro: lift_pI)
  done

lemma [transfer_rule]:
  "rel_state (op =) get_k2 get_k2'"
  unfolding get_k2_def get_k2'_def
  apply (rule rel_state_ofI2)
  subgoal
    by (auto intro: success_lookupI)
  subgoal
    unfolding get_k2_def[symmetric] by (auto dest: pair.get_state(2) intro: lift_pI)
  done

lemma [transfer_rule]:
  "(op = ===> op = ===> rel_state (op =)) update1 update1'"
  unfolding update1_def update1'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_update_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.update_inv(1) unfolding update1_def .
  done

lemma [transfer_rule]:
  "(op = ===> op = ===> rel_state (op =)) update2 update2'"
  unfolding update2_def update2'_def
  apply (intro rel_funI)
  apply simp
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_update_def inv_pair_lengthD2 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.update_inv(2) unfolding update2_def .
  done

lemma [transfer_rule]:
  "(op = ===> rel_state (rel_option op =)) lookup1 mem_lookup1"
  unfolding lookup1_def mem_lookup1_def
  apply (intro rel_funI)
  apply (simp add: option.rel_eq)
  apply (rule rel_state_ofI2)
  subgoal
    by (auto 4 3
        simp: mem_lookup_def inv_pair_lengthD1 execute_simps Let_def
        intro: success_intros intro!: success_bind_I
       )
  subgoal
    using pair.lookup_inv(1) unfolding lookup1_def .
  done

lemma rel_state_lookup:
  "(op = ===> rel_state op =) pair.lookup_pair lookup_pair"
  unfolding pair.lookup_pair_def lookup_pair_def
  unfolding
    mem_lookup1_def[symmetric] mem_lookup2_def[symmetric]
    get_k2_def[symmetric] get_k2'_def[symmetric]
    get_k1_def[symmetric] get_k1'_def[symmetric]
  by transfer_prover

lemma rel_state_update:
  "(op = ===> op = ===> rel_state op =) pair.update_pair update_pair"
  unfolding pair.update_pair_def update_pair_def
  unfolding move12'_def[symmetric]
  unfolding
    update1'_def[symmetric] update2'_def[symmetric]
    get_k2_def[symmetric] get_k2'_def[symmetric]
    get_k1_def[symmetric] get_k1'_def[symmetric]
  by transfer_prover

interpretation mem: heap_mem_defs pair.inv_pair lookup_pair update_pair .

lemma inv_pairD:
  "inv_pair_weak heap" if "pair.inv_pair heap"
  using that unfolding pair.inv_pair_def by (auto simp: Let_def)

lemma mem_rel_state_ofI:
  "mem.rel_state op = m' m" if
  "rel_state op = m' m"
  "\<And> heap. pair.inv_pair heap \<Longrightarrow>
    (case State_Monad.run_state m' heap of (_, heap) \<Rightarrow> inv_pair_weak heap \<longrightarrow> pair.inv_pair heap)"
proof -
  show ?thesis
    apply (rule mem.rel_state_intro)
    subgoal for heap v heap'
      by (auto elim: rel_state_elim[OF that(1)] dest!: inv_pairD)
    subgoal premises prems for heap v heap'
    proof -
      from prems that(1) have "inv_pair_weak heap'"
        by (fastforce elim: rel_state_elim dest: inv_pairD)
      with prems show ?thesis
        by (auto dest: that(2))
    qed
    done
qed

lemma mem_rel_state_ofI':
  "mem.rel_state op = m' m" if
  "rel_state op = m' m"
  "DP_CRelVS.lift_p pair.inv_pair m'"
  using that by (auto elim: DP_CRelVS.lift_p_P intro: mem_rel_state_ofI)

context
  assumes keys: "\<forall>k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
begin

interpretation mem_correct pair.lookup_pair pair.update_pair pair.inv_pair
  by (rule mem_correct_pair[OF keys])

lemma rel_state_lookup':
  "(op = ===> mem.rel_state op =) pair.lookup_pair lookup_pair"
  apply (intro rel_funI)
  apply simp
  apply (rule mem_rel_state_ofI')
  subgoal for x y
    using rel_state_lookup by (rule rel_funD) (rule HOL.refl)
  by (rule lookup_inv)

lemma rel_state_update':
  "(op = ===> op = ===> mem.rel_state op =) pair.update_pair update_pair"
  apply (intro rel_funI)
  apply simp
  apply (rule mem_rel_state_ofI')
  subgoal for x y a b
    using rel_state_update by (blast dest: rel_funD)
  by (rule update_inv)

interpretation heap_correct pair.inv_pair update_pair lookup_pair
  by (rule mem.mem_correct_heap_correct[OF _ rel_state_lookup' rel_state_update']) standard

lemmas heap_correct_pairI = heap_correct_axioms 

(* TODO: Generalize *)
lemma mem_rel_state_resultD:
  "result_of m heap = fst (run_state m' heap)" if "mem.rel_state op = m' m" "pair.inv_pair heap"
  by (metis (mono_tags, lifting) mem.rel_state_elim option.sel that)

lemma map_of_heap_eq:
  "mem.map_of_heap heap = pair.pair.map_of heap" if "pair.inv_pair heap"
  unfolding mem.map_of_heap_def pair.pair.map_of_def
  using that by (simp add: mem_rel_state_resultD[OF rel_state_lookup'[THEN rel_funD]])

context
  fixes k1 k2 heap heap'
  assumes init: "execute (init_state k1 k2) heap = Some ((k_ref1, k_ref2, m_ref1, m_ref2), heap')"
begin

lemma init_state_empty1:
  "pair.mem1.map_of heap' k = None"
  using init
  unfolding pair.mem1.map_of_def lookup1_def mem_lookup_def init_state_def
  by (auto
        simp: init_state_inner_nth init_state_inner_alloc(3) execute_simps Let_def
        elim!: execute_bind_success'[OF success_empty])
     (metis
        Array.present_alloc Memory_Heap.length_mem_empty execute_new execute_nth(1) fst_conv
        length_def mem_empty_def nth_mem_empty option.sel present_alloc_get snd_conv
     )

lemma init_state_empty2:
  "pair.mem2.map_of heap' k = None"
  using init
  unfolding pair.mem2.map_of_def lookup2_def mem_lookup_def init_state_def
  by (auto
        simp: execute_simps init_state_inner_nth init_state_inner_alloc(4) Let_def
        elim!: execute_bind_success'[OF success_empty]
     )
     (metis fst_conv nth_mem_empty option.sel snd_conv)

lemma
  shows init_state_k1: "result_of (!k_ref1) heap' = k1"
    and init_state_k2: "result_of (!k_ref2) heap' = k2"
  using init init_state_inner_alloc
  by (auto simp: execute_simps init_state_def elim!: execute_bind_success'[OF success_empty])

context
  assumes neq: "k1 \<noteq> k2"
begin

lemma init_state_inv':
  "pair.inv_pair heap'"
  unfolding pair.inv_pair_def
  apply (auto simp: Let_def)
  subgoal
    using init_state_empty1 by simp
  subgoal
    using init_state_empty2 by simp
  subgoal
    using neq init by (simp add: get_k1_def get_k2_def init_state_k1 init_state_k2)
  subgoal
    by (rule init_state_inv[OF init])
  done

lemma init_state_empty:
  "pair.pair.map_of heap' \<subseteq>\<^sub>m Map.empty"
  using neq by (intro pair.emptyI init_state_inv' map_emptyI init_state_empty1 init_state_empty2)

interpretation heap_correct_empty pair.inv_pair update_pair lookup_pair heap'
  apply (rule heap_correct_empty.intro)
   apply (rule heap_correct_pairI)
  apply standard
  subgoal
    by (subst map_of_heap_eq; intro init_state_inv' init_state_empty)
  subgoal
    by (rule init_state_inv')
  done

lemmas heap_correct_empty_pairI = heap_correct_empty_axioms

context
  fixes dp :: "'k \<Rightarrow> 'v"
begin

interpretation dp_consistency_heap_empty
  pair.inv_pair update_pair lookup_pair dp heap'
  by standard

lemmas consistent_empty_pairI = dp_consistency_heap_empty_axioms

end (* DP *)

end (* Unequal Keys *)

end (* Init State *)

end (* Keys injective *)

end (* Lifting Syntax *)

end (* Disjoint *)

end (* Injectivity *)

end (* Refs *)

end (* Key functions & Size *)

end (* Theory *)