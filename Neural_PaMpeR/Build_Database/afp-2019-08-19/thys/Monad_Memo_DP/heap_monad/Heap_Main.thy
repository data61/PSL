theory Heap_Main
  imports
    "../heap_monad/Memory_Heap"
    "../transform/Transform_Cmd"
    Bottom_Up_Computation_Heap
    "../util/Solve_Cong"
begin

context includes heap_monad_syntax begin

thm if_cong
lemma ifT_cong:
  assumes "b = c" "c \<Longrightarrow> x = u" "\<not>c \<Longrightarrow> y = v"
  shows "Heap_Monad_Ext.if\<^sub>T \<langle>b\<rangle> x y = Heap_Monad_Ext.if\<^sub>T \<langle>c\<rangle> u v"
  unfolding Heap_Monad_Ext.if\<^sub>T_def
  unfolding return_bind
  using if_cong[OF assms] .

lemma return_app_return_cong:
  assumes "f x = g y"
  shows "\<langle>f\<rangle> . \<langle>x\<rangle> = \<langle>g\<rangle> . \<langle>y\<rangle>"
  unfolding Heap_Monad_Ext.return_app_return_meta assms ..

lemmas [fundef_cong] =
  return_app_return_cong
  ifT_cong
end
memoize_fun comp\<^sub>T: comp monadifies (heap) comp_def
thm comp\<^sub>T'.simps
lemma (in dp_consistency_heap) shows comp\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R1 ===>\<^sub>T R2) ===>\<^sub>T (R0 ===>\<^sub>T R1) ===>\<^sub>T (R0 ===>\<^sub>T R2)) comp comp\<^sub>T"
  apply memoize_combinator_init
  subgoal premises IH [transfer_rule] by memoize_unfold_defs transfer_prover
  done

memoize_fun map\<^sub>T: map monadifies (heap) list.map
lemma (in dp_consistency_heap) map\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T list_all2 R1) map map\<^sub>T"
  apply memoize_combinator_init
  apply (erule list_all2_induct)
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  done

memoize_fun fold\<^sub>T: fold monadifies (heap) fold.simps
lemma (in dp_consistency_heap) fold\<^sub>T_transfer[transfer_rule]:
  "crel_vs ((R0 ===>\<^sub>T R1 ===>\<^sub>T R1) ===>\<^sub>T list_all2 R0 ===>\<^sub>T R1 ===>\<^sub>T R1) fold fold\<^sub>T"
  apply memoize_combinator_init
  apply (erule list_all2_induct)
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  subgoal premises [transfer_rule] by memoize_unfold_defs transfer_prover
  done

context includes heap_monad_syntax begin

thm map_cong
lemma mapT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "map\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = map\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding map\<^sub>T_def 
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: Heap_Monad_Ext.return_app_return_meta)

thm fold_cong
lemma foldT_cong:
  assumes "xs = ys" "\<And>x. x\<in>set ys \<Longrightarrow> f x = g x"
  shows "fold\<^sub>T . \<langle>f\<rangle> . \<langle>xs\<rangle> = fold\<^sub>T . \<langle>g\<rangle> . \<langle>ys\<rangle>"
  unfolding fold\<^sub>T_def
  unfolding assms(1)
  using assms(2) by (induction ys) (auto simp: Heap_Monad_Ext.return_app_return_meta)

lemma abs_unit_cong:
  (* for lazy checkmem *)
  assumes "x = y"
  shows "(\<lambda>_::unit. x) = (\<lambda>_. y)"
  using assms ..


lemma arg_cong4:
  "f a b c d = f a' b' c' d'" if "a = a'" "b = b'" "c = c'" "d = d'"
  by (simp add: that)

lemmas [fundef_cong, cong_rules] =
  return_app_return_cong
  ifT_cong
  mapT_cong
  foldT_cong
  abs_unit_cong
lemmas [cong_rules] =
  arg_cong4[where f = heap_mem_defs.checkmem]
  arg_cong2[where f = fun_app_lifted]
end


context dp_consistency_heap begin
context includes lifting_syntax heap_monad_syntax begin

named_theorems dp_match_rule

thm if_cong
lemma if\<^sub>T_cong2:
  assumes "Rel (=) b c" "c \<Longrightarrow> Rel (crel_vs R) x x\<^sub>T" "\<not>c \<Longrightarrow> Rel (crel_vs R) y y\<^sub>T"
  shows "Rel (crel_vs R) (if (Wrap b) then x else y) (Heap_Monad_Ext.if\<^sub>T \<langle>c\<rangle> x\<^sub>T y\<^sub>T)"
  using assms unfolding Heap_Monad_Ext.if\<^sub>T_def bind_left_identity Rel_def Wrap_def
  by (auto split: if_split)

lemma map\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs S) (f x) (f\<^sub>T' x)"
  shows "Rel (crel_vs (list_all2 S)) (App (App map (Wrap f)) (Wrap xs)) (map\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding map\<^sub>T_def
  unfolding Heap_Monad_Ext.return_app_return_meta
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def Wrap_def App_def
  apply (induction ys)
  subgoal premises by (memoize_unfold_defs (heap) map) transfer_prover
  subgoal premises prems for a ys
  apply (memoize_unfold_defs (heap) map)
    apply (unfold Heap_Monad_Ext.return_app_return_meta Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

lemma fold\<^sub>T_cong2:
  assumes
    "is_equality R"
    "Rel R xs ys"
    "\<And>x. x\<in>set ys \<Longrightarrow> Rel (crel_vs (S ===> crel_vs S)) (f x) (f\<^sub>T' x)"
  shows
    "Rel (crel_vs (S ===> crel_vs S)) (fold f xs) (fold\<^sub>T . \<langle>f\<^sub>T'\<rangle> . \<langle>ys\<rangle>)"
  unfolding fold\<^sub>T_def
  unfolding Heap_Monad_Ext.return_app_return_meta
  unfolding assms(2)[unfolded Rel_def assms(1)[unfolded is_equality_def]]
  using assms(3)
  unfolding Rel_def
  apply (induction ys)
  subgoal premises by (memoize_unfold_defs (heap) fold) transfer_prover
  subgoal premises prems for a ys
    apply (memoize_unfold_defs (heap) fold)
    apply (unfold Heap_Monad_Ext.return_app_return_meta Wrap_App_Wrap)
    supply [transfer_rule] =
      prems(2)[OF list.set_intros(1)]
      prems(1)[OF prems(2)[OF list.set_intros(2)], simplified]
    by transfer_prover
  done

lemma refl2:
  "is_equality R \<Longrightarrow> Rel R x x"
  unfolding is_equality_def Rel_def by simp

lemma rel_fun2:
  assumes "is_equality R0" "\<And>x. Rel R1 (f x) (g x)"
  shows "Rel (rel_fun R0 R1) f g"
  using assms unfolding is_equality_def Rel_def by auto

lemma crel_vs_return_app_return:
  assumes "Rel R (f x) (g x)"
  shows "Rel R (App (Wrap f) (Wrap x)) (\<langle>g\<rangle> . \<langle>x\<rangle>)"
  using assms unfolding Heap_Monad_Ext.return_app_return_meta Wrap_App_Wrap .

thm option.case_cong[no_vars]
lemma option_case_cong':
"Rel (=) option' option \<Longrightarrow>
(option = None \<Longrightarrow> Rel R f1 g1) \<Longrightarrow>
(\<And>x2. option = Some x2 \<Longrightarrow> Rel R (f2 x2) (g2 x2)) \<Longrightarrow>
Rel R (case option' of None \<Rightarrow> f1 | Some x2 \<Rightarrow> f2 x2)
(case option of None \<Rightarrow> g1 | Some x2 \<Rightarrow> g2 x2)"
  unfolding Rel_def by (auto split: option.split)

thm prod.case_cong[no_vars]
lemma prod_case_cong': fixes prod prod' shows
"Rel (=) prod prod' \<Longrightarrow>
(\<And>x1 x2. prod' = (x1, x2) \<Longrightarrow> Rel R (f x1 x2) (g x1 x2)) \<Longrightarrow>
Rel R (case prod of (x1, x2) \<Rightarrow> f x1 x2)
(case prod' of (x1, x2) \<Rightarrow> g x1 x2)"
  unfolding Rel_def by (auto split: prod.splits)

lemmas [dp_match_rule] = prod_case_cong' option_case_cong'


lemmas [dp_match_rule] =
  crel_vs_return_app_return

lemmas [dp_match_rule] =
  map\<^sub>T_cong2
  fold\<^sub>T_cong2
  if\<^sub>T_cong2

lemmas [dp_match_rule] =
  crel_vs_return
  crel_vs_fun_app
  refl2
  rel_fun2

(*
lemmas [dp_match_rule] =
  crel_vs_checkmem_tupled
*)

end (* context lifting_syntax *)
end (* context dp_consistency *)

subsubsection \<open>More Heap\<close>

lemma execute_heap_ofD:
  "heap_of c h = h'" if "execute c h = Some (v, h')"
  using that by auto

lemma execute_result_ofD:
  "result_of c h = v" if "execute c h = Some (v, h')"
  using that by auto

locale heap_correct_init_defs =
  fixes P :: "'m \<Rightarrow> heap \<Rightarrow> bool"
    and lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option Heap"
    and update :: "'m \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

definition map_of_heap' where
  "map_of_heap' m heap k = fst (the (execute (lookup m k) heap))"

end

locale heap_correct_init_inv = heap_correct_init_defs +
  assumes lookup_inv: "\<And> m. lift_p (P m) (lookup m k)"
  assumes update_inv: "\<And> m. lift_p (P m) (update m k v)"

locale heap_correct_init =
  heap_correct_init_inv +
  assumes lookup_correct:
      "\<And> a. P a m \<Longrightarrow> map_of_heap' a (snd (the (execute (lookup a k) m))) \<subseteq>\<^sub>m (map_of_heap' a m)"
  and update_correct:
      "\<And> a. P a m \<Longrightarrow>
        map_of_heap' a (snd (the (execute (update a k v) m))) \<subseteq>\<^sub>m (map_of_heap' a m)(k \<mapsto> v)"
begin

end

locale dp_consistency_heap_init = heap_correct_init _ lookup for lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option Heap"  +
  fixes dp :: "'k \<Rightarrow> 'v"
  fixes init :: "'m Heap"
  assumes success: "success init Heap.empty"
  assumes empty_correct:
    "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> map_of_heap' empty heap \<subseteq>\<^sub>m Map.empty"
    and P_empty: "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> P empty heap"
begin

definition "init_mem = result_of init Heap.empty"

sublocale dp_consistency_heap
  where P="P init_mem"
    and lookup="lookup init_mem"
    and update="update init_mem"
  apply standard
       apply (rule lookup_inv[of init_mem])
      apply (rule update_inv[of init_mem])
  subgoal
    unfolding heap_mem_defs.map_of_heap_def
    by (rule lookup_correct[of init_mem, unfolded map_of_heap'_def])
  subgoal
    unfolding heap_mem_defs.map_of_heap_def
    by (rule update_correct[of init_mem, unfolded map_of_heap'_def])
  done

interpretation consistent: dp_consistency_heap_empty
  where P="P init_mem"
    and lookup="lookup init_mem"
    and update="update init_mem"
    and empty= "heap_of init Heap.empty"
  apply standard
  subgoal
    apply (rule successE[OF success])
    apply (frule empty_correct)
    unfolding heap_mem_defs.map_of_heap_def init_mem_def map_of_heap'_def
    by simp
  subgoal
    apply (rule successE[OF success])
    apply (frule P_empty)
    unfolding init_mem_def
    by simp
  done

lemma memoized_empty:
  "dp x = result_of (init \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP (dp\<^sub>T (result_of init Heap.empty))"
  by (simp add: execute_bind_success consistent.memoized[OF that(1)] success)

end

locale dp_consistency_heap_init' = heap_correct_init _ lookup for lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option Heap"  +
  fixes dp :: "'k \<Rightarrow> 'v"
  fixes init :: "'m Heap"
  assumes success: "success init Heap.empty"
  assumes empty_correct:
    "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> map_of_heap' empty heap \<subseteq>\<^sub>m Map.empty"
    and P_empty: "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> P empty heap"
begin

sublocale dp_consistency_heap
  where P="P init_mem"
    and lookup="lookup init_mem"
    and update="update init_mem"
  apply standard
       apply (rule lookup_inv[of init_mem])
      apply (rule update_inv[of init_mem])
  subgoal
    unfolding heap_mem_defs.map_of_heap_def
    by (rule lookup_correct[of init_mem, unfolded map_of_heap'_def])
  subgoal
    unfolding heap_mem_defs.map_of_heap_def
    by (rule update_correct[of init_mem, unfolded map_of_heap'_def])
  done

definition "init_mem = result_of init Heap.empty"

interpretation consistent: dp_consistency_heap_empty
  where P="P init_mem"
    and lookup="lookup init_mem"
    and update="update init_mem"
    and empty= "heap_of init Heap.empty"
  apply standard
  subgoal
    apply (rule successE[OF success])
    apply (frule empty_correct)
    unfolding heap_mem_defs.map_of_heap_def init_mem_def map_of_heap'_def
    by simp
  subgoal
    apply (rule successE[OF success])
    apply (frule P_empty)
    unfolding init_mem_def
    by simp
  done

lemma memoized_empty:
  "dp x = result_of (init \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP init_mem (dp\<^sub>T (result_of init Heap.empty))"
  by (simp add: execute_bind_success consistent.memoized[OF that(1)] success)

end

locale dp_consistency_new =
  fixes dp :: "'k \<Rightarrow> 'v"
  fixes P :: "'m \<Rightarrow> heap \<Rightarrow> bool"
    and lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option Heap"
    and update :: "'m \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and init
  assumes
    success: "success init Heap.empty"
  assumes
    inv_init: "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> P empty heap"
  assumes consistent:
    "\<And> empty heap. execute init Heap.empty = Some (empty, heap)
    \<Longrightarrow> dp_consistency_heap_empty (P empty) (update empty) (lookup empty) heap"
begin

sublocale dp_consistency_heap_empty
  where P="P (result_of init Heap.empty)"
    and lookup="lookup (result_of init Heap.empty)"
    and update="update (result_of init Heap.empty)"
    and empty= "heap_of init Heap.empty"
  using success by (auto 4 3 intro: consistent successE) (* Extract Theorem *)

lemma memoized_empty:
  "dp x = result_of (init \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP (dp\<^sub>T (result_of init Heap.empty))"
  by (simp add: execute_bind_success memoized[OF that(1)] success)

end

locale dp_consistency_new' =
  fixes dp :: "'k \<Rightarrow> 'v"
  fixes P :: "'m \<Rightarrow> heap \<Rightarrow> bool"
    and lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option Heap"
    and update :: "'m \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and init
    and mem :: 'm
  assumes mem_is_init: "mem = result_of init Heap.empty"
  assumes
    success: "success init Heap.empty"
  assumes
    inv_init: "\<And> empty heap. execute init Heap.empty = Some (empty, heap) \<Longrightarrow> P empty heap"
  assumes consistent:
    "\<And> empty heap. execute init Heap.empty = Some (empty, heap)
    \<Longrightarrow> dp_consistency_heap_empty (P empty) (update empty) (lookup empty) heap"
begin

sublocale dp_consistency_heap_empty
  where P="P mem"
    and lookup="lookup mem"
    and update="update mem"
    and empty= "heap_of init Heap.empty"
  unfolding mem_is_init
  using success by (auto 4 3 intro: consistent successE) (* Extract Theorem *)

lemma memoized_empty:
  "dp x = result_of (init \<bind> (\<lambda>mem. dp\<^sub>T mem x)) Heap.empty"
  if "consistentDP (dp\<^sub>T (result_of init Heap.empty))"
  by (simp add: execute_bind_success memoized[OF that(1)] success)

end

locale dp_consistency_heap_array_new' =
  fixes size :: nat
    and to_index :: "('k :: heap) \<Rightarrow> nat"
    and mem :: "('v::heap) option array"
    and dp :: "'k \<Rightarrow> 'v::heap"
  assumes mem_is_init: "mem = result_of (mem_empty size) Heap.empty"
  assumes injective: "injective size to_index"
begin

sublocale dp_consistency_new'
  where P      = "\<lambda> mem heap. Array.length heap mem = size"
    and lookup = "\<lambda> mem. mem_lookup size to_index mem"
    and update = "\<lambda> mem. mem_update size to_index mem"
    and init   = "mem_empty size"
    and mem    = mem
  apply (rule dp_consistency_new'.intro)
  subgoal
    by (rule mem_is_init)
  subgoal
    by (rule success_empty)
  subgoal for empty heap
    using length_mem_empty by (metis fst_conv option.sel snd_conv)
  subgoal
    apply (frule execute_heap_ofD[symmetric])
    apply (frule execute_result_ofD[symmetric])
    apply simp
    apply (rule array_consistentI[OF injective HOL.refl])
    done
  done

thm memoized_empty

end

locale dp_consistency_heap_array_new =
  fixes size :: nat
    and to_index :: "('k :: heap) \<Rightarrow> nat"
    and dp :: "'k \<Rightarrow> 'v::heap"
  assumes injective: "injective size to_index"
begin

sublocale dp_consistency_new
  where P      = "\<lambda> mem heap. Array.length heap mem = size"
    and lookup = "\<lambda> mem. mem_lookup size to_index mem"
    and update = "\<lambda> mem. mem_update size to_index mem"
    and init   = "mem_empty size"
  apply (rule dp_consistency_new.intro)
  subgoal
    by (rule success_empty)
  subgoal for empty heap
    using length_mem_empty by (metis fst_conv option.sel snd_conv)
  subgoal
    apply (frule execute_heap_ofD[symmetric])
    apply (frule execute_result_ofD[symmetric])
    apply simp
    apply (rule array_consistentI[OF injective HOL.refl])
    done
  done

thm memoized_empty

end

locale dp_consistency_heap_array =
  fixes size :: nat
    and to_index :: "('k :: heap) \<Rightarrow> nat"
    and dp :: "'k \<Rightarrow> 'v::heap"
  assumes injective: "injective size to_index"
begin

sublocale dp_consistency_heap_init
  where P="\<lambda>mem heap. Array.length heap mem = size"
    and lookup="\<lambda> mem. mem_lookup size to_index mem"
    and update="\<lambda> mem. mem_update size to_index mem"
    and init="mem_empty size"
  apply standard
  subgoal lookup_inv
    unfolding lift_p_def mem_lookup_def by (simp add: Let_def execute_simps)
  subgoal update_inv
    unfolding State_Heap.lift_p_def mem_update_def by (simp add: Let_def execute_simps)
  subgoal for k heap
    unfolding heap_correct_init_defs.map_of_heap'_def map_le_def mem_lookup_def
    by (auto simp: execute_simps Let_def split: if_split_asm)
  subgoal for heap k
    unfolding heap_correct_init_defs.map_of_heap'_def map_le_def mem_lookup_def mem_update_def
    apply (auto simp: execute_simps Let_def length_def split: if_split_asm)
    apply (subst (asm) nth_list_update_neq)
    using injective[unfolded injective_def] apply auto
    done
  subgoal
    by (rule success_empty)
  subgoal for empty' heap
    unfolding heap_correct_init_defs.map_of_heap'_def mem_lookup_def
    by (auto intro!: map_emptyI simp: Let_def ) (metis fst_conv option.sel snd_conv nth_mem_empty)
  subgoal for empty' heap
    unfolding heap_correct_init_defs.map_of_heap'_def mem_lookup_def map_le_def
    using length_mem_empty by (metis fst_conv option.sel snd_conv)
  done

end


locale dp_consistency_heap_array_pair' =
  fixes size :: nat
  fixes key1 :: "'k \<Rightarrow> ('k1 :: heap)" and key2 :: "'k \<Rightarrow> 'k2 :: heap"
    and to_index :: "'k2 \<Rightarrow> nat"
    and dp :: "'k \<Rightarrow> 'v::heap"
    and k1 k2 :: "'k1"
    and mem :: "('k1 ref \<times>
             'k1 ref \<times>
             'v option array ref \<times>
             'v option array ref)"
  assumes mem_is_init: "mem = result_of (init_state size k1 k2) Heap.empty"
  assumes injective: "injective size to_index"
      and keys_injective: "\<forall>k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
      and keys_neq: "k1 \<noteq> k2"
begin

definition
  "inv_pair' = (\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      pair_mem_defs.inv_pair (lookup1 size to_index m_ref1)
        (lookup2 size to_index m_ref2) (get_k1 k_ref1)
        (get_k2 k_ref2)
        (inv_pair_weak size m_ref1 m_ref2 k_ref1 k_ref2) key1 key2)"

sublocale dp_consistency_new'
  where P=inv_pair'
    and lookup="\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      lookup_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2"
    and update="\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      update_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2"
    and init="init_state size k1 k2"
  apply (rule dp_consistency_new'.intro)
  subgoal
    by (rule mem_is_init)
  subgoal
    by (rule succes_init_state)
  subgoal for empty heap
    unfolding inv_pair'_def
    apply safe
    apply (rule init_state_inv')
        apply (rule injective)
       apply (erule init_state_distinct)
      apply (rule keys_injective)
     apply assumption
    apply (rule keys_neq)
    done
  apply safe
  unfolding inv_pair'_def
  apply simp
  apply (rule consistent_empty_pairI)
      apply (rule injective)
     apply (erule init_state_distinct)
    apply (rule keys_injective)
   apply assumption
  apply (rule keys_neq)
  done

end

locale dp_consistency_heap_array_pair_iterator =
  dp_consistency_heap_array_pair' where dp = dp + iterator where cnt = cnt
  for dp :: "'k \<Rightarrow> 'v::heap" and cnt :: "'k \<Rightarrow> bool"
begin

sublocale dp_consistency_iterator_heap
  where P = "inv_pair' mem"
  and update = "(case mem of
  (k_ref1, k_ref2, m_ref1, m_ref2) \<Rightarrow>
    update_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2)"
  and lookup = "(case mem of
  (k_ref1, k_ref2, m_ref1, m_ref2) \<Rightarrow>
    lookup_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2)"
  ..

end


locale dp_consistency_heap_array_pair =
  fixes size :: nat
  fixes key1 :: "'k \<Rightarrow> ('k1 :: heap)" and key2 :: "'k \<Rightarrow> 'k2 :: heap"
    and to_index :: "'k2 \<Rightarrow> nat"
    and dp :: "'k \<Rightarrow> 'v::heap"
    and k1 k2 :: "'k1"
  assumes injective: "injective size to_index"
      and keys_injective: "\<forall>k k'. key1 k = key1 k' \<and> key2 k = key2 k' \<longrightarrow> k = k'"
      and keys_neq: "k1 \<noteq> k2"
begin

definition
  "inv_pair' = (\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      pair_mem_defs.inv_pair (lookup1 size to_index m_ref1)
        (lookup2 size to_index m_ref2) (get_k1 k_ref1)
        (get_k2 k_ref2)
        (inv_pair_weak size m_ref1 m_ref2 k_ref1 k_ref2) key1 key2)"

sublocale dp_consistency_new
  where P=inv_pair'
    and lookup="\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      lookup_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2"
    and update="\<lambda> (k_ref1, k_ref2, m_ref1, m_ref2).
      update_pair size to_index key1 key2 m_ref1 m_ref2 k_ref1 k_ref2"
    and init="init_state size k1 k2"
  apply (rule dp_consistency_new.intro)
  subgoal
    by (rule succes_init_state)
  subgoal for empty heap
    unfolding inv_pair'_def
    apply safe
    apply (rule init_state_inv')
        apply (rule injective)
       apply (erule init_state_distinct)
      apply (rule keys_injective)
     apply assumption
    apply (rule keys_neq)
    done
  apply safe
  unfolding inv_pair'_def
  apply simp
  apply (rule consistent_empty_pairI)
      apply (rule injective)
     apply (erule init_state_distinct)
    apply (rule keys_injective)
   apply assumption
  apply (rule keys_neq)
  done

end

subsubsection \<open>Code Setup\<close>
lemmas [code_unfold] = heap_mem_defs.checkmem_checkmem'[symmetric]
lemmas [code] =
  heap_mem_defs.checkmem'_def
  Heap_Main.map\<^sub>T_def

end (* theory *)
