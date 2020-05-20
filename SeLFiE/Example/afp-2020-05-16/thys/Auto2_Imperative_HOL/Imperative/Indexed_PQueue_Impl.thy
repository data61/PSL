(*
  File: Indexed_PQueue_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of the indexed priority queue\<close>

theory Indexed_PQueue_Impl
  imports DynamicArray "../Functional/Indexed_PQueue"
begin

text \<open>
  Imperative implementation of indexed priority queue. The data structure
  is also verified in \cite{Refine_Imperative_HOL-AFP} by Peter Lammich.
\<close>

datatype 'a indexed_pqueue =
  Indexed_PQueue (pqueue: "(nat \<times> 'a) dynamic_array") (index: "nat option array")
setup \<open>add_simple_datatype "indexed_pqueue"\<close>

fun idx_pqueue :: "'a::heap idx_pqueue \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue (xs, m) (Indexed_PQueue pq idx) = (dyn_array xs pq * idx \<mapsto>\<^sub>a m)"
setup \<open>add_rewrite_ent_rule @{thm idx_pqueue.simps}\<close>

subsection \<open>Basic operations\<close>

definition idx_pqueue_empty :: "nat \<Rightarrow> 'a::heap indexed_pqueue Heap" where
  "idx_pqueue_empty k = do {
    pq \<leftarrow> dyn_array_new;
    idx \<leftarrow> Array.new k None;
    return (Indexed_PQueue pq idx) }"

lemma idx_pqueue_empty_rule [hoare_triple]:
  "<emp>
   idx_pqueue_empty n
   <idx_pqueue ([], replicate n None)>" by auto2

definition idx_pqueue_nth :: "'a::heap indexed_pqueue \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) Heap" where
  "idx_pqueue_nth p i = array_nth (pqueue p) i"

lemma idx_pqueue_nth_rule [hoare_triple]:
  "<idx_pqueue (xs, m) p * \<up>(i < length xs)>
   idx_pqueue_nth p i
   <\<lambda>r. idx_pqueue (xs, m) p * \<up>(r = xs ! i)>" by auto2

definition idx_nth :: "'a::heap indexed_pqueue \<Rightarrow> nat \<Rightarrow> nat option Heap" where
  "idx_nth p i = Array.nth (index p) i"

lemma idx_nth_rule [hoare_triple]:
  "<idx_pqueue (xs, m) p * \<up>(i < length m)>
   idx_nth p i
   <\<lambda>r. idx_pqueue (xs, m) p * \<up>(r = m ! i)>" by auto2

definition idx_pqueue_length :: "'a indexed_pqueue \<Rightarrow> nat Heap" where
  "idx_pqueue_length a = array_length (pqueue a)"

lemma idx_pqueue_length_rule [hoare_triple]:
  "<idx_pqueue (xs, m) p>
   idx_pqueue_length p
   <\<lambda>r. idx_pqueue (xs, m) p * \<up>(r = length xs)>" by auto2

definition idx_pqueue_swap ::
  "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_pqueue_swap p i j = do {
     pr_i \<leftarrow> array_nth (pqueue p) i;
     pr_j \<leftarrow> array_nth (pqueue p) j;
     Array.upd (fst pr_i) (Some j) (index p);
     Array.upd (fst pr_j) (Some i) (index p);
     array_swap (pqueue p) i j
   }"

lemma idx_pqueue_swap_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   idx_pqueue_swap p i j
   <\<lambda>_. idx_pqueue (idx_pqueue_swap_fun (xs, m) i j) p>"
@proof @unfold "idx_pqueue_swap_fun (xs, m) i j" @qed

definition idx_pqueue_push :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "idx_pqueue_push k v p = do {
     len \<leftarrow> array_length (pqueue p);
     d' \<leftarrow> push_array (k, v) (pqueue p);
     Array.upd k (Some len) (index p);
     return (Indexed_PQueue d' (index p))
   }"

lemma idx_pqueue_push_rule [hoare_triple]:
  "k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   idx_pqueue_push k v p
   <idx_pqueue (idx_pqueue_push_fun k v (xs, m))>\<^sub>t"
@proof @unfold "idx_pqueue_push_fun k v (xs, m)" @qed

definition idx_pqueue_pop :: "'a::heap indexed_pqueue \<Rightarrow> ((nat \<times> 'a) \<times> 'a indexed_pqueue) Heap" where
  "idx_pqueue_pop p = do {
     (x, d') \<leftarrow> pop_array (pqueue p);
     Array.upd (fst x) None (index p);
     return (x, Indexed_PQueue d' (index p))
   }"

lemma idx_pqueue_pop_rule [hoare_triple]:
  "xs \<noteq> [] \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   idx_pqueue_pop p
   <\<lambda>(x, r). idx_pqueue (idx_pqueue_pop_fun (xs, m)) r * \<up>(x = last xs)>"
@proof @unfold "idx_pqueue_pop_fun (xs, m)" @qed

definition idx_pqueue_array_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> unit Heap" where
  "idx_pqueue_array_upd i x d = array_upd i x d"

lemma array_upd_idx_pqueue_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> k = fst (xs ! i) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   idx_pqueue_array_upd i (k, v) (pqueue p)
   <\<lambda>_. idx_pqueue (list_update xs i (k, v), m) p>" by auto2

definition has_key_idx_pqueue :: "nat \<Rightarrow> 'a::{heap,linorder} indexed_pqueue \<Rightarrow> bool Heap" where
  "has_key_idx_pqueue k p = do {
    i_opt \<leftarrow> Array.nth (index p) k;
    return (i_opt \<noteq> None) }"

lemma has_key_idx_pqueue_rule [hoare_triple]:
  "k < length m \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   has_key_idx_pqueue k p
   <\<lambda>r. idx_pqueue (xs, m) p * \<up>(r \<longleftrightarrow> has_key_alist xs k)>" by auto2

setup \<open>del_prfstep_thm @{thm idx_pqueue.simps}\<close>
setup \<open>del_simple_datatype "indexed_pqueue"\<close>

subsection \<open>Bubble up and down\<close>

partial_function (heap) idx_bubble_down :: "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_down a k = do {
    len \<leftarrow> idx_pqueue_length a;
    (if s2 k < len then do {
      vk \<leftarrow> idx_pqueue_nth a k;
      vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
      vs2k \<leftarrow> idx_pqueue_nth a (s2 k);
      (if snd vs1k \<le> snd vs2k then
         if snd vk > snd vs1k then
           do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
         else return ()
       else
         if snd vk > snd vs2k then
           do { idx_pqueue_swap a k (s2 k); idx_bubble_down a (s2 k) }
         else return ()) }
     else if s1 k < len then do {
       vk \<leftarrow> idx_pqueue_nth a k;
       vs1k \<leftarrow> idx_pqueue_nth a (s1 k);
       (if snd vk > snd vs1k then
          do { idx_pqueue_swap a k (s1 k); idx_bubble_down a (s1 k) }
        else return ()) }
     else return ()) }"

lemma idx_bubble_down_rule [hoare_triple]:
  "index_of_pqueue x \<Longrightarrow>
   <idx_pqueue x a>
   idx_bubble_down a k
   <\<lambda>_. idx_pqueue (idx_bubble_down_fun x k) a>"
@proof @fun_induct "idx_bubble_down_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_down_fun (xs, m) k"
  @case "s2 k < length xs" @with
    @case "snd (xs ! s1 k) \<le> snd (xs ! s2 k)"
  @end
  @case "s1 k < length xs" @end
@qed

partial_function (heap) idx_bubble_up :: "'a::{heap,linorder} indexed_pqueue \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "idx_bubble_up a k =
    (if k = 0 then return () else do {
       len \<leftarrow> idx_pqueue_length a;
       (if k < len then do {
          vk \<leftarrow> idx_pqueue_nth a k;
          vpk \<leftarrow> idx_pqueue_nth a (par k);
          (if snd vk < snd vpk then
             do { idx_pqueue_swap a k (par k); idx_bubble_up a (par k) }
           else return ()) }
        else return ())})"

lemma idx_bubble_up_rule [hoare_triple]:
  "index_of_pqueue x \<Longrightarrow>
   <idx_pqueue x a>
   idx_bubble_up a k
   <\<lambda>_. idx_pqueue (idx_bubble_up_fun x k) a>"
@proof @fun_induct "idx_bubble_up_fun x k" @with
  @subgoal "(x = (xs, m), k = k)"
  @unfold "idx_bubble_up_fun (xs, m) k" @end
@qed

subsection \<open>Main operations\<close>

definition delete_min_idx_pqueue :: "'a::{heap,linorder} indexed_pqueue \<Rightarrow> ((nat \<times> 'a) \<times> 'a indexed_pqueue) Heap" where
  "delete_min_idx_pqueue p = do {
     len \<leftarrow> idx_pqueue_length p;
     if len = 0 then raise STR ''delete_min''
     else do {
       idx_pqueue_swap p 0 (len - 1);
       (x', r) \<leftarrow> idx_pqueue_pop p;
       idx_bubble_down r 0;
       return (x', r)
     }
   }"

lemma delete_min_idx_pqueue_rule [hoare_triple]:
  "xs \<noteq> [] \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). idx_pqueue (snd (delete_min_idx_pqueue_fun (xs, m))) r *
       \<up>(x = fst (delete_min_idx_pqueue_fun (xs, m)))>"
@proof @unfold "delete_min_idx_pqueue_fun (xs, m)" @qed

definition insert_idx_pqueue :: "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "insert_idx_pqueue k v p = do {
     p' \<leftarrow> idx_pqueue_push k v p;
     len \<leftarrow> idx_pqueue_length p';
     idx_bubble_up p' (len - 1);
     return p'
   }"

lemma insert_idx_pqueue_rule [hoare_triple]:
  "k < length m \<Longrightarrow> \<not>has_key_alist xs k \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   insert_idx_pqueue k v p
   <idx_pqueue (insert_idx_pqueue_fun k v (xs, m))>\<^sub>t"
@proof @unfold "insert_idx_pqueue_fun k v (xs, m)" @qed

definition update_idx_pqueue ::
  "nat \<Rightarrow> 'a::{heap,linorder} \<Rightarrow> 'a indexed_pqueue \<Rightarrow> 'a indexed_pqueue Heap" where
  "update_idx_pqueue k v p = do {
    i_opt \<leftarrow> idx_nth p k;
    case i_opt of
      None \<Rightarrow> insert_idx_pqueue k v p
    | Some i \<Rightarrow> do {
      x \<leftarrow> idx_pqueue_nth p i;
      idx_pqueue_array_upd i (k, v) (pqueue p);
      (if snd x \<le> v then do {idx_bubble_down p i; return p}
       else do {idx_bubble_up p i; return p}) }}"

lemma update_idx_pqueue_rule [hoare_triple]:
  "k < length m \<Longrightarrow> index_of_pqueue (xs, m) \<Longrightarrow>
   <idx_pqueue (xs, m) p>
   update_idx_pqueue k v p
   <idx_pqueue (update_idx_pqueue_fun k v (xs, m))>\<^sub>t"
@proof @unfold "update_idx_pqueue_fun k v (xs, m)" @qed

subsection \<open>Outer interface\<close>

text \<open>Express Hoare triples for indexed priority queue operations in terms of
  the mapping represented by the queue.\<close>
definition idx_pqueue_map :: "(nat, 'a::{heap,linorder}) map \<Rightarrow> nat \<Rightarrow> 'a indexed_pqueue \<Rightarrow> assn" where
  "idx_pqueue_map M n p = (\<exists>\<^sub>Axs m. idx_pqueue (xs, m) p *
      \<up>(index_of_pqueue (xs, m)) * \<up>(is_heap xs) * \<up>(M = map_of_alist xs) * \<up>(n = length m))"
setup \<open>add_rewrite_ent_rule @{thm idx_pqueue_map_def}\<close>

lemma heap_implies_hd_min2 [resolve]:
  "is_heap xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (map_of_alist xs)\<langle>k\<rangle> = Some v \<Longrightarrow> snd (hd xs) \<le> v"
@proof
  @obtain i where "i < length xs" "xs ! i = (k, v)"
  @have "snd (hd xs) \<le> snd (xs ! i)"
@qed

theorem idx_pqueue_empty_map [hoare_triple]:
  "<emp>
   idx_pqueue_empty n
   <idx_pqueue_map empty_map n>" by auto2

theorem delete_min_idx_pqueue_map [hoare_triple]:
  "<idx_pqueue_map M n p * \<up>(M \<noteq> empty_map)>
   delete_min_idx_pqueue p
   <\<lambda>(x, r). idx_pqueue_map (delete_map (fst x) M) n r * \<up>(fst x < n) *
                \<up>(is_heap_min (fst x) M) * \<up>(M\<langle>fst x\<rangle> = Some (snd x))>" by auto2

theorem insert_idx_pqueue_map [hoare_triple]:
  "k < n \<Longrightarrow> k \<notin> keys_of M \<Longrightarrow>
   <idx_pqueue_map M n p>
   insert_idx_pqueue k v p
   <idx_pqueue_map (M {k \<rightarrow> v}) n>\<^sub>t" by auto2

theorem has_key_idx_pqueue_map [hoare_triple]:
  "k < n \<Longrightarrow>
   <idx_pqueue_map M n p>
   has_key_idx_pqueue k p
   <\<lambda>r. idx_pqueue_map M n p * \<up>(r \<longleftrightarrow> k \<in> keys_of M)>" by auto2

theorem update_idx_pqueue_map [hoare_triple]:
  "k < n \<Longrightarrow>
   <idx_pqueue_map M n p>
   update_idx_pqueue k v p
   <idx_pqueue_map (M {k \<rightarrow> v}) n>\<^sub>t" by auto2

setup \<open>del_prfstep_thm @{thm idx_pqueue_map_def}\<close>

end
