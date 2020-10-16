section \<open>Open Singly Linked Lists\<close>
theory Open_List
imports List_Seg Imp_List_Spec
begin

subsection \<open>Definitions\<close>
type_synonym 'a os_list = "'a node ref option"

abbreviation os_list :: "'a list \<Rightarrow> ('a::heap) os_list \<Rightarrow> assn" where
  "os_list l p \<equiv> lseg l p None"

subsection \<open>Precision\<close>
lemma os_prec: 
  "precise os_list"
  by rule (simp add: lseg_prec2)

lemma os_imp_list_impl: "imp_list os_list"
  apply unfold_locales
  apply (rule os_prec)
  done
interpretation os: imp_list os_list by (rule os_imp_list_impl)

subsection \<open>Operations\<close>
subsubsection \<open>Allocate Empty List\<close>

definition os_empty :: "'a::heap os_list Heap" where
  "os_empty \<equiv> return None"

lemma os_empty_rule: "<emp> os_empty <os_list []>"
  unfolding os_empty_def
  apply sep_auto
  done

lemma os_empty_impl: "imp_list_empty os_list os_empty"
  apply unfold_locales
  apply (sep_auto heap add: os_empty_rule)
  done
interpretation os: imp_list_empty os_list os_empty by (rule os_empty_impl)
  
subsubsection \<open>Emptiness check\<close>
text \<open>A linked list is empty, iff it is the null pointer.\<close>

definition os_is_empty :: "'a::heap os_list \<Rightarrow> bool Heap" where
  "os_is_empty b \<equiv> return (b = None)"

lemma os_is_empty_rule: 
  "<os_list xs b> os_is_empty b <\<lambda>r. os_list xs b * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding os_is_empty_def
  apply sep_auto
  done

lemma os_is_empty_impl: "imp_list_is_empty os_list os_is_empty"
  apply unfold_locales
  apply (sep_auto heap add: os_is_empty_rule)
  done
interpretation os: imp_list_is_empty os_list os_is_empty
  by (rule os_is_empty_impl)

subsubsection \<open>Prepend\<close>

text \<open>To push an element to the front of a list we allocate a new node which
  stores the element and the old list as successor. The new list is the new 
  allocated reference.\<close>

definition os_prepend :: "'a \<Rightarrow> 'a::heap os_list \<Rightarrow> 'a os_list Heap" where
  "os_prepend a n = do { p \<leftarrow> ref (Node a n); return (Some p) }"

lemma os_prepend_rule:
  "<os_list xs n> os_prepend x n <os_list (x # xs)>"
  unfolding os_prepend_def
  apply sep_auto
  done

lemma os_prepend_impl: "imp_list_prepend os_list os_prepend"
  apply unfold_locales
  apply (sep_auto heap add: os_prepend_rule)
  done
interpretation os: imp_list_prepend os_list os_prepend 
  by (rule os_prepend_impl)

subsubsection\<open>Pop\<close>
text \<open>To pop the first element out of the list we look up the value and the
  reference of the node and return the pair of those.\<close>

fun os_pop :: "'a::heap os_list \<Rightarrow> ('a \<times> 'a os_list) Heap" where
  "os_pop None   = raise STR ''Empty Os_list''" |
  "os_pop (Some p) = do {m \<leftarrow> !p; return (val m, next m)}"

declare os_pop.simps[simp del]

lemma os_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <os_list xs r> 
  os_pop r 
  <\<lambda>(x,r'). os_list (tl xs) r' * (the r) \<mapsto>\<^sub>r (Node x r') * \<up>(x = hd xs)>"

  apply (cases r, simp_all)
  apply (cases xs, simp_all)

  apply (sep_auto simp: os_pop.simps)
  done

lemma os_pop_impl: "imp_list_pop os_list os_pop"
  apply unfold_locales
  apply (sep_auto heap add: os_pop_rule)
  done
interpretation os: imp_list_pop os_list os_pop by (rule os_pop_impl)

subsubsection \<open>Reverse\<close>

text \<open>The following reversal function is equivalent to the one from 
  Imperative HOL. And gives a more difficult example.\<close>

partial_function (heap) os_reverse_aux 
  :: "'a::heap os_list \<Rightarrow> 'a os_list \<Rightarrow> 'a os_list Heap" 
  where [code]:
  "os_reverse_aux q p = (case p of 
    None \<Rightarrow> return q |
    Some r \<Rightarrow> do {
      v \<leftarrow> !r;
      r := Node (val v) q;
      os_reverse_aux p (next v) })"

lemma [simp, sep_dflt_simps]:
  "os_reverse_aux q None = return q"
  "os_reverse_aux q (Some r) = do {
      v \<leftarrow> !r;
      r := Node (val v) q;
      os_reverse_aux (Some r) (next v) }"
  apply (subst os_reverse_aux.simps)
  apply simp
  apply (subst os_reverse_aux.simps)
  apply simp
  done

definition "os_reverse p = os_reverse_aux None p"

lemma os_reverse_aux_rule: 
  "<os_list xs p * os_list ys q> 
    os_reverse_aux q p 
  <os_list ((rev xs) @ ys) >"
proof (induct xs arbitrary: p q ys)
  case Nil thus ?case
    apply sep_auto
    done
next
  case (Cons x xs)
  show ?case
    apply (cases p, simp_all)
    apply (sep_auto heap add: cons_pre_rule[OF _ Cons.hyps])
    done
qed

lemma os_reverse_rule: "<os_list xs p> os_reverse p <os_list (rev xs)>"
  unfolding os_reverse_def
  apply (auto simp: os_reverse_aux_rule[where ys="[]", simplified, rule_format])
  done

lemma os_reverse_impl: "imp_list_reverse os_list os_reverse"
  apply unfold_locales
  apply (sep_auto heap add: os_reverse_rule)
  done
interpretation os: imp_list_reverse os_list os_reverse
  by (rule os_reverse_impl)

subsubsection \<open>Remove\<close>
 
text \<open>Remove all appearances of an element from a linked list.\<close>

partial_function (heap) os_rem 
  :: "'a::heap \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option Heap" 
  where [code]:
  "os_rem x b = (case b of 
     None \<Rightarrow> return None |
     Some p \<Rightarrow> do { 
       n \<leftarrow> !p;
       q \<leftarrow> os_rem x (next n);
       (if (val n = x) 
         then return q
         else do { 
           p := Node (val n) q; 
           return (Some p) }) })"

lemma [simp, sep_dflt_simps]: 
  "os_rem x None = return None"
  "os_rem x (Some p) = do { 
       n \<leftarrow> !p;
       q \<leftarrow> os_rem x (next n);
       (if (val n = x) 
         then return q
         else do { 
           p := Node (val n) q; 
           return (Some p) }) }"
  apply (subst os_rem.simps, simp)+
  done

lemma os_rem_rule[sep_heap_rules]: 
  "<os_list xs b> os_rem x b <\<lambda>r. os_list (removeAll x xs) r * true>"
proof (induct xs arbitrary: b x) (* Have to generalize over x, as 
    sep_auto preprocessor introduces a new variable. Alternative: 
    No preprocessing. (See alternative proof below) *)
  case Nil show ?case
    apply sep_auto
    done
next
  case (Cons y xs) 
  show ?case by (sep_auto heap add: Cons.hyps)
qed

lemma os_rem_rule_alt_proof: 
  "<os_list xs b> os_rem x b <\<lambda>r. os_list (removeAll x xs) r * true>"
proof (induct xs arbitrary: b) 
  case Nil show ?case
    apply sep_auto
    done
next
  case (Cons y xs)
  show ?case 
    by (sep_auto (nopre) heap add: Cons.hyps) (* Switching off preprocessor *)
qed

subsubsection \<open>Iterator\<close>

type_synonym 'a os_list_it = "'a os_list"
definition "os_is_it l p l2 it 
  \<equiv> \<exists>\<^sub>Al1. \<up>(l=l1@l2) * lseg l1 p it * os_list l2 it"

definition os_it_init :: "'a os_list \<Rightarrow> ('a os_list_it) Heap" 
  where "os_it_init l = return l"

fun os_it_next where 
  "os_it_next (Some p) = do {
    n \<leftarrow> !p;
    return (val n,next n)
  }"

definition os_it_has_next :: "'a os_list_it \<Rightarrow> bool Heap" where
  "os_it_has_next it \<equiv> return (it\<noteq>None)"

lemma os_iterate_impl: 
  "imp_list_iterate os_list os_is_it os_it_init os_it_has_next os_it_next"
  apply unfold_locales
  unfolding os_it_init_def os_is_it_def[abs_def] 
  apply sep_auto

  apply (case_tac it, simp)
  apply (case_tac l', simp)
  apply sep_auto
  apply (rule ent_frame_fwd[OF lseg_append])
    apply frame_inference
    apply simp

  unfolding os_it_has_next_def
  apply (sep_auto elim!: neq_NilE)

  apply solve_entails
  apply (rule ent_frame_fwd[OF lseg_conc])
    apply frame_inference
    apply solve_entails
  done
interpretation os: 
  imp_list_iterate os_list os_is_it os_it_init os_it_has_next os_it_next
  by (rule os_iterate_impl)

subsubsection \<open>List-Sum\<close>

partial_function (heap) os_sum' :: "int os_list_it \<Rightarrow> int \<Rightarrow> int Heap" 
  where [code]:
  "os_sum' it s = do {
    b \<leftarrow> os_it_has_next it;
    if b then do {
      (x,it') \<leftarrow> os_it_next it;
      os_sum' it' (s+x)
    } else return s
  }"

lemma os_sum'_rule[sep_heap_rules]: 
  "<os_is_it l p l' it> 
    os_sum' it s 
  <\<lambda>r. os_list l p * \<up>(r = s + sum_list l')>\<^sub>t"
proof (induct l' arbitrary: it s)
  case Nil thus ?case
    apply (subst os_sum'.simps)
    apply (sep_auto intro: os.quit_iteration)
    done
next
  case (Cons x l')
  show ?case
    apply (subst os_sum'.simps)
    apply (sep_auto heap: Cons.hyps)
    done
qed

definition "os_sum p \<equiv> do { 
  it \<leftarrow> os_it_init p;
  os_sum' it 0}"

lemma os_sum_rule[sep_heap_rules]: 
  "<os_list l p> os_sum p <\<lambda>r. os_list l p * \<up>(r=sum_list l)>\<^sub>t"
  unfolding os_sum_def
  by sep_auto

end
