(*
  File: IntervalTree_Impl.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of interval tree\<close>

theory IntervalTree_Impl
  imports SepAuto "../Functional/Interval_Tree"
begin

text \<open>Imperative version of interval tree.\<close>

subsection \<open>Interval and IdxInterval\<close>

fun interval_encode :: "('a::heap) interval \<Rightarrow> nat" where
  "interval_encode (Interval l h) = to_nat (l, h)"

instance interval :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "interval_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun idx_interval_encode :: "('a::heap) idx_interval \<Rightarrow> nat" where
  "idx_interval_encode (IdxInterval it i) = to_nat (it, i)"

instance idx_interval :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "idx_interval_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

subsection \<open>Tree nodes\<close>

datatype 'a node =
  Node (lsub: "'a node ref option") (val: "'a idx_interval") (tmax: nat) (rsub: "'a node ref option")
setup \<open>fold add_rewrite_rule @{thms node.sel}\<close>

fun node_encode :: "('a::heap) node \<Rightarrow> nat" where
  "node_encode (Node l v m r) = to_nat (l, v, m, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

fun int_tree :: "interval_tree \<Rightarrow> nat node ref option \<Rightarrow> assn" where
  "int_tree Tip p = \<up>(p = None)"
| "int_tree (interval_tree.Node lt v m rt) (Some p) = (\<exists>\<^sub>Alp rp. p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp)"
| "int_tree (interval_tree.Node lt v m rt) None = false"
setup \<open>fold add_rewrite_ent_rule @{thms int_tree.simps}\<close>

lemma int_tree_Tip [forward_ent]: "int_tree Tip p \<Longrightarrow>\<^sub>A \<up>(p = None)" by auto2

lemma int_tree_Node [forward_ent]:
  "int_tree (interval_tree.Node lt v m rt) p \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Alp rp. the p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp * \<up>(p \<noteq> None))"
@proof @case "p = None" @qed

lemma int_tree_none: "emp \<Longrightarrow>\<^sub>A int_tree interval_tree.Tip None" by auto2

lemma int_tree_constr_ent:
  "p \<mapsto>\<^sub>r Node lp v m rp * int_tree lt lp * int_tree rt rp \<Longrightarrow>\<^sub>A int_tree (interval_tree.Node lt v m rt) (Some p)" by auto2

setup \<open>fold add_entail_matcher [@{thm int_tree_none}, @{thm int_tree_constr_ent}]\<close>
setup \<open>fold del_prfstep_thm @{thms int_tree.simps}\<close>

type_synonym int_tree = "nat node ref option"

subsection \<open>Operations\<close>

subsubsection \<open>Basic operation\<close>

definition int_tree_empty :: "int_tree Heap" where
  "int_tree_empty = return None"

lemma int_tree_empty_to_fun [hoare_triple]:
  "<emp> int_tree_empty <int_tree Tip>" by auto2

definition int_tree_is_empty :: "int_tree \<Rightarrow> bool Heap" where
  "int_tree_is_empty b = return (b = None)"

lemma int_tree_is_empty_rule [hoare_triple]:
  "<int_tree t b>
   int_tree_is_empty b
   <\<lambda>r. int_tree t b * \<up>(r \<longleftrightarrow> t = Tip)>" by auto2

definition get_tmax :: "int_tree \<Rightarrow> nat Heap" where
  "get_tmax b = (case b of
     None \<Rightarrow> return 0
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      return (tmax t) })"

lemma get_tmax_rule [hoare_triple]:
  "<int_tree t b> get_tmax b <\<lambda>r. int_tree t b * \<up>(r = interval_tree.tmax t)>"
@proof @case "t = Tip" @qed

definition compute_tmax :: "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree \<Rightarrow> nat Heap" where
  "compute_tmax it l r = do {
    lm \<leftarrow> get_tmax l;
    rm \<leftarrow> get_tmax r;
    return (max3 it lm rm)
  }"

lemma compute_tmax_rule [hoare_triple]:
  "<int_tree t1 b1 * int_tree t2 b2>
   compute_tmax it b1 b2
   <\<lambda>r. int_tree t1 b1 * int_tree t2 b2 * \<up>(r = max3 it (interval_tree.tmax t1) (interval_tree.tmax t2))>"
  by auto2

definition int_tree_constr :: "int_tree \<Rightarrow> nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_constr lp v rp = do {
    m \<leftarrow> compute_tmax v lp rp;
    p \<leftarrow> ref (Node lp v m rp);
    return (Some p) }"

lemma int_tree_constr_rule [hoare_triple]:
  "<int_tree lt lp * int_tree rt rp>
   int_tree_constr lp v rp
   <int_tree (interval_tree.Node lt v (max3 v (interval_tree.tmax lt) (interval_tree.tmax rt)) rt)>"
  by auto2

subsubsection \<open>Insertion\<close>
  
partial_function (heap) insert_impl :: "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "insert_impl v b = (case b of
    None \<Rightarrow> int_tree_constr None v None
  | Some p \<Rightarrow> do {
    t \<leftarrow> !p;
    (if v = val t then do {
       return (Some p) }
     else if v < val t then do {
       q \<leftarrow> insert_impl v (lsub t);
       m \<leftarrow> compute_tmax (val t) q (rsub t);
       p := Node q (val t) m (rsub t);
       return (Some p) }
     else do {
       q \<leftarrow> insert_impl v (rsub t);
       m \<leftarrow> compute_tmax (val t) (lsub t) q;
       p := Node (lsub t) (val t) m q;
       return (Some p) })})"

lemma int_tree_insert_to_fun [hoare_triple]:
  "<int_tree t b>
    insert_impl v b
   <int_tree (insert v t)>"
@proof @induct t arbitrary b @qed

subsubsection \<open>Deletion\<close>

partial_function (heap) int_tree_del_min :: "int_tree \<Rightarrow> (nat idx_interval \<times> int_tree) Heap" where
  "int_tree_del_min b = (case b of
     None \<Rightarrow> raise STR ''del_min: empty tree''
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if lsub t = None then
         return (val t, rsub t)
       else do {
         r \<leftarrow> int_tree_del_min (lsub t);
         m \<leftarrow> compute_tmax (val t) (snd r) (rsub t);
         p := Node (snd r) (val t) m (rsub t);
         return (fst r, Some p) })})"

lemma int_tree_del_min_to_fun [hoare_triple]:
  "<int_tree t b * \<up>(b \<noteq> None)>
   int_tree_del_min b
   <\<lambda>r. int_tree (snd (del_min t)) (snd r) * \<up>(fst(r) = fst (del_min t))>\<^sub>t"
@proof @induct t arbitrary b @qed

definition int_tree_del_elt :: "int_tree \<Rightarrow> int_tree Heap" where
  "int_tree_del_elt b = (case b of
     None \<Rightarrow> raise STR ''del_elt: empty tree''
   | Some p \<Rightarrow> do {
       t \<leftarrow> !p;
       (if lsub t = None then return (rsub t)
        else if rsub t = None then return (lsub t)
        else do {
          r \<leftarrow> int_tree_del_min (rsub t);
          m \<leftarrow> compute_tmax (fst r) (lsub t) (snd r);
          p := Node (lsub t) (fst r) m (snd r);
          return (Some p) }) })"

lemma int_tree_del_elt_to_fun [hoare_triple]:
  "<int_tree (interval_tree.Node lt v m rt) b>
   int_tree_del_elt b
   <int_tree (delete_elt_tree (interval_tree.Node lt v m rt))>\<^sub>t" by auto2

partial_function (heap) delete_impl :: "nat idx_interval \<Rightarrow> int_tree \<Rightarrow> int_tree Heap" where
  "delete_impl x b = (case b of
     None \<Rightarrow> return None
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if x = val t then do {
         r \<leftarrow> int_tree_del_elt b;
         return r }
       else if x < val t then do {
         q \<leftarrow> delete_impl x (lsub t);
         m \<leftarrow> compute_tmax (val t) q (rsub t);
         p := Node q (val t) m (rsub t);
         return (Some p) }
       else do {
         q \<leftarrow> delete_impl x (rsub t);
         m \<leftarrow> compute_tmax (val t) (lsub t) q;
         p := Node (lsub t) (val t) m q;
         return (Some p) })})"

lemma int_tree_delete_to_fun [hoare_triple]:
  "<int_tree t b>
    delete_impl x b
   <int_tree (delete x t)>\<^sub>t"
@proof @induct t arbitrary b @qed

subsubsection \<open>Search\<close>

partial_function (heap) search_impl :: "nat interval \<Rightarrow> int_tree \<Rightarrow> bool Heap" where
  "search_impl x b = (case b of
     None \<Rightarrow> return False
   | Some p \<Rightarrow> do {
      t \<leftarrow> !p;
      (if is_overlap (int (val t)) x then return True
       else case lsub t of
           None \<Rightarrow> do { b \<leftarrow> search_impl x (rsub t); return b }
         | Some lp \<Rightarrow> do {
            lt \<leftarrow> !lp;
            if tmax lt \<ge> low x then
              do { b \<leftarrow> search_impl x (lsub t); return b }
            else
              do { b \<leftarrow> search_impl x (rsub t); return b }})})"

lemma search_impl_correct [hoare_triple]:
  "<int_tree t b>
    search_impl x b
   <\<lambda>r. int_tree t b * \<up>(r \<longleftrightarrow> search t x)>"
@proof @induct t arbitrary b @with
  @subgoal "t = interval_tree.Node l v m r"
    @case "is_overlap (int v) x"
    @case "l \<noteq> Tip \<and> interval_tree.tmax l \<ge> low x"
  @endgoal @end
@qed

subsection \<open>Outer interface\<close>

text \<open>Express Hoare triples for operations on interval tree in terms of
  the set of intervals represented by the tree.\<close>
definition int_tree_set :: "nat idx_interval set \<Rightarrow> int_tree \<Rightarrow> assn" where
  "int_tree_set S p = (\<exists>\<^sub>At. int_tree t p * \<up>(is_interval_tree t) * \<up>(S = tree_set t))"
setup \<open>add_rewrite_ent_rule @{thm int_tree_set_def}\<close>

theorem int_tree_empty_rule [hoare_triple]:
  "<emp> int_tree_empty <int_tree_set {}>" by auto2

theorem int_tree_insert_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval (int x))>
   insert_impl x b
   <int_tree_set (S \<union> {x})>" by auto2

theorem int_tree_delete_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval (int x))>
   delete_impl x b
   <int_tree_set (S - {x})>\<^sub>t" by auto2

theorem int_tree_search_rule [hoare_triple]:
  "<int_tree_set S b * \<up>(is_interval x)>
   search_impl x b
   <\<lambda>r. int_tree_set S b * \<up>(r \<longleftrightarrow> has_overlap S x)>" by auto2

setup \<open>del_prfstep_thm @{thm int_tree_set_def}\<close>

end
