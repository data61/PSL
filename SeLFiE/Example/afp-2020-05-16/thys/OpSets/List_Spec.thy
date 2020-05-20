(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
   Alastair Beresford, University of Cambridge
*)

section\<open>Relationship to Strong List Specification\<close>

text\<open>In this section we show that our list specification is stronger than the
$\mathcal{A}_\textsf{strong}$ specification of collaborative text editing by
Attiya et al.~\cite{Attiya:2016kh}. We do this by showing that the OpSet
interpretation of any set of insertion and deletion operations satisfies all
of the consistency criteria that constitute the $\mathcal{A}_\textsf{strong}$
specification.

Attiya et al.'s specification is as follows~\cite{Attiya:2016kh}:

\begin{displayquote}
An abstract execution $A = (H, \textsf{vis})$ belongs to the
\emph{strong list specification} $\mathcal{A}_\textsf{strong}$ if and only if
there is a relation
$\textsf{lo} \subseteq \textsf{elems}(A) \times \textsf{elems}(A)$, called the
\emph{list order}, such that:
\begin{enumerate}
\item Each event $e = \mathit{do}(\mathit{op}, w) \in H$ returns a sequence of
elements $w=a_0 \dots a_{n-1}$, where $a_i \in \textsf{elems}(A)$, such that
\begin{enumerate}
\item $w$ contains exactly the elements visible to $e$ that have been inserted,
but not deleted:
\[ \forall a.\; a \in w \quad\Longleftrightarrow\quad (\mathit{do}(\textsf{ins}(a, \_), \_) \le_\textsf{vis} e)
\;\wedge\; \neg(\mathit{do}(\textsf{del}(a), \_) \le_\textsf{vis} e). \]
\item The order of the elements is consistent with the list order:
\[ \forall i, j.\; (i < j) \;\Longrightarrow\; (a_i, a_j) \in \textsf{lo}. \]
\item Elements are inserted at the specified position:
if $\mathit{op} = \textsf{ins}(a, k)$, then $a = a_{\mathrm{min} \{k,\; n-1\}}$.
\end{enumerate}
\item The list order $\textsf{lo}$ is transitive, irreflexive and total, and
thus determines the order of all insert operations in the execution.
\end{enumerate}
\end{displayquote}

This specification considers only insertion and deletion operations, but no
assignment. Moreover, it considers only a single list object, not a graph of
composable objects like in our paper. Thus, we prove the relationship to
$\mathcal{A}_\textsf{strong}$ using a simplified interpretation function that
defines only insertion and deletion on a single list.\<close>

theory List_Spec
  imports Insert_Spec
begin

text\<open>We first define a datatype for list operations, with two constructors:
\isa{Insert ref val}, and \isa{Delete ref}. For insertion, the \isa{ref} argument
is the ID of the existing element after which we want to insert, or \isa{None}
to insert at the head of the list.
The \isa{val} argument is an arbitrary value to associate with the list element.
For deletion, the \isa{ref} argument is the ID of the existing list element
to delete.\<close>

datatype ('oid, 'val) list_op =
  Insert "'oid option" "'val" |
  Delete "'oid"

text\<open>When interpreting operations, the result is a pair (\isa{list, vals}).
The \isa{list} contains the IDs of list elements in the correct order
(equivalent to the list relation in the paper), and \isa{vals} is a mapping
from list element IDs to values (equivalent to the element relation in the paper).

Insertion delegates to the previously defined \isa{insert-spec} interpretation
function. Deleting a list element removes it from \isa{vals}.\<close>

fun interp_op :: "('oid list \<times> ('oid \<rightharpoonup> 'val)) \<Rightarrow> ('oid \<times> ('oid, 'val) list_op)
               \<Rightarrow> ('oid list \<times> ('oid \<rightharpoonup> 'val))" where
  "interp_op (list, vals) (oid, Insert ref val) = (insert_spec list (oid, ref), vals(oid \<mapsto> val))" |
  "interp_op (list, vals) (oid, Delete ref    ) = (list, vals(ref := None))"

definition interp_ops :: "('oid \<times> ('oid, 'val) list_op) list \<Rightarrow> ('oid list \<times> ('oid \<rightharpoonup> 'val))" where
  "interp_ops ops \<equiv> foldl interp_op ([], Map.empty) ops"

text\<open>\isa{list-order ops x y} holds iff, after interpreting the list of
operations \isa{ops}, the list element with ID \isa{x} appears before the
list element with ID \isa{y} in the resulting list.\<close>

definition list_order :: "('oid \<times> ('oid, 'val) list_op) list \<Rightarrow> 'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "list_order ops x y \<equiv> \<exists>xs ys zs. fst (interp_ops ops) = xs @ [x] @ ys @ [y] @ zs"

text\<open>The \isa{make-insert} function generates a new operation for insertion into
a given index in a given list.
The exclamation mark is Isabelle's list subscript operator.\<close>

fun make_insert :: "'oid list \<Rightarrow> 'val \<Rightarrow> nat \<Rightarrow> ('oid, 'val) list_op" where
  "make_insert list val 0       = Insert None val" |
  "make_insert []   val k       = Insert None val" |
  "make_insert list val (Suc k) = Insert (Some (list ! (min k (length list - 1)))) val"

text\<open>The \isa{list-ops} predicate is a specialisation of \isa{spec-ops} to
the \isa{list-op} datatype: it describes a list of (ID, operation) pairs that
is sorted by ID, and can thus be used for the sequential interpretation of
the OpSet.\<close>

fun list_op_deps :: "('oid, 'val) list_op \<Rightarrow> 'oid set" where
  "list_op_deps (Insert (Some ref) _) = {ref}" |
  "list_op_deps (Insert  None      _) = {}"    |
  "list_op_deps (Delete  ref        ) = {ref}"

locale list_opset = opset opset list_op_deps
  for opset :: "('oid::{linorder} \<times> ('oid, 'val) list_op) set"

definition list_ops :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> bool" where
  "list_ops ops \<equiv> spec_ops ops list_op_deps"


subsection\<open>Lemmas about insertion and deletion\<close>

definition insertions :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> ('oid \<times> 'oid option) list" where
  "insertions ops \<equiv> List.map_filter (\<lambda>oper.
      case oper of (oid, Insert ref val) \<Rightarrow> Some (oid, ref) |
                   (oid, Delete ref    ) \<Rightarrow> None) ops"

definition inserted_ids :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> 'oid list" where
  "inserted_ids ops \<equiv> List.map_filter (\<lambda>oper.
      case oper of (oid, Insert ref val) \<Rightarrow> Some oid |
                   (oid, Delete ref    ) \<Rightarrow> None) ops"

definition deleted_ids :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> 'oid list" where
  "deleted_ids ops \<equiv> List.map_filter (\<lambda>oper.
      case oper of (oid, Insert ref val) \<Rightarrow> None |
                   (oid, Delete ref    ) \<Rightarrow> Some ref) ops"

lemma interp_ops_unfold_last:
  shows "interp_ops (xs @ [x]) = interp_op (interp_ops xs) x"
  by (simp add: interp_ops_def)

lemma map_filter_append:
  shows "List.map_filter P (xs @ ys) = List.map_filter P xs @ List.map_filter P ys"
  by (auto simp add: List.map_filter_def)

lemma map_filter_Some:
  assumes "P x = Some y"
  shows "List.map_filter P [x] = [y]"
  by (simp add: assms map_filter_simps(1) map_filter_simps(2))

lemma map_filter_None:
  assumes "P x = None"
  shows "List.map_filter P [x] = []"
  by (simp add: assms map_filter_simps(1) map_filter_simps(2))

lemma insertions_last_ins:
  shows "insertions (xs @ [(oid, Insert ref val)]) = insertions xs @ [(oid, ref)]"
  by (simp add: insertions_def map_filter_Some map_filter_append)

lemma insertions_last_del:
  shows "insertions (xs @ [(oid, Delete ref)]) = insertions xs"
  by (simp add: insertions_def map_filter_None map_filter_append)

lemma insertions_fst_subset:
  shows "set (map fst (insertions ops)) \<subseteq> set (map fst ops)"
proof(induction ops rule: List.rev_induct)
  case Nil
  then show "set (map fst (insertions [])) \<subseteq> set (map fst [])"
    by (simp add: insert_ops_def spec_ops_def insertions_def map_filter_def)
next
  case (snoc a ops)
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  then show "set (map fst (insertions (ops @ [a]))) \<subseteq> set (map fst (ops @ [a]))"
  proof(cases oper)
    case (Insert ref val)
    hence "insertions (ops @ [a]) = insertions ops @ [(oid, ref)]"
      by (simp add: a_pair insertions_last_ins)
    then show ?thesis using snoc.IH a_pair by auto
  next
    case (Delete ref)
    hence "insertions (ops @ [a]) = insertions ops"
      by (simp add: a_pair insertions_last_del)
    then show ?thesis using snoc.IH by auto
  qed
qed

lemma insertions_subset:
  assumes "list_ops A" and "list_ops B"
    and "set A \<subseteq> set B"
  shows "set (insertions A) \<subseteq> set (insertions B)"
  using assms proof(induction B arbitrary: A rule: List.rev_induct)
  case Nil
  then show "set (insertions A) \<subseteq> set (insertions [])"
    by (simp add: insertions_def map_filter_simps(2))
next
  case (snoc a ops)
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  have "list_ops ops"
    using list_ops_def spec_ops_rem_last snoc.prems(2) by blast
  then show "set (insertions A) \<subseteq> set (insertions (ops @ [a]))"
  proof(cases "a \<in> set A")
    case True
    then obtain as bs where A_split: "A = as @ a # bs \<and> a \<notin> set as"
      by (meson split_list_first)
    hence "remove1 a A = as @ bs"
      by (simp add: remove1_append)
    hence as_bs: "insertions (remove1 a A) = insertions as @ insertions bs"
      by (simp add: insertions_def map_filter_append)
    moreover have "A = as @ [a] @ bs"
      by (simp add: A_split)
    hence as_a_bs: "insertions A = insertions as @ insertions [a] @ insertions bs"
      by (metis insertions_def map_filter_append)
    moreover have IH: "set (insertions (remove1 a A)) \<subseteq> set (insertions ops)"
    proof -
      have "list_ops (remove1 a A)"
        using snoc.prems(1) list_ops_def spec_ops_remove1 by blast
      moreover have "set (remove1 a A) \<subseteq> set ops"
      proof -
        have "distinct A"
          using snoc.prems(1) list_ops_def spec_ops_distinct by blast
        hence "a \<notin> set (remove1 a A)"
          by auto
        moreover have "set (ops @ [a]) = set ops \<union> {a}"
          by auto
        moreover have "set (remove1 a A) \<subseteq> set A"
          by (simp add: set_remove1_subset)
        ultimately show "set (remove1 a A) \<subseteq> set ops"
          using snoc.prems(3) by blast
      qed
      ultimately show ?thesis
        by (simp add: \<open>list_ops ops\<close> snoc.IH)
    qed
    ultimately show ?thesis
    proof(cases oper)
      case (Insert ref val)
      hence "insertions [a] = [(oid, ref)]"
        by (simp add: insertions_def map_filter_Some a_pair)
      hence "set (insertions A) = set (insertions (remove1 a A)) \<union> {(oid, ref)}"
        using as_a_bs as_bs by auto
      moreover have "set (insertions (ops @ [a])) = set (insertions ops) \<union> {(oid, ref)}"
        by (simp add: Insert a_pair insertions_last_ins)
      ultimately show ?thesis
        using IH by auto
    next
      case (Delete ref)
      hence "insertions [a] = []"
        by (simp add: insertions_def map_filter_None a_pair)
      hence "set (insertions A) = set (insertions (remove1 a A))"
        using as_a_bs as_bs by auto
      moreover have "set (insertions (ops @ [a])) = set (insertions ops)"
        by (simp add: Delete a_pair insertions_last_del)
      ultimately show ?thesis
        using IH by auto
    qed
  next
    case False
    hence "set A \<subseteq> set ops"
      using DiffE snoc.prems by auto
    hence "set (insertions A) \<subseteq> set (insertions ops)"
      using snoc.IH snoc.prems(1) \<open>list_ops ops\<close> by blast
    moreover have "set (insertions ops) \<subseteq> set (insertions (ops @ [a]))"
      by (simp add: insertions_def map_filter_append)
    ultimately show ?thesis
      by blast
  qed
qed

lemma list_ops_insertions:
  assumes "list_ops ops"
  shows "insert_ops (insertions ops)"
  using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show "insert_ops (insertions [])"
    by (simp add: insert_ops_def spec_ops_def insertions_def map_filter_def)
next
  case (snoc a ops)
  hence IH: "insert_ops (insertions ops)"
    using list_ops_def spec_ops_rem_last by blast
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  then show "insert_ops (insertions (ops @ [a]))"
  proof(cases oper)
    case (Insert ref val)
    hence "insertions (ops @ [a]) = insertions ops @ [(oid, ref)]"
      by (simp add: a_pair insertions_last_ins)
    moreover have "\<And>i. i \<in> set (map fst ops) \<Longrightarrow> i < oid"
      using a_pair list_ops_def snoc.prems spec_ops_id_inc by fastforce
    hence "\<And>i. i \<in> set (map fst (insertions ops)) \<Longrightarrow> i < oid"
      using insertions_fst_subset by blast
    moreover have "list_op_deps oper = set_option ref"
      using Insert by (cases ref, auto)
    hence "\<And>r. r \<in> set_option ref \<Longrightarrow> r < oid"
      using list_ops_def spec_ops_ref_less
      by (metis a_pair last_in_set snoc.prems snoc_eq_iff_butlast)
    ultimately show ?thesis
      using IH insert_ops_def spec_ops_add_last by metis
  next
    case (Delete ref)
    hence "insertions (ops @ [a]) = insertions ops"
      by (simp add: a_pair insertions_last_del)
    then show ?thesis by (simp add: IH)
  qed
qed

lemma inserted_ids_last_ins:
  shows "inserted_ids (xs @ [(oid, Insert ref val)]) = inserted_ids xs @ [oid]"
  by (simp add: inserted_ids_def map_filter_Some map_filter_append)

lemma inserted_ids_last_del:
  shows "inserted_ids (xs @ [(oid, Delete ref)]) = inserted_ids xs"
  by (simp add: inserted_ids_def map_filter_None map_filter_append)

lemma inserted_ids_exist:
  shows "oid \<in> set (inserted_ids ops) \<longleftrightarrow> (\<exists>ref val. (oid, Insert ref val) \<in> set ops)"
proof(induction ops rule: List.rev_induct)
  case Nil
  then show "oid \<in> set (inserted_ids []) \<longleftrightarrow> (\<exists>ref val. (oid, Insert ref val) \<in> set [])"
    by (simp add: inserted_ids_def List.map_filter_def)
next
  case (snoc a ops)
  obtain i oper where a_pair: "a = (i, oper)"
    by fastforce
  then show "oid \<in> set (inserted_ids (ops @ [a])) \<longleftrightarrow>
             (\<exists>ref val. (oid, Insert ref val) \<in> set (ops @ [a]))"
  proof(cases oper)
    case (Insert r v)
    moreover from this have "inserted_ids (ops @ [a]) = inserted_ids ops @ [i]"
      by (simp add: a_pair inserted_ids_last_ins)
    ultimately show ?thesis
      using snoc.IH a_pair by auto
  next
    case (Delete r)
    moreover from this have "inserted_ids (ops @ [a]) = inserted_ids ops"
      by (simp add: a_pair inserted_ids_last_del)
    ultimately show ?thesis
      by (simp add: a_pair snoc.IH)
  qed
qed

lemma deleted_ids_last_ins:
  shows "deleted_ids (xs @ [(oid, Insert ref val)]) = deleted_ids xs"
  by (simp add: deleted_ids_def map_filter_None map_filter_append)

lemma deleted_ids_last_del:
  shows "deleted_ids (xs @ [(oid, Delete ref)]) = deleted_ids xs @ [ref]"
  by (simp add: deleted_ids_def map_filter_Some map_filter_append)

lemma deleted_ids_exist:
  shows "ref \<in> set (deleted_ids ops) \<longleftrightarrow> (\<exists>i. (i, Delete ref) \<in> set ops)"
proof(induction ops rule: List.rev_induct)
  case Nil
  then show "ref \<in> set (deleted_ids []) \<longleftrightarrow> (\<exists>i. (i, Delete ref) \<in> set [])"
    by (simp add: deleted_ids_def List.map_filter_def)
next
  case (snoc a ops)
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  then show "ref \<in> set (deleted_ids (ops @ [a])) \<longleftrightarrow> (\<exists>i. (i, Delete ref) \<in> set (ops @ [a]))"
  proof(cases oper)
    case (Insert r v)
    moreover from this have "deleted_ids (ops @ [a]) = deleted_ids ops"
      by (simp add: a_pair deleted_ids_last_ins)
    ultimately show ?thesis
      using a_pair snoc.IH by auto
  next
    case (Delete r)
    moreover from this have "deleted_ids (ops @ [a]) = deleted_ids ops @ [r]"
      by (simp add: a_pair deleted_ids_last_del)
    ultimately show ?thesis
      using a_pair snoc.IH by auto
  qed
qed

lemma deleted_ids_refs_older:
  assumes "list_ops (ops @ [(oid, oper)])"
  shows "\<And>ref. ref \<in> set (deleted_ids ops) \<Longrightarrow> ref < oid"
proof -
  fix ref
  assume "ref \<in> set (deleted_ids ops)"
  then obtain i where in_ops: "(i, Delete ref) \<in> set ops"
    using deleted_ids_exist by blast
  have "ref < i"
  proof -
    have "\<And>i oper r. (i, oper) \<in> set ops \<Longrightarrow> r \<in> list_op_deps oper \<Longrightarrow> r < i"
      by (meson assms list_ops_def spec_ops_ref_less spec_ops_rem_last)
    thus "ref < i"
      using in_ops by auto
  qed
  moreover have "i < oid"
  proof -
    have "\<And>i. i \<in> set (map fst ops) \<Longrightarrow> i < oid"
      using assms by (simp add: list_ops_def spec_ops_id_inc)
    thus ?thesis
      by (metis in_ops in_set_zipE zip_map_fst_snd)
  qed
  ultimately show "ref < oid"
    using order.strict_trans by blast
qed


subsection\<open>Lemmas about interpreting operations\<close>

lemma interp_ops_list_equiv:
  shows "fst (interp_ops ops) = interp_ins (insertions ops)"
proof(induction ops rule: List.rev_induct)
  case Nil
  have 1: "fst (interp_ops []) = []"
    by (simp add: interp_ops_def)
  have 2: "interp_ins (insertions []) = []"
    by (simp add: insertions_def map_filter_def interp_ins_def)
  show "fst (interp_ops []) = interp_ins (insertions [])"
    by (simp add: 1 2)
next
  case (snoc a ops)
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  then show "fst (interp_ops (ops @ [a])) = interp_ins (insertions (ops @ [a]))"
  proof(cases oper)
    case (Insert ref val)
    hence "insertions (ops @ [a]) = insertions ops @ [(oid, ref)]"
      by (simp add: a_pair insertions_last_ins)
    hence "interp_ins (insertions (ops @ [a])) = insert_spec (interp_ins (insertions ops)) (oid, ref)"
      by (simp add: interp_ins_tail_unfold)
    moreover have "fst (interp_ops (ops @ [a])) = insert_spec (fst (interp_ops ops)) (oid, ref)"
      by (metis Insert a_pair fst_conv interp_op.simps(1) interp_ops_unfold_last prod.collapse)
    ultimately show ?thesis
      using snoc.IH by auto
  next
    case (Delete ref)
    hence "insertions (ops @ [a]) = insertions ops"
      by (simp add: a_pair insertions_last_del)
    moreover have "fst (interp_ops (ops @ [a])) = fst (interp_ops ops)"
      by (metis Delete a_pair eq_fst_iff interp_op.simps(2) interp_ops_unfold_last)
    ultimately show ?thesis
      using snoc.IH by auto
  qed
qed

lemma interp_ops_distinct:
  assumes "list_ops ops"
  shows "distinct (fst (interp_ops ops))"
  by (simp add: assms interp_ins_distinct interp_ops_list_equiv list_ops_insertions)

lemma list_order_equiv:
  shows "list_order ops x y \<longleftrightarrow> Insert_Spec.list_order (insertions ops) x y"
  by (simp add: Insert_Spec.list_order_def List_Spec.list_order_def interp_ops_list_equiv)

lemma interp_ops_vals_domain:
  assumes "list_ops ops"
  shows "dom (snd (interp_ops ops)) = set (inserted_ids ops) - set (deleted_ids ops)"
  using assms proof(induction ops rule: List.rev_induct)
  case Nil
  have 1: "interp_ops [] = ([], Map.empty)"
    by (simp add: interp_ops_def)
  moreover have 2: "inserted_ids [] = []" and "deleted_ids [] = []"
    by (auto simp add: inserted_ids_def deleted_ids_def map_filter_simps(2))
  ultimately show "dom (snd (interp_ops [])) = set (inserted_ids []) - set (deleted_ids [])"
    by (simp add: 1 2)
next
  case (snoc x xs)
  hence IH: "dom (snd (interp_ops xs)) = set (inserted_ids xs) - set (deleted_ids xs)"
    using list_ops_def spec_ops_rem_last by blast
  obtain oid oper where x_pair: "x = (oid, oper)"
    by fastforce
  obtain list vals where interp_xs: "interp_ops xs = (list, vals)"
    by fastforce
  then show "dom (snd (interp_ops (xs @ [x]))) =
             set (inserted_ids (xs @ [x])) - set (deleted_ids (xs @ [x]))"
  proof(cases oper)
    case (Insert ref val)
    hence "interp_ops (xs @ [x]) = (insert_spec list (oid, ref), vals(oid \<mapsto> val))"
      by (simp add: interp_ops_unfold_last interp_xs x_pair)
    hence "dom (snd (interp_ops (xs @ [x]))) = (dom vals) \<union> {oid}"
      by simp
    moreover have "set (inserted_ids xs) - set (deleted_ids xs) = dom vals"
      using IH interp_xs by auto
    moreover have "inserted_ids (xs @ [x]) = inserted_ids xs @ [oid]"
      by (simp add: Insert inserted_ids_last_ins x_pair)
    moreover have "deleted_ids (xs @ [x]) = deleted_ids xs"
      by (simp add: Insert deleted_ids_last_ins x_pair)
    hence "set (inserted_ids (xs @ [x])) - set (deleted_ids (xs @ [x])) =
           {oid} \<union> set (inserted_ids xs) - set (deleted_ids xs)"
      using calculation(3) by auto
    moreover have "... = {oid} \<union> (set (inserted_ids xs) - set (deleted_ids xs))"
      using deleted_ids_refs_older snoc.prems x_pair by blast
    ultimately show ?thesis by auto
  next
    case (Delete ref)
    hence "interp_ops (xs @ [x]) = (list, vals(ref := None))"
      by (simp add: interp_ops_unfold_last interp_xs x_pair)
    hence "dom (snd (interp_ops (xs @ [x]))) = (dom vals) - {ref}"
      by simp
    moreover have "set (inserted_ids xs) - set (deleted_ids xs) = dom vals"
      using IH interp_xs by auto
    moreover have "inserted_ids (xs @ [x]) = inserted_ids xs"
      by (simp add: Delete inserted_ids_last_del x_pair)
    moreover have "deleted_ids (xs @ [x]) = deleted_ids xs @ [ref]"
      by (simp add: Delete deleted_ids_last_del x_pair)
    hence "set (inserted_ids (xs @ [x])) - set (deleted_ids (xs @ [x])) =
           set (inserted_ids xs) - (set (deleted_ids xs) \<union> {ref})"
      using calculation(3) by auto
    moreover have "... = set (inserted_ids xs) - set (deleted_ids xs) - {ref}"
      by blast
    ultimately show ?thesis by auto
  qed
qed

lemma insert_spec_nth_oid:
  assumes "distinct xs"
    and "n < length xs"
  shows "insert_spec xs (oid, Some (xs ! n)) ! Suc n = oid"
  using assms proof(induction xs arbitrary: n)
  case Nil
  then show "insert_spec [] (oid, Some ([] ! n)) ! Suc n = oid"
    by simp
next
  case (Cons a xs)
  have "distinct (a # xs)"
    using Cons.prems(1) by auto
  then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
  proof(cases "a = (a # xs) ! n")
    case True
    then have "n = 0"
      using \<open>distinct (a # xs)\<close> Cons.prems(2) gr_implies_not_zero by force
    then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
      by auto
  next
    case False
    then have "n > 0"
      using \<open>distinct (a # xs)\<close> Cons.prems(2) gr_implies_not_zero by force
    then obtain m where "n = Suc m"
      using Suc_pred' by blast
    then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
      using Cons.IH Cons.prems by auto
  qed
qed

lemma insert_spec_inc_length:
  assumes "distinct xs"
    and "n < length xs"
  shows "length (insert_spec xs (oid, Some (xs ! n))) = Suc (length xs)"
  using assms proof(induction xs arbitrary: n, simp)
  case (Cons a xs)
  have "distinct (a # xs)"
    using Cons.prems(1) by auto
  then show "length (insert_spec (a # xs) (oid, Some ((a # xs) ! n))) = Suc (length (a # xs))"
  proof(cases n)
    case 0
    hence "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) = a # oid # xs"
      by simp
    then show ?thesis
      by simp
  next
    case (Suc nat)
    hence "nat < length xs"
      using Cons.prems(2) by auto
    hence "length (insert_spec xs (oid, Some (xs ! nat))) = Suc (length xs)"
      using Cons.IH Cons.prems(1) by auto
    then show ?thesis
      by (simp add: Suc)
  qed
qed

lemma list_split_two_elems:
  assumes "distinct xs"
    and "x \<in> set xs" and "y \<in> set xs"
    and "x \<noteq> y"
  shows "\<exists>pre mid suf. xs = pre @ x # mid @ y # suf \<or> xs = pre @ y # mid @ x # suf"
proof -
  obtain as bs where as_bs: "xs = as @ [x] @ bs"
    using assms(2) split_list_first by fastforce
  show ?thesis
  proof(cases "y \<in> set as")
    case True
    then obtain cs ds where "as = cs @ [y] @ ds"
      using assms(3) split_list_first by fastforce
    then show ?thesis
      by (auto simp add: as_bs)
  next
    case False
    then have "y \<in> set bs"
      using as_bs assms(3) assms(4) by auto
    then obtain cs ds where "bs = cs @ [y] @ ds"
      using assms(3) split_list_first by fastforce
    then show ?thesis
      by (auto simp add: as_bs)
  qed
qed


subsection\<open>Satisfying all conditions of $\mathcal{A}_\textsf{strong}$\<close>

text\<open>Part 1(a) of Attiya et al.'s specification states that whenever the
list is observed, the elements of the list are exactly those that have
been inserted but not deleted. $\mathcal{A}_\textsf{strong}$ uses the
visibility relation $\le_\textsf{vis}$ to capture the operations known
to a node at some arbitrary point in the execution; in the OpSet model,
we can simply prove the theorem for an arbitrary OpSet, since the
contents of the OpSet at a particular time on a particular node correspond
exactly to the set of operations known to that node at that time.\<close>

theorem inserted_but_not_deleted:
  assumes "list_ops ops"
    and "interp_ops ops = (list, vals)"
  shows "a \<in> dom (vals) \<longleftrightarrow> (\<exists>ref val. (a, Insert ref val) \<in> set ops) \<and>
                            (\<nexists>i. (i, Delete a) \<in> set ops)"
  using assms deleted_ids_exist inserted_ids_exist interp_ops_vals_domain
  by (metis Diff_iff snd_conv)


text\<open>Part 1(b) states that whenever the list is observed, the order of
list elements is consistent with the global list order. We can define the
global list order simply as the list order that arises from interpreting
the OpSet containing all operations in the entire execution. Then, at any
point in the execution, the OpSet is some subset of the set of all
operations.

We can then rephrase condition 1(b) as follows: whenever list element \isa{x}
appears before list element \isa{y} in the interpretation of \isa{some-ops},
then for any OpSet \isa{all-ops} that is a superset of \isa{some-ops},
\isa{x} must also appear before \isa{y} in the interpretation of \isa{all-ops}.
In other words, adding more operations to the OpSet does not change the
relative order of any existing list elements.\<close>

theorem list_order_consistent:
  assumes "list_ops some_ops" and "list_ops all_ops"
    and "set some_ops \<subseteq> set all_ops"
    and "list_order some_ops x y"
  shows "list_order all_ops x y"
  using assms list_order_monotonic list_ops_insertions insertions_subset list_order_equiv by metis


text\<open>Part 1(c) states that inserted elements appear at the specified position:
that is, immediately after an insertion of \isa{oid} at index \isa{k}, the list
index \isa{k} does indeed contain \isa{oid} (provided that \isa{k} is less than the
length of the list). We prove this property below.\<close>

theorem correct_position_insert:
  assumes "list_ops (ops @ [(oid, ins)])"
    and "ins = make_insert (fst (interp_ops ops)) val k"
    and "list = fst (interp_ops (ops @ [(oid, ins)]))"
  shows "list ! (min k (length list - 1)) = oid"
proof(cases "k = 0 \<or> fst (interp_ops ops) = []")
  case True
  moreover from this
  have "make_insert (fst (interp_ops ops)) val k = Insert None val"
    and min_k: "min k (length (fst (interp_ops ops))) = 0"
    by (cases k, auto)
  hence "fst (interp_ops (ops @ [(oid, ins)])) = oid # fst (interp_ops ops)"
    using assms(2) interp_ops_unfold_last
    by (metis fst_conv insert_spec.simps(1) interp_op.simps(1) prod.collapse)
  ultimately show ?thesis
    by (simp add: min_k assms(3))
next
  case False
  moreover from this have "k > 0" and "fst (interp_ops ops) \<noteq> []"
    using neq0_conv by blast+
  from this obtain nat where "k = Suc nat"
    using gr0_implies_Suc by blast
  hence "make_insert (fst (interp_ops ops)) val k =
      Insert (Some ((fst (interp_ops ops)) ! (min nat (length (fst (interp_ops ops)) - 1)))) val"
    using False by (cases "fst (interp_ops ops)", auto)
  hence "fst (interp_ops (ops @ [(oid, ins)])) =
         insert_spec (fst (interp_ops ops)) (oid, Some ((fst (interp_ops ops)) ! (min nat (length (fst (interp_ops ops)) - 1))))"
    by (metis assms(2) fst_conv interp_op.simps(1) interp_ops_unfold_last prod.collapse)
  moreover have "min nat (length (fst (interp_ops ops)) - 1) < length (fst (interp_ops ops))"
    by (simp add: \<open>fst (interp_ops ops) \<noteq> []\<close> min.strict_coboundedI2)
  moreover have "distinct (fst (interp_ops ops))"
    using interp_ops_distinct list_ops_def spec_ops_rem_last assms(1) by blast
  moreover have "length list = Suc (length (fst (interp_ops ops)))"
    using assms(3) calculation by (simp add: insert_spec_inc_length)
  ultimately show ?thesis
    using assms insert_spec_nth_oid
    by (metis Suc_diff_1 \<open>k = Suc nat\<close> diff_Suc_1 length_greater_0_conv min_Suc_Suc)
qed


text\<open>Part 2 states that the list order relation must be transitive, irreflexive,
and total. These three properties are straightforward to prove, using our
definition of the \isa{list-order} predicate.\<close>

theorem list_order_trans:
  assumes "list_ops ops"
    and "list_order ops x y"
    and "list_order ops y z"
  shows "list_order ops x z"
  using assms list_order_trans list_ops_insertions list_order_equiv by blast

theorem list_order_irrefl:
  assumes "list_ops ops"
  shows "\<not> list_order ops x x"
proof -
  have "list_order ops x x \<Longrightarrow> False"
  proof -
    assume "list_order ops x x"
    then obtain xs ys zs where split: "fst (interp_ops ops) = xs @ [x] @ ys @ [x] @ zs"
      by (meson List_Spec.list_order_def)
    moreover have "distinct (fst (interp_ops ops))"
      by (simp add: assms interp_ops_distinct)
    ultimately show False
      by (simp add: split)
  qed
  thus "\<not> list_order ops x x"
    by blast
qed

theorem list_order_total:
  assumes "list_ops ops"
    and "x \<in> set (fst (interp_ops ops))"
    and "y \<in> set (fst (interp_ops ops))"
    and "x \<noteq> y"
  shows "list_order ops x y \<or> list_order ops y x"
proof -
  have "distinct (fst (interp_ops ops))"
    using assms(1) by (simp add: interp_ops_distinct)
  then obtain pre mid suf
    where "fst (interp_ops ops) = pre @ x # mid @ y # suf \<or>
           fst (interp_ops ops) = pre @ y # mid @ x # suf"
    using list_split_two_elems assms by metis
  then show "list_order ops x y \<or> list_order ops y x"
    by (simp add: list_order_def, blast)
qed

end
