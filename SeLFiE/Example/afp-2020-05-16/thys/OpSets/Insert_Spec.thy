(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
   Alastair Beresford, University of Cambridge
*)

section\<open>Specifying list insertion\<close>

theory Insert_Spec
  imports OpSet
begin

text\<open>In this section we consider only list insertion. We model an insertion
operation as a pair (\isa{ID, ref}), where \isa{ref} is either \isa{None}
(signifying an insertion at the head of the list) or \isa{Some r}
(an insertion immediately after a reference element with ID \isa{r}).
If the reference element does not exist, the operation does nothing.

We provide two different definitions of the interpretation function for list
insertion: \isa{insert-spec} and \isa{insert-alt}. The \isa{insert-alt} definition
matches the paper, while \isa{insert-spec} uses the Isabelle/HOL list datatype,
making it more suitable for formal reasoning. In a later subsection we prove
that the two definitions are in fact equivalent.\<close>

fun insert_spec :: "'oid list \<Rightarrow> ('oid \<times> 'oid option) \<Rightarrow> 'oid list" where
  "insert_spec xs     (oid, None)     = oid#xs" |
  "insert_spec []     (oid, _)        = []" |
  "insert_spec (x#xs) (oid, Some ref) =
     (if x = ref then x # oid # xs
                 else x # (insert_spec xs (oid, Some ref)))"

fun insert_alt :: "('oid \<times> 'oid option) set \<Rightarrow> ('oid \<times> 'oid) \<Rightarrow> ('oid \<times> 'oid option) set" where
  "insert_alt list_rel (oid, ref) = (
      if \<exists>n. (ref, n) \<in> list_rel
      then {(p, n) \<in> list_rel. p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> list_rel}
      else list_rel)"

text\<open>\isa{interp-ins} is the sequential interpretation of a set of insertion
operations. It starts with an empty list as initial state, and then applies
the operations from left to right.\<close>

definition interp_ins :: "('oid \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "interp_ins ops \<equiv> foldl insert_spec [] ops"


subsection \<open>The \isa{insert-ops} predicate\<close>

text\<open>We now specialise the definitions from the abstract OpSet section for list
insertion. \isa{insert-opset} is an opset consisting only of insertion operations,
and \isa{insert-ops} is the specialisation of the \isa{spec-ops} predicate for
insertion operations. We prove several useful lemmas about \isa{insert-ops}.\<close>

locale insert_opset = opset opset set_option
  for opset :: "('oid::{linorder} \<times> 'oid option) set"

definition insert_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "insert_ops list \<equiv> spec_ops list set_option"

lemma insert_ops_NilI [intro!]:
  shows "insert_ops []"
  by (auto simp add: insert_ops_def spec_ops_def)

lemma insert_ops_rem_last [dest]:
  assumes "insert_ops (xs @ [x])"
  shows "insert_ops xs"
  using assms insert_ops_def spec_ops_rem_last by blast

lemma insert_ops_rem_cons:
  assumes "insert_ops (x # xs)"
  shows "insert_ops xs"
  using assms insert_ops_def spec_ops_rem_cons by blast

lemma insert_ops_appendD:
  assumes "insert_ops (xs @ ys)"
  shows "insert_ops xs"
  using assms by (induction ys rule: List.rev_induct,
      auto, metis insert_ops_rem_last append_assoc)

lemma insert_ops_rem_prefix:
  assumes "insert_ops (pre @ suf)"
  shows "insert_ops suf"
  using assms proof(induction pre)
  case Nil
  then show "insert_ops ([] @ suf) \<Longrightarrow> insert_ops suf"
    by auto
next
  case (Cons a pre)
  have "sorted (map fst suf)"
    using assms by (simp add: insert_ops_def sorted_append spec_ops_def)
  moreover have "distinct (map fst suf)"
    using assms by (simp add: insert_ops_def spec_ops_def)
  ultimately show "insert_ops ((a # pre) @ suf) \<Longrightarrow> insert_ops suf"
    by (simp add: insert_ops_def spec_ops_def)
qed

lemma insert_ops_remove1:
  assumes "insert_ops xs"
  shows "insert_ops (remove1 x xs)"
  using assms insert_ops_def spec_ops_remove1 by blast

lemma last_op_greatest:
  assumes "insert_ops (op_list @ [(oid, oper)])"
    and "x \<in> set (map fst op_list)"
  shows "x < oid"
  using assms spec_ops_id_inc insert_ops_def by metis

lemma insert_ops_ref_older:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
  shows "ref < oid"
  using assms by (auto simp add: insert_ops_def spec_ops_def)

lemma insert_ops_memb_ref_older:
  assumes "insert_ops op_list"
    and "(oid, Some ref) \<in> set op_list"
  shows "ref < oid"
  using assms insert_ops_ref_older split_list_first by fastforce


subsection \<open>Properties of the \isa{insert-spec} function\<close>

lemma insert_spec_none [simp]:
  shows "set (insert_spec xs (oid, None)) = set xs \<union> {oid}"
  by (induction xs, auto simp add: insert_commute sup_commute)

lemma insert_spec_set [simp]:
  assumes "ref \<in> set xs"
  shows "set (insert_spec xs (oid, Some ref)) = set xs \<union> {oid}"
  using assms proof(induction xs)
  assume "ref \<in> set []"
  thus "set (insert_spec [] (oid, Some ref)) = set [] \<union> {oid}"
    by auto
next
  fix a xs
  assume "ref \<in> set xs \<Longrightarrow> set (insert_spec xs (oid, Some ref)) = set xs \<union> {oid}"
    and "ref \<in> set (a#xs)"
  thus "set (insert_spec (a#xs) (oid, Some ref)) = set (a#xs) \<union> {oid}"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed

lemma insert_spec_nonex [simp]:
  assumes "ref \<notin> set xs"
  shows "insert_spec xs (oid, Some ref) = xs"
  using assms proof(induction xs)
  show "insert_spec [] (oid, Some ref) = []"
    by simp
next
  fix a xs
  assume "ref \<notin> set xs \<Longrightarrow> insert_spec xs (oid, Some ref) = xs"
    and "ref \<notin> set (a#xs)"
  thus "insert_spec (a#xs) (oid, Some ref) = a#xs"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed

lemma list_greater_non_memb:
  fixes oid :: "'oid::{linorder}"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and "oid \<in> set xs"
  shows "False"
  using assms by blast  

lemma inserted_item_ident:
  assumes "a \<in> set (insert_spec xs (e, i))"
    and "a \<notin> set xs"
  shows "a = e"
  using assms proof(induction xs)
  case Nil
  then show "a = e" by (cases i, auto)
next
  case (Cons x xs)
  then show "a = e"
  proof(cases i)
    case None
    then show "a = e" using assms by auto
  next
    case (Some ref)
    then show "a = e" using Cons by (case_tac "x = ref", auto)
  qed
qed

lemma insert_spec_distinct [intro]:
  fixes oid :: "'oid::{linorder}"
  assumes "distinct xs"
    and "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and "ref = Some r \<longrightarrow> r < oid"
  shows "distinct (insert_spec xs (oid, ref))"
  using assms(1) assms(2) proof(induction xs)
  show "distinct (insert_spec [] (oid, ref))"
    by(cases ref, auto)
next
  fix a xs
  assume IH: "distinct xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x < oid) \<Longrightarrow> distinct (insert_spec xs (oid, ref))"
    and D: "distinct (a#xs)"
    and L: "\<And>x. x \<in> set (a#xs) \<Longrightarrow> x < oid"
  show "distinct (insert_spec (a#xs) (oid, ref))"
  proof(cases "ref")
    assume "ref = None"
    thus "distinct (insert_spec (a#xs) (oid, ref))"
      using D L by auto
  next
    fix id
    assume S: "ref = Some id"
    {
      assume EQ: "a = id"
      hence "id \<noteq> oid"
        using D L by auto
      moreover have "id \<notin> set xs"
        using D EQ by auto
      moreover have "oid \<notin> set xs"
        using L by auto
      ultimately have "id \<noteq> oid \<and> id \<notin> set xs \<and> oid \<notin> set xs \<and> distinct xs"
        using D by auto
    }
    note T = this
    {
      assume NEQ: "a \<noteq> id"
      have 0: "a \<notin> set (insert_spec xs (oid, Some id))"
        using D L by(metis distinct.simps(2) insert_spec.simps(1) insert_spec_none insert_spec_nonex
            insert_spec_set insert_iff list.set(2) not_less_iff_gr_or_eq)
      have 1: "distinct xs"
        using D by auto
      have "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
        using L by auto
      hence "distinct (insert_spec xs (oid, Some id))"
        using S IH[OF 1] by blast
      hence "a \<notin> set (insert_spec xs (oid, Some id)) \<and> distinct (insert_spec xs (oid, Some id))"
        using 0 by auto
    }
    from this S T show "distinct (insert_spec (a # xs) (oid, ref))"
      by clarsimp
  qed
qed

lemma insert_after_ref:
  assumes "distinct (xs @ ref # ys)"
  shows "insert_spec (xs @ ref # ys) (oid, Some ref) = xs @ ref # oid # ys"
  using assms by (induction xs, auto)

lemma insert_somewhere:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set list)"
  shows "\<exists>xs ys. list = xs @ ys \<and> insert_spec list (oid, ref) = xs @ oid # ys"
  using assms proof(induction list)
  assume "ref = None \<or> ref = Some r \<and> r \<in> set []"
  thus "\<exists>xs ys. [] = xs @ ys \<and> insert_spec [] (oid, ref) = xs @ oid # ys"
  proof
    assume "ref = None"
    thus "\<exists>xs ys. [] = xs @ ys \<and> insert_spec [] (oid, ref) = xs @ oid # ys"
      by auto
  next
    assume "ref = Some r \<and> r \<in> set []"
    thus "\<exists>xs ys. [] = xs @ ys \<and> insert_spec [] (oid, ref) = xs @ oid # ys"
      by auto
  qed
next
  fix a list
  assume 1: "ref = None \<or> ref = Some r \<and> r \<in> set (a#list)"
    and IH: "ref = None \<or> ref = Some r \<and> r \<in> set list \<Longrightarrow>
         \<exists>xs ys. list = xs @ ys \<and> insert_spec list (oid, ref) = xs @ oid # ys"
  show "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
  proof(rule disjE[OF 1])
    assume "ref = None"
    thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
      by force
  next
    assume "ref = Some r \<and> r \<in> set (a # list)"
    hence 2: "r = a \<or> r \<in> set list" and 3: "ref = Some r"
      by auto
    show "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
    proof(rule disjE[OF 2])
      assume "r = a"
      thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
        using 3 by(metis append_Cons append_Nil insert_spec.simps(3))
    next
      assume "r \<in> set list"
      from this obtain xs ys
        where "list = xs @ ys \<and> insert_spec list (oid, ref) = xs @ oid # ys"
        using IH 3 by auto
      thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
        using 3 by clarsimp (metis append_Cons append_Nil)
    qed
  qed
qed

lemma insert_first_part:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set xs)"
  shows "insert_spec (xs @ ys) (oid, ref) = (insert_spec xs (oid, ref)) @ ys"
  using assms proof(induction ys rule: rev_induct)
  assume "ref = None \<or> ref = Some r \<and> r \<in> set xs"
  thus "insert_spec (xs @ []) (oid, ref) = insert_spec xs (oid, ref) @ []"
    by auto
next
  fix x xsa
  assume IH: "ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa) (oid, ref) = insert_spec xs (oid, ref) @ xsa"
    and "ref = None \<or> ref = Some r \<and> r \<in> set xs"
  thus "insert_spec (xs @ xsa @ [x]) (oid, ref) = insert_spec xs (oid, ref) @ xsa @ [x]"
  proof(induction xs)
    assume "ref = None \<or> ref = Some r \<and> r \<in> set []"
    thus "insert_spec ([] @ xsa @ [x]) (oid, ref) = insert_spec [] (oid, ref) @ xsa @ [x]"
      by auto
  next
    fix a xs
    assume 1: "ref = None \<or> ref = Some r \<and> r \<in> set (a # xs)"
      and 2: "((ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa) (oid, ref) = insert_spec xs (oid, ref) @ xsa) \<Longrightarrow>
             ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa @ [x]) (oid, ref) = insert_spec xs (oid, ref) @ xsa @ [x])"
      and 3: "(ref = None \<or> ref = Some r \<and> r \<in> set (a # xs) \<Longrightarrow> insert_spec ((a # xs) @ xsa) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa)"
    show "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
    proof(rule disjE[OF 1])
      assume "ref = None"
      thus "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
        by auto
    next
      assume "ref = Some r \<and> r \<in> set (a # xs)"
      thus "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
        using 2 3 by auto
    qed
  qed
qed

lemma insert_second_part:
  assumes "ref = Some r"
    and "r \<notin> set xs"
    and "r \<in> set ys"
  shows "insert_spec (xs @ ys) (oid, ref) = xs @ (insert_spec ys (oid, ref))"
  using assms proof(induction xs)
  assume "ref = Some r"
  thus "insert_spec ([] @ ys) (oid, ref) = [] @ insert_spec ys (oid, ref)"
    by auto
next
  fix a xs
  assume "ref = Some r" and "r \<notin> set (a # xs)" and "r \<in> set ys"
    and "ref = Some r \<Longrightarrow> r \<notin> set xs \<Longrightarrow> r \<in> set ys \<Longrightarrow> insert_spec (xs @ ys) (oid, ref) = xs @ insert_spec ys (oid, ref)"
  thus "insert_spec ((a # xs) @ ys) (oid, ref) = (a # xs) @ insert_spec ys (oid, ref)"
    by auto
qed


subsection \<open>Properties of the \isa{interp-ins} function\<close>

lemma interp_ins_empty [simp]:
  shows "interp_ins [] = []"
  by (simp add: interp_ins_def)

lemma interp_ins_tail_unfold:
  shows "interp_ins (xs @ [x]) = insert_spec (interp_ins xs) x"
  by (clarsimp simp add: interp_ins_def)

lemma interp_ins_subset [simp]:
  shows "set (interp_ins op_list) \<subseteq> set (map fst op_list)"
proof(induction op_list rule: List.rev_induct)
  case Nil
  then show "set (interp_ins []) \<subseteq> set (map fst [])"
    by (simp add: interp_ins_def)
next
  case (snoc x xs)
  hence IH: "set (interp_ins xs) \<subseteq> set (map fst xs)"
    using interp_ins_def by blast
  obtain oid ref where x_pair: "x = (oid, ref)"
    by fastforce
  hence spec: "interp_ins (xs @ [x]) = insert_spec (interp_ins xs) (oid, ref)"
    by (simp add: interp_ins_def)
  then show "set (interp_ins (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
  proof(cases ref)
    case None
    then show "set (interp_ins (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
      using IH spec x_pair by auto
  next
    case (Some a)
    then show "set (interp_ins (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
      using IH spec x_pair by (cases "a \<in> set (interp_ins xs)", auto)
  qed
qed

lemma interp_ins_distinct:
  assumes "insert_ops op_list"
  shows "distinct (interp_ins op_list)"
  using assms proof(induction op_list rule: rev_induct)
  case Nil
  then show "distinct (interp_ins [])"
    by (simp add: interp_ins_def)
next
  case (snoc x xs)
  hence IH: "distinct (interp_ins xs)" by blast
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  hence "\<forall>x \<in> set (map fst xs). x < oid"
    using last_op_greatest snoc.prems by blast
  hence "\<forall>x \<in> set (interp_ins xs). x < oid"
    using interp_ins_subset by fastforce
  hence "distinct (insert_spec (interp_ins xs) (oid, ref))"
    using IH insert_spec_distinct insert_spec_nonex by metis
  then show "distinct (interp_ins (xs @ [x]))"
    by (simp add: x_pair interp_ins_tail_unfold)
qed


subsection \<open>Equivalence of the two definitions of insertion\<close>

text\<open>At the beginning of this section we gave two different definitions of
interpretation functions for list insertion: \isa{insert-spec} and
\isa{insert-alt}. In this section we prove that the two are equivalent.

We first define how to derive the successor relation from an Isabelle list.
This relation contains (\isa{id}, \isa{None}) if \isa{id} is the last element
of the list, and (\isa{id1}, \isa{id2}) if \isa{id1} is immediately
followed by \isa{id2} in the list.\<close>

fun succ_rel :: "'oid list \<Rightarrow> ('oid \<times> 'oid option) set" where
  "succ_rel [] = {}" |
  "succ_rel [head] = {(head, None)}" |
  "succ_rel (head#x#xs) = {(head, Some x)} \<union> succ_rel (x#xs)"

text\<open>\isa{interp-alt} is the equivalent of \isa{interp-ins}, but using
\isa{insert-alt} instead of \isa{insert-spec}. To match the paper, it uses a
distinct head element to refer to the beginning of the list.\<close>

definition interp_alt :: "'oid \<Rightarrow> ('oid \<times> 'oid option) list \<Rightarrow> ('oid \<times> 'oid option) set" where
  "interp_alt head ops \<equiv> foldl insert_alt {(head, None)}
     (map (\<lambda>x. case x of
            (oid, None)     \<Rightarrow> (oid, head) |
            (oid, Some ref) \<Rightarrow> (oid, ref)) 
      ops)"

lemma succ_rel_set_fst:
  shows "fst ` (succ_rel xs) = set xs"
  by (induction xs rule: succ_rel.induct, auto)

lemma succ_rel_functional:
  assumes "(a, b1) \<in> succ_rel xs"
    and "(a, b2) \<in> succ_rel xs"
    and "distinct xs"
  shows "b1 = b2"
  using assms proof(induction xs rule: succ_rel.induct)
  case 1
  then show ?case by simp
next
  case (2 head)
  then show ?case by simp
next
  case (3 head x xs)
  then show ?case
  proof(cases "a = head")
    case True
    hence "a \<notin> set (x#xs)"
      using 3 by auto
    hence "a \<notin> fst ` (succ_rel (x#xs))"
      using succ_rel_set_fst by metis
    then show "b1 = b2"
      using 3 image_iff by fastforce
  next
    case False
    hence "{(a, b1), (a, b2)} \<subseteq> succ_rel (x#xs)"
      using 3 by auto
    moreover have "distinct (x#xs)"
      using 3 by auto
    ultimately show "b1 = b2"
      using "3.IH" by auto
  qed
qed

lemma succ_rel_rem_head:
  assumes "distinct (x # xs)"
  shows "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel xs"
proof -
  have head_notin: "x \<notin> fst ` succ_rel xs"
    using assms by (simp add: succ_rel_set_fst)
  moreover obtain y where "(x, y) \<in> succ_rel (x # xs)"
    by (cases xs, auto)
  moreover have "succ_rel (x # xs) = {(x, y)} \<union> succ_rel xs"
    using calculation head_notin image_iff by (cases xs, fastforce+)
  moreover from this have "\<And>n. (x, n) \<in> succ_rel (x # xs) \<Longrightarrow> n = y"
    by (metis Pair_inject fst_conv head_notin image_eqI insertE insert_is_Un)
  hence "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel (x # xs) - {(x, y)}"
    by blast
  moreover have "succ_rel (x # xs) - {(x, y)} = succ_rel xs"
    using image_iff calculation by fastforce
  ultimately show "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel xs"
    by simp
qed

lemma succ_rel_swap_head:
  assumes "distinct (ref # list)"
    and "(ref, n) \<in> succ_rel (ref # list)"
  shows "succ_rel (oid # list) = {(oid, n)} \<union> succ_rel list"
proof(cases list)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons a list)
  moreover from this have "n = Some a"
    by (metis Un_iff assms singletonI succ_rel.simps(3) succ_rel_functional)
  ultimately show ?thesis by simp
qed

lemma succ_rel_insert_alt:
  assumes "a \<noteq> ref"
    and "distinct (oid # a # b # list)"
  shows "insert_alt (succ_rel (a # b # list)) (oid, ref) =
         {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
proof(cases "\<exists>n. (ref, n) \<in> succ_rel (a # b # list)")
  case True
  hence "insert_alt (succ_rel (a # b # list)) (oid, ref) =
           {(p, n) \<in> succ_rel (a # b # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (a # b # list)}"
    by simp
  moreover have "{(p, n) \<in> succ_rel (a # b # list). p \<noteq> ref} =
                 {(a, Some b)} \<union> {(p, n) \<in> succ_rel (b # list). p \<noteq> ref}"
    using assms(1) by auto
  moreover have "insert_alt (succ_rel (b # list)) (oid, ref) =
           {(p, n) \<in> succ_rel (b # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (b # list)}"
  proof -
    have "\<exists>n. (ref, n) \<in> succ_rel (b # list)"
      using assms(1) True by auto
    thus ?thesis by simp
  qed
  moreover have "{(i, n). i = oid \<and> (ref, n) \<in> succ_rel (a # b # list)} =
                 {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (b # list)}"
    using assms(1) by auto
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis by auto
qed

lemma succ_rel_insert_head:
  assumes "distinct (ref # list)"
  shows "succ_rel (insert_spec (ref # list) (oid, Some ref)) =
         insert_alt (succ_rel (ref # list)) (oid, ref)"
proof -
  obtain n where ref_in_rel: "(ref, n) \<in> succ_rel (ref # list)"
    by (cases list, auto)
  moreover from this have "{(p, n) \<in> succ_rel (ref # list). p \<noteq> ref} = succ_rel list"
    using assms succ_rel_rem_head by (metis (mono_tags, lifting))
  moreover have "{(i, n). i = oid \<and> (ref, n) \<in> succ_rel (ref # list)} = {(oid, n)}"
  proof -
    have "\<And>nx. (ref, nx) \<in> succ_rel (ref # list) \<Longrightarrow> nx = n"
      using assms by (simp add: succ_rel_functional ref_in_rel)
    hence "{(i, n) \<in> succ_rel (ref # list). i = ref} \<subseteq> {(ref, n)}"
      by blast
    moreover have "{(ref, n)} \<subseteq> {(i, n) \<in> succ_rel (ref # list). i = ref}"
      by (simp add: ref_in_rel)
    ultimately show ?thesis by blast
  qed
  moreover have "insert_alt (succ_rel (ref # list)) (oid, ref) =
                   {(p, n) \<in> succ_rel (ref # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
                   {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (ref # list)}"
  proof -
    have "\<exists>n. (ref, n) \<in> succ_rel (ref # list)"
      using ref_in_rel by blast
    thus ?thesis by simp
  qed
  ultimately have "insert_alt (succ_rel (ref # list)) (oid, ref) =
                   succ_rel list \<union> {(ref, Some oid)} \<union> {(oid, n)}"
    by simp
  moreover have "succ_rel (oid # list) = {(oid, n)} \<union> succ_rel list"
    using assms ref_in_rel succ_rel_swap_head by metis
  hence "succ_rel (ref # oid # list) = {(ref, Some oid), (oid, n)} \<union> succ_rel list"
    by auto
  ultimately show "succ_rel (insert_spec (ref # list) (oid, Some ref)) =
                   insert_alt (succ_rel (ref # list)) (oid, ref)"
    by auto
qed

lemma succ_rel_insert_later:
  assumes "succ_rel (insert_spec (b # list) (oid, Some ref)) =
           insert_alt (succ_rel (b # list)) (oid, ref)"
    and "a \<noteq> ref"
    and "distinct (a # b # list)"
  shows "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         insert_alt (succ_rel (a # b # list)) (oid, ref)"
proof -
  have "succ_rel (a # b # list) = {(a, Some b)} \<union> succ_rel (b # list)"
    by simp
  moreover have "insert_spec (a # b # list) (oid, Some ref) =
                 a # (insert_spec (b # list) (oid, Some ref))"
    using assms(2) by simp
  hence "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         {(a, Some b)} \<union> succ_rel (insert_spec (b # list) (oid, Some ref))"
    by auto
  hence "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
    using assms(1) by auto
  moreover have "insert_alt (succ_rel (a # b # list)) (oid, ref) =
                 {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
    using succ_rel_insert_alt assms(2) by auto
  ultimately show ?thesis by blast
qed

lemma succ_rel_insert_Some:
  assumes "distinct list"
  shows "succ_rel (insert_spec list (oid, Some ref)) = insert_alt (succ_rel list) (oid, ref)"
  using assms proof(induction list)
  case Nil
  then show "succ_rel (insert_spec [] (oid, Some ref)) = insert_alt (succ_rel []) (oid, ref)"
    by simp
next
  case (Cons a list)
  hence "distinct (a # list)"
    by simp
  then show "succ_rel (insert_spec (a # list) (oid, Some ref)) =
             insert_alt (succ_rel (a # list)) (oid, ref)"
  proof(cases "a = ref")
    case True
    then show ?thesis
      using succ_rel_insert_head \<open>distinct (a # list)\<close> by metis
  next
    case False
    hence "a \<noteq> ref" by simp
    moreover have "succ_rel (insert_spec list (oid, Some ref)) =
                   insert_alt (succ_rel list) (oid, ref)"
      using Cons.IH Cons.prems by auto
    ultimately show "succ_rel (insert_spec (a # list) (oid, Some ref)) =
                     insert_alt (succ_rel (a # list)) (oid, ref)"
      by (cases list, force, metis Cons.prems succ_rel_insert_later)
  qed
qed

text\<open>The main result of this section, that \isa{insert-spec} and \isa{insert-alt}
are equivalent.\<close>

theorem insert_alt_equivalent:
  assumes "insert_ops ops"
    and "head \<notin> fst ` set ops"
    and "\<And>r. Some r \<in> snd ` set ops \<Longrightarrow> r \<noteq> head"
  shows "succ_rel (head # interp_ins ops) = interp_alt head ops"
  using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show "succ_rel (head # interp_ins []) = interp_alt head []"
    by (simp add: interp_ins_def interp_alt_def)
next
  case (snoc x xs)
  have IH: "succ_rel (head # interp_ins xs) = interp_alt head xs"
    using snoc by auto
  have distinct_list: "distinct (head # interp_ins xs)"
  proof -
    have "distinct (interp_ins xs)"
      using interp_ins_distinct snoc.prems(1) by blast
    moreover have "set (interp_ins xs) \<subseteq> fst ` set xs"
      using interp_ins_subset snoc.prems(1) by fastforce
    ultimately show "distinct (head # interp_ins xs)"
      using snoc.prems(2) by auto
  qed
  obtain oid r where x_pair: "x = (oid, r)" by force
  then show "succ_rel (head # interp_ins (xs @ [x])) = interp_alt head (xs @ [x])"
  proof(cases r)
    case None
    have "interp_alt head (xs @ [x]) = insert_alt (interp_alt head xs) (oid, head)"
      by (simp add: interp_alt_def None x_pair)
    moreover have "... = insert_alt (succ_rel (head # interp_ins xs)) (oid, head)"
      by (simp add: IH)
    moreover have "... = succ_rel (insert_spec (head # interp_ins xs) (oid, Some head))"
      using distinct_list succ_rel_insert_Some by metis
    moreover have "... = succ_rel (head # (insert_spec (interp_ins xs) (oid, None)))"
      by auto
    moreover have "... = succ_rel (head # (interp_ins (xs @ [x])))"
      by (simp add: interp_ins_tail_unfold None x_pair)
    ultimately show ?thesis by simp
  next
    case (Some ref)
    have "ref \<noteq> head"
      by (simp add: Some snoc.prems(3) x_pair)
    have "interp_alt head (xs @ [x]) = insert_alt (interp_alt head xs) (oid, ref)"
      by (simp add: interp_alt_def Some x_pair)
    moreover have "... = insert_alt (succ_rel (head # interp_ins xs)) (oid, ref)"
      by (simp add: IH)
    moreover have "... = succ_rel (insert_spec (head # interp_ins xs) (oid, Some ref))"
      using distinct_list succ_rel_insert_Some by metis
    moreover have "... = succ_rel (head # (insert_spec (interp_ins xs) (oid, Some ref)))"
      using \<open>ref \<noteq> head\<close> by auto
    moreover have "... = succ_rel (head # (interp_ins (xs @ [x])))"
      by (simp add: interp_ins_tail_unfold Some x_pair)
    ultimately show ?thesis by simp
  qed
qed


subsection \<open>The \isa{list-order} predicate\<close>

text\<open>\isa{list-order ops x y} holds iff, after interpreting the list of
insertion operations \isa{ops}, the list element with ID \isa{x} appears
before the list element with ID \isa{y} in the resulting list. We prove several
lemmas about this predicate; in particular, that executing additional insertion
operations does not change the relative ordering of existing list elements.\<close>

definition list_order :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> 'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "list_order ops x y \<equiv> \<exists>xs ys zs. interp_ins ops = xs @ [x] @ ys @ [y] @ zs"

lemma list_orderI:
  assumes "interp_ins ops = xs @ [x] @ ys @ [y] @ zs"
  shows "list_order ops x y"
  using assms by (auto simp add: list_order_def)

lemma list_orderE:
  assumes "list_order ops x y"
  shows "\<exists>xs ys zs. interp_ins ops = xs @ [x] @ ys @ [y] @ zs"
  using assms by (auto simp add: list_order_def)

lemma list_order_memb1:
  assumes "list_order ops x y"
  shows "x \<in> set (interp_ins ops)"
  using assms by (auto simp add: list_order_def)

lemma list_order_memb2:
  assumes "list_order ops x y"
  shows "y \<in> set (interp_ins ops)"
  using assms by (auto simp add: list_order_def)

lemma list_order_trans:
  assumes "insert_ops op_list"
    and "list_order op_list x y"
    and "list_order op_list y z"
  shows "list_order op_list x z"
proof -
  obtain xxs xys xzs where 1: "interp_ins op_list = (xxs@[x]@xys)@(y#xzs)"
    using assms by (auto simp add: list_order_def interp_ins_def)
  obtain yxs yys yzs where 2: "interp_ins op_list = yxs@y#(yys@[z]@yzs)"
    using assms by (auto simp add: list_order_def interp_ins_def)
  have 3: "distinct (interp_ins op_list)"
    using assms interp_ins_distinct by blast
  hence "xzs = yys@[z]@yzs"
    using distinct_list_split[OF 3, OF 2, OF 1] by auto
  hence "interp_ins op_list = xxs@[x]@xys@[y]@yys@[z]@yzs"
    using 1 2 3 by clarsimp
  thus "list_order op_list x z"
    using assms by (metis append.assoc list_orderI)
qed

lemma insert_preserves_order:
  assumes "insert_ops ops" and "insert_ops rest"
    and "rest = before @ after"
    and "ops  = before @ (oid, ref) # after"
  shows "\<exists>xs ys zs. interp_ins rest = xs @ zs \<and> interp_ins ops = xs @ ys @ zs"
  using assms proof(induction after arbitrary: rest ops rule: List.rev_induct)
  case Nil
  then have 1: "interp_ins ops = insert_spec (interp_ins before) (oid, ref)"
    by (simp add: interp_ins_tail_unfold)
  then show "\<exists>xs ys zs. interp_ins rest = xs @ zs \<and> interp_ins ops = xs @ ys @ zs"
  proof(cases ref)
    case None
    hence "interp_ins rest = [] @ (interp_ins before) \<and>
           interp_ins ops = [] @ [oid] @ (interp_ins before)"
      using 1 Nil.prems(3) by simp
    then show ?thesis by blast
  next
    case (Some a)
    then show ?thesis
    proof(cases "a \<in> set (interp_ins before)")
      case True
      then obtain xs ys where "interp_ins before = xs @ ys \<and>
          insert_spec (interp_ins before) (oid, ref) = xs @ oid # ys"
        using insert_somewhere Some by metis
      hence "interp_ins rest = xs @ ys \<and> interp_ins ops = xs @ [oid] @ ys"
        using 1 Nil.prems(3) by auto
      then show ?thesis by blast
    next
      case False
      hence "interp_ins ops = (interp_ins rest) @ [] @ []"
        using insert_spec_nonex 1 Nil.prems(3) Some by simp
      then show ?thesis by blast
    qed
  qed
next
  case (snoc oper op_list)
  then have "insert_ops ((before @ (oid, ref) # op_list) @ [oper])"
    and "insert_ops ((before @ op_list) @ [oper])"
    by auto
  then have ops1: "insert_ops (before @ op_list)"
    and ops2: "insert_ops (before @ (oid, ref) # op_list)"
    using insert_ops_appendD by blast+
  then obtain xs ys zs where IH1: "interp_ins (before @ op_list) = xs @ zs"
    and IH2: "interp_ins (before @ (oid, ref) # op_list) = xs @ ys @ zs"
    using snoc.IH by blast
  obtain i2 r2 where "oper = (i2, r2)" by force
  then show "\<exists>xs ys zs. interp_ins rest = xs @ zs \<and> interp_ins ops = xs @ ys @ zs"
  proof(cases r2)
    case None
    hence "interp_ins (before @ op_list @ [oper]) = (i2 # xs) @ zs"
      by (metis IH1 \<open>oper = (i2, r2)\<close> append.assoc append_Cons insert_spec.simps(1)
          interp_ins_tail_unfold)
    moreover have "interp_ins (before @ (oid, ref) # op_list @ [oper]) = (i2 # xs) @ ys @ zs"
      by (metis IH2 None \<open>oper = (i2, r2)\<close> append.assoc append_Cons insert_spec.simps(1)
          interp_ins_tail_unfold)
    ultimately show ?thesis
      using snoc.prems(3) snoc.prems(4) by blast
  next
    case (Some r)
    then have 1: "interp_ins (before @ (oid, ref) # op_list @ [(i2, r2)]) =
                  insert_spec (xs @ ys @ zs) (i2, Some r)"
      by (metis IH2 append.assoc append_Cons interp_ins_tail_unfold)
    have 2: "interp_ins (before @ op_list @ [(i2, r2)]) = insert_spec (xs @ zs) (i2, Some r)"
      by (metis IH1 append.assoc interp_ins_tail_unfold Some)
    consider (r_xs) "r \<in> set xs" | (r_ys) "r \<in> set ys" | (r_zs) "r \<in> set zs" |
      (r_nonex) "r \<notin> set (xs @ ys @ zs)"
      by auto
    then show "\<exists>xs ys zs. interp_ins rest = xs @ zs \<and> interp_ins ops = xs @ ys @ zs"
    proof(cases)
      case r_xs
      from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                      (insert_spec xs (i2, Some r)) @ ys @ zs"
        by (meson insert_first_part)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = (insert_spec xs (i2, Some r)) @ zs"
        by (meson r_xs insert_first_part)
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_ys
      hence "r \<notin> set xs" and "r \<notin> set zs"
        using IH2 ops2 interp_ins_distinct by force+
      moreover from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                               xs @ (insert_spec ys (i2, Some r)) @ zs"
        using insert_first_part insert_second_part insert_spec_nonex
        by (metis Some UnE r_ys set_append)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ zs"
        by (simp add: Some calculation(1) calculation(2))
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_zs
      hence "r \<notin> set xs" and "r \<notin> set ys"
        using IH2 ops2 interp_ins_distinct by force+
      moreover from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                               xs @ ys @ (insert_spec zs (i2, Some r))"
        by (metis Some UnE insert_second_part insert_spec_nonex set_append)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ (insert_spec zs (i2, Some r))"
        by (simp add: r_zs calculation(1) insert_second_part)
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_nonex
      then have "insert_spec (xs @ ys @ zs) (i2, Some r) = xs @ ys @ zs"
        by simp
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ zs"
        using r_nonex by simp
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    qed
  qed
qed

lemma distinct_fst:
  assumes "distinct (map fst A)"
  shows "distinct A"
  using assms by (induction A) auto

lemma subset_distinct_le:
  assumes "set A \<subseteq> set B" and "distinct A" and "distinct B"
  shows "length A \<le> length B"
  using assms proof(induction B arbitrary: A)
  case Nil
  then show "length A \<le> length []" by simp
next
  case (Cons a B)
  then show "length A \<le> length (a # B)"
  proof(cases "a \<in> set A")
    case True
    have "set (remove1 a A) \<subseteq> set B"
      using Cons.prems by auto
    hence "length (remove1 a A) \<le> length B"
      using Cons.IH Cons.prems by auto
    then show "length A \<le> length (a # B)"
      by (simp add: True length_remove1)
  next
    case False
    hence "set A \<subseteq> set B"
      using Cons.prems by auto
    hence "length A \<le> length B"
      using Cons.IH Cons.prems by auto
    then show "length A \<le> length (a # B)"
      by simp
  qed
qed

lemma set_subset_length_eq:
  assumes "set A \<subseteq> set B" and "length B \<le> length A"
    and "distinct A" and "distinct B"
  shows "set A = set B"
proof -
  have "length A \<le> length B"
    using assms by (simp add: subset_distinct_le)
  moreover from this have "card (set A) = card (set B)"
    using assms by (simp add: distinct_card le_antisym)
  ultimately show "set A = set B"
    using assms(1) by (simp add: card_subset_eq)
qed

lemma length_diff_Suc_exists:
  assumes "length xs - length ys = Suc m"
    and "set ys \<subseteq> set xs"
    and "distinct ys" and "distinct xs"
  shows "\<exists>e. e \<in> set xs \<and> e \<notin> set ys"
  using assms proof(induction xs arbitrary: ys)
  case Nil
  then show "\<exists>e. e \<in> set [] \<and> e \<notin> set ys"
    by simp
next
  case (Cons a xs)
  then show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
  proof(cases "a \<in> set ys")
    case True
    have IH: "\<exists>e. e \<in> set xs \<and> e \<notin> set (remove1 a ys)"
    proof -
      have "length xs - length (remove1 a ys) = Suc m"
        by (metis Cons.prems(1) One_nat_def Suc_pred True diff_Suc_Suc length_Cons
            length_pos_if_in_set length_remove1)
      moreover have "set (remove1 a ys) \<subseteq> set xs"
        using Cons.prems by auto
      ultimately show ?thesis
        by (meson Cons.IH Cons.prems distinct.simps(2) distinct_remove1)
    qed
    moreover have "set ys - {a} \<subseteq> set xs"
      using Cons.prems(2) by auto
    ultimately show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
      by (metis Cons.prems(4) distinct.simps(2) in_set_remove1 set_subset_Cons subsetCE)
  next
    case False
    then show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
      by auto
  qed
qed

lemma app_length_lt_exists:
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "xsa @ (drop (length xsa) xs) = xs"
  using assms by (induction xsa arbitrary: xs zsa ys, simp,
      metis append_eq_append_conv_if append_take_drop_id)

lemma list_order_monotonic:
  assumes "insert_ops A" and "insert_ops B"
    and "set A \<subseteq> set B"
    and "list_order A x y"
  shows "list_order B x y"
  using assms proof(induction rule: measure_induct_rule[where f="\<lambda>x. (length x - length A)"])
  case (less xa)
  have "distinct (map fst A)" and "distinct (map fst xa)" and
    "sorted (map fst A)" and "sorted (map fst xa)"
    using less.prems by (auto simp add: insert_ops_def spec_ops_def)
  hence "distinct A" and "distinct xa"
    by (auto simp add: distinct_fst)
  then show "list_order xa x y"
  proof(cases "length xa - length A")
    case 0
    hence "set A = set xa"
      using set_subset_length_eq less.prems(3) \<open>distinct A\<close> \<open>distinct xa\<close> diff_is_0_eq by blast
    hence "A = xa"
      using \<open>distinct (map fst A)\<close> \<open>distinct (map fst xa)\<close>
        \<open>sorted (map fst A)\<close> \<open>sorted (map fst xa)\<close> map_sorted_distinct_set_unique
      by (metis distinct_map less.prems(3) subset_Un_eq)
    then show "list_order xa x y" 
      using less.prems(4) by blast
  next
    case (Suc nat)
    then obtain e where "e \<in> set xa" and "e \<notin> set A"
      using length_diff_Suc_exists \<open>distinct A\<close> \<open>distinct xa\<close> less.prems(3) by blast
    hence IH: "list_order (remove1 e xa) x y"
    proof -
      have "length (remove1 e xa) - length A < Suc nat"
        using diff_Suc_1 diff_commute length_remove1 less_Suc_eq Suc \<open>e \<in> set xa\<close> by metis
      moreover have "insert_ops (remove1 e xa)"
        by (simp add: insert_ops_remove1 less.prems(2))
      moreover have "set A \<subseteq> set (remove1 e xa)"
        by (metis (no_types, lifting) \<open>e \<notin> set A\<close> in_set_remove1 less.prems(3) rev_subsetD subsetI)
      ultimately show ?thesis
        by (simp add: Suc less.IH less.prems(1) less.prems(4))
    qed
    then obtain xs ys zs where "interp_ins (remove1 e xa) = xs @ x # ys @ y # zs"
      using list_order_def by fastforce
    moreover obtain oid ref where e_pair: "e = (oid, ref)"
      by fastforce
    moreover obtain ps ss where xa_split: "xa = ps @ [e] @ ss" and "e \<notin> set ps"
      using split_list_first \<open>e \<in> set xa\<close> by fastforce
    hence "remove1 e (ps @ e # ss) = ps @ ss"
      by (simp add: remove1_append)
    moreover from this have "insert_ops (ps @ ss)" and "insert_ops (ps @ e # ss)"
      using xa_split less.prems(2) by (metis append_Cons append_Nil insert_ops_remove1, auto)
    then obtain xsa ysa zsa where "interp_ins (ps @ ss) = xsa @ zsa"
      and interp_xa: "interp_ins (ps @ (oid, ref) # ss) = xsa @ ysa @ zsa"
      using insert_preserves_order e_pair by metis
    moreover have xsa_zsa: "xsa @ zsa = xs @ x # ys @ y # zs"
      using interp_ins_def remove1_append calculation xa_split by auto
    then show "list_order xa x y"
    proof(cases "length xsa \<le> length xs")
      case True
      then obtain ts where "xsa@ts = xs"
        using app_length_lt_exists xsa_zsa by blast
      hence "interp_ins xa = (xsa @ ysa @ ts) @ [x] @ ys @ [y] @ zs"
        using calculation xa_split by auto
      then show "list_order xa x y"
        using list_order_def by blast
    next
      case False
      then show "list_order xa x y"
      proof(cases "length xsa \<le> length (xs @ x # ys)")
        case True
        have xsa_zsa1: "xsa @ zsa = (xs @ x # ys) @ (y # zs)"
          by (simp add: xsa_zsa)
        then obtain us where "xsa @ us = xs @ x # ys"
          using app_length_lt_exists True by blast
        moreover from this have "xs @ x # (drop (Suc (length xs)) xsa) = xsa"
          using append_eq_append_conv_if id_take_nth_drop linorder_not_less
            nth_append nth_append_length False by metis
        moreover have "us @ y # zs = zsa"
          by (metis True xsa_zsa1 append_eq_append_conv_if append_eq_conv_conj calculation(1))
        ultimately have "interp_ins xa = xs @ [x] @
              ((drop (Suc (length xs)) xsa) @ ysa @ us) @ [y] @ zs"
          by (simp add: e_pair interp_xa xa_split)
        then show "list_order xa x y"
          using list_order_def by blast
      next
        case False
        hence "length (xs @ x # ys) < length xsa"
          using not_less by blast
        hence "length (xs @ x # ys @ [y]) \<le> length xsa"
          by simp
        moreover have "(xs @ x # ys @ [y]) @ zs = xsa @ zsa"
          by (simp add: xsa_zsa)
        ultimately obtain vs where "(xs @ x # ys @ [y]) @ vs = xsa"
          using app_length_lt_exists by blast
        hence "xsa @ ysa @ zsa = xs @ [x] @ ys @ [y] @ vs @ ysa @ zsa"
          by simp
        hence "interp_ins xa = xs @ [x] @ ys @ [y] @ (vs @ ysa @ zsa)"
          using e_pair interp_xa xa_split by auto
        then show "list_order xa x y"
          using list_order_def by blast
      qed
    qed
  qed
qed


end
