(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
   Alastair Beresford, University of Cambridge
*)

section\<open>Abstract OpSet\<close>

text\<open>In this section, we define a general-purpose OpSet abstraction that is not
specific to any one particular datatype. We develop a library of useful lemmas
that we can build upon later when reasoning about a specific datatype.\<close>

theory OpSet
  imports Main
begin

subsection\<open>OpSet definition\<close>

text\<open>An OpSet is a set of (ID, operation) pairs with an associated total order
on IDs (represented here with the \isa{linorder} typeclass), and satisfying the
following properties:
\begin{enumerate}
\item The ID is unique (that is, if any two pairs in the set have the same ID,
then their operation is also the same).
\item If the operation references the IDs of any other operations, those
referenced IDs are less than that of the operation itself, according to the
total order on IDs. To avoid assuming anything about the structure of operations
here, we use a function \isa{deps} that returns the set of dependent IDs for a
given operation. This requirement is a weak expression of causality: an operation
can only depend on causally prior operations, and by making the total order on
IDs a linear extension of the causal order, we can easily ensure that any
referenced IDs are less than that of the operation itself.
\item The OpSet is finite (but we do not assume any particular maximum size).
\end{enumerate}\<close>

locale opset =
  fixes opset :: "('oid::{linorder} \<times> 'oper) set"
    and deps  :: "'oper \<Rightarrow> 'oid set"
  assumes unique_oid: "(oid, op1) \<in> opset \<Longrightarrow> (oid, op2) \<in> opset \<Longrightarrow> op1 = op2"
    and ref_older: "(oid, oper) \<in> opset \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
    and finite_opset: "finite opset"

text\<open>We prove that any subset of an OpSet is also a valid OpSet. This is the
case because, although an operation can depend on causally prior operations,
the OpSet does not require those prior operations to actually exist. This weak
assumption makes the OpSet model more general and simplifies reasoning about
OpSets.\<close>

lemma opset_subset:
  assumes "opset Y deps"
    and "X \<subseteq> Y"
  shows "opset X deps"
proof
  fix oid op1 op2
  assume "(oid, op1) \<in> X" and "(oid, op2) \<in> X"
  thus "op1 = op2"
    using assms by (meson opset.unique_oid subsetD)
next
  fix oid oper ref
  assume "(oid, oper) \<in> X" and "ref \<in> deps oper"
  thus "ref < oid"
    using assms by (meson opset.ref_older rev_subsetD)
next
  show "finite X"
    using assms opset.finite_opset finite_subset by blast
qed

lemma opset_insert:
  assumes "opset (insert x ops) deps"
  shows "opset ops deps"
  using assms opset_subset by blast

lemma opset_sublist:
  assumes "opset (set (xs @ ys @ zs)) deps"
  shows "opset (set (xs @ zs)) deps"
proof -
  have "set (xs @ zs) \<subseteq> set (xs @ ys @ zs)"
    by auto
  thus "opset (set (xs @ zs)) deps"
    using assms opset_subset by blast
qed


subsection\<open>Helper lemmas about lists\<close>

text\<open>Some general-purpose lemas about lists and sets that are helpful for
subsequent proofs.\<close>

lemma distinct_rem_mid:
  assumes "distinct (xs @ [x] @ ys)"
  shows "distinct (xs @ ys)"
  using assms by (induction ys rule: rev_induct, simp_all)

lemma distinct_fst_append:
  assumes "x \<in> set (map fst xs)"
    and "distinct (map fst (xs @ ys))"
  shows "x \<notin> set (map fst ys)"
  using assms by (induction ys, force+)

lemma distinct_set_remove_last:
  assumes "distinct (xs @ [x])"
  shows "set xs = set (xs @ [x]) - {x}"
  using assms by force

lemma distinct_set_remove_mid:
  assumes "distinct (xs @ [x] @ ys)"
  shows "set (xs @ ys) = set (xs @ [x] @ ys) - {x}"
  using assms by force

lemma distinct_list_split:
  assumes "distinct xs"
    and "xs = xa @ x # ya"
    and "xs = xb @ x # yb"
  shows "xa = xb \<and> ya = yb"
  using assms proof(induction xs arbitrary: xa xb x)
  fix xa xb x
  assume "[] = xa @ x # ya"
  thus "xa = xb \<and> ya = yb"
    by auto
next
  fix a xs xa xb x
  assume IH: "\<And>xa xb x. distinct xs \<Longrightarrow> xs = xa @ x # ya \<Longrightarrow> xs = xb @ x # yb \<Longrightarrow> xa = xb \<and> ya = yb"
    and "distinct (a # xs)" and "a # xs = xa @ x # ya" and "a # xs = xb @ x # yb"
  thus "xa = xb \<and> ya = yb"
    by(case_tac xa; case_tac xb) auto
qed

lemma distinct_append_swap:
  assumes "distinct (xs @ ys)"
  shows "distinct (ys @ xs)"
  using assms by (induction ys, auto)

lemma append_subset:
  assumes "set xs = set (ys @ zs)"
  shows "set ys \<subseteq> set xs" and "set zs \<subseteq> set xs"
  by (metis Un_iff assms set_append subsetI)+

lemma append_set_rem_last:
  assumes "set (xs @ [x]) = set (ys @ [x] @ zs)"
    and "distinct (xs @ [x])" and "distinct (ys @ [x] @ zs)"
  shows "set xs = set (ys @ zs)"
proof -
  have "distinct xs"
    using assms distinct_append by blast
  moreover from this have "set xs = set (xs @ [x]) - {x}"
    by (meson assms distinct_set_remove_last)
  moreover have "distinct (ys @ zs)"
    using assms distinct_rem_mid by simp
  ultimately show "set xs = set (ys @ zs)"
    using assms distinct_set_remove_mid by metis
qed

lemma distinct_map_fst_remove1:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (remove1 x xs))"
  using assms proof(induction xs)
  case Nil
  then show "distinct (map fst (remove1 x []))"
    by simp
next
  case (Cons a xs)
  hence IH: "distinct (map fst (remove1 x xs))"
    by simp
  then show "distinct (map fst (remove1 x (a # xs)))"
  proof(cases "a = x")
    case True
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    moreover have "fst a \<notin> fst ` set (remove1 x xs)"
      by (metis (no_types, lifting) Cons.prems distinct.simps(2) image_iff
          list.simps(9) notin_set_remove1 set_map)
    ultimately show ?thesis
      using IH by auto
  qed
qed


subsection\<open>The \isa{spec-ops} predicate\<close>

text\<open>The \isa{spec-ops} predicate describes a list of (ID, operation) pairs that
corresponds to the linearisation of an OpSet, and which we use for sequentially
interpreting the OpSet. A list satisfies \isa{spec-ops} iff it is sorted in ascending
order of IDs, if the IDs are unique, and if every operation's dependencies have
lower IDs than the operation itself. A list is implicitly finite in Isabelle/HOL.
These requirements correspond to the OpSet definition above, and indeed we prove
later that every OpSet has a linearisation that satisfies \isa{spec-ops}.\<close>

definition spec_ops :: "('oid::{linorder} \<times> 'oper) list \<Rightarrow> ('oper \<Rightarrow> 'oid set) \<Rightarrow> bool" where
  "spec_ops ops deps \<equiv> (sorted (map fst ops) \<and> distinct (map fst ops) \<and>
           (\<forall>oid oper ref. (oid, oper) \<in> set ops \<and> ref \<in> deps oper \<longrightarrow> ref < oid))"

lemma spec_ops_empty:
  shows "spec_ops [] deps"
  by (simp add: spec_ops_def)

lemma spec_ops_distinct:
  assumes "spec_ops ops deps"
  shows "distinct ops"
  using assms distinct_map spec_ops_def by blast

lemma spec_ops_distinct_fst:
  assumes "spec_ops ops deps"
  shows "distinct (map fst ops)"
  using assms by (simp add: spec_ops_def)

lemma spec_ops_sorted:
  assumes "spec_ops ops deps"
  shows "sorted (map fst ops)"
  using assms by (simp add: spec_ops_def)

lemma spec_ops_rem_cons:
  assumes "spec_ops (x # xs) deps"
  shows "spec_ops xs deps"
proof -
  have "sorted (map fst (x # xs))" and "distinct (map fst (x # xs))"
    using assms spec_ops_def by blast+
  moreover from this have "sorted (map fst xs)"
    by simp
  moreover have "\<forall>oid oper ref. (oid, oper) \<in> set xs \<and> ref \<in> deps oper \<longrightarrow> ref < oid"
    by (meson assms set_subset_Cons spec_ops_def subsetCE)
  ultimately show "spec_ops xs deps"
    by (simp add: spec_ops_def)
qed

lemma spec_ops_rem_last:
  assumes "spec_ops (xs @ [x]) deps"
  shows "spec_ops xs deps"
proof -
  have "sorted (map fst (xs @ [x]))" and "distinct (map fst (xs @ [x]))"
    using assms spec_ops_def by blast+
  moreover from this have "sorted (map fst xs)" and "distinct xs"
    by (auto simp add: sorted_append distinct_butlast distinct_map)
  moreover have "\<forall>oid oper ref. (oid, oper) \<in> set xs \<and> ref \<in> deps oper \<longrightarrow> ref < oid"
    by (metis assms butlast_snoc in_set_butlastD spec_ops_def)
  ultimately show "spec_ops xs deps"
    by (simp add: spec_ops_def)
qed

lemma spec_ops_remove1:
  assumes "spec_ops xs deps"
  shows "spec_ops (remove1 x xs) deps"
  using assms distinct_map_fst_remove1 spec_ops_def
  by (metis notin_set_remove1 sorted_map_remove1 spec_ops_def)

lemma spec_ops_ref_less:
  assumes "spec_ops xs deps"
    and "(oid, oper) \<in> set xs"
    and "r \<in> deps oper"
  shows "r < oid"
  using assms spec_ops_def by force

lemma spec_ops_ref_less_last:
  assumes "spec_ops (xs @ [(oid, oper)]) deps"
    and "r \<in> deps oper"
  shows "r < oid"
  using assms spec_ops_ref_less by fastforce

lemma spec_ops_id_inc:
  assumes "spec_ops (xs @ [(oid, oper)]) deps"
    and "x \<in> set (map fst xs)"
  shows "x < oid"
proof -
  have "sorted ((map fst xs) @ (map fst [(oid, oper)]))"
    using assms(1) by (simp add: spec_ops_def)
  hence "\<forall>i \<in> set (map fst xs). i \<le> oid"
    by (simp add: sorted_append)
  moreover have "distinct ((map fst xs) @ (map fst [(oid, oper)]))"
    using assms(1) by (simp add: spec_ops_def)
  hence "\<forall>i \<in> set (map fst xs). i \<noteq> oid"
    by auto
  ultimately show "x < oid"
    using assms(2) le_neq_trans by auto
qed

lemma spec_ops_add_last:
  assumes "spec_ops xs deps"
    and "\<forall>i \<in> set (map fst xs). i < oid"
    and "\<forall>ref \<in> deps oper. ref < oid"
  shows "spec_ops (xs @ [(oid, oper)]) deps"
proof -
  have "sorted ((map fst xs) @ [oid])"
    using assms sorted_append spec_ops_sorted by fastforce
  moreover have "distinct ((map fst xs) @ [oid])"
    using assms spec_ops_distinct_fst by fastforce
  moreover have "\<forall>oid oper ref. (oid, oper) \<in> set xs \<and> ref \<in> deps oper \<longrightarrow> ref < oid"
    using assms(1) spec_ops_def by fastforce
  hence "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)]) \<and> r \<in> deps opr \<longrightarrow> r < i"
    using assms(3) by auto
  ultimately show "spec_ops (xs @ [(oid, oper)]) deps"
    by (simp add: spec_ops_def)
qed

lemma spec_ops_add_any:
  assumes "spec_ops (xs @ ys) deps"
    and "\<forall>i \<in> set (map fst xs). i < oid"
    and "\<forall>i \<in> set (map fst ys). oid < i"
    and "\<forall>ref \<in> deps oper. ref < oid"
  shows "spec_ops (xs @ [(oid, oper)] @ ys) deps"
  using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "spec_ops (xs @ [(oid, oper)] @ []) deps"
    by (simp add: spec_ops_add_last)
next
  case (snoc y ys)
  have IH: "spec_ops (xs @ [(oid, oper)] @ ys) deps"
  proof -
    from snoc have "spec_ops (xs @ ys) deps"
      by (metis append_assoc spec_ops_rem_last)
    thus "spec_ops (xs @ [(oid, oper)] @ ys) deps"
      using assms(2) snoc by auto
  qed
  obtain yi yo where y_pair: "y = (yi, yo)"
    by force
  have oid_yi: "oid < yi"
    by (simp add: snoc.prems(3) y_pair)
  have yi_biggest: "\<forall>i \<in> set (map fst (xs @ [(oid, oper)] @ ys)). i < yi"
  proof -
    have "\<forall>i \<in> set (map fst xs). i < yi"
      using oid_yi assms(2) less_trans by blast
    moreover have "\<forall>i \<in> set (map fst ys). i < yi"
      by (metis UnCI append_assoc map_append set_append snoc.prems(1) spec_ops_id_inc y_pair)
    ultimately show ?thesis
      using oid_yi by auto
  qed
  have "sorted (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
  proof -
    from IH have "sorted (map fst (xs @ [(oid, oper)] @ ys))"
      using spec_ops_def by blast
    hence "sorted (map fst (xs @ [(oid, oper)] @ ys) @ [yi])"
      using yi_biggest
      by (simp add: sorted_append dual_order.strict_implies_order)
    thus "sorted (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
      by (simp add: y_pair)
  qed
  moreover have "distinct (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
  proof -
    have "distinct (map fst (xs @ [(oid, oper)] @ ys) @ [yi])"
      using IH yi_biggest spec_ops_def
      by (metis distinct.simps(2) distinct1_rotate order_less_irrefl rotate1.simps(2))
    thus "distinct (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
      by (simp add: y_pair)
  qed
  moreover have "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)] @ ys @ [y])
                     \<and> r \<in> deps opr \<longrightarrow> r < i"
  proof -
    have "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)] @ ys) \<and> r \<in> deps opr \<longrightarrow> r < i"
      by (meson IH spec_ops_def)
    moreover have "\<forall>ref. ref \<in> deps yo \<longrightarrow> ref < yi"
      by (metis spec_ops_ref_less append_is_Nil_conv last_appendR last_in_set last_snoc
          list.simps(3) snoc.prems(1) y_pair)
    ultimately show ?thesis
      using y_pair by auto
  qed
  ultimately show "spec_ops (xs @ [(oid, oper)] @ ys @ [y]) deps"
    using spec_ops_def by blast
qed

lemma spec_ops_split:
  assumes "spec_ops xs deps"
    and "oid \<notin> set (map fst xs)"
  shows "\<exists>pre suf. xs = pre @ suf \<and>
            (\<forall>i \<in> set (map fst pre). i < oid) \<and>
            (\<forall>i \<in> set (map fst suf). oid < i)"
  using assms proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by force
next
  case (snoc x xs)
  obtain xi xr where y_pair: "x = (xi, xr)"
    by force
  obtain pre suf where IH: "xs = pre @ suf \<and>
               (\<forall>a\<in>set (map fst pre). a < oid) \<and>
               (\<forall>a\<in>set (map fst suf). oid < a)"
    by (metis UnCI map_append set_append snoc spec_ops_rem_last)
  then show ?case
  proof(cases "xi < oid")
    case xi_less: True
    have "\<forall>x \<in> set (map fst (pre @ suf)). x < xi"
      using IH spec_ops_id_inc snoc.prems(1) y_pair by metis
    hence "\<forall>x \<in> set suf. fst x < xi"
      by simp
    hence "\<forall>x \<in> set suf. fst x < oid"
      using xi_less by auto
    hence "suf = []"
      using IH last_in_set by fastforce
    hence "xs @ [x] = (pre @ [(xi, xr)]) @ [] \<and>
              (\<forall>a\<in>set (map fst ((pre @ [(xi, xr)]))). a < oid) \<and>
              (\<forall>a\<in>set (map fst []). oid < a)"
      by (simp add: IH xi_less y_pair)
    then show ?thesis by force
  next
    case False
    hence "oid < xi" using snoc.prems(2) y_pair by auto
    hence "xs @ [x] = pre @ (suf @ [(xi, xr)]) \<and>
              (\<forall>i \<in> set (map fst pre). i < oid) \<and>
              (\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i)"
      by (simp add: IH y_pair)
    then show ?thesis by blast
  qed
qed

lemma spec_ops_exists_base:
  assumes "finite ops"
    and "\<And>oid op1 op2. (oid, op1) \<in> ops \<Longrightarrow> (oid, op2) \<in> ops \<Longrightarrow> op1 = op2"
    and "\<And>oid oper ref. (oid, oper) \<in> ops \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
  shows "\<exists>op_list. set op_list = ops \<and> spec_ops op_list deps"
  using assms proof(induct ops rule: Finite_Set.finite_induct_select)
  case empty
  then show "\<exists>op_list. set op_list = {} \<and> spec_ops op_list deps"
    by (simp add: spec_ops_empty)
next
  case (select subset)
  from this obtain op_list where "set op_list = subset" and "spec_ops op_list deps"
    using assms by blast
  moreover obtain oid oper where select: "(oid, oper) \<in> ops - subset"
    using select.hyps(1) by auto
  moreover from this have "\<And>op2. (oid, op2) \<in> ops \<Longrightarrow> op2 = oper"
    using assms(2) by auto
  hence "oid \<notin> fst ` subset"
    by (metis (no_types, lifting) DiffD2 select image_iff prod.collapse psubsetD select.hyps(1))
  from this obtain pre suf
    where "op_list = pre @ suf"
      and "\<forall>i \<in> set (map fst pre). i < oid"
      and "\<forall>i \<in> set (map fst suf). oid < i"
    using spec_ops_split calculation by (metis (no_types, lifting) set_map)
  moreover have "set (pre @ [(oid, oper)] @ suf) = insert (oid, oper) subset"
    using calculation by auto
  moreover have "spec_ops (pre @ [(oid, oper)] @ suf) deps"
    using calculation spec_ops_add_any assms(3) by (metis DiffD1)
  ultimately show ?case by blast
qed

text\<open>We prove that for any given OpSet, a \isa{spec-ops} linearisation exists:\<close>

lemma spec_ops_exists:
  assumes "opset ops deps"
  shows "\<exists>op_list. set op_list = ops \<and> spec_ops op_list deps"
proof -
  have "finite ops"
    using assms opset.finite_opset by force
  moreover have "\<And>oid op1 op2. (oid, op1) \<in> ops \<Longrightarrow> (oid, op2) \<in> ops \<Longrightarrow> op1 = op2"
    using assms opset.unique_oid by force
  moreover have "\<And>oid oper ref. (oid, oper) \<in> ops \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
    using assms opset.ref_older by force
  ultimately show "\<exists>op_list. set op_list = ops \<and> spec_ops op_list deps"
    by (simp add: spec_ops_exists_base)
qed

lemma spec_ops_oid_unique:
  assumes "spec_ops op_list deps"
    and "(oid, op1) \<in> set op_list"
    and "(oid, op2) \<in> set op_list"
  shows "op1 = op2"
  using assms proof(induction op_list, simp)
  case (Cons x op_list)
  have "distinct (map fst (x # op_list))"
    using Cons.prems(1) spec_ops_def by blast
  hence notin: "fst x \<notin> set (map fst op_list)"
    by simp
  then show "op1 = op2"
  proof(cases "fst x = oid")
    case True
    then show "op1 = op2"
      using Cons.prems notin by (metis Pair_inject in_set_zipE set_ConsD zip_map_fst_snd)
  next
    case False
    then have "(oid, op1) \<in> set op_list" and "(oid, op2) \<in> set op_list"
      using Cons.prems by auto
    then show "op1 = op2"
      using Cons.IH Cons.prems(1) spec_ops_rem_cons by blast
  qed
qed

text\<open>Conversely, for any given \isa{spec-ops} list, the set of pairs in the
list is an OpSet:\<close>

lemma spec_ops_is_opset:
  assumes "spec_ops op_list deps"
  shows "opset (set op_list) deps"
proof -
  have "\<And>oid op1 op2. (oid, op1) \<in> set op_list \<Longrightarrow> (oid, op2) \<in> set op_list \<Longrightarrow> op1 = op2"
    using assms spec_ops_oid_unique by fastforce
  moreover have "\<And>oid oper ref. (oid, oper) \<in> set op_list \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
    by (meson assms spec_ops_ref_less)
  moreover have "finite (set op_list)"
    by simp
  ultimately show "opset (set op_list) deps"
    by (simp add: opset_def)
qed


subsection\<open>The \isa{crdt-ops} predicate\<close>

text\<open>Like \isa{spec-ops}, the \isa{crdt-ops} predicate describes the linearisation of
an OpSet into a list. Like \isa{spec-ops}, it requires IDs to be unique. However,
its other properties are different: \isa{crdt-ops} does not require operations to
appear in sorted order, but instead, whenever any operation references the
ID of a prior operation, that prior operation must appear previously in the
\isa{crdt-ops} list. Thus, the order of operations is partially constrained:
operations must appear in causal order, but concurrent operations can be
ordered arbitrarily.

This list describes the operation sequence in the order it is typically applied to
an operation-based CRDT. Applying operations in the order they appear in
\isa{crdt-ops} requires that concurrent operations commute. For any \isa{crdt-ops}
operation sequence, there is a permutation that satisfies the \isa{spec-ops}
predicate. Thus, to check whether a CRDT satisfies its sequential specification,
we can prove that interpreting any \isa{crdt-ops} operation sequence with the
commutative operation interpretation results in the same end result as
interpreting the \isa{spec-ops} permutation of that operation sequence with the
sequential operation interpretation.\<close>

inductive crdt_ops :: "('oid::{linorder} \<times> 'oper) list \<Rightarrow> ('oper \<Rightarrow> 'oid set) \<Rightarrow> bool" where
  "crdt_ops [] deps" |
  "\<lbrakk>crdt_ops xs deps;
    oid \<notin> set (map fst xs);
    \<forall>ref \<in> deps oper. ref \<in> set (map fst xs) \<and> ref < oid
   \<rbrakk> \<Longrightarrow> crdt_ops (xs @ [(oid, oper)]) deps"

inductive_cases crdt_ops_last: "crdt_ops (xs @ [x]) deps"

lemma crdt_ops_intro:
  assumes "\<And>r. r \<in> deps oper \<Longrightarrow> r \<in> fst ` set xs \<and> r < oid"
    and "oid \<notin> fst ` set xs"
    and "crdt_ops xs deps"
  shows "crdt_ops (xs @ [(oid, oper)]) deps"
  using assms crdt_ops.simps by force

lemma crdt_ops_rem_last:
  assumes "crdt_ops (xs @ [x]) deps"
  shows "crdt_ops xs deps"
  using assms crdt_ops.cases snoc_eq_iff_butlast by blast

lemma crdt_ops_ref_less:
  assumes "crdt_ops xs deps"
    and "(oid, oper) \<in> set xs"
    and "r \<in> deps oper"
  shows "r < oid"
  using assms by (induction rule: crdt_ops.induct, auto)

lemma crdt_ops_ref_less_last:
  assumes "crdt_ops (xs @ [(oid, oper)]) deps"
    and "r \<in> deps oper"
  shows "r < oid"
  using assms crdt_ops_ref_less by fastforce

lemma crdt_ops_distinct_fst:
  assumes "crdt_ops xs deps"
  shows "distinct (map fst xs)"
  using assms proof (induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  hence "distinct (map fst xs)"
    using crdt_ops_last by blast
  moreover have "fst x \<notin> set (map fst xs)"
    using snoc by (metis crdt_ops_last fstI image_set)
  ultimately show "distinct (map fst (xs @ [x]))"
    by simp
qed

lemma crdt_ops_distinct:
  assumes "crdt_ops xs deps"
  shows "distinct xs"
  using assms crdt_ops_distinct_fst distinct_map by blast

lemma crdt_ops_unique_last:
  assumes "crdt_ops (xs @ [(oid, oper)]) deps"
  shows "oid \<notin> set (map fst xs)"
  using assms crdt_ops.cases by blast

lemma crdt_ops_unique_mid:
  assumes "crdt_ops (xs @ [(oid, oper)] @ ys) deps"
  shows "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
  using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst [])"
    by (metis crdt_ops_unique_last Nil_is_map_conv append_Nil2 empty_iff empty_set)
next
  case (snoc y ys)
  obtain yi yr where y_pair: "y = (yi, yr)"
    by fastforce
  have IH: "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
    using crdt_ops_rem_last snoc by (metis append_assoc)
  have "(xs @ (oid, oper) # ys) @ [(yi, yr)] = xs @ (oid, oper) # ys @ [(yi, yr)]"
    by simp
  hence "yi \<notin> set (map fst (xs @ (oid, oper) # ys))"
    using crdt_ops_unique_last by (metis append_Cons append_self_conv2 snoc.prems y_pair)
  thus "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst (ys @ [y]))"
    using IH y_pair by auto
qed

lemma crdt_ops_ref_exists:
  assumes "crdt_ops (pre @ (oid, oper) # suf) deps"
    and "ref \<in> deps oper"
  shows "ref \<in> fst ` set pre"
  using assms proof(induction suf rule: List.rev_induct)
  case Nil thus ?case
    by (metis crdt_ops_last prod.sel(2))
next
  case (snoc x xs) thus ?case
    using crdt_ops.cases by force
qed

lemma crdt_ops_no_future_ref:
  assumes "crdt_ops (xs @ [(oid, oper)] @ ys) deps"
  shows "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> fst ` set ys"
proof -
  from assms(1) have "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<in> set (map fst xs)"
    by (simp add: crdt_ops_ref_exists)
  moreover have "distinct (map fst (xs @ [(oid, oper)] @ ys))"
    using assms crdt_ops_distinct_fst by blast
  ultimately have "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> set (map fst ([(oid, oper)] @ ys))"
    using distinct_fst_append by metis
  thus "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> fst ` set ys"
    by simp
qed

lemma crdt_ops_reorder:
  assumes "crdt_ops (xs @ [(oid, oper)] @ ys) deps"
    and "\<And>op2 r. op2 \<in> snd ` set ys \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
  shows "crdt_ops (xs @ ys @ [(oid, oper)]) deps"
  using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "crdt_ops (xs @ [] @ [(oid, oper)]) deps"
    using crdt_ops_rem_last by auto
next
  case (snoc y ys)
  then obtain yi yo where y_pair: "y = (yi, yo)"
    by fastforce
  have IH: "crdt_ops (xs @ ys @ [(oid, oper)]) deps"
  proof -
    have "crdt_ops (xs @ [(oid, oper)] @ ys) deps"
      by (metis snoc(2) append.assoc crdt_ops_rem_last)
    thus "crdt_ops (xs @ ys @ [(oid, oper)]) deps"
      using snoc.IH snoc.prems(2) by auto
  qed
  have "crdt_ops (xs @ ys @ [y]) deps"
  proof -
    have "yi \<notin> fst ` set (xs @ [(oid, oper)] @ ys)"
      by (metis y_pair append_assoc crdt_ops_unique_last set_map snoc.prems(1))
    hence "yi \<notin> fst ` set (xs @ ys)"
      by auto
    moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ ys) \<and> r < yi"
    proof -
      have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<noteq> oid"
        using snoc.prems(2) y_pair by fastforce
      moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ [(oid, oper)] @ ys)"
        by (metis y_pair append_assoc snoc.prems(1) crdt_ops_ref_exists)
      moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r < yi"
        using crdt_ops_ref_less snoc.prems(1) y_pair by fastforce
      ultimately show "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ ys) \<and> r < yi"
        by simp
    qed
    moreover from IH have "crdt_ops (xs @ ys) deps"
      using crdt_ops_rem_last by force
    ultimately show "crdt_ops (xs @ ys @ [y]) deps"
      using y_pair crdt_ops_intro by (metis append.assoc)
  qed
  moreover have "oid \<notin> fst ` set (xs @ ys @ [y])"
    using crdt_ops_unique_mid by (metis (no_types, lifting) UnE image_Un
        image_set set_append snoc.prems(1))
  moreover have "\<And>r. r \<in> deps oper \<Longrightarrow> r \<in> fst ` set (xs @ ys @ [y])"
    using crdt_ops_ref_exists
    by (metis UnCI append_Cons image_Un set_append snoc.prems(1))
  moreover have "\<And>r. r \<in> deps oper \<Longrightarrow> r < oid"
    using IH crdt_ops_ref_less by fastforce
  ultimately show "crdt_ops (xs @ (ys @ [y]) @ [(oid, oper)]) deps"
    using crdt_ops_intro by (metis append_assoc)
qed

lemma crdt_ops_rem_middle:
  assumes "crdt_ops (xs @ [(oid, ref)] @ ys) deps"
    and "\<And>op2 r. op2 \<in> snd ` set ys \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
  shows "crdt_ops (xs @ ys) deps"
  using assms crdt_ops_rem_last crdt_ops_reorder append_assoc by metis

lemma crdt_ops_independent_suf:
  assumes "spec_ops (xs @ [(oid, oper)]) deps"
    and "crdt_ops (ys @ [(oid, oper)] @ zs) deps"
    and "set (xs @ [(oid, oper)]) = set (ys @ [(oid, oper)] @ zs)"
  shows "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
proof -
  have "\<And>op2 r. op2 \<in> snd ` set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < oid"
  proof -
    from assms(1) have "\<And>i. i \<in> fst ` set xs \<Longrightarrow> i < oid"
      using spec_ops_id_inc by fastforce
    moreover have "\<And>i2 op2 r. (i2, op2) \<in> set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < i2"
      using assms(1) spec_ops_ref_less spec_ops_rem_last by fastforce
    ultimately show "\<And>op2 r. op2 \<in> snd ` set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < oid"
      by fastforce
  qed
  moreover have "set zs \<subseteq> set xs"
  proof -
    have "distinct (xs @ [(oid, oper)])" and "distinct (ys @ [(oid, oper)] @ zs)"
      using assms spec_ops_distinct crdt_ops_distinct by blast+
    hence "set xs = set (ys @ zs)"
      by (meson append_set_rem_last assms(3))
    then show "set zs \<subseteq> set xs"
      using append_subset(2) by simp
  qed
  ultimately show "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
    by fastforce
qed

lemma crdt_ops_reorder_spec:
  assumes "spec_ops (xs @ [x]) deps"
    and "crdt_ops (ys @ [x] @ zs) deps"
    and "set (xs @ [x]) = set (ys @ [x] @ zs)"
  shows "crdt_ops (ys @ zs @ [x]) deps"
  using assms proof -
  obtain oid oper where x_pair: "x = (oid, oper)" by force
  hence "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
    using assms crdt_ops_independent_suf by fastforce
  thus "crdt_ops (ys @ zs @ [x]) deps"
    using assms(2) crdt_ops_reorder x_pair by metis
qed

lemma crdt_ops_rem_spec:
  assumes "spec_ops (xs @ [x]) deps"
    and "crdt_ops (ys @ [x] @ zs) deps"
    and "set (xs @ [x]) = set (ys @ [x] @ zs)"
  shows "crdt_ops (ys @ zs) deps"
  using assms crdt_ops_rem_last crdt_ops_reorder_spec append_assoc by metis

lemma crdt_ops_rem_penultimate:
  assumes "crdt_ops (xs @ [(i1, r1)] @ [(i2, r2)]) deps"
    and "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<noteq> i1"
  shows "crdt_ops (xs @ [(i2, r2)]) deps"
proof -
  have "crdt_ops (xs @ [(i1, r1)]) deps"
    using assms(1) crdt_ops_rem_last by force
  hence "crdt_ops xs deps"
    using crdt_ops_rem_last by force
  moreover have "distinct (map fst (xs @ [(i1, r1)] @ [(i2, r2)]))"
    using assms(1) crdt_ops_distinct_fst by blast
  hence "i2 \<notin> set (map fst xs)"
    by auto
  moreover have "crdt_ops ((xs @ [(i1, r1)]) @ [(i2, r2)]) deps"
    using assms(1) by auto
  hence "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<in> fst ` set (xs @ [(i1, r1)])"
    using crdt_ops_ref_exists by metis
  hence "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<in> set (map fst xs)"
    using assms(2) by auto
  moreover have "\<And>r. r \<in> deps r2 \<Longrightarrow> r < i2"
    using assms(1) crdt_ops_ref_less by fastforce
  ultimately show "crdt_ops (xs @ [(i2, r2)]) deps"
    by (simp add: crdt_ops_intro)
qed

lemma crdt_ops_spec_ops_exist:
  assumes "crdt_ops xs deps"
  shows "\<exists>ys. set xs = set ys \<and> spec_ops ys deps"
  using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "\<exists>ys. set [] = set ys \<and> spec_ops ys deps"
    by (simp add: spec_ops_empty)
next
  case (snoc x xs)
  hence IH: "\<exists>ys. set xs = set ys \<and> spec_ops ys deps"
    using crdt_ops_rem_last by blast
  then obtain ys oid ref
    where "set xs = set ys" and "spec_ops ys deps" and "x = (oid, ref)"
    by force
  moreover have "\<exists>pre suf. ys = pre@suf \<and>
                       (\<forall>i \<in> set (map fst pre). i < oid) \<and>
                       (\<forall>i \<in> set (map fst suf). oid < i)"
  proof -
    have "oid \<notin> set (map fst xs)"
      using calculation(3) crdt_ops_unique_last snoc.prems by force
    hence "oid \<notin> set (map fst ys)"
      by (simp add: calculation(1))
    thus ?thesis
      using spec_ops_split \<open>spec_ops ys deps\<close> by blast
  qed
  from this obtain pre suf where "ys = pre @ suf" and
    "\<forall>i \<in> set (map fst pre). i < oid" and
    "\<forall>i \<in> set (map fst suf). oid < i" by force
  moreover have "set (xs @ [(oid, ref)]) = set (pre @ [(oid, ref)] @ suf)"
    using crdt_ops_distinct calculation snoc.prems by simp
  moreover have "spec_ops (pre @ [(oid, ref)] @ suf) deps"
  proof -
    have "\<forall>r \<in> deps ref. r < oid"
      using calculation(3) crdt_ops_ref_less_last snoc.prems by fastforce
    hence "spec_ops (pre @ [(oid, ref)] @ suf) deps"
      using spec_ops_add_any calculation by metis
    thus ?thesis by simp
  qed
  ultimately show "\<exists>ys. set (xs @ [x]) = set ys \<and> spec_ops ys deps"
    by blast
qed

end
