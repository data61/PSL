(*  Title:       A General Method for the Proof of Theorems on Tail-recursive Functions
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "Case study 2"

theory CaseStudy2
imports Main "HOL-Library.Multiset"
begin

text \<open>
\null

In the second case study, the problem will be examined of defining a function
\<open>t_ins\<close> performing item insertion into binary search trees (admitting value
repetitions) of elements of a linear order, and then proving the correctness of
this definition, i.e. that the trees output by the function still be sorted if
the input ones are and contain one more occurrence of the inserted value, the
number of occurrences of any other value being left unaltered.

Here below is a naive tail-recursive definition of such function:

\null
\<close>

datatype 'a bintree = Leaf | Branch 'a "'a bintree" "'a bintree"

function (sequential) t_ins_naive ::
 "bool \<Rightarrow> 'a::linorder \<Rightarrow> 'a bintree list \<Rightarrow> 'a bintree"
where
"t_ins_naive False x (Branch y yl yr # ts) = (if x \<le> y
  then t_ins_naive False x (yl # Branch y yl yr # ts)
  else t_ins_naive False x (yr # Branch y yl yr # ts))" |
"t_ins_naive False x (Leaf # ts) =
  t_ins_naive True x (Branch x Leaf Leaf # ts)" |
"t_ins_naive True x (xt # Branch y yl yr # ts) = (if x \<le> y
  then t_ins_naive True x (Branch y xt yr # ts)
  else t_ins_naive True x (Branch y yl xt # ts))" |
"t_ins_naive True x [xt] = xt"
by pat_completeness auto

text \<open>
\null

The list appearing as the third argument, deputed to initially contain the sole
tree into which the second argument has to be inserted, is used to unfold all the
involved subtrees until a leaf is reached; then, such leaf is replaced with a branch
whose root value matches the second argument, and the subtree list is folded again.
The information on whether unfolding or folding is taking place is conveyed by the
first argument, whose value will respectively be \<open>False\<close> or \<open>True\<close>.

According to this plan, the computation is meant to terminate in correspondence
with pattern \<open>True\<close>, \<open>_\<close>, \<open>[_]\<close>. Hence, the above naive
definition comprises a non-recursive equation for this pattern only, so that the
residual ones \<open>True\<close>, \<open>_\<close>, \<open>_ # Leaf # _\<close> and \<open>_\<close>,
\<open>_\<close>, \<open>[]\<close> are not covered by any equation.

That which decreases in recursive calls is the size of the head of the subtree
list during unfolding, and the length of the list during folding. Furthermore,
unfolding precedes folding in the recursive call pipeline, viz. there is a
recursive equation switching from unfolding to folding, but no one carrying out
the opposite transition. These considerations suggest that a measure function
suitable to prove the termination of function \<open>t_ins_naive\<close> should roughly
match the sum of the length of the list and the size of the list head during
unfolding, and the length of the list alone during folding.

This idea can be refined by observing that the length of the list increases by one
at each recursive call during unfolding, and does not change in the recursive call
leading from unfolding to folding, at which the size of the input list head (a
leaf) equals zero. Therefore, in order that the measure function value be strictly
decreasing in each recursive call, the size of the list head has to be counted more
than once during unfolding -- e.g. twice --, and the length of the list has to be
decremented by one during folding -- no more than that, as otherwise the function
value would not change in the passage from a two-item to a one-item list.

As a result, a suitable measure function and the corresponding termination proof
are as follows:

\null
\<close>

fun t_ins_naive_measure :: "bool \<times> 'a \<times> 'a bintree list \<Rightarrow> nat" where
"t_ins_naive_measure (b, x, ts) = (if b
  then length ts - 1
  else length ts + 2 * size (hd ts))"

termination t_ins_naive
by (relation "measure t_ins_naive_measure", simp_all)

text \<open>
\null

Some further functions are needed to express the aforesaid correctness
properties of function \<open>t_ins_naive\<close>:

\null
\<close>

primrec t_set :: "'a bintree \<Rightarrow> 'a set" where
"t_set Leaf = {}" |
"t_set (Branch x xl xr) = {x} \<union> t_set xl \<union> t_set xr"

primrec t_multiset :: "'a bintree \<Rightarrow> 'a multiset" where
"t_multiset Leaf = {#}" |
"t_multiset (Branch x xl xr) = {#x#} + t_multiset xl + t_multiset xr"

lemma t_set_multiset: "t_set xt = set_mset (t_multiset xt)"
by (induction, simp_all)

primrec t_sorted :: "'a::linorder bintree \<Rightarrow> bool" where
"t_sorted Leaf = True" |
"t_sorted (Branch x xl xr) =
  ((\<forall>y \<in> t_set xl. y \<le> x) \<and> (\<forall>y \<in> t_set xr. x < y) \<and> t_sorted xl \<and> t_sorted xr)"

definition t_count :: "'a \<Rightarrow> 'a bintree \<Rightarrow> nat" where
"t_count x xt \<equiv> count (t_multiset xt) x"

text \<open>
\null

Functions \<open>t_set\<close> and \<open>t_multiset\<close> return the set and the multiset,
respectively, of the items of the input tree; the connection between them
expressed by lemma \<open>t_set_multiset\<close> will be used in step 9.

The target correctness theorems can then be enunciated as follows:

\null

\<open>t_sorted xt \<longrightarrow> t_sorted (t_ins_naive False x [xt])\<close>

\null

\<open>t_count y (t_ins_naive False x [xt]) =\<close>

\<open>(if y = x then Suc else id) (t_count y xt)\<close>
\<close>

subsection "Step 1"

text \<open>
This time, the Cartesian product of the input types will be implemented as a
record type. The second command instructs the system to regard such type as a
datatype, thus enabling record patterns:

\null
\<close>

record 'a t_type =
 folding :: bool
 item :: 'a
 subtrees :: "'a bintree list"

function (sequential) t_ins_aux :: "'a::linorder t_type \<Rightarrow> 'a t_type" where
"t_ins_aux \<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr> =
  (if x \<le> y
  then t_ins_aux \<lparr>folding = False, item = x,
    subtrees = yl # Branch y yl yr # ts\<rparr>
  else t_ins_aux \<lparr>folding = False, item = x,
    subtrees = yr # Branch y yl yr # ts\<rparr>)" |
"t_ins_aux \<lparr>folding = False, item = x, subtrees = Leaf # ts\<rparr> =
  t_ins_aux \<lparr>folding = True, item = x, subtrees = Branch x Leaf Leaf # ts\<rparr>" |
"t_ins_aux \<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr> =
  (if x \<le> y
  then t_ins_aux \<lparr>folding = True, item = x, subtrees = Branch y xt yr # ts\<rparr>
  else t_ins_aux \<lparr>folding = True, item = x, subtrees = Branch y yl xt # ts\<rparr>)" |
"t_ins_aux X = X"
by pat_completeness auto

text \<open>
\null

Observe that the pattern appearing in the non-recursive equation matches any
one of the residual patterns
\<open>\<lparr>folding = True, item = _, subtrees = [_]\<rparr>\<close>,
\<open>\<lparr>folding = True, item = _, subtrees = _ # Leaf # _\<rparr>\<close>,
\<open>\<lparr>folding = _, item = _, subtrees = []\<rparr>\<close>, thus complying with the
requirement that the definition of function \<open>t_ins_aux\<close> be total.

Since the arguments of recursive calls in the definition of function
\<open>t_ins_aux\<close> are the same as those of function \<open>t_ins_naive\<close>,
the termination proof developed for the latter can be applied to the former
as well by just turning the input product type of the previous measure
function into the input record type of function \<open>t_ins_aux\<close>.

\null
\<close>

fun t_ins_aux_measure :: "'a t_type \<Rightarrow> nat" where
"t_ins_aux_measure \<lparr>folding = b, item = x, subtrees = ts\<rparr> = (if b
  then length ts - 1
  else length ts + 2 * size (hd ts))"

termination t_ins_aux
by (relation "measure t_ins_aux_measure", simp_all)

subsection "Step 2"

definition t_ins_in :: "'a \<Rightarrow> 'a bintree \<Rightarrow> 'a t_type" where
"t_ins_in x xt \<equiv> \<lparr>folding = False, item = x, subtrees = [xt]\<rparr>"

definition t_ins_out :: "'a t_type \<Rightarrow> 'a bintree" where
"t_ins_out X \<equiv> hd (subtrees X)"

definition t_ins :: "'a::linorder \<Rightarrow> 'a bintree \<Rightarrow> 'a bintree" where
"t_ins x xt \<equiv> t_ins_out (t_ins_aux (t_ins_in x xt))"

text \<open>
\null

Since the significant inputs of function \<open>t_ins_naive\<close> match pattern
\<open>False\<close>, \<open>_\<close>, \<open>[_]\<close>, those of function \<open>t_ins_aux\<close>
match pattern \<open>\<lparr>folding = False, item = _, subtrees = [_]\<rparr>\<close>, thus
being in a one-to-one correspondence with the Cartesian product of the types
of the second and the third component.

Then, the target correctness theorems can be put into the following equivalent
form:

\null

\<open>t_sorted xt \<longrightarrow> t_sorted (t_ins x xt)\<close>

\null

\<open>t_count y (t_ins x xt) =\<close>
\<open>(if y = x then Suc else id) (t_count y xt)\<close>
\<close>

subsection "Step 3"

inductive_set t_ins_set :: "'a::linorder t_type \<Rightarrow> 'a t_type set"
for X :: "'a t_type" where
R0: "X \<in> t_ins_set X" |
R1: "\<lbrakk>\<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr> \<in> t_ins_set X;
     x \<le> y\<rbrakk> \<Longrightarrow>
     \<lparr>folding = False, item = x, subtrees = yl # Branch y yl yr # ts\<rparr>
       \<in> t_ins_set X" |
R2: "\<lbrakk>\<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr> \<in> t_ins_set X;
     \<not> x \<le> y\<rbrakk> \<Longrightarrow>
     \<lparr>folding = False, item = x, subtrees = yr # Branch y yl yr # ts\<rparr>
       \<in> t_ins_set X" |
R3: "\<lparr>folding = False, item = x, subtrees = Leaf # ts\<rparr> \<in> t_ins_set X \<Longrightarrow>
     \<lparr>folding = True, item = x, subtrees = Branch x Leaf Leaf # ts\<rparr>
       \<in> t_ins_set X" |
R4: "\<lbrakk>\<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr>
       \<in> t_ins_set X; x \<le> y\<rbrakk> \<Longrightarrow>
     \<lparr>folding = True, item = x, subtrees = Branch y xt yr # ts\<rparr> \<in> t_ins_set X" |
R5: "\<lbrakk>\<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr>
       \<in> t_ins_set X; \<not> x \<le> y\<rbrakk> \<Longrightarrow>
     \<lparr>folding = True, item = x, subtrees = Branch y yl xt # ts\<rparr> \<in> t_ins_set X"

subsection "Step 4"

lemma t_ins_subset:
  assumes XY: "Y \<in> t_ins_set X"
  shows "t_ins_set Y \<subseteq> t_ins_set X"
proof (rule subsetI, erule t_ins_set.induct)
  show "Y \<in> t_ins_set X" using XY .
next
  fix x y yl yr ts
  assume
   "\<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr> \<in> t_ins_set X"
  and "x \<le> y"
  thus "\<lparr>folding = False, item = x, subtrees = yl # Branch y yl yr # ts\<rparr>
   \<in> t_ins_set X" by (rule R1)
next
  fix x y yl yr ts
  assume
   "\<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr> \<in> t_ins_set X"
  and "\<not> x \<le> y"
  thus "\<lparr>folding = False, item = x, subtrees = yr # Branch y yl yr # ts\<rparr>
   \<in> t_ins_set X" by (rule R2)
next
  fix x ts
  assume "\<lparr>folding = False, item = x, subtrees = Leaf # ts\<rparr> \<in> t_ins_set X"
  thus "\<lparr>folding = True, item = x, subtrees = Branch x Leaf Leaf # ts\<rparr>
   \<in> t_ins_set X" by (rule R3)
next
  fix x xt y yl yr ts
  assume
   "\<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr> \<in> t_ins_set X"
  and "x \<le> y"
  thus "\<lparr>folding = True, item = x, subtrees = Branch y xt yr # ts\<rparr> \<in> t_ins_set X"
   by (rule R4)
next
  fix x xt y yl yr ts
  assume
   "\<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr> \<in> t_ins_set X"
  and "\<not> x \<le> y"
  thus "\<lparr>folding = True, item = x, subtrees = Branch y yl xt # ts\<rparr> \<in> t_ins_set X"
   by (rule R5)
qed

lemma t_ins_aux_set: "t_ins_aux X \<in> t_ins_set X"
proof (induction rule: t_ins_aux.induct,
 simp_all add: R0 del: t_ins_aux.simps(1, 3))
  fix x :: 'a and y yl yr ts
  let
   ?X = "\<lparr>folding = False, item = x, subtrees = Branch y yl yr # ts\<rparr>" and
   ?X' = "\<lparr>folding = False, item = x, subtrees = yl # Branch y yl yr # ts\<rparr>" and
   ?X'' = "\<lparr>folding = False, item = x, subtrees = yr # Branch y yl yr # ts\<rparr>"
  assume
   case1: "x \<le> y \<Longrightarrow> t_ins_aux ?X' \<in> t_ins_set ?X'" and
   case2: "\<not> x \<le> y \<Longrightarrow> t_ins_aux ?X'' \<in> t_ins_set ?X''"
  have 0: "?X \<in> t_ins_set ?X" by (rule R0)
  show "t_ins_aux ?X \<in> t_ins_set ?X"
  proof (cases "x \<le> y", simp_all)
    assume "x \<le> y"
    with 0 have "?X' \<in> t_ins_set ?X" by (rule R1)
    hence "t_ins_set ?X' \<subseteq> t_ins_set ?X" by (rule t_ins_subset)
    moreover have "t_ins_aux ?X' \<in> t_ins_set ?X'"
     using case1 and \<open>x \<le> y\<close> by simp
    ultimately show "t_ins_aux ?X' \<in> t_ins_set ?X" by (rule subsetD)
  next
    assume "\<not> x \<le> y"
    with 0 have "?X'' \<in> t_ins_set ?X" by (rule R2)
    hence "t_ins_set ?X'' \<subseteq> t_ins_set ?X" by (rule t_ins_subset)
    moreover have "t_ins_aux ?X'' \<in> t_ins_set ?X''"
     using case2 and \<open>\<not> x \<le> y\<close> by simp
    ultimately show "t_ins_aux ?X'' \<in> t_ins_set ?X" by (rule subsetD)
  qed
next
  fix x :: 'a and ts
  let
   ?X = "\<lparr>folding = False, item = x, subtrees = Leaf # ts\<rparr>" and
   ?X' = "\<lparr>folding = True, item = x, subtrees = Branch x Leaf Leaf # ts\<rparr>"
  have "?X \<in> t_ins_set ?X" by (rule R0)
  hence "?X' \<in> t_ins_set ?X" by (rule R3)
  hence "t_ins_set ?X' \<subseteq> t_ins_set ?X" by (rule t_ins_subset)
  moreover assume "t_ins_aux ?X' \<in> t_ins_set ?X'"
  ultimately show "t_ins_aux ?X' \<in> t_ins_set ?X" by (rule subsetD)
next
  fix x :: 'a and xt y yl yr ts
  let
   ?X = "\<lparr>folding = True, item = x, subtrees = xt # Branch y yl yr # ts\<rparr>" and
   ?X' = "\<lparr>folding = True, item = x, subtrees = Branch y xt yr # ts\<rparr>" and
   ?X'' = "\<lparr>folding = True, item = x, subtrees = Branch y yl xt # ts\<rparr>"
  assume
   case1: "x \<le> y \<Longrightarrow> t_ins_aux ?X' \<in> t_ins_set ?X'" and
   case2: "\<not> x \<le> y \<Longrightarrow> t_ins_aux ?X'' \<in> t_ins_set ?X''"
  have 0: "?X \<in> t_ins_set ?X" by (rule R0)
  show "t_ins_aux ?X \<in> t_ins_set ?X"
  proof (cases "x \<le> y", simp_all)
    assume "x \<le> y"
    with 0 have "?X' \<in> t_ins_set ?X" by (rule R4)
    hence "t_ins_set ?X' \<subseteq> t_ins_set ?X" by (rule t_ins_subset)
    moreover have "t_ins_aux ?X' \<in> t_ins_set ?X'"
     using case1 and \<open>x \<le> y\<close> by simp
    ultimately show "t_ins_aux ?X' \<in> t_ins_set ?X" by (rule subsetD)
  next
    assume "\<not> x \<le> y"
    with 0 have "?X'' \<in> t_ins_set ?X" by (rule R5)
    hence "t_ins_set ?X'' \<subseteq> t_ins_set ?X" by (rule t_ins_subset)
    moreover have "t_ins_aux ?X'' \<in> t_ins_set ?X''"
     using case2 and \<open>\<not> x \<le> y\<close> by simp
    ultimately show "t_ins_aux ?X'' \<in> t_ins_set ?X" by (rule subsetD)
  qed
qed

subsection "Step 5"

primrec t_val :: "'a bintree \<Rightarrow> 'a" where
"t_val (Branch x xl xr) = x"

primrec t_left :: "'a bintree \<Rightarrow> 'a bintree" where
"t_left (Branch x xl xr) = xl"

primrec t_right :: "'a bintree \<Rightarrow> 'a bintree" where
"t_right (Branch x xl xr) = xr"

text \<open>
\null

The partiality of the definition of the previous functions, which merely return
the root value and either subtree of the input branch, does not matter as they
will be applied to branches only.

These functions are used to define the following invariant -- this time, a single
invariant for both of the target correctness theorems:

\null
\<close>

fun t_ins_inv :: "'a::linorder \<Rightarrow> 'a bintree \<Rightarrow> 'a t_type \<Rightarrow> bool" where
"t_ins_inv x xt \<lparr>folding = b, item = y, subtrees = ts\<rparr> =
  (y = x \<and>
  (\<forall>n \<in> {..<length ts}.
    (t_sorted xt \<longrightarrow> t_sorted (ts ! n)) \<and>
    (0 < n \<longrightarrow> (\<exists>y yl yr. ts ! n = Branch y yl yr)) \<and>
    (let ts' = ts @ [Branch x xt Leaf] in t_multiset (ts ! n) =
      (if b \<and> n = 0 then {#x#} else {#}) +
      (if x \<le> t_val (ts' ! Suc n)
        then t_multiset (t_left (ts' ! Suc n))
        else t_multiset (t_right (ts' ! Suc n))))))"

text \<open>
\null

More precisely, the invariant, whose type has to match \<open>'a t_type \<Rightarrow> bool\<close>
according to the method specification, shall be comprised of function
\<open>t_ins_inv x xt\<close>, where \<open>x\<close>, \<open>xt\<close> are the free variables
appearing in the target theorems as the arguments of function \<open>t_ins\<close>.
\<close>

subsection "Step 6"

lemma t_ins_input: "t_ins_inv x xt \<lparr>folding = False, item = x, subtrees = [xt]\<rparr>"
by simp

subsection "Step 7"

fun t_ins_form :: "'a t_type \<Rightarrow> bool" where
"t_ins_form \<lparr>folding = True, item = _, subtrees = [_]\<rparr> = True" |
"t_ins_form \<lparr>folding = True, item = _, subtrees = _ # Leaf # _\<rparr> = True" |
"t_ins_form _ = False"

lemma t_ins_intro_1:
 "\<lbrakk>t_ins_inv x xt X; t_ins_form X\<rbrakk> \<Longrightarrow>
  t_sorted xt \<longrightarrow> t_sorted (t_ins_out X)"
proof (rule t_ins_form.cases [of X], simp_all add: t_ins_out_def)
qed (erule conjE, drule_tac x = "Suc 0" in bspec, simp_all)

lemma t_ins_intro_2:
 "\<lbrakk>t_ins_inv x xt X; t_ins_form X\<rbrakk> \<Longrightarrow>
  t_count y (t_ins_out X) = (if y = x then Suc else id) (t_count y xt)"
proof (rule t_ins_form.cases [of X], simp_all add: t_ins_out_def t_count_def)
qed (erule conjE, drule_tac x = "Suc 0" in bspec, simp_all)

text \<open>
\null

Defining predicate \<open>t_ins_form\<close> by means of pattern matching rather than
quantifiers permits a faster proof of the introduction rules through a case
distinction followed by simplification. These steps leave the subgoal
corresponding to pattern
\<open>\<lparr>folding = True, item = _, subtrees = _ # Leaf # _\<rparr>\<close> to be proven, which
can be done \emph{ad absurdum} as this pattern is incompatible with the invariant,
stating that all the subtrees in the list except for its head are branches.

The reason why this pattern, unlike
\<open>\<lparr>folding = _, item = _, subtrees = []\<rparr>\<close>, is not filtered by predicate
\<open>t_ins_form\<close>, is that the lack of its occurrences in recursive calls in
correspondence with significant inputs cannot be proven by rule inversion,
being it compatible with the patterns introduced by rules \<open>R3\<close>,
\<open>R4\<close>, and \<open>R5\<close>.
\<close>

subsection "Step 8"

text \<open>
This step will be accomplished by first proving by recursion induction that
the outputs of function \<open>t_ins_aux\<close> match either of the patterns
satisfying predicate \<open>t_ins_form\<close> or else the residual one
\<open>\<lparr>folding = _, item = _, subtrees = []\<rparr>\<close>, and then proving by rule
inversion that the last pattern may not occur in recursive calls in
correspondence with significant inputs.

\null
\<close>

definition t_ins_form_all :: "'a t_type \<Rightarrow> bool" where
"t_ins_form_all X \<equiv> t_ins_form X \<or> subtrees X = []"

lemma t_ins_form_aux_all: "t_ins_form_all (t_ins_aux X)"
by (rule t_ins_aux.induct [of "\<lambda>X. t_ins_form_all (t_ins_aux X)"],
 simp_all add: t_ins_form_all_def)

lemma t_ins_form_aux:
 "t_ins_form (t_ins_aux \<lparr>folding = False, item = x, subtrees = [xt]\<rparr>)"
 (is "_ (t_ins_aux ?X)")
using t_ins_aux_set [of ?X]
proof (rule t_ins_set.cases, insert t_ins_form_aux_all [of ?X])
qed (simp_all add: t_ins_form_all_def)

subsection "Step 9"

lemma t_ins_invariance:
  assumes XY: "Y \<in> t_ins_set X" and X: "t_ins_inv x xt X"
  shows "t_ins_inv x xt Y"
using XY
proof (rule t_ins_set.induct, simp_all split del: if_split)
  show "t_ins_inv x xt X" using X .
next
  fix z :: "'a::linorder" and y yl yr ts
  assume "z = x \<and>
   (\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. ts ! (n - Suc 0) = Branch y' yl' yr')) \<and>
     (let ts' = Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((Branch y yl yr # ts) ! n) =
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n)))))"
   (is "_ \<and> (\<forall>n \<in> {..<Suc (length ts)}. ?P n)")
  hence I: "\<forall>n \<in> {..<Suc (length ts)}. ?P n" ..
  assume xy: "x \<le> y"
  show
   "\<forall>n \<in> {..<Suc (Suc (length ts))}.
     (t_sorted xt \<longrightarrow> t_sorted ((yl # Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. (Branch y yl yr # ts) ! (n - Suc 0) =
       Branch y' yl' yr')) \<and>
     (let ts' = yl # Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((yl # Branch y yl yr # ts) ! n) =
         (if x \<le> t_val ((Branch y yl yr # ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n))))"
   (is "\<forall>n \<in> {..<Suc (Suc (length ts))}. ?Q n")
  proof
    fix n
    assume n: "n \<in> {..<Suc (Suc (length ts))}"
    show "?Q n"
    proof (cases n)
      case 0
      have "0 \<in> {..<Suc (length ts)}" by simp
      with I have "?P 0" ..
      thus ?thesis by (simp add: Let_def xy 0)
    next
      case (Suc m)
      hence "m \<in> {..<Suc (length ts)}" using n by simp
      with I have "?P m" ..
      thus ?thesis
      proof (simp add: Let_def Suc)
      qed (cases m, simp_all)
    qed
  qed
next
  fix z :: "'a::linorder" and y yl yr ts
  assume "z = x \<and>
   (\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. ts ! (n - Suc 0) = Branch y' yl' yr')) \<and>
     (let ts' = Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((Branch y yl yr # ts) ! n) =
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n)))))"
   (is "_ \<and> (\<forall>n \<in> {..<Suc (length ts)}. ?P n)")
  hence I: "\<forall>n \<in> {..<Suc (length ts)}. ?P n" ..
  assume xy: "\<not> x \<le> y"
  show
   "\<forall>n \<in> {..<Suc (Suc (length ts))}.
     (t_sorted xt \<longrightarrow> t_sorted ((yr # Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. (Branch y yl yr # ts) ! (n - Suc 0) =
       Branch y' yl' yr')) \<and>
     (let ts' = yr # Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((yr # Branch y yl yr # ts) ! n) =
         (if x \<le> t_val ((Branch y yl yr # ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n))))"
   (is "\<forall>n \<in> {..<Suc (Suc (length ts))}. ?Q n")
  proof
    fix n
    assume n: "n \<in> {..<Suc (Suc (length ts))}"
    show "?Q n"
    proof (cases n)
      case 0
      have "0 \<in> {..<Suc (length ts)}" by simp
      with I have "?P 0" ..
      thus ?thesis by (simp add: Let_def xy 0)
    next
      case (Suc m)
      hence "m \<in> {..<Suc (length ts)}" using n by simp
      with I have "?P m" ..
      thus ?thesis
      proof (simp add: Let_def Suc)
      qed (cases m, simp_all)
    qed
  qed
next
  fix z :: 'a and ts
  assume "z = x \<and>
   (\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Leaf # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y yl yr. ts ! (n - Suc 0) = Branch y yl yr)) \<and>
     (let ts' = Leaf # ts @ [Branch x xt Leaf]
       in t_multiset ((Leaf # ts) ! n) =
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n)))))"
   (is "_ \<and> (\<forall>n \<in> {..<Suc (length ts)}. ?P n)")
  hence I: "\<forall>n \<in> {..<Suc (length ts)}. ?P n" ..
  show
   "\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Branch x Leaf Leaf # ts) ! n)) \<and>
     (let ts' = Branch x Leaf Leaf # ts @ [Branch x xt Leaf]
       in t_multiset ((Branch x Leaf Leaf # ts) ! n) =
         (if n = 0 then {#x#} else {#}) +
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n))))"
   (is "\<forall>n \<in> {..<Suc (length ts)}. ?Q n")
  proof
    fix n
    assume n: "n \<in> {..<Suc (length ts)}"
    show "?Q n"
    proof (cases n)
      case 0
      have "0 \<in> {..<Suc (length ts)}" by simp
      with I have "?P 0" ..
      thus ?thesis by (simp add: Let_def 0 split: if_split_asm)
    next
      case (Suc m)
      have "?P n" using I and n ..
      thus ?thesis by (simp add: Let_def Suc)
    qed
  qed
next
  fix z :: 'a and zt y yl yr ts
  assume "z = x \<and>
   (\<forall>n \<in> {..<Suc (Suc (length ts))}.
     (t_sorted xt \<longrightarrow> t_sorted ((zt # Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. (Branch y yl yr # ts) ! (n - Suc 0) =
       Branch y' yl' yr')) \<and>
     (let ts' = zt # Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((zt # Branch y yl yr # ts) ! n) =
         (if n = 0 then {#x#} else {#}) +
         (if x \<le> t_val ((Branch y yl yr # ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n)))))"
   (is "_ \<and> (\<forall>n \<in> {..<Suc (Suc (length ts))}. ?P n)")
  hence I: "\<forall>n \<in> {..<Suc (Suc (length ts))}. ?P n" ..
  assume xy: "x \<le> y"
  show
   "\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Branch y zt yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. ts ! (n - Suc 0) = Branch y' yl' yr')) \<and>
     (let ts' = Branch y zt yr # ts @ [Branch x xt Leaf]
       in t_multiset ((Branch y zt yr # ts) ! n) =
         (if n = 0 then {#x#} else {#}) +
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n))))"
   (is "\<forall>n \<in> {..<Suc (length ts)}. ?Q n")
  proof
    fix n
    assume n: "n \<in> {..<Suc (length ts)}"
    show "?Q n"
    proof (cases n)
      case 0
      have "0 \<in> {..<Suc (Suc (length ts))}" by simp
      with I have "?P 0" ..
      hence I0: "(t_sorted xt \<longrightarrow> t_sorted zt) \<and>
       t_multiset zt = {#x#} + t_multiset yl"
       by (simp add: Let_def xy)
      have "Suc 0 \<in> {..<Suc (Suc (length ts))}" by simp
      with I have "?P (Suc 0)" ..
      hence I1: "(t_sorted xt \<longrightarrow> t_sorted (Branch y yl yr)) \<and>
       t_multiset (Branch y yl yr) =
       (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)
        then t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0))
        else t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)))"
       by (simp add: Let_def)
      show ?thesis
      proof (simp add: Let_def 0 del: t_sorted.simps split del: if_split,
       rule conjI, simp_all add: Let_def 0 del: t_sorted.simps,
       rule_tac [2] conjI, rule_tac [!] impI)
        assume s: "t_sorted xt"
        hence "t_sorted zt" using I0 by simp
        moreover have "t_sorted (Branch y yl yr)" using I1 and s by simp
        moreover have "t_set zt = {x} \<union> t_set yl" using I0
         by (simp add: t_set_multiset)
        ultimately show "t_sorted (Branch y zt yr)" using xy by simp
      next
        assume "x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)"
        hence "t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0)) =
         t_multiset (Branch y yl yr)" using I1 by simp
        thus "add_mset y (t_multiset zt + t_multiset yr) =
         add_mset x (t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0)))" using I0
         by simp
      next
        assume "\<not> x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)"
        hence "t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)) =
         t_multiset (Branch y yl yr)" using I1 by simp
        thus "add_mset y (t_multiset zt + t_multiset yr) =
         add_mset x (t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)))" using I0
         by simp
      qed
    next
      case (Suc m)
      have "Suc n \<in> {..<Suc (Suc (length ts))}" using n by simp
      with I have "?P (Suc n)" ..
      thus ?thesis by (simp add: Let_def Suc)
    qed
  qed
next
  fix z :: 'a and zt y yl yr ts
  assume "z = x \<and>
   (\<forall>n \<in> {..<Suc (Suc (length ts))}.
     (t_sorted xt \<longrightarrow> t_sorted ((zt # Branch y yl yr # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. (Branch y yl yr # ts) ! (n - Suc 0) =
       Branch y' yl' yr')) \<and>
     (let ts' = zt # Branch y yl yr # ts @ [Branch x xt Leaf]
       in t_multiset ((zt # Branch y yl yr # ts) ! n) =
         (if n = 0 then {#x#} else {#}) +
         (if x \<le> t_val ((Branch y yl yr # ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n)))))"
   (is "_ \<and> (\<forall>n \<in> {..<Suc (Suc (length ts))}. ?P n)")
  hence I: "\<forall>n \<in> {..<Suc (Suc (length ts))}. ?P n" ..
  assume xy: "\<not> x \<le> y"
  show
   "\<forall>n \<in> {..<Suc (length ts)}.
     (t_sorted xt \<longrightarrow> t_sorted ((Branch y yl zt # ts) ! n)) \<and>
     (0 < n \<longrightarrow> (\<exists>y' yl' yr'. ts ! (n - Suc 0) = Branch y' yl' yr')) \<and>
     (let ts' = Branch y yl zt # ts @ [Branch x xt Leaf]
       in t_multiset ((Branch y yl zt # ts) ! n) =
         (if n = 0 then {#x#} else {#}) +
         (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! n)
           then t_multiset (t_left (ts' ! Suc n))
           else t_multiset (t_right (ts' ! Suc n))))"
   (is "\<forall>n \<in> {..<Suc (length ts)}. ?Q n")
  proof
    fix n
    assume n: "n \<in> {..<Suc (length ts)}"
    show "?Q n"
    proof (cases n)
      case 0
      have "0 \<in> {..<Suc (Suc (length ts))}" by simp
      with I have "?P 0" ..
      hence I0: "(t_sorted xt \<longrightarrow> t_sorted zt) \<and>
       t_multiset zt = {#x#} + t_multiset yr"
       by (simp add: Let_def xy)
      have "Suc 0 \<in> {..<Suc (Suc (length ts))}" by simp
      with I have "?P (Suc 0)" ..
      hence I1: "(t_sorted xt \<longrightarrow> t_sorted (Branch y yl yr)) \<and>
       t_multiset (Branch y yl yr) =
       (if x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)
        then t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0))
        else t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)))"
       by (simp add: Let_def)
      show ?thesis
      proof (simp add: Let_def 0 del: t_sorted.simps split del: if_split,
       rule conjI, simp_all add: Let_def 0 del: t_sorted.simps,
       rule_tac [2] conjI, rule_tac [!] impI)
        assume s: "t_sorted xt"
        hence "t_sorted zt" using I0 by simp
        moreover have "t_sorted (Branch y yl yr)" using I1 and s by simp
        moreover have "t_set zt = {x} \<union> t_set yr" using I0
         by (simp add: t_set_multiset)
        ultimately show "t_sorted (Branch y yl zt)" using xy by simp
      next
        assume "x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)"
        hence "t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0)) =
         t_multiset (Branch y yl yr)" using I1 by simp
        thus "add_mset y (t_multiset yl + t_multiset zt) =
         add_mset x (t_multiset (t_left ((ts @ [Branch x xt Leaf]) ! 0)))" using I0
         by simp
      next
        assume "\<not> x \<le> t_val ((ts @ [Branch x xt Leaf]) ! 0)"
        hence "t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)) =
         t_multiset (Branch y yl yr)" using I1 by simp
        thus "add_mset y (t_multiset yl + t_multiset zt) =
         add_mset x (t_multiset (t_right ((ts @ [Branch x xt Leaf]) ! 0)))" using I0
         by simp
      qed
    next
      case (Suc m)
      have "Suc n \<in> {..<Suc (Suc (length ts))}" using n by simp
      with I have "?P (Suc n)" ..
      thus ?thesis by (simp add: Let_def Suc)
    qed
  qed
qed

subsection "Step 10"

theorem "t_sorted xt \<longrightarrow> t_sorted (t_ins x xt)"
proof -
  let ?X = "\<lparr>folding = False, item = x, subtrees = [xt]\<rparr>"
  have "t_ins_aux ?X \<in> t_ins_set ?X" by (rule t_ins_aux_set)
  moreover have "t_ins_inv x xt ?X" by (rule t_ins_input)
  ultimately have "t_ins_inv x xt (t_ins_aux ?X)" by (rule t_ins_invariance)
  moreover have "t_ins_form (t_ins_aux ?X)" by (rule t_ins_form_aux)
  ultimately have "t_sorted xt \<longrightarrow> t_sorted (t_ins_out (t_ins_aux ?X))"
   by (rule t_ins_intro_1)
  moreover have "?X = t_ins_in x xt" by (simp add: t_ins_in_def)
  ultimately show ?thesis by (simp add: t_ins_def)
qed

theorem "t_count y (t_ins x xt) = (if y = x then Suc else id) (t_count y xt)"
proof -
  let ?X = "\<lparr>folding = False, item = x, subtrees = [xt]\<rparr>"
  have "t_ins_aux ?X \<in> t_ins_set ?X" by (rule t_ins_aux_set)
  moreover have "t_ins_inv x xt ?X" by (rule t_ins_input)
  ultimately have "t_ins_inv x xt (t_ins_aux ?X)" by (rule t_ins_invariance)
  moreover have "t_ins_form (t_ins_aux ?X)" by (rule t_ins_form_aux)
  ultimately have "t_count y (t_ins_out (t_ins_aux ?X)) =
   (if y = x then Suc else id) (t_count y xt)"
   by (rule t_ins_intro_2)
  moreover have "?X = t_ins_in x xt" by (simp add: t_ins_in_def)
  ultimately show ?thesis by (simp add: t_ins_def)
qed

end
