(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

section \<open>Partitions of sets\<close>

theory Partitions
imports
  SetUtils

begin

text \<open>
We define the set of all partitions of a set (@{term all_partitions}) in textbook style, as well as a computable function @{term all_partitions_list} to algorithmically compute this set (then represented as a list).  This function is suitable for code generation.  We prove the equivalence of the two definition in order to ensure that the generated code correctly implements the original textbook-style definition.  For further background on the overall approach, see Caminati, Kerber, Lange, Rowat: \href{http://arxiv.org/abs/1308.1779}{Proving soundness of combinatorial Vickrey auctions and generating verified executable code}, 2013.
\<close>

text \<open>@{term P} is a family of non-overlapping  sets.\<close>
definition is_non_overlapping 
           where "is_non_overlapping P = (\<forall> X\<in>P . \<forall> Y\<in> P . (X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y))"
(* alternative, less concise formalisation:
"is_non_overlapping P = (\<forall> ec1 \<in> P . ec1 \<noteq> {} \<and> (\<forall> ec2 \<in> P - {ec1}. ec1 \<inter> ec2 = {}))"
*)

text \<open>A subfamily of a non-overlapping family is also a non-overlapping family\<close>

lemma subset_is_non_overlapping:
  assumes subset: "P \<subseteq> Q" and 
          non_overlapping: "is_non_overlapping Q"
  shows "is_non_overlapping P"
(* CL: The following takes 387 ms with Isabelle2013-1-RC1:
   by (metis is_non_overlapping_def non_overlapping rev_subsetD subset). MC: possibly useful for TPTP *)
proof -
  {
    fix X Y assume "X \<in> P \<and> Y \<in> P"
    then have "X \<in> Q \<and> Y \<in> Q" using subset by fast
    then have "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y" using non_overlapping unfolding is_non_overlapping_def by force
  }
  then show ?thesis unfolding is_non_overlapping_def by force
qed

(* This is not used at the moment, but it is interesting, as the proof
   was very hard to find for Sledgehammer. MC: possibly useful for TPTP *)

text \<open>The family that results from removing one element from an equivalence class of a non-overlapping family is not otherwise a member of the family.\<close>
lemma remove_from_eq_class_preserves_disjoint:
      fixes elem::'a
        and X::"'a set"
        and P::"'a set set"
      assumes non_overlapping: "is_non_overlapping P"
        and eq_class: "X \<in> P"
        and elem: "elem \<in> X"
      shows "X - {elem} \<notin> P"
  using assms Int_Diff is_non_overlapping_def Diff_disjoint Diff_eq_empty_iff 
        Int_absorb2 insert_Diff_if insert_not_empty by (metis)

text \<open>Inserting into a non-overlapping family @{term P} a set @{term X}, which is disjoint with the set 
  partitioned by @{term P}, yields another non-overlapping family.\<close>

lemma non_overlapping_extension1:
  fixes P::"'a set set"
    and X::"'a set"
  assumes partition: "is_non_overlapping P"
       and disjoint: "X \<inter> \<Union> P = {}" 
      and non_empty: "X \<noteq> {}"
  shows "is_non_overlapping (insert X P)"
proof -
  {
    fix Y::"'a set" and Z::"'a set"
    assume Y_Z_in_ext_P: "Y \<in> insert X P \<and> Z \<in> insert X P"
    have "Y \<inter> Z \<noteq> {} \<longleftrightarrow> Y = Z"
    proof
      assume "Y \<inter> Z \<noteq> {}"
      then show "Y = Z"
        using Y_Z_in_ext_P partition disjoint
        unfolding is_non_overlapping_def
        by fast
    next
      assume "Y = Z"
      then show "Y \<inter> Z \<noteq> {}"
        using Y_Z_in_ext_P partition non_empty
        unfolding is_non_overlapping_def
        by auto
    qed
  }
  then show ?thesis unfolding is_non_overlapping_def by force
qed

text \<open>An element of a non-overlapping family has no intersection with any other of its elements.\<close>
lemma disj_eq_classes:
  fixes P::"'a set set"
    and X::"'a set"
  assumes "is_non_overlapping P"
      and "X \<in> P"
  shows "X \<inter> \<Union> (P - {X}) = {}" 
proof -
  {
    fix x::'a
    assume x_in_two_eq_classes: "x \<in> X \<inter> \<Union> (P - {X})"
    then obtain Y where other_eq_class: "Y \<in> P - {X} \<and> x \<in> Y" by blast
    have "x \<in> X \<inter> Y \<and> Y \<in> P"
      using x_in_two_eq_classes other_eq_class by force
    then have "X = Y" using assms is_non_overlapping_def by fast
    then have "x \<in> {}" using other_eq_class by fast
  }
  then show ?thesis by blast
qed

text \<open>The empty set is not element of a non-overlapping family.\<close>
lemma no_empty_in_non_overlapping:
  assumes "is_non_overlapping p"
  shows "{} \<notin> p"
(* CL: The following takes 36 ms with Isabelle2013-1-RC1:
   by (metis Int_iff all_not_in_conv assms is_non_overlapping_def). MC: possibly useful for TPTP *)
  using assms is_non_overlapping_def by fast

text \<open>@{term P} is a partition of the set @{term A}. The infix notation takes the form ``noun-verb-object''\<close>
definition is_partition_of (infix "partitions" 75)
           where "is_partition_of P A = (\<Union> P = A \<and> is_non_overlapping P)"

text \<open>No partition of a non-empty set is empty.\<close>
lemma non_empty_imp_non_empty_partition:
  assumes "A \<noteq> {}"
      and "P partitions A"
  shows "P \<noteq> {}"
  using assms unfolding is_partition_of_def by fast

text \<open>Every element of a partitioned set ends up in one element in the partition.\<close>
lemma elem_in_partition:
  assumes in_set: "x \<in> A"
      and part: "P partitions A"
  obtains X where "x \<in> X" and "X \<in> P"
  using part in_set unfolding is_partition_of_def is_non_overlapping_def by (auto simp add: UnionE)

text \<open>Every element of the difference of a set @{term A} and another set @{term B} ends up in 
  an element of a partition of @{term A}, but not in an element of the partition of @{term "{B}"}.\<close>
lemma diff_elem_in_partition:
  assumes x: "x \<in> A - B"
      and part: "P partitions A"
  shows "\<exists> S \<in> P - { B } . x \<in> S"
(* Sledgehammer in Isabelle2013-1-RC1 can't do this within the default time limit. 
MC: possibly useful for TPTP *)
proof -
  from part x obtain X where "x \<in> X" and "X \<in> P"
    by (metis Diff_iff elem_in_partition)
  with x have "X \<noteq> B" by fast
  with \<open>x \<in> X\<close> \<open>X \<in> P\<close> show ?thesis by blast
qed

text \<open>Every element of a partitioned set ends up in exactly one set.\<close>
lemma elem_in_uniq_set:
  assumes in_set: "x \<in> A"
      and part: "P partitions A"
  shows "\<exists>! X \<in> P . x \<in> X"
proof -
  from assms obtain X where *: "X \<in> P \<and> x \<in> X"
    by (rule elem_in_partition) blast
  moreover {
    fix Y assume "Y \<in> P \<and> x \<in> Y"
    then have "Y = X"
      using part in_set *
      unfolding is_partition_of_def is_non_overlapping_def
      by (metis disjoint_iff_not_equal)
  }
  ultimately show ?thesis by (rule ex1I)
qed

text \<open>A non-empty set ``is'' a partition of itself.\<close>
lemma set_partitions_itself:
  assumes "A \<noteq> {}"
  shows "{A} partitions A" unfolding is_partition_of_def is_non_overlapping_def
(* CL: the following takes 48 ms on my machine with Isabelle2013:
   by (metis Sup_empty Sup_insert assms inf_idem singletonE sup_bot_right). MC: possibly useful for TPTP *)
proof
  show "\<Union> {A} = A" by simp
  {
    fix X Y
    assume "X \<in> {A}"
    then have "X = A" by (rule singletonD)
    assume "Y \<in> {A}"
    then have "Y = A" by (rule singletonD)
    from \<open>X = A\<close> \<open>Y = A\<close> have "X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y" using assms by simp
  }
  then show "\<forall> X \<in> {A} . \<forall> Y \<in> {A} . X \<inter> Y \<noteq> {} \<longleftrightarrow> X = Y" by force
qed

text \<open>The empty set is a partition of the empty set.\<close>
lemma emptyset_part_emptyset1:
  shows "{} partitions {}" 
  unfolding is_partition_of_def is_non_overlapping_def by fast

text \<open>Any partition of the empty set is empty.\<close>
lemma emptyset_part_emptyset2:
  assumes "P partitions {}"
  shows "P = {}"
  using assms unfolding is_partition_of_def is_non_overlapping_def
  by fastforce

text \<open>Classical set-theoretical definition of ``all partitions of a set @{term A}''\<close>
definition all_partitions where 
"all_partitions A = {P . P partitions A}"

text \<open>The set of all partitions of the empty set only contains the empty set.
  We need this to prove the base case of @{term all_partitions_paper_equiv_alg}.\<close>
lemma emptyset_part_emptyset3:
  shows "all_partitions {} = {{}}"
  unfolding all_partitions_def using emptyset_part_emptyset1 emptyset_part_emptyset2 by fast

text \<open>inserts an element new\_el into a specified set S inside a given family of sets\<close>
definition insert_into_member :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set"
   where "insert_into_member new_el Sets S = insert (S \<union> {new_el}) (Sets - {S})"

text \<open>Using @{const insert_into_member} to insert a fresh element, which is not a member of the
  set @{term S} being partitioned, into a non-overlapping family of sets yields another
  non-overlapping family.\<close>
lemma non_overlapping_extension2:
  fixes new_el::'a
    and P::"'a set set"
    and X::"'a set"
  assumes non_overlapping: "is_non_overlapping P"
      and class_element: "X \<in> P"
      and new: "new_el \<notin> \<Union> P"
  shows "is_non_overlapping (insert_into_member new_el P X)"
proof -
  let ?Y = "insert new_el X"
  have rest_is_non_overlapping: "is_non_overlapping (P - {X})"
    using non_overlapping subset_is_non_overlapping by blast
  have *: "X \<inter> \<Union> (P - {X}) = {}"
   using non_overlapping class_element by (rule disj_eq_classes)
  from * have non_empty: "?Y \<noteq> {}" by blast
  from * have disjoint: "?Y \<inter> \<Union> (P - {X}) = {}" using new by force
  have "is_non_overlapping (insert ?Y (P - {X}))"
    using rest_is_non_overlapping disjoint non_empty by (rule non_overlapping_extension1)
  then show ?thesis unfolding insert_into_member_def by simp
qed

text \<open>inserts an element into a specified set inside the given list of sets --
   the list variant of @{const insert_into_member}

   The rationale for this variant and for everything that depends on it is:
   While it is possible to computationally enumerate ``all partitions of a set'' as an
   @{typ "'a set set set"}, we need a list representation to apply further computational
   functions to partitions.  Because of the way we construct partitions (using functions
   such as @{term all_coarser_partitions_with} below) it is not sufficient to simply use 
   @{typ "'a set set list"}, but we need @{typ "'a set list list"}.  This is because it is hard 
   to impossible to convert a set to a list, whereas it is easy to convert a @{type list} to a @{type set}.
\<close>
definition insert_into_member_list :: "'a \<Rightarrow> 'a set list \<Rightarrow> 'a set \<Rightarrow> 'a set list"
  where "insert_into_member_list new_el Sets S = (S \<union> {new_el}) # (remove1 S Sets)"

text \<open>@{const insert_into_member_list} and @{const insert_into_member} are equivalent
  (as in returning the same set).\<close>
lemma insert_into_member_list_equivalence:
  fixes new_el::'a
    and Sets::"'a set list"
    and S::"'a set"
  assumes "distinct Sets"
  shows "set (insert_into_member_list new_el Sets S) = insert_into_member new_el (set Sets) S"
  unfolding insert_into_member_list_def insert_into_member_def using assms by simp

text \<open>an alternative characterization of the set partitioned by a partition obtained by 
  inserting an element into an equivalence class of a given partition (if @{term P}
  \emph{is} a partition)\<close>
lemma insert_into_member_partition1:
  fixes elem::'a
    and P::"'a set set"
    and set::"'a set"
  shows "\<Union> (insert_into_member elem P set) = \<Union> (insert (set \<union> {elem}) (P - {set}))"
(* CL: The following takes 12 ms in Isabelle2013-1-RC1:
   by (metis insert_into_member_def). MC: possibly useful for TPTP *)
    unfolding insert_into_member_def
    by fast

text \<open>Assuming that @{term P} is a partition of a set @{term S}, and @{term "new_el \<notin> S"}, the function defined below yields
  all possible partitions of @{term "S \<union> {new_el}"} that are coarser than @{term P}
  (i.e.\ not splitting classes that already exist in @{term P}).  These comprise one partition 
  with a class @{term "{new_el}"} and all other classes unchanged,
  as well as all partitions obtained by inserting @{term new_el} into one class of @{term P} at a time. While we use the definition to build coarser partitions of an existing partition P, the definition itself does not require P to be a partition.\<close>
definition coarser_partitions_with ::"'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set set"
  where "coarser_partitions_with new_el P = 
    insert
    \<comment> \<open>Let \<open>P\<close> be a partition of a set \<open>Set\<close>,\<close>
    \<comment> \<open>and suppose \<open>new_el \<notin> Set\<close>, i.e. \<open>{new_el} \<notin> P\<close>,\<close>
    \<comment> \<open>then the following constructs a partition of \<open>Set \<union> {new_el}\<close> obtained by\<close>
    \<comment> \<open>inserting a new class \<open>{new_el}\<close> and leaving all previous classes unchanged.\<close>
    (insert {new_el} P)
    \<comment> \<open>Let \<open>P\<close> be a partition of a set \<open>Set\<close>,\<close>
    \<comment> \<open>and suppose \<open>new_el \<notin> Set\<close>,\<close>
    \<comment> \<open>then the following constructs\<close>
    \<comment> \<open>the set of those partitions of \<open>Set \<union> {new_el}\<close> obtained by\<close>
    \<comment> \<open>inserting \<open>new_el\<close> into one class of \<open>P\<close> at a time.\<close>
    ((insert_into_member new_el P) ` P)"


text \<open>the list variant of @{const coarser_partitions_with}\<close>
definition coarser_partitions_with_list ::"'a \<Rightarrow> 'a set list \<Rightarrow> 'a set list list"
  where "coarser_partitions_with_list new_el P = 
    \<comment> \<open>Let \<open>P\<close> be a partition of a set \<open>Set\<close>,\<close>
    \<comment> \<open>and suppose \<open>new_el \<notin> Set\<close>, i.e. \<open>{new_el} \<notin> set P\<close>,\<close>
    \<comment> \<open>then the following constructs a partition of \<open>Set \<union> {new_el}\<close> obtained by\<close>
    \<comment> \<open>inserting a new class \<open>{new_el}\<close> and leaving all previous classes unchanged.\<close>
    ({new_el} # P)
    #
    \<comment> \<open>Let \<open>P\<close> be a partition of a set \<open>Set\<close>,\<close>
    \<comment> \<open>and suppose \<open>new_el \<notin> Set\<close>,\<close>
    \<comment> \<open>then the following constructs\<close>
    \<comment> \<open>the set of those partitions of \<open>Set \<union> {new_el}\<close> obtained by\<close>
    \<comment> \<open>inserting \<open>new_el\<close> into one class of \<open>P\<close> at a time.\<close>
    (map ((insert_into_member_list new_el P)) P)"

text \<open>@{const coarser_partitions_with_list} and @{const coarser_partitions_with} are equivalent.\<close>
lemma coarser_partitions_with_list_equivalence:
  assumes "distinct P"
  shows "set (map set (coarser_partitions_with_list new_el P)) = 
         coarser_partitions_with new_el (set P)"
proof -
  have "set (map set (coarser_partitions_with_list new_el P)) = set (map set (({new_el} # P) # (map ((insert_into_member_list new_el P)) P)))"
    unfolding coarser_partitions_with_list_def ..
  also have "\<dots> = insert (insert {new_el} (set P)) ((set \<circ> (insert_into_member_list new_el P)) ` set P)"
    by simp
  also have "\<dots> = insert (insert {new_el} (set P)) ((insert_into_member new_el (set P)) ` set P)"
    using assms insert_into_member_list_equivalence by (metis comp_apply)
  finally show ?thesis unfolding coarser_partitions_with_def .
qed

text \<open>Any member of the set of coarser partitions of a given partition, obtained by inserting 
  a given fresh element into each of its classes, is non\_overlapping.\<close>
lemma non_overlapping_extension3:
  fixes elem::'a
    and P::"'a set set"
    and Q::"'a set set"
  assumes P_non_overlapping: "is_non_overlapping P"
      and new_elem: "elem \<notin> \<Union> P"
      and Q_coarser: "Q \<in> coarser_partitions_with elem P"
  shows "is_non_overlapping Q"
proof -
  let ?q = "insert {elem} P"
  have Q_coarser_unfolded: "Q \<in> insert ?q (insert_into_member elem P ` P)" 
    using Q_coarser 
    unfolding coarser_partitions_with_def
    by fast
  show ?thesis
  proof (cases "Q = ?q")
    case True
    then show ?thesis
      using P_non_overlapping new_elem non_overlapping_extension1
      by fastforce
  next
    case False
    then have "Q \<in> (insert_into_member elem P) ` P" using Q_coarser_unfolded by fastforce
    then show ?thesis using non_overlapping_extension2 P_non_overlapping new_elem by fast
  qed
qed

text \<open>Let @{term P} be a partition of a set @{term S}, and @{term elem} an element (which may or may not be
  in @{term S} already).  Then, any member of @{term "coarser_partitions_with elem P"} is a set of sets
  whose union is @{term "S \<union> {elem}"}, i.e.\ it satisfies one of the necessary criteria for being a partition of @{term "S \<union> {elem}"}.
\<close>
lemma coarser_partitions_covers:
  fixes elem::'a
    and P::"'a set set"
    and Q::"'a set set"
  assumes "Q \<in> coarser_partitions_with elem P"
  shows "\<Union> Q = insert elem (\<Union> P)"
proof -
  let ?S = "\<Union> P"
  have Q_cases: "Q \<in> (insert_into_member elem P) ` P \<or> Q = insert {elem} P"
    using assms unfolding coarser_partitions_with_def by fast
  {
    fix eq_class assume eq_class_in_P: "eq_class \<in> P"
    have "\<Union> (insert (eq_class \<union> {elem}) (P - {eq_class})) = ?S \<union> (eq_class \<union> {elem})"
      using insert_into_member_partition1
      by (metis Sup_insert Un_commute Un_empty_right Un_insert_right insert_Diff_single)
    with eq_class_in_P have "\<Union> (insert (eq_class \<union> {elem}) (P - {eq_class})) = ?S \<union> {elem}" by blast
    then have "\<Union> (insert_into_member elem P eq_class) = ?S \<union> {elem}"
      using insert_into_member_partition1
      by (rule subst)
  }
  then show ?thesis using Q_cases by blast
qed

text \<open>Removes the element @{term elem} from every set in @{term P}, and removes from @{term P} any
  remaining empty sets.  This function is intended to be applied to partitions, i.e. @{term elem}
  occurs in at most one set.  @{term "partition_without e"} reverses @{term "coarser_partitions_with e"}.
@{const coarser_partitions_with} is one-to-many, while this is one-to-one, so we can think of a tree relation,
where coarser partitions of a set @{term "S \<union> {elem}"} are child nodes of one partition of @{term S}.\<close>
definition partition_without :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set set"
  where "partition_without elem P = (\<lambda>X . X - {elem}) ` P - {{}}"
(* Set comprehension notation { x - {elem} | x . x \<in> P } would look nicer but is harder to do proofs about *)

(* We don't need to define partition_without_list. *)

text \<open>alternative characterization of the set partitioned by the partition obtained 
  by removing an element from a given partition using @{const partition_without}\<close>
lemma partition_without_covers:
  fixes elem::'a
    and P::"'a set set"
  shows "\<Union> (partition_without elem P) = (\<Union> P) - {elem}"
proof -
  have "\<Union> (partition_without elem P) = \<Union> ((\<lambda>x . x - {elem}) ` P - {{}})"
    unfolding partition_without_def by fast
  also have "\<dots> = \<Union> P - {elem}" by blast
  finally show ?thesis .
qed

text \<open>Any class of the partition obtained by removing an element @{term elem} from an
  original partition @{term P} using @{const partition_without} equals some
  class of @{term P}, reduced by @{term elem}.\<close>
lemma super_class:
  assumes "X \<in> partition_without elem P"
  obtains Z where "Z \<in> P" and "X = Z - {elem}"
proof -
  from assms have "X \<in> (\<lambda>X . X - {elem}) ` P - {{}}" unfolding partition_without_def .
  then obtain Z where Z_in_P: "Z \<in> P" and Z_sup: "X = Z - {elem}"
    by (metis (lifting) Diff_iff image_iff)
  then show ?thesis ..
qed

text \<open>The class of sets obtained by removing an element from a non-overlapping class is another
  non-overlapping clas.\<close>
lemma non_overlapping_without_is_non_overlapping:
  fixes elem::'a
    and P::"'a set set"
  assumes "is_non_overlapping P"
  shows "is_non_overlapping (partition_without elem P)" (is "is_non_overlapping ?Q")
proof -   
  have "\<forall> X1 \<in> ?Q. \<forall> X2 \<in> ?Q. X1 \<inter> X2 \<noteq> {} \<longleftrightarrow> X1 = X2"
  proof 
    fix X1 assume X1_in_Q: "X1 \<in> ?Q"
    then obtain Z1 where Z1_in_P: "Z1 \<in> P" and Z1_sup: "X1 = Z1 - {elem}"
      by (rule super_class)
    have X1_non_empty: "X1 \<noteq> {}" using X1_in_Q partition_without_def by fast
    show "\<forall> X2 \<in> ?Q. X1 \<inter> X2 \<noteq> {} \<longleftrightarrow> X1 = X2" 
    proof
      fix X2 assume "X2 \<in> ?Q"
      then obtain Z2 where Z2_in_P: "Z2 \<in> P" and Z2_sup: "X2 = Z2 - {elem}"
        by (rule super_class)
      have "X1 \<inter> X2 \<noteq> {} \<longrightarrow> X1 = X2"
      proof
        assume "X1 \<inter> X2 \<noteq> {}"
        then have "Z1 \<inter> Z2 \<noteq> {}" using Z1_sup Z2_sup by fast
        then have "Z1 = Z2" using Z1_in_P Z2_in_P assms unfolding is_non_overlapping_def by fast
        then show "X1 = X2" using Z1_sup Z2_sup by fast
      qed
      moreover have "X1 = X2 \<longrightarrow> X1 \<inter> X2 \<noteq> {}" using X1_non_empty by auto
      ultimately show "(X1 \<inter> X2 \<noteq> {}) \<longleftrightarrow> X1 = X2" by blast
    qed
  qed
  then show ?thesis unfolding is_non_overlapping_def .
qed

text \<open>@{term "coarser_partitions_with elem"} is the ``inverse'' of 
  @{term "partition_without elem"}.\<close>
lemma coarser_partitions_inv_without:
  fixes elem::'a
    and P::"'a set set"
  assumes non_overlapping: "is_non_overlapping P"
      and elem: "elem \<in> \<Union> P" 
  shows "P \<in> coarser_partitions_with elem (partition_without elem P)"
    (is "P \<in> coarser_partitions_with elem ?Q")
proof -
  let ?remove_elem = "\<lambda>X . X - {elem}" (* function that removes elem out of a set *)
  obtain Y (* the equivalence class of elem *)
    where elem_eq_class: "elem \<in> Y" and elem_eq_class': "Y \<in> P" using elem ..
  let ?elem_neq_classes = "P - {Y}" (* those equivalence classes of which elem is not a member *)
  have P_wrt_elem: "P = ?elem_neq_classes \<union> {Y}" using elem_eq_class' by blast
  let ?elem_eq = "Y - {elem}" (* other elements equivalent to elem *)
  have Y_elem_eq: "?remove_elem ` {Y} = {?elem_eq}" by fast
  (* those classes,of which elem is not a member, form a partition *)
  have elem_neq_classes_part: "is_non_overlapping ?elem_neq_classes"
    using subset_is_non_overlapping non_overlapping
    by blast
  have elem_eq_wrt_P: "?elem_eq \<in> ?remove_elem ` P" using elem_eq_class' by blast
  
  { (* consider a class W, of which elem is not a member *)
    fix W assume W_eq_class: "W \<in> ?elem_neq_classes"
    then have "elem \<notin> W"
      using elem_eq_class elem_eq_class' non_overlapping is_non_overlapping_def
      by fast
    then have "?remove_elem W = W" by simp
  }
  then have elem_neq_classes_id: "?remove_elem ` ?elem_neq_classes = ?elem_neq_classes" by fastforce

  have Q_unfolded: "?Q = ?remove_elem ` P - {{}}"
    unfolding partition_without_def
    using image_Collect_mem
    by blast
  also have "\<dots> = ?remove_elem ` (?elem_neq_classes \<union> {Y}) - {{}}" using P_wrt_elem by presburger
  also have "\<dots> = ?elem_neq_classes \<union> {?elem_eq} - {{}}"
    using Y_elem_eq elem_neq_classes_id image_Un by metis
  finally have Q_wrt_elem: "?Q = ?elem_neq_classes \<union> {?elem_eq} - {{}}" .

  have "?elem_eq = {} \<or> ?elem_eq \<notin> P"
    using elem_eq_class elem_eq_class' non_overlapping Diff_Int_distrib2 Diff_iff empty_Diff insert_iff
unfolding is_non_overlapping_def by metis
  then have "?elem_eq \<notin> P"
    using non_overlapping no_empty_in_non_overlapping
    by metis
  then have elem_neq_classes: "?elem_neq_classes - {?elem_eq} = ?elem_neq_classes" by fastforce

  show ?thesis
  proof cases
    assume "?elem_eq \<notin> ?Q" (* the class of elem is not a member of ?Q = partition_without elem P *)
    then have "?elem_eq \<in> {{}}"
      using elem_eq_wrt_P Q_unfolded
      by (metis DiffI)
    then have Y_singleton: "Y = {elem}" using elem_eq_class by fast
    then have "?Q = ?elem_neq_classes - {{}}"
      using Q_wrt_elem
      by force
    then have "?Q = ?elem_neq_classes"
      using no_empty_in_non_overlapping elem_neq_classes_part
      by blast
    then have "insert {elem} ?Q = P"
      using Y_singleton elem_eq_class'
      by fast
    then show ?thesis unfolding coarser_partitions_with_def by auto
  next
    assume True: "\<not> ?elem_eq \<notin> ?Q"
    hence Y': "?elem_neq_classes \<union> {?elem_eq} - {{}} = ?elem_neq_classes \<union> {?elem_eq}"
      using no_empty_in_non_overlapping non_overlapping non_overlapping_without_is_non_overlapping
      by force
    have "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = insert (?elem_eq \<union> {elem}) (({?elem_eq} \<union> ?elem_neq_classes) - {?elem_eq})"
      unfolding insert_into_member_def ..
    also have "\<dots> = ({} \<union> ?elem_neq_classes) \<union> {?elem_eq \<union> {elem}}" using elem_neq_classes by force
    also have "\<dots> = ?elem_neq_classes \<union> {Y}" using elem_eq_class by blast
    finally have "insert_into_member elem ({?elem_eq} \<union> ?elem_neq_classes) ?elem_eq = ?elem_neq_classes \<union> {Y}" .
    then have "?elem_neq_classes \<union> {Y} = insert_into_member elem ?Q ?elem_eq"
      using Q_wrt_elem Y' partition_without_def
      by force
    then have "{Y} \<union> ?elem_neq_classes \<in> insert_into_member elem ?Q ` ?Q" using True by blast
    then have "{Y} \<union> ?elem_neq_classes \<in> coarser_partitions_with elem ?Q" unfolding coarser_partitions_with_def by simp
    then show ?thesis using P_wrt_elem by simp
  qed
qed

text \<open>Given a set @{term Ps} of partitions, this is intended to compute the set of all coarser
  partitions (given an extension element) of all partitions in @{term Ps}.\<close>
definition all_coarser_partitions_with :: " 'a \<Rightarrow> 'a set set set \<Rightarrow> 'a set set set"
   where "all_coarser_partitions_with elem Ps = \<Union> (coarser_partitions_with elem ` Ps)"

text \<open>the list variant of @{const all_coarser_partitions_with}\<close>
definition all_coarser_partitions_with_list :: " 'a \<Rightarrow> 'a set list list \<Rightarrow> 'a set list list"
  where "all_coarser_partitions_with_list elem Ps = 
         concat (map (coarser_partitions_with_list elem) Ps)"

text \<open>@{const all_coarser_partitions_with_list} and @{const all_coarser_partitions_with} are equivalent.\<close>
lemma all_coarser_partitions_with_list_equivalence:
  fixes elem::'a
    and Ps::"'a set list list"
  assumes distinct: "\<forall> P \<in> set Ps . distinct P"
  shows "set (map set (all_coarser_partitions_with_list elem Ps)) = all_coarser_partitions_with elem (set (map set Ps))"
    (is "?list_expr = ?set_expr")
proof -
  have "?list_expr = set (map set (concat (map (coarser_partitions_with_list elem) Ps)))"
    unfolding all_coarser_partitions_with_list_def ..
  also have "\<dots> = set ` (\<Union> x \<in> (coarser_partitions_with_list elem) ` (set Ps) . set x)" by simp
  also have "\<dots> = set ` (\<Union> x \<in> { coarser_partitions_with_list elem P | P . P \<in> set Ps } . set x)"
    by (simp add: image_Collect_mem)
  also have "\<dots> = \<Union> { set (map set (coarser_partitions_with_list elem P)) | P . P \<in> set Ps }" by auto
  also have "\<dots> = \<Union> { coarser_partitions_with elem (set P) | P . P \<in> set Ps }"
    using distinct coarser_partitions_with_list_equivalence by fast
  also have "\<dots> = \<Union> (coarser_partitions_with elem ` (set ` (set Ps)))" by (simp add: image_Collect_mem)
  also have "\<dots> = \<Union> (coarser_partitions_with elem ` (set (map set Ps)))" by simp
  also have "\<dots> = ?set_expr" unfolding all_coarser_partitions_with_def ..
  finally show ?thesis .
qed

text \<open>all partitions of a set (given as list) in form of a set\<close>
fun all_partitions_set :: "'a list \<Rightarrow> 'a set set set"
  where 
   "all_partitions_set [] = {{}}" |
   "all_partitions_set (e # X) = all_coarser_partitions_with e (all_partitions_set X)"

text \<open>all partitions of a set (given as list) in form of a list\<close>
fun all_partitions_list :: "'a list \<Rightarrow> 'a set list list"
  where 
   "all_partitions_list [] = [[]]" |
   "all_partitions_list (e # X) = all_coarser_partitions_with_list e (all_partitions_list X)"

text \<open>A list of partitions coarser than a given partition in list representation (constructed
  with @{const coarser_partitions_with} is distinct under certain conditions.\<close>
lemma coarser_partitions_with_list_distinct:
  fixes ps
  assumes ps_coarser: "ps \<in> set (coarser_partitions_with_list x Q)"
      and distinct: "distinct Q"
      and partition: "is_non_overlapping (set Q)"
      and new: "{x} \<notin> set Q"
  shows "distinct ps"
proof -
  have "set (coarser_partitions_with_list x Q) = insert ({x} # Q) (set (map (insert_into_member_list x Q) Q))"
    unfolding coarser_partitions_with_list_def by simp
  with ps_coarser have "ps \<in> insert ({x} # Q) (set (map ((insert_into_member_list x Q)) Q))" by blast
  then show ?thesis
  proof
    assume "ps = {x} # Q"
    with distinct and new show ?thesis by simp
  next
    assume "ps \<in> set (map (insert_into_member_list x Q) Q)"
    then obtain X where X_in_Q: "X \<in> set Q" and ps_insert: "ps = insert_into_member_list x Q X" by auto
    from ps_insert have "ps = (X \<union> {x}) # (remove1 X Q)" unfolding insert_into_member_list_def .
    also have "\<dots> = (X \<union> {x}) # (removeAll X Q)" using distinct by (metis distinct_remove1_removeAll)
    finally have ps_list: "ps = (X \<union> {x}) # (removeAll X Q)" .
    
    have distinct_tl: "X \<union> {x} \<notin> set (removeAll X Q)"
    proof
      from partition have partition': "\<forall>x\<in>set Q. \<forall>y\<in>set Q. (x \<inter> y \<noteq> {}) = (x = y)" unfolding is_non_overlapping_def .
      assume "X \<union> {x} \<in> set (removeAll X Q)"
      with X_in_Q partition show False by (metis partition' inf_sup_absorb member_remove no_empty_in_non_overlapping remove_code(1))
    qed
    with ps_list distinct show ?thesis by (metis (full_types) distinct.simps(2) distinct_removeAll)
  qed
qed

text \<open>The classical definition @{const all_partitions} and the algorithmic (constructive) definition @{const all_partitions_list} are equivalent.\<close>
lemma all_partitions_equivalence':
  fixes xs::"'a list"
  shows "distinct xs \<Longrightarrow> 
         ((set (map set (all_partitions_list xs)) = 
          all_partitions (set xs)) \<and> (\<forall> ps \<in> set (all_partitions_list xs) . distinct ps))"
proof (induct xs)
  case Nil
  have "set (map set (all_partitions_list [])) = all_partitions (set [])"
    unfolding List.set_simps(1) emptyset_part_emptyset3 by simp
    (* Sledgehammer no longer seems to find this, maybe after we have added the "distinct" part to the theorem statement. *)
  moreover have "\<forall> ps \<in> set (all_partitions_list []) . distinct ps" by fastforce
  ultimately show ?case ..
next
  case (Cons x xs)
  from Cons.prems Cons.hyps
    have hyp_equiv: "set (map set (all_partitions_list xs)) = all_partitions (set xs)" by simp
  from Cons.prems Cons.hyps
    have hyp_distinct: "\<forall> ps \<in> set (all_partitions_list xs) . distinct ps" by simp

  have distinct_xs: "distinct xs" using Cons.prems by simp
  have x_notin_xs: "x \<notin> set xs" using Cons.prems by simp
  
  have "set (map set (all_partitions_list (x # xs))) = all_partitions (set (x # xs))"
  proof (rule equalitySubsetI) (* -- {* case set \<rightarrow> list *} *)
    fix P::"'a set set" (* a partition *)
    let ?P_without_x = "partition_without x P"
    have P_partitions_exc_x: "\<Union> ?P_without_x = \<Union> P - {x}" using partition_without_covers .

    assume "P \<in> all_partitions (set (x # xs))"
    then have is_partition_of: "P partitions (set (x # xs))" unfolding all_partitions_def ..
    then have is_non_overlapping: "is_non_overlapping P" unfolding is_partition_of_def by simp
    from is_partition_of have P_covers: "\<Union> P = set (x # xs)" unfolding is_partition_of_def by simp

    have "?P_without_x partitions (set xs)"
      unfolding is_partition_of_def
      using is_non_overlapping non_overlapping_without_is_non_overlapping partition_without_covers P_covers x_notin_xs
      by (metis Diff_insert_absorb List.set_simps(2))
    with hyp_equiv have p_list: "?P_without_x \<in> set (map set (all_partitions_list xs))"
      unfolding all_partitions_def by fast
    have "P \<in> coarser_partitions_with x ?P_without_x"
      using coarser_partitions_inv_without is_non_overlapping P_covers
      by (metis List.set_simps(2) insertI1)
    then have "P \<in> \<Union> (coarser_partitions_with x ` set (map set (all_partitions_list xs)))"
      using p_list by blast
    then have "P \<in> all_coarser_partitions_with x (set (map set (all_partitions_list xs)))"
      unfolding all_coarser_partitions_with_def by fast
    then show "P \<in> set (map set (all_partitions_list (x # xs)))"
      using all_coarser_partitions_with_list_equivalence hyp_distinct
      by (metis all_partitions_list.simps(2))
  next (* -- {* case list \<rightarrow> set *} *)
    fix P::"'a set set" (* a partition *)
    assume P: "P \<in> set (map set (all_partitions_list (x # xs)))"

    have "set (map set (all_partitions_list (x # xs))) = set (map set (all_coarser_partitions_with_list x (all_partitions_list xs)))"
      by simp
    also have "\<dots> = all_coarser_partitions_with x (set (map set (all_partitions_list xs)))"
      using distinct_xs hyp_distinct all_coarser_partitions_with_list_equivalence by fast
    also have "\<dots> = all_coarser_partitions_with x (all_partitions (set xs))"
      using distinct_xs hyp_equiv by auto
    finally have P_set: "set (map set (all_partitions_list (x # xs))) = all_coarser_partitions_with x (all_partitions (set xs))" .

    with P have "P \<in> all_coarser_partitions_with x (all_partitions (set xs))" by fast
    then have "P \<in> \<Union> (coarser_partitions_with x ` (all_partitions (set xs)))"
      unfolding all_coarser_partitions_with_def .
    then obtain Y
      where P_in_Y: "P \<in> Y"
        and Y_coarser: "Y \<in> coarser_partitions_with x ` (all_partitions (set xs))" ..
    from Y_coarser obtain Q
      where Q_part_xs: "Q \<in> all_partitions (set xs)"
        and Y_coarser': "Y = coarser_partitions_with x Q" ..
    from P_in_Y Y_coarser' have P_wrt_Q: "P \<in> coarser_partitions_with x Q" by fast
    then have "Q \<in> all_partitions (set xs)" using Q_part_xs by simp
    then have "Q partitions (set xs)" unfolding all_partitions_def ..
    then have "is_non_overlapping Q" and Q_covers: "\<Union> Q = set xs"
      unfolding is_partition_of_def by simp_all
    then have P_partition: "is_non_overlapping P"
      using non_overlapping_extension3 P_wrt_Q x_notin_xs by fast
    have "\<Union> P = set xs \<union> {x}"
      using Q_covers P_in_Y Y_coarser' coarser_partitions_covers by fast
    then have "\<Union> P = set (x # xs)"
      using x_notin_xs P_wrt_Q Q_covers
      by (metis List.set_simps(2) insert_is_Un sup_commute)
    then have "P partitions (set (x # xs))"
      using P_partition unfolding is_partition_of_def by blast
    then show "P \<in> all_partitions (set (x # xs))" unfolding all_partitions_def ..
  qed
  moreover have "\<forall> ps \<in> set (all_partitions_list (x # xs)) . distinct ps"
  proof
    fix ps::"'a set list" assume ps_part: "ps \<in> set (all_partitions_list (x # xs))"

    have "set (all_partitions_list (x # xs)) = set (all_coarser_partitions_with_list x (all_partitions_list xs))"
      by simp
    also have "\<dots> = set (concat (map (coarser_partitions_with_list x) (all_partitions_list xs)))"
      unfolding all_coarser_partitions_with_list_def ..
    also have "\<dots> = \<Union> ((set \<circ> (coarser_partitions_with_list x)) ` (set (all_partitions_list xs)))"
      by simp
    finally have all_parts_unfolded: "set (all_partitions_list (x # xs)) = \<Union> ((set \<circ> (coarser_partitions_with_list x)) ` (set (all_partitions_list xs)))" .
    (* \<dots> = \<Union> { set (coarser_partitions_with_list x ps) | ps . ps \<in> set (all_partitions_list xs) }
       (more readable, but less useful in proofs) *)

    with ps_part obtain qs
      where qs: "qs \<in> set (all_partitions_list xs)"
        and ps_coarser: "ps \<in> set (coarser_partitions_with_list x qs)"
      using UnionE comp_def imageE by auto

    from qs have "set qs \<in> set (map set (all_partitions_list (xs)))" by simp
    with distinct_xs hyp_equiv have qs_hyp: "set qs \<in> all_partitions (set xs)" by fast
    then have qs_part: "is_non_overlapping (set qs)"
      using all_partitions_def is_partition_of_def
      by (metis mem_Collect_eq)
    then have distinct_qs: "distinct qs"
      using qs distinct_xs hyp_distinct by fast
    
    from Cons.prems have "x \<notin> set xs" by simp
    then have new: "{x} \<notin> set qs"
      using qs_hyp
      unfolding all_partitions_def is_partition_of_def
      by (metis (lifting, mono_tags) UnionI insertI1 mem_Collect_eq)

    from ps_coarser distinct_qs qs_part new
      show "distinct ps" by (rule coarser_partitions_with_list_distinct)
  qed
  ultimately show ?case ..
qed

text \<open>The classical definition @{const all_partitions} and the algorithmic (constructive) definition @{const all_partitions_list} are equivalent.  This is a front-end theorem derived from
  @{thm all_partitions_equivalence'}; it does not make the auxiliary statement about partitions
  being distinct lists.\<close>
theorem all_partitions_paper_equiv_alg:
  fixes xs::"'a list"
  shows "distinct xs \<Longrightarrow> set (map set (all_partitions_list xs)) = all_partitions (set xs)"
  using all_partitions_equivalence' by blast

text \<open>The function that we will be using in practice to compute all partitions of a set,
  a set-oriented front-end to @{const all_partitions_list}\<close>
definition all_partitions_alg :: "'a::linorder set \<Rightarrow> 'a set list list"
  where "all_partitions_alg X = all_partitions_list (sorted_list_of_set X)"

end

