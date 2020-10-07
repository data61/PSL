(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Defining data structure and \\
          key function remove\_max\<close>

theory RemoveMax
imports Sort
begin

subsection \<open>Describing data structure\<close>

text\<open>
We have already said that we are going to formalize heap and selection
sort and to show connections between these two sorts.  However, one
can immediately notice that selection sort is using list and heap sort
is using heap during its work. It would be very difficult to show
equivalency between these two sorts if it is continued straightforward
and independently proved that they satisfy conditions of locale
\verb|Sort|. They work with different objects. Much better thing to do
is to stay on the abstract level and to add the new locale, one that
describes characteristics of both list and heap. 
\<close>

locale Collection = 
  fixes empty :: "'b"
  \<comment> \<open>-- Represents empty element of the object (for example, for list it is $[]$)\<close>
  fixes is_empty :: "'b \<Rightarrow> bool"
  \<comment> \<open>-- Function that checks weather the object is empty or not\<close>
  fixes of_list :: "'a list \<Rightarrow> 'b"
  \<comment> \<open>-- Function transforms given list to desired object (for example, 
    for heap sort, function {\em of\_list} transforms list to heap)\<close>
  fixes multiset :: "'b \<Rightarrow> 'a multiset" 
  \<comment> \<open>-- Function makes a multiset from the given object. A multiset is a collection without order.\<close>
  assumes is_empty_inj: "is_empty e \<Longrightarrow> e = empty" 
  \<comment> \<open>-- It must be assured that the empty element is {\em empty}\<close>
  assumes is_empty_empty: "is_empty empty"
  \<comment> \<open>-- Must be satisfied that function {\em is\_empty} returns true for element {\em empty}\<close>
  assumes multiset_empty: "multiset empty = {#}"
  \<comment> \<open>-- Multiset of an empty object is empty multiset.\<close>
  assumes multiset_of_list: "multiset (of_list i) = mset i"
  \<comment> \<open>-- Multiset of an object gained by
  applying function {\em of\_list} must be the same as the multiset of
  the list. This, practically, means that function {\em of\_list} does
  not delete or change elements of the starting list.\<close>
begin
  lemma is_empty_as_list: "is_empty e \<Longrightarrow> multiset e = {#}"
    using is_empty_inj multiset_empty
    by auto

  definition set :: "'b \<Rightarrow> 'a set" where
     [simp]: "set l = set_mset (multiset l)"
end

subsection \<open>Function remove\_max\<close>

text\<open>
We wanted to emphasize that algorithms are same. Due to
the complexity of the implementation it usually happens that simple
properties are omitted, such as the connection between these two
sorting algorithms. This is a key feature that should be presented to
students in order to understand these algorithms. It is not unknown
that students usually prefer selection sort for its simplicity whereas
avoid heap sort for its complexity. However, if we can present them as
the algorithms that are same they may hesitate less in using the heap
sort. This is why the refinement is important. Using this technique we
were able to notice these characteristics. Separate verification would
not bring anything new. Being on the abstract level does not only
simplify the verifications, but also helps us to notice and to show
students important features. Even further, we can prove them formally
and completely justify our observation.
\<close>

locale RemoveMax = Collection empty is_empty of_list  multiset for 
  empty :: "'b" and 
  is_empty :: "'b \<Rightarrow> bool" and 
  of_list :: "'a::linorder list \<Rightarrow> 'b" and 
  multiset :: "'b \<Rightarrow> 'a::linorder multiset" + 
  fixes remove_max :: "'b \<Rightarrow> 'a \<times> 'b"
  \<comment> \<open>--- Function that removes maximum element from the object of type $'b$. 
      It returns maximum element and the object without that maximum element.\<close>
  fixes inv :: "'b \<Rightarrow> bool"
  \<comment> \<open>--- It checks weather the object is in required condition.
      For example, if we expect to work with heap it checks weather the object 
      is heap. This is called {\em invariant condition}\<close>
  assumes of_list_inv: "inv (of_list x)"
  \<comment> \<open>--- This condition assures that function {\em of\_list}
      made a object with desired property.\<close>
  assumes remove_max_max: 
     "\<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> m = Max (set l)"
  \<comment> \<open>--- First parameter of the return value of the 
      function {\em remove\_max} is the maximum element\<close>
  assumes remove_max_multiset: 
     "\<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> 
      add_mset m (multiset l') = multiset l"
  \<comment> \<open>--- Condition for multiset, ensures that nothing new is added or nothing 
      is lost after applying {\em remove\_max} function.\<close>
  assumes remove_max_inv: 
     "\<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> inv l'"
  \<comment> \<open>--- Ensures that invariant condition is true after removing maximum element. 
      Invariant condition must be true in each step of sorting algorithm, for example
      if we are sorting using heap than in each iteration we must have heap and function
      {\em remove\_max} must not change that.\<close>
begin

lemma remove_max_multiset_size: 
  "\<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> 
               size (multiset l) > size (multiset l')"
using remove_max_multiset[of l m l']
by (metis mset_subset_size multi_psub_of_add_self)

lemma remove_max_set: 
  "\<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> 
                                 set l' \<union> {m} = set l"
using remove_max_multiset[of l m l']
by (metis Un_insert_right local.set_def set_mset_add_mset_insert sup_bot_right)

text\<open>As it is said before
in each iteration invariant condition must be satisfied, so the {\em
  inv l} is always true, e.g. before and after execution of any
function. This is also the reason why sort function must be defined as
partial. This function parameters stay the same in each step of
iteration -- list stays list, and heap stays heap. As we said before,
in Isabelle/HOL we can only define total function, but there is a
mechanism that enables total function to appear as partial one:\<close>

partial_function (tailrec) ssort' where 
  "ssort' l sl = 
      (if is_empty l then 
          sl
       else 
          let 
            (m, l') = remove_max l 
          in
            ssort' l' (m # sl))"
declare ssort'.simps[code] 
definition ssort :: "'a list \<Rightarrow> 'a list" where 
  "ssort l = ssort' (of_list l) []"

inductive ssort'_dom where
   step: "\<lbrakk>\<And>m l'. \<lbrakk>\<not> is_empty l; (m, l') = remove_max l\<rbrakk> \<Longrightarrow> 
                  ssort'_dom (l', m # sl)\<rbrakk> \<Longrightarrow> ssort'_dom (l, sl)"
lemma ssort'_termination:
  assumes "inv (fst p)"
  shows "ssort'_dom p"
using assms
proof (induct p rule: wf_induct[of "measure (\<lambda>(l, sl). size (multiset l))"])
  let ?r = "measure (\<lambda>(l, sl). size (multiset l))"
  fix p :: "'b \<times> 'a list"
  assume "inv (fst p)" and *: 
         "\<forall>y. (y, p) \<in> ?r \<longrightarrow> inv (fst y) \<longrightarrow> ssort'_dom y"
  obtain l sl where "p = (l, sl)"
    by (cases p) auto
  show "ssort'_dom p"
  proof (subst \<open>p = (l, sl)\<close>, rule ssort'_dom.step)
    fix m l'
    assume "\<not> is_empty l" "(m, l') = remove_max l"
    show "ssort'_dom (l', m#sl)"
    proof (rule *[rule_format])
      show "((l', m#sl), p) \<in> ?r" "inv (fst (l', m#sl))"
        using \<open>p = (l, sl)\<close> \<open>inv (fst p)\<close> \<open>\<not> is_empty l\<close> 
        using \<open>(m, l') = remove_max l\<close>
        using remove_max_inv[of l m l']
        using remove_max_multiset_size[of l m l']
        by auto
    qed
  qed
qed simp

lemma ssort'Induct:
  assumes "inv l" "P l sl"
   "\<And> l sl m l'. 
    \<lbrakk>\<not> is_empty l; inv l; (m, l') = remove_max l; P l sl\<rbrakk> \<Longrightarrow> P l' (m # sl)"
  shows "P empty (ssort' l sl)"
proof-
  from \<open>inv l\<close> have "ssort'_dom (l, sl)"
    using ssort'_termination
    by auto
  thus ?thesis
    using assms
  proof (induct "(l, sl)" arbitrary: l sl rule: ssort'_dom.induct)
    case (step l sl)
    show ?case
    proof (cases "is_empty l")
      case True
      thus ?thesis
        using step(4) step(5) ssort'.simps[of l sl] is_empty_inj[of l]
        by simp
    next
      case False
      let ?p = "remove_max l" 
      let ?m = "fst ?p" and ?l' = "snd ?p"
      show ?thesis
        using False step(2)[of ?m ?l'] step(3) 
        using step(4) step(5)[of l ?m ?l' sl] step(5)
        using remove_max_inv[of l ?m ?l'] 
        using ssort'.simps[of l sl]
        by (cases ?p) auto
    qed
  qed
qed

lemma mset_ssort':
  assumes "inv l"
  shows "mset (ssort' l sl) = multiset l + mset sl"
using assms
proof-
    have "multiset empty + mset (ssort' l sl) = multiset l + mset sl"
      using assms
    proof (rule ssort'Induct)
      fix l1 sl1 m l'
      assume "\<not> is_empty l1" 
             "inv l1" 
             "(m, l') = remove_max l1" 
             "multiset l1 + mset sl1 = multiset l + mset sl"
      thus "multiset l' + mset (m # sl1) = multiset l + mset sl"
        using remove_max_multiset[of l1 m l']
        by (metis union_mset_add_mset_left union_mset_add_mset_right mset.simps(2))
    qed simp
    thus ?thesis
      using multiset_empty
      by simp
qed

lemma sorted_ssort':
  assumes "inv l" "sorted sl \<and> (\<forall> x \<in> set l. (\<forall> y \<in> List.set sl. x \<le> y))"
  shows "sorted (ssort' l sl)"
using assms
proof-
  have "sorted (ssort' l sl) \<and> 
        (\<forall> x \<in> set empty. (\<forall> y \<in> List.set (ssort' l sl). x \<le> y))"
    using assms
  proof (rule ssort'Induct)
    fix l sl m l'
    assume "\<not> is_empty l" 
           "inv l" 
           "(m, l') = remove_max l" 
           "sorted sl \<and> (\<forall>x\<in>set l. \<forall>y\<in>List.set sl. x \<le> y)"
    thus "sorted (m # sl) \<and> (\<forall>x\<in>set l'. \<forall>y\<in>List.set (m # sl). x \<le> y)"
      using remove_max_set[of l m l'] remove_max_max[of l m l']
      by (auto intro: Max_ge)
  qed
  thus ?thesis
    by simp
qed

lemma sorted_ssort: "sorted (ssort i)"
unfolding ssort_def
using sorted_ssort'[of "of_list i" "[]"] of_list_inv
by auto

lemma permutation_ssort: "ssort l <~~> l"
proof (subst mset_eq_perm[symmetric])
  show "mset (ssort l) = mset l"
    unfolding ssort_def
    using mset_ssort'[of "of_list l" "[]"]
    using multiset_of_list of_list_inv
    by simp
qed
end

text\<open>Using assumptions given in the definitions of the locales {\em
  Collection} and {\em RemoveMax} for the functions {\em multiset},
{\em is\_empty}, {\em of\_list} and {\em remove\_max} it is no
difficulty to show:\<close>

sublocale RemoveMax < Sort ssort
by (unfold_locales) (auto simp add: sorted_ssort permutation_ssort)

end
