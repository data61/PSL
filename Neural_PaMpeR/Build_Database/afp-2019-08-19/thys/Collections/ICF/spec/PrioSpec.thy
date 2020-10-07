section \<open>\isaheader{Specification of Priority Queues}\<close>
theory PrioSpec
imports ICF_Spec_Base "HOL-Library.Multiset"
begin

(*@intf Prio
  @abstype ('e \<times> 'a::linorder) multiset
  Priority queues that may contain duplicate elements.
*)

text \<open>
  We specify priority queues, that are abstracted to
  multisets of pairs of elements and priorities.
\<close>

locale prio = 
  fixes \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset" \<comment> \<open>Abstraction to multiset\<close>
  fixes invar :: "'p \<Rightarrow> bool"                     \<comment> \<open>Invariant\<close>

locale prio_no_invar = prio +
  assumes invar[simp, intro!]: "\<And>s. invar s"

subsection "Basic Priority Queue Functions"
subsubsection "Empty Queue"
locale prio_empty = prio +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes empty :: "unit \<Rightarrow> 'p"
  assumes empty_correct: 
  "invar (empty ())" 
  "\<alpha> (empty ()) = {#}"


subsubsection "Emptiness Predicate"
locale prio_isEmpty = prio +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes isEmpty :: "'p \<Rightarrow> bool"
  assumes isEmpty_correct: 
  "invar p \<Longrightarrow> (isEmpty p) = (\<alpha> p = {#})" 


subsubsection "Find Minimal Element"
locale prio_find = prio +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes find :: "'p \<Rightarrow> ('e \<times> 'a::linorder)"
  assumes find_correct: "\<lbrakk>invar p; \<alpha> p \<noteq> {#}\<rbrakk> \<Longrightarrow> 
       (find p) \<in># (\<alpha> p) \<and> (\<forall>y \<in> set_mset (\<alpha> p). snd (find p) \<le> snd y)"

subsubsection "Insert"
locale prio_insert = prio +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes insert :: "'e \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'p"
  assumes insert_correct: 
  "invar p \<Longrightarrow> invar (insert e a p)"
  "invar p \<Longrightarrow> \<alpha> (insert e a p) = (\<alpha> p) + {#(e,a)#}" 

subsubsection "Meld Two Queues"
locale prio_meld = prio +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes meld :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
  assumes meld_correct:
  "\<lbrakk>invar p; invar p'\<rbrakk> \<Longrightarrow> invar (meld p p')"
  "\<lbrakk>invar p; invar p'\<rbrakk> \<Longrightarrow> \<alpha> (meld p p') = (\<alpha> p) + (\<alpha> p')"

subsubsection "Delete Minimal Element"
text \<open>Delete the same element that find will return\<close>
locale prio_delete = prio_find +
  constrains \<alpha> :: "'p \<Rightarrow> ('e \<times> 'a::linorder) multiset"
  fixes delete :: "'p \<Rightarrow> 'p"
  assumes delete_correct:
  "\<lbrakk>invar p; \<alpha> p \<noteq> {#}\<rbrakk> \<Longrightarrow> invar (delete p)"
  "\<lbrakk>invar p; \<alpha> p \<noteq> {#}\<rbrakk> \<Longrightarrow> \<alpha> (delete p) = (\<alpha> p) - {# (find p) #}"


subsection "Record based interface"
record ('e, 'a, 'p) prio_ops =
  prio_op_\<alpha> :: "'p \<Rightarrow> ('e \<times> 'a) multiset" 
  prio_op_invar :: "'p \<Rightarrow> bool" 
  prio_op_empty :: "unit \<Rightarrow> 'p" 
  prio_op_isEmpty :: "'p \<Rightarrow> bool" 
  prio_op_insert :: "'e \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> 'p" 
  prio_op_find :: "'p \<Rightarrow> 'e \<times> 'a" 
  prio_op_delete :: "'p \<Rightarrow> 'p" 
  prio_op_meld :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"

locale StdPrioDefs =
  fixes ops :: "('e,'a::linorder,'p) prio_ops"
begin
  abbreviation \<alpha> where "\<alpha> == prio_op_\<alpha> ops"
  abbreviation invar where "invar == prio_op_invar ops"
  abbreviation empty where "empty == prio_op_empty ops"
  abbreviation isEmpty where "isEmpty == prio_op_isEmpty ops"
  abbreviation insert where "insert == prio_op_insert ops"
  abbreviation find where "find == prio_op_find ops"
  abbreviation delete where "delete == prio_op_delete ops"
  abbreviation meld where "meld == prio_op_meld ops"
end

locale StdPrio = StdPrioDefs ops +
  prio \<alpha> invar +
  prio_empty \<alpha> invar empty +
  prio_isEmpty \<alpha> invar isEmpty +
  prio_find \<alpha> invar find +
  prio_insert \<alpha> invar insert +
  prio_meld \<alpha> invar meld +
  prio_delete \<alpha> invar find delete
  for ops
begin
  lemmas correct =
    empty_correct
    isEmpty_correct
    find_correct
    insert_correct
    meld_correct
    delete_correct
end

locale StdPrio_no_invar = StdPrio + prio_no_invar \<alpha> invar

end
