section \<open>\isaheader{Specification of Unique Priority Queues}\<close>
theory PrioUniqueSpec
imports ICF_Spec_Base
begin

(*@intf PrioUnique
  @abstype ('e \<rightharpoonup> 'a::linorder)
  Priority queues without duplicate elements. This interface defines a
  decrease-key operation.
*)

text \<open>
  We define unique priority queues, where each element may occur at most once.
  We provide operations to get and remove the element with the minimum priority,
  as well as to access and change an elements priority (decrease-key operation).

  Unique priority queues are abstracted to maps from elements to priorities.
\<close>
locale uprio =  
  fixes \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)" 
  fixes invar :: "'s \<Rightarrow> bool"                     

locale uprio_no_invar = uprio +
  assumes invar[simp, intro!]: "\<And>s. invar s"
  
locale uprio_finite = uprio +
  assumes finite_correct: 
  "invar s \<Longrightarrow> finite (dom (\<alpha> s))"

subsection "Basic Upriority Queue Functions"

subsubsection "Empty Queue"
locale uprio_empty = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct: 
  "invar (empty ())" 
  "\<alpha> (empty ()) = Map.empty"

subsubsection "Emptiness Predicate"
locale uprio_isEmpty = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct: 
  "invar s \<Longrightarrow> (isEmpty s) = (\<alpha> s = Map.empty)" 

subsubsection "Find and Remove Minimal Element"
locale uprio_pop = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes pop :: "'s \<Rightarrow> ('e \<times> 'a \<times> 's)"
  assumes pop_correct:
  "\<lbrakk>invar s; \<alpha> s \<noteq> Map.empty; pop s = (e,a,s')\<rbrakk> \<Longrightarrow> 
    invar s' \<and> 
    \<alpha> s' = (\<alpha> s)(e := None) \<and> 
    (\<alpha> s) e = Some a \<and> 
    (\<forall>y \<in> ran (\<alpha> s). a \<le> y)"
begin

  lemma popE: 
    assumes 
    "invar s" 
    "\<alpha> s \<noteq> Map.empty" 
    obtains e a s' where 
    "pop s = (e, a, s')" 
    "invar s'" 
    "\<alpha> s' = (\<alpha> s)(e := None)" 
    "(\<alpha> s) e = Some a" 
    "(\<forall>y \<in> ran (\<alpha> s). a \<le> y)"
    using assms
    apply (cases "pop s")
    apply (drule (2) pop_correct)
    apply blast
    done

end

subsubsection "Insert"
text \<open>
  If an existing element is inserted, its priority will be overwritten.
  This can be used to implement a decrease-key operation.
\<close>
(* TODO: Implement decrease-key generic algorithm, and specify decrease-key operation here! *)
locale uprio_insert = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes insert :: "'s \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's"
  assumes insert_correct: 
  "invar s \<Longrightarrow> invar (insert s e a)"
  "invar s \<Longrightarrow> \<alpha> (insert s e a) = (\<alpha> s)(e \<mapsto> a)" 

subsubsection "Distinct Insert"
text \<open>
  This operation only allows insertion of elements
  that are not yet in the queue.
\<close>
locale uprio_distinct_insert = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes insert :: "'s \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's"
  assumes distinct_insert_correct: 
  "\<lbrakk>invar s; e \<notin> dom (\<alpha> s)\<rbrakk> \<Longrightarrow> invar (insert s e a)"
  "\<lbrakk>invar s; e \<notin> dom (\<alpha> s)\<rbrakk> \<Longrightarrow> \<alpha> (insert s e a) = (\<alpha> s)(e \<mapsto> a)" 


subsubsection "Looking up Priorities"
locale uprio_prio = uprio +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a::linorder)"
  fixes prio :: "'s \<Rightarrow> 'e \<Rightarrow> 'a option"
  assumes prio_correct: 
  "invar s \<Longrightarrow> prio s e = (\<alpha> s) e"


subsection "Record Based Interface"

record ('e, 'a, 's) uprio_ops =
  upr_\<alpha> :: "'s \<Rightarrow> ('e \<rightharpoonup> 'a)" 
  upr_invar :: "'s \<Rightarrow> bool"                 
  upr_empty :: "unit \<Rightarrow> 's"
  upr_isEmpty :: "'s \<Rightarrow> bool"
  upr_insert :: "'s \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's"
  upr_pop :: "'s \<Rightarrow> ('e \<times> 'a \<times> 's)"
  upr_prio :: "'s \<Rightarrow> 'e \<Rightarrow> 'a option"


locale StdUprioDefs =
  fixes ops :: "('e,'a::linorder,'s, 'more) uprio_ops_scheme"
begin
  abbreviation \<alpha> where "\<alpha> == upr_\<alpha> ops"
  abbreviation invar where "invar == upr_invar ops"
  abbreviation empty where "empty == upr_empty ops"
  abbreviation isEmpty where "isEmpty == upr_isEmpty ops"
  abbreviation insert where "insert == upr_insert ops"
  abbreviation pop where "pop == upr_pop ops"
  abbreviation prio where "prio == upr_prio ops"
end

locale StdUprio =  StdUprioDefs ops +
  uprio_finite \<alpha> invar + 
  uprio_empty \<alpha> invar empty + 
  uprio_isEmpty \<alpha> invar isEmpty + 
  uprio_insert \<alpha> invar insert + 
  uprio_pop \<alpha> invar pop + 
  uprio_prio \<alpha> invar prio
  for ops
begin
  lemmas correct = 
    finite_correct 
    empty_correct 
    isEmpty_correct 
    insert_correct 
    prio_correct
end

locale StdUprio_no_invar = StdUprio + uprio_no_invar \<alpha> invar

end
