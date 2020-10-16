section \<open>Interface for Lists\<close>
theory Imp_List_Spec
imports "../Sep_Main"
begin
text \<open>
  This file specifies an abstract interface for list data structures. It can
  be implemented by concrete list data structures, as demonstrated in the open
  and circular singly linked list examples.
\<close>

locale imp_list =
  fixes is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  assumes precise: "precise is_list"
    (*"\<forall>l l'. h\<Turnstile>(is_list l p * F1) \<and>\<^sub>A (is_list l' p * F2) \<longrightarrow> l=l'"*)

locale imp_list_empty = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes empty :: "'l Heap"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_list []>\<^sub>t"

locale imp_list_is_empty = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes is_empty :: "'l \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_list l p> is_empty p <\<lambda>r. is_list l p * \<up>(r \<longleftrightarrow> l=[])>\<^sub>t"

locale imp_list_append = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes append :: "'a \<Rightarrow> 'l \<Rightarrow> 'l Heap"
  assumes append_rule[sep_heap_rules]: 
    "<is_list l p> append a p <is_list (l@[a])>\<^sub>t"

locale imp_list_prepend = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes prepend :: "'a \<Rightarrow> 'l \<Rightarrow> 'l Heap"
  assumes prepend_rule[sep_heap_rules]: 
    "<is_list l p> prepend a p <is_list (a#l)>\<^sub>t"
    
locale imp_list_head = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes head :: "'l \<Rightarrow> 'a Heap"
  assumes head_rule[sep_heap_rules]: 
    "l\<noteq>[] \<Longrightarrow> <is_list l p> head p <\<lambda>r. is_list l p * \<up>(r=hd l)>\<^sub>t"

locale imp_list_pop = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes pop :: "'l \<Rightarrow> ('a\<times>'l) Heap"
  assumes pop_rule[sep_heap_rules]: 
    "l\<noteq>[] \<Longrightarrow> 
      <is_list l p> 
      pop p 
      <\<lambda>(r,p'). is_list (tl l) p' * \<up>(r=hd l)>\<^sub>t"

locale imp_list_rotate = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes rotate :: "'l \<Rightarrow> 'l Heap"
  assumes rotate_rule[sep_heap_rules]: 
    "<is_list l p> rotate p <is_list (rotate1 l)>\<^sub>t"

locale imp_list_reverse = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes reverse :: "'l \<Rightarrow> 'l Heap"
  assumes reverse_rule[sep_heap_rules]: 
    "<is_list l p> reverse p <is_list (rev l)>\<^sub>t"

locale imp_list_iterate = imp_list +
  constrains is_list :: "'a list \<Rightarrow> 'l \<Rightarrow> assn"
  fixes is_it :: "'a list \<Rightarrow> 'l \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'l \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> ('a\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_list l p> it_init p <is_it l p l>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: "l'\<noteq>[] \<Longrightarrow> 
    <is_it l p l' it> 
      it_next it 
    <\<lambda>(a,it'). is_it l p (tl l') it' * \<up>(a=hd l')>"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it l p l' it> 
       it_has_next it 
     <\<lambda>r. is_it l p l' it * \<up>(r\<longleftrightarrow>l'\<noteq>[])>"
  assumes quit_iteration:
    "is_it l p l' it \<Longrightarrow>\<^sub>A is_list l p * true"

end
