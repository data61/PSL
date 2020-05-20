section \<open>Interface for Sets\<close>
theory Imp_Set_Spec
imports "../Sep_Main"
begin
text \<open>
  This file specifies an abstract interface for set data structures. It can
  be implemented by concrete set data structures, as demonstrated in the 
  hash set example.
\<close>

locale imp_set =
  fixes is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  assumes precise: "precise is_set"

locale imp_set_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes empty :: "'s Heap"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_set {}>\<^sub>t"

locale imp_set_is_empty = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_empty :: "'s \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_set s p> is_empty p <\<lambda>r. is_set s p * \<up>(r \<longleftrightarrow> s={})>\<^sub>t"

locale imp_set_memb = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes memb :: "'a \<Rightarrow> 's \<Rightarrow> bool Heap"
  assumes memb_rule[sep_heap_rules]: 
    "<is_set s p> memb a p <\<lambda>r. is_set s p * \<up>(r \<longleftrightarrow> a \<in> s)>\<^sub>t"

locale imp_set_ins = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes ins :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes ins_rule[sep_heap_rules]: 
    "<is_set s p> ins a p <is_set (Set.insert a s)>\<^sub>t"
    
locale imp_set_delete = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes delete :: "'a \<Rightarrow> 's \<Rightarrow> 's Heap"
  assumes delete_rule[sep_heap_rules]: 
    "<is_set s p> delete a p <is_set (s - {a})>\<^sub>t"

locale imp_set_size = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes size :: "'s \<Rightarrow> nat Heap"
  assumes size_rule[sep_heap_rules]: 
    "<is_set s p> size p <\<lambda>r. is_set s p * \<up>(r = card s)>\<^sub>t"

locale imp_set_iterate = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_it :: "'a set \<Rightarrow> 's \<Rightarrow> 'a set \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'s \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> ('a\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_set s p> it_init p <is_it s p s>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: "s'\<noteq>{} \<Longrightarrow> 
    <is_it s p s' it> 
      it_next it 
    <\<lambda>(a,it'). is_it s p (s' - {a}) it' * \<up>(a \<in> s')>"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it s p s' it> it_has_next it <\<lambda>r. is_it s p s' it * \<up>(r\<longleftrightarrow>s'\<noteq>{})>"
  assumes quit_iteration:
    "is_it s p s' it \<Longrightarrow>\<^sub>A is_set s p * true"

end
