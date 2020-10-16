section \<open>Interface for Maps\<close>
theory Imp_Map_Spec
imports "../Sep_Main"
begin
text \<open>
  This file specifies an abstract interface for map data structures. It can
  be implemented by concrete map data structures, as demonstrated in the 
  hash map example.
\<close>

locale imp_map = 
  fixes is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  assumes precise: "precise is_map"

locale imp_map_empty = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes empty :: "'m Heap"
  assumes empty_rule[sep_heap_rules]: "<emp> empty <is_map Map.empty>\<^sub>t"

locale imp_map_is_empty = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes is_empty :: "'m \<Rightarrow> bool Heap"
  assumes is_empty_rule[sep_heap_rules]: 
    "<is_map m p> is_empty p <\<lambda>r. is_map m p * \<up>(r \<longleftrightarrow> m=Map.empty)>\<^sub>t"

locale imp_map_lookup = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes lookup :: "'k \<Rightarrow> 'm \<Rightarrow> ('v option) Heap"
  assumes lookup_rule[sep_heap_rules]: 
    "<is_map m p> lookup k p <\<lambda>r. is_map m p * \<up>(r = m k)>\<^sub>t"

locale imp_map_update = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes update :: "'k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm Heap"
  assumes update_rule[sep_heap_rules]: 
    "<is_map m p> update k v p <is_map (m(k \<mapsto> v))>\<^sub>t"
    
locale imp_map_delete = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes delete :: "'k \<Rightarrow> 'm \<Rightarrow> 'm Heap"
  assumes delete_rule[sep_heap_rules]: 
    "<is_map m p> delete k p <is_map (m |` (-{k}))>\<^sub>t"

locale imp_map_add = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes add :: "'m \<Rightarrow> 'm \<Rightarrow> 'm Heap"
  assumes add_rule[sep_heap_rules]: 
    "<is_map m p * is_map m' p'> add p p' 
     <\<lambda>r. is_map m p * is_map m' p' * is_map (m ++ m') r>\<^sub>t"


locale imp_map_size = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes size :: "'m \<Rightarrow> nat Heap"
  assumes size_rule[sep_heap_rules]: 
    "<is_map m p> size p <\<lambda>r. is_map m p * \<up>(r = card (dom m))>\<^sub>t"

locale imp_map_iterate = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes is_it :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'m \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> (('k\<times>'v)\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_map s p> it_init p <is_it s p s>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: "m'\<noteq>Map.empty \<Longrightarrow> 
    <is_it m p m' it> 
      it_next it 
    <\<lambda>((k,v),it'). is_it m p (m' |` (-{k})) it' * \<up>(m' k = Some v)>"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it m p m' it> it_has_next it <\<lambda>r. is_it m p m' it * \<up>(r\<longleftrightarrow>m'\<noteq>Map.empty)>"
  assumes quit_iteration:
    "is_it m p m' it \<Longrightarrow>\<^sub>A is_map m p * true"

locale imp_map_iterate' = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes is_it :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> ('k\<times>'v) list \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'m \<Rightarrow> ('it) Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> (('k\<times>'v)\<times>'it) Heap"
  assumes it_init_rule[sep_heap_rules]: 
    "<is_map s p> it_init p <\<lambda>r. \<exists>\<^sub>Al. \<up>(map_of l = s) * is_it s p l r>\<^sub>t"
  assumes it_next_rule[sep_heap_rules]: " 
    <is_it m p (kv#l) it> 
      it_next it 
    <\<lambda>(kv',it'). is_it m p l it' * \<up>(kv'=kv)>"
  assumes it_has_next_rule[sep_heap_rules]: 
    "<is_it m p l it> it_has_next it <\<lambda>r. is_it m p l it * \<up>(r\<longleftrightarrow>l\<noteq>[])>"
  assumes quit_iteration:
    "is_it m p l it \<Longrightarrow>\<^sub>A is_map m p * true"

end
