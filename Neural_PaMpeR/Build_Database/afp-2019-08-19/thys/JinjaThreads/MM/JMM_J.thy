theory JMM_J
imports
  JMM_Framework
  "../J/Threaded"
begin

sublocale J_heap_base < red_mthr: 
  heap_multithreaded_base 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    "final_expr" "mred P" convert_RA
  for P
.

context J_heap_base begin

abbreviation J_\<E> ::
  "'addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> status 
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) llist set"
where
  "J_\<E> P \<equiv> red_mthr.\<E>_start P J_local_start P"

end

end

