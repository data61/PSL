theory JMM_JVM
imports
  JMM_Framework
  "../JVM/JVMThreaded"
begin

sublocale JVM_heap_base < execd_mthr: 
  heap_multithreaded_base 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    JVM_final "mexecd P" convert_RA
  for P
.

context JVM_heap_base begin

abbreviation JVMd_\<E> ::
  "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> status
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) llist set"
where "JVMd_\<E> P \<equiv> execd_mthr.\<E>_start P JVM_local_start P"

end

end
