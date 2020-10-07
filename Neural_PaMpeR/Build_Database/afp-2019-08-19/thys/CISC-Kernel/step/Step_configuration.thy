section \<open>Instantiation by a separation kernel with concrete actions \label{sect:instantiation}\<close>

theory Step_configuration
  imports Main
begin

text \<open>
{\em In the previous section, no concrete actions for the step function were given.
The foremost point we want to make by this instantiation is to show 
that we can instantiate the CISK model of the previous section with 
an implementation that, for the step function, as actions, provides
events and interprocess communication (IPC). 
System call invocations that can be interrupted at 
certain interrupt points are split 
into several atomic steps.
A communication interface of events and IPC is less
``trivial'' than it may seem it at a first glance, for example the 
L4 microkernel API {\em only} provided IPC as communication primitive~\cite{Liedtke1995}. 
In particular, the concrete actions illustrate how an application
of the CISK framework can be used to separate policy enforcement from other 
computations unrelated to policy enforcement.

Our separation kernel instantiation also has a notion of {\em partitions}.
A {\em partition} is a logical unit that serves to encapsulate a group of 
CISK threads by, amongst others, enforcing a static
per-partition access control policy to system resources.
In the following instantiation, while the subjects of the step function 
are individual threads, the information flow policy
$ifp$ is defined at the granularity of partitions, which is 
realistic for many separation kernel implementations.

Lastly, 
as a limited manipulation of an access control policy is often needed,
we also provide an invariant for having a dynamic access 
control policy whose maximal closure is bounded by the 
static per-partition access control policy. That the 
dynamic access control policy is a subset of a static
access control policy is expressed by the invariant 
sp\_subset. A use case for this is when you have statically configured
access to files by subjects, but whether a file can 
be read/written also depends on whether the file has been
dynamically opened or not. 
The instantiation provides infrastructure for such an 
invariant on the relation of a dynamic policy to 
a static policy, and shows how the invariant is 
maintained, without modeling any API for an open/close operation.}
\<close>

subsection \<open>Model of a separation kernel configuration\<close>

subsubsection \<open>Type definitions\<close>

text \<open>The separation kernel partitions are considered to be the ``subjects" of the 
    information flow policy @{term ifp}. A file provider is a partition that, via 
    a file API (read/write), provides files to other partitions.
    The configuration statically defines which partitions can act as a file provider 
    and also the access rights (right/write) of other partitions to the files 
    provided by the file provider. 
    Some separation kernels include a management for address spaces (tasks), that may be hierachically structured. Such a task hierarchy is not part of this model.\<close>

typedecl partition_id_t
typedecl thread_id_t

typedecl page_t \<comment> \<open>physical address of a memory page\<close>
typedecl filep_t \<comment> \<open>name of file provider\<close>

datatype obj_id_t =
   PAGE page_t
 | FILEP filep_t 

datatype mode_t =
   READ \<comment> \<open>The subject has right to read from the memory page, from the files served by a file provider.\<close>
 | WRITE \<comment> \<open>The subject has right to write to the memory page, from the files served by a file provider.\<close>
 | PROVIDE \<comment> \<open>The subject has right serve as the file provider. This mode is not used for memory pages or ports.\<close>

subsubsection \<open>Configuration\<close>

text \<open>The information flow policy is implicitly specified by the configuration. The configuration does not contain
  the communication rights between partitions (subjects). However, the rights can be 
  derived from the configuration. For example, if two partitions @{term p} and @{term p'} can
  access a file @{term f}, then @{term p} and @{term p'} can communicate. See below.\<close>

consts
  configured_subj_obj :: "partition_id_t \<Rightarrow> obj_id_t \<Rightarrow> mode_t \<Rightarrow> bool"

text \<open>Each user thread belongs to a partition. The relation is fixed
  at system startup. The configuration specifies how many threads a partition can create,
  but this limit is not part of the model.\<close>

consts
  partition :: "thread_id_t \<Rightarrow> partition_id_t"

end
