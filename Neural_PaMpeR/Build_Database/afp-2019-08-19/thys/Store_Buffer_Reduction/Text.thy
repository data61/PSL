(*<*)
theory Text
imports Variants 
begin
(*>*)
section \<open>Programming discipline \label{sec:discipline}\<close>

text \<open>
For sequential code on a single processor the store buffer is invisible, since reads respect outstanding writes in the buffer. 
This argument can be extended to thread local memory in the context of a multiprocessor architecture. 
Memory typically becomes temporarily thread local by means of locking. 
The C-idiom to identify shared portions of the memory is the \texttt{volatile} 
tag on variables and type declarations. 
Thread local memory can be accessed non-volatilely, whereas accesses to shared memory are tagged as volatile. 
This prevents the compiler from applying certain optimizations to those accesses which could cause undesired behavior, \eg to store intermediate values in registers instead of writing them to the memory.

  The basic idea behind the programming discipline is, that before gathering new information about the shared state (via reading) the thread has to make its outstanding changes to the shared state visible to others (by flushing the store buffer). 
This allows to sequentialize the reads and writes to obtain a sequentially consistent execution of the global system. 
In this sequentialization a write to shared memory happens when the write instruction exits the store buffer, and a read from the shared memory happens when all preceding writes have exited. 

We distinguish thread local and shared memory by an ownership model. 
Ownership is maintained in ghost state and can be transferred as side effect of write operations and by a dedicated ghost operation.
Every thread has a set of owned addresses. Owned addresses of different threads are disjoint. 
Moreover, there is a global set of shared addresses which can additionally be marked as read-only. 
Unowned addresses --- addresses owned by no thread --- can be accessed concurrently by all threads. They are a subset of the shared addresses. The read-only addresses are a subset of the unowned addresses (and thus of the shared addresses).
We only allow a thread to write to owned addresses and unowned, read-write addresses.
We only allow a thread to read from owned addresses and from shared addresses (even if they are owned by another thread).

All writes to shared memory have to be volatile. Reads from shared addresses also have to be volatile, except if the address is owned (\ie single writer, multiple readers) or if the address is read-only. Moreover, non-volatile writes are restricted to owned, unshared memory.
As long as a thread owns an address it is guaranteed that it is the only one writing to that address. Hence this thread can safely perform non-volatile reads to that address without missing any write. Similar it is safe for any thread to access read-only memory via non-volatile reads since there are no outstanding writes at all.


Recall that a volatile read is \Def{clean} if it is guaranteed that there is no outstanding volatile write (to any address) in the store buffer. Moreover every non-volatile read is clean.
To regain sequential consistency under the presence of store buffers every thread has to make sure that every read is clean, by flushing the store buffer when necessary. To check the flushing policy of a thread, we keep track of clean reads by means of ghost state. For every thread we maintain a dirty flag. It is reset as the store buffer gets flushed. Upon a volatile write the dirty flag is set. The dirty flag is considered to guarantee that a volatile read is clean.  



Table \ref{tab:access-grid} summarizes the access policy and Table \ref{tab:flushing} the associated flushing policy of the programming discipline.
The key motivation is to improve performance by minimizing the number of store buffer flushes, 
while staying sequentially consistent.
The need for flushing the store buffer decreases from interlocked accesses (where flushing is a side-effect) over volatile accesses to non-volatile accesses. From the viewpoint of access rights there is no difference between interlocked and volatile accesses. However, keep in mind that some interlocked operations can read from, modify and write to an address in a single atomic step of the underlying hardware and are typically used in lock-free algorithms or for the implementation of locks.



\begin{table}
\centering
\caption{Programming discipline.}
\captionsetup[table]{position=top}
\captionsetup[subtable]{position=top}
\newcommand{\mycomment}[1]{}
\subfloat[Access policy\label{tab:access-grid}]{
\begin{tabular}{m{1.2cm}@ {\hspace{2mm}}m{1.7cm}@ {\hspace{3mm}}m{1.8cm}m{2.2 cm}}
\toprule
               &     shared        &   shared   &  unshared            \\
               &     (read-write)  &   (read-only)   &                 \\
\midrule
unowned        & \mycomment{iRW, iR, iW,} vR, vW         & \mycomment{iR,} vR, R              &  unreachable\\
owned          & \mycomment{iRW, iR, iW,} vR, vW, R      & unreachable            &  \mycomment{iRW, iR, iW,} vR, vW, R, W \\
owned \mbox{by other} & \mycomment{iR,}       vR                & unreachable            &                           \\

\bottomrule
\multicolumn{4}{l}{(v)olatile, (R)ead, (W)rite}\\
\multicolumn{4}{l}{all reads have to be clean }
\end{tabular}
%\caption{Access policy \label{tab:access-grid}}
}\hspace{0.3cm}
%
%\end{table}
%
%\begin{table}
%
\subfloat[Flushing policy\label{tab:flushing}]{
\begin{tabular}{lc}
\toprule
                & flush (before)          \\     
\midrule
interlocked     & as side effect                 \\
vR            & if not clean               \\
R, vW, W           & never                  \\
\bottomrule
\end{tabular}
%\caption{Flushing policy \label{tab:flushing}}
}

\end{table}


\<close>
section \<open>Formalization \label{sec:formalization}\<close>

text \<open>

In this section we go into the details of our formalization. In our model, we distinguish the plain `memory system' from the 
`programming language semantics' which we both describe as a small-step transition relation. 
During a computation the programming language issues memory instructions (read / write) to the memory system, 
which itself returns the results in temporary registers. 
This clean interface allows us to parameterize the program semantics over the 
memory system. Our main theorem allows us to simulate a computation step in the semantics based on a 
memory system with store buffers by @{term "n"} steps in the semantics based on a   
sequentially consistent memory system. 
We refer to the former one as \Def{store buffer machine}  and to the latter one as \Def{virtual machine}. The simulation theorem is independent of the programming language.

We continue with introducing the common parts of both machines. 
In Section \ref{sec:storebuffermachine} we describe the store buffer machine and in Section \ref{sec:virtualmachine} we then describe the virtual machine. The main reduction theorem is presented in \ref{sec:reduction}.

\medskip
Addresses @{term "a"}, values @{term "v"} and temporaries @{term "t"} are natural numbers. 
Ghost annotations for manipulating the ownership information are the following sets of addresses: the acquired addresses @{term "A"}, the unshared (local) fraction @{term "L"} of the acquired addresses, the released addresses @{term "R"} and the writable fraction @{term "W"} of the released addresses (the remaining addresses are considered read-only). 
These ownership annotations are considered as side-effects on volatile writes and interlocked operations (in case a write is performed). 
Moreover, a special ghost instruction allows to transfer ownership.
The possible status changes of an address due to these ownership transfer operations are depicted in Figure \ref{fig:ownership-transfer}. Note that ownership of an address is not directly transferred between threads, but is first released by one thread and then can be acquired by another thread.
%
\begin{figure}
\begin{center}
\begin{tikzpicture}
[auto,
 outernode/.style    = {rectangle, rounded corners, draw, text centered, minimum height=3cm, minimum width=2.7cm, fill=gray!20},
 innernode/.style  = {rectangle, rounded corners, draw, text centered, minimum height=1cm, minimum width=1cm, text width=1.5cm, fill=white}
]
\node[outernode] (owned) {};
\node[innernode] (oshared)  [below] at ($ (owned.north) -(0,0.2cm) $) {shared read-write};
\node[innernode] (onshared) [above] at ($ (owned.south) +(0,0.2cm) $) {unshared};
\node[above] at (owned.north) {owned};

\node[outernode] (unowned) [right] at ($ (owned.east) +(1.5cm,0cm) $) {};
\node[innernode] (rwshared)  [below] at ($ (unowned.north) -(0,0.2cm) $) {shared read-write};
\node[innernode] (roshared) [above] at ($ (unowned.south) +(0,0.2cm) $) {shared read-only};
\node[above] at (unowned.north) {unowned};

\path (rwshared.east) -- coordinate (middlex) (oshared.west);

\draw[->] (owned.east |- rwshared.170) -- (rwshared.170); 
  \node [above] at (rwshared.170 -| middlex) {@{term "R \<inter> W"}};

\draw[->] (unowned.west |- oshared.350) -- (oshared.350);
  \node [below] at (oshared.350 -| middlex) {@{term "A \<inter> - L"}};

\draw[->] (unowned.west |- onshared.350) -- (onshared.350);
  \node [below] at (onshared.350 -| middlex) {@{term "A \<inter> L"}};

\draw[->] (owned.east |- roshared.170) -- (roshared.170);
  \node [above] at (roshared.170 -| middlex) {@{term "R \<inter> - W"}};


\draw[->] (oshared.292) -- node {@{term "A \<inter> L"}} (onshared.68);
\draw[->] (onshared.84) -- node {@{term "A \<inter> - L"}} (oshared.276);

\node (legende) [below right] at (owned.south west) {(A)cquire, keep (L)ocal; (R)elease, mark (W)riteable };
\end{tikzpicture}
\end{center}

\caption{Ownership transfer \label{fig:ownership-transfer}}
\end{figure}
%
A memory instruction is a datatype with the following constructors:
\begin{itemize}
\item @{term "Read volatile a t"} for reading from address @{term "a"} to temporary @{term "t"}, where the Boolean @{term "volatile"} determines whether the access is volatile or not.
\item @{term "Write volatile a sop A L R W"} to write the result of evaluating the store operation @{term "sop"} at address @{term "a"}. A store operation is a pair @{term "(D,f)"}, with the domain @{term "D"} and the function @{term "f"}.
The function @{term "f"} takes temporaries @{term "\<theta>"} as a parameter, which maps a temporary to a value. 
The subset of temporaries that is considered by function @{term "f"} is specified by the domain @{term "D"}.
We consider store operations as valid when they only depend on their domain: 
@{thm [display]"valid_sop_def" [simplified conj_to_impl [symmetric], no_vars]}
Again the Boolean @{term "volatile"} specifies the kind of memory access.
\item @{term "RMW a t sop cond ret A L R W"}, for atomic interlocked `read-modify-write' instructions (flushing the store buffer). First the value at address @{term "a"} is loaded to temporary @{term "t"}, and then the condition @{term "cond"} on the temporaries is considered to decide whether a store operation is also executed. In case of a store the function @{term "ret"}, depending on both the old value at address @{term "a"} and the new value (according to store operation @{term "sop"}), specifies the final result stored in temporary @{term "t"}. With a trivial condition @{term "cond"} this instruction also covers interlocked reads and writes.
\item @{term "Fence"}, a memory fence that flushes the store buffer. %todo: rename to flush?
\item @{term "Ghost A L R W"} for ownership transfer.
\end{itemize}

\<close>

subsection \<open>Store buffer machine \label{sec:storebuffermachine}\<close>

text (in program) \<open>
For the store buffer machine the configuration of a single thread is a tuple @{term "(p, is, \<theta>, sb)"} consisting of the program state @{term "p"}, a memory instruction list @{term "is"}, the map of temporaries @{term "\<theta>"} and the store buffer @{term "sb"}. A global configuration of the store buffer machine @{term "(ts, m)"} consists of a list of thread configurations @{term "ts"} and the memory @{term "m"}, which is a function from addresses to values. 


We describe the computation of the global system by the non-deterministic transition relation @{term "(ts, m, ()) \<Rightarrow>\<^sub>s\<^sub>b (ts', m',())"} defined in Figure~\ref{fig:global-transitions}. 

\begin{figure}[H]
\begin{center}
@{thm [mode=Rule] store_buffer.concurrent_step.Program 
                    [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] store_buffer.concurrent_step.Memop [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()"
                and \<D>'="()" and \<O>'="()" and \<R>'="()" and \<S>'="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] store_buffer.concurrent_step.StoreBuffer [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()" and  \<O>'="()" and \<R>'="()" and \<S>'="()",no_vars]}
\end{center}
\caption{Global transitions of store buffer machine\label{fig:global-transitions}}
\end{figure}

A transition selects a thread @{term "ts!i = (p,is,\<theta>,sb,(),())"} and either the `program' the `memory'  or the `store buffer' makes a step defined by sub-relations. 

The program step relation is a parameter to the global 
transition relation. A program step @{thm (prem 3) "store_buffer.concurrent_step.Program" [no_vars]} takes the temporaries @{term "\<theta>"} and the current program state @{term "p"} and makes a step by returning a new program state @{term "p'"} and an instruction list @{term "is'"} which is appended to the remaining instructions. 

A memory step @{thm (prem 3) "store_buffer.concurrent_step.Memop" [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()"
                and \<D>'="()" and \<O>'="()" and \<R>'="()" and \<S>'="()",no_vars]} of a machine with store buffer may only fill its store buffer with new writes.

In a store buffer step @{thm (prem 3) "store_buffer.concurrent_step.StoreBuffer" [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()" and  \<O>'="()" and \<R>'="()" and \<S>'="()",no_vars]} the store buffer may release outstanding writes to the memory.

The store buffer maintains the list of outstanding memory writes. 
Write instructions are appended to the end of the store buffer and emerge to memory from the front of the list. A read instructions is satisfied from the store buffer if possible. 
An entry in the store buffer is of the form @{term "Write\<^sub>s\<^sub>b volatile a sop v"} for an outstanding write (keeping the volatile flag), where operation @{term "sop"} evaluated to value @{term "v"}.

As defined in Figure \ref{fig:store-buffer-transition} a write updates the memory when it exits the store buffer.
%
\begin{figure}
\begin{center}
@{thm [mode=Axiom] SBWrite\<^sub>s\<^sub>b [where rs=sb and \<O>="()" and \<R>="()" and \<S>="()", no_vars]}\\[0.5\baselineskip]
\end{center}
\caption{Store buffer transition \label{fig:store-buffer-transition}}
\end{figure}
%

The memory transition are defined in Figure \ref{fig:store-buffer-memory}.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] SBRead [where ghst="((),(),(),())",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SBWrite' [where ghst="((),(),(),())",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SBRMWReadOnly' [where ghst="((),(),(),())",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SBRMWWrite' [where ghst="((),(),(),())",no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] sb_memop_step.SBFence [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()",no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] sb_memop_step.SBGhost [where \<D>="()" and \<O>="()" and \<R>="()" and \<S>="()",no_vars]}
\end{center}
\caption{Memory transitions of store buffer machine\label{fig:store-buffer-memory}}
\end{figure}
%
With @{term "buffered_val sb a"} we obtain the value of the last write to address @{term "a"} which is still pending in the store buffer. 
In case no outstanding write is in the store buffer we read from the memory. 
Store operations have no immediate effect on the memory but are queued in the store buffer instead. 
Interlocked operations and the fence operation require an empty store buffer, which means that it has to be flushed before the action can take place. 
The read-modify-write instruction first adds the current value at address @{term "a"} to temporary @{term "t"} and then checks the store condition @{term "cond"} on the temporaries. 
If it fails this read is the final result of the operation. 
Otherwise the store is performed. 
The resulting value of the temporary @{term "t"} is specified by the function @{term "ret"} which considers both the old and new value as input. 
The fence and the ghost instruction are just skipped.



\<close>
subsection \<open>Virtual machine \label{sec:virtualmachine}\<close>
text (in program) \<open>
The virtual machine is a sequentially consistent machine without store buffers, maintaining additional ghost state to check for the programming discipline.
A thread configuration is a tuple @{term "(p, is, \<theta>, (), \<D>, \<O>,())"}, with a dirty flag @{term "\<D>"} indicating whether there may be an outstanding volatile write in the store buffer and the set of owned addresses @{term "\<O>"}. 
The dirty flag @{term "\<D>"} is considered to specify if a read is clean: for \emph{all} volatile reads the dirty flag must not be set.
The global configuration of the virtual machine @{term "(ts, m,\<S>)"} maintains a Boolean map of shared addresses @{term "\<S>"} (indicating write permission).
Addresses in the domain of mapping @{term "\<S>"} are considered shared and the set of read-only addresses is obtained  from @{term "\<S>"} by: @{thm "read_only_def" [no_vars]}

According to the rules in Fig \ref{fig:global-virtual-step} a global transition of the virtual machine 
@{term "(ts, m, \<S>) \<Rightarrow>\<^sub>v (ts', m', \<S>')"} is either a program or a memory step.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] virtual.concurrent_step.Program [where sb="()" and \<R>="()", no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] virtual.concurrent_step.Memop [where sb="()" and sb'="()" and \<R>="()" and \<R>'="()",no_vars]}
\end{center}
\caption{Global transitions of virtual machine \label{fig:global-virtual-step}}
\end{figure}
The transition rules for its memory system are defined in Figure~\ref{fig:virtual-memory}.
%
\begin{figure}
\begin{center}
@{thm [mode=Axiom] VRead [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] VWriteNonVolatile [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] VWriteVolatile [where \<R>="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] VRMWReadOnly [where \<R>="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] VRMWWrite [where \<R>="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] VFence [where \<R>="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] VGhost [where \<R>="()", no_vars]}\\[0.1\baselineskip]
\end{center}
\caption{Memory transitions of the virtual machine \label{fig:virtual-memory}}
\end{figure}
%
In addition to the transition rules for the virtual machine we introduce the \emph{safety} judgment @{term "\<O>s,i\<turnstile> (is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"} in Figure~\ref{fig:safe-virtual-memory}, where @{term "\<O>s"} is the list of ownership sets obtained from the thread list @{term "ts"} and @{term "i"} is the index of the current thread.
Safety of all reachable states of the virtual machine ensures that the programming discipline is obeyed by the program and is our formal prerequisite for the simulation theorem.
It is left as a proof obligation to be discharged by means of a proper program logic for sequentially consistent executions.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] safe_direct_memop_state.Read [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] safe_direct_memop_state.WriteNonVolatile [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeWriteVolatile [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeRMWReadOnly [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeRMWWrite [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] safe_direct_memop_state.Fence [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] safe_direct_memop_state.Ghost [no_vars]}\\[0.1\baselineskip]
\end{center}
\caption{Safe configurations of a virtual machine \label{fig:safe-virtual-memory}}
\end{figure}
%
%
In the following we elaborate on the rules of Figures \ref{fig:virtual-memory} and \ref{fig:safe-virtual-memory} in parallel.
To read from an address it either has to be owned or read-only or it has to be volatile and shared. Moreover the read has to be clean.
%TODO: mention the difference distinction of 'single writer' that covered by this: for 'owned and shared' non-volatile read is ok
The memory content of address @{term "a"} is stored in temporary @{term "t"}. 
%
Non-volatile writes are only allowed to owned and unshared addresses. 
The result is written directly into the memory. 
%
A volatile write is only allowed when no other thread owns the address and the address is not marked as read-only.
Simultaneously with the volatile write we can transfer ownership as specified by the annotations @{term "A"}, @{term "L"}, @{term "R"} and @{term "W"}. 
The acquired addresses @{term "A"} must not be owned by any other thread and stem from the shared addresses or are already owned.
Reacquiring owned addresses can be used to change the shared-status via the set of local addresses @{term "L"} which have to be a subset of @{term "A"}. 
The released addresses @{term "R"} have to be owned and distinct from the acquired addresses @{term "A"}. 
After the write the new ownership set of the thread is obtained by adding the acquired addresses @{term "A"} and releasing the addresses @{term "R"}: @{term "\<O> \<union> A - R"}. The released addresses @{term "R"} are augmented to the shared addresses @{term "S"} and the local addresses @{term "L"} are removed. We also take care about the write permissions in the shared state: the released addresses in set @{term "W"} as well as the acquired addresses are marked writable: @{term "\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"}. The auxiliary ternary operators to augment and subtract addresses from the sharing map are defined as follows:

@{thm [display] augment_shared_def [where S=R, no_vars]}
@{thm [display,margin=80] restrict_shared_def [no_vars]}

The read-modify-write instruction first adds the current value at address @{term "a"} to temporary @{term "t"} and then checks the store condition @{term "cond"} on the temporaries. 
If it fails this read is the final result of the operation. 
Otherwise the store is performed. 
The resulting value of the temporary @{term "t"} is specified by the function @{term "ret"} which considers both the old and new value as input. 
As the read-modify-write instruction is an interlocked operation which flushes the store buffer as a side effect the dirty flag @{term "\<D>"} is reset.
The other effects on the ghost state and the safety sideconditions are the same as for the volatile read and volatile write, respectively.

The only effect of the fence instruction in the system without store buffer is to reset the dirty flag.

The ghost instruction @{term "Ghost A L R W"} allows to transfer ownership when no write is involved \ie when merely reading from memory. It has the same safety requirements as the corresponding parts in the write instructions. 
\<close>

subsection \<open>Reduction \label{sec:reduction}\<close>

text (in xvalid_program_progress) \<open>
The reduction theorem we aim at reduces a computation of a machine with store buffers to a sequential consistent computation of the virtual machine. We formulate this as a
 simulation theorem which states that a computation of the store buffer machine @{term "(ts\<^sub>s\<^sub>b,m,()) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',())"} can be simulated by a computation of the virtual machine @{term "(ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (ts',m',\<S>')"}. 
The main theorem only considers computations that start in an initial configuration where all store buffers are empty and end in a configuration where all store buffers are empty again. A configuration of the store buffer machine is obtained from a virtual configuration by removing all ghost components and assuming empty store buffers. This coupling relation between the thread configurations is written as @{term "ts\<^sub>s\<^sub>b \<sim>\<^sub>d ts"}. Moreover, the precondition  @{term "initial\<^sub>v ts \<S> valid"} ensures that the ghost state of the initial configuration of the virtual machine is properly initialized: the ownership sets of the threads are distinct, an address marked as read-only (according to @{term \<S>}) is unowned and every unowned address is shared. %TODO (ommit): and the instruction lists are empty. 
Finally with @{term [names_short] "safe_reach_virtual_free_flowing (ts,m,S)"} we ensure conformance to the programming discipline by assuming that all reachable configuration in the virtual machine are safe (according to the rules in Figure~\ref{fig:safe-virtual-memory}). 
%
\begin{theorem}[Reduction]\label{thm:reduction}
@{thm [display,   mode=compact, mode=holimplnl, margin=90,names_short]  store_buffer_execution_result_sequential_consistent'_hol [where x="()" and x'="()",no_vars]}
\end{theorem}
%
This theorem captures our intiution that every result that can be obtained from a computation of the store buffer machine can also be obtained by a sequentially consistent computation. However, to prove it we need some generalizations that we sketch in the following sections. First of all the theorem is not inductive as we do not consider arbitrary intermediate configurations but only those where all store buffers are empty. For intermediate confiugrations the coupling relation becomes more involved. The major obstacle is that a volatile read (from memory) can overtake non-volatile writes that are still in the store-buffer and have not yet emerged to memory. Keep in mind that our programming discipline only ensures that no \emph{volatile} writes can be in the store buffer the moment we do a volatile read, outstanding non-volatile writes are allowed. This reordering of operations is reflected in the coupling relation for intermediate configurations as discussed in the following section.
\<close>

section \<open>Building blocks of the proof \label{sec:buildingblocks}\<close>

text (in program) \<open>
A corner stone of the proof is a proper coupling relation between an \emph{intermediate} configuration of a machine with store buffers and the virtual machine without store buffers. 
It allows us to simulate every computation step of the store buffer machine by a sequence of steps (potentially empty) on the virtual machine. 
This transformation is essentially a sequentialization of the trace of the store buffer machine. 
When a thread of the store buffer machine executes a non-volatile operation, it only accesses memory which is not modified by any other thread (it is either owned or read-only). 
Although a non-volatile store is buffered, we can immediately execute it on the virtual machine, as there is no competing store of another thread. 
However, with volatile writes we have to be careful, since concurrent threads may also compete with some volatile write to the same address. 
At the moment the volatile write enters the store buffer we do not yet know when it will be issued to memory and how it is ordered relatively to other outstanding writes of other threads.
We therefore have to suspend the write on the virtual machine from the moment it enters the store buffer to the moment it is issued to memory.
For volatile reads our programming discipline guarantees that there is no volatile write in the store buffer by flushing the store buffer if necessary. 
So there are at most some outstanding non-volatile writes in the store buffer, which are already executed on the virtual machine, as described before.
One simple coupling relation one may think of is to suspend the whole store buffer as not yet executed intructions of the virtual machine. However, consider the following scenario. A thread is reading from a volatile address. 
It can still have non-volatile writes in its store buffer. 
Hence the read would be suspended in the virutal machine, and other writes to the address (e.g. interlocked or volatile writes of another thread) could invalidate the value.
Altogether this suggests the following refined coupling relation: the state of the virtual machine is obtained from the state of the store buffer machine, by executing each store buffer until we reach the first volatile write. 
The remaining store buffer entries are suspended as instructions. As we only execute non volatile writes the order in which we execute the store buffers should be irrelevant.
This coupling relation allows a volatile read to be simulated immediately on the virtual machine as it happens on the store buffer machine. 
 
From the viewpoint of the memory the virtual machine is ahead of the store buffer machine, as leading non-volatile writes already took effect on the memory of the virtual machine while they are still pending in the store buffer. 
However, if there is a volatile write in the store buffer the corresponding thread in the virtual machine is suspended until the write leaves the store buffer. 
So from the viewpoint of the already executed instructions the store buffer machine is ahead of the virtual machine. To keep track of this delay we introduce a variant of the store buffer machine below, which maintains the history of executed instructions in the store buffer (including reads and program steps). Moreover, the intermediate machine also maintains the ghost state of the virtual machine to support the coupling relation. We also introduce a refined version of the virutal machine below, which we try to motivate now.
Esentially the programming discipline only allows races between volatile (or interlocked) operations. By race we mean two competing memory accesses of different threads of which at least one is a write. 
For example the discipline guarantees that a volatile read may not be invalidated by a non-volatile write of another thread. 
While proving the simulation theorem this manifests in the argument that a read of the store-buffer machine and the virtual machine sees the same value in both machines: the value seen by a  read in the store buffer machine stays valid as long as it has not yet made its way out in the virtual machine. 
To rule out certain races from the execution traces we make use of the programming discipline, which is formalized in the safety of all reachable configurations of the virtual machine. Some races can be ruled out by continuing the computation of the virtual machine until we reach a safety violation. 
However, some cannot be ruled out by the future computation of the current trace, but can be invalidated by a safety violation of another trace that deviated from the current one at some point in the past. Consider two threads. 
Thread 1 attempts to do a volatile read from address @{term a} which is currently owned (and not shared) by thread 2, which attempts to do a non-volatile write on @{term a} with value @{term "42::nat"} and then release the address. 
In this configuration there is already a safety violation. Thread 1 is not allowed to perform a volatile read from an address that is not shared. 
However, when Thread 2 has executed his update and has released ownership (both are non-volatile operations) there is no safety violation anymore. 
Unfortunately this is the state of the virtual machine when we consider the instructions of Thread 2 to be in the store buffer. The store buffer machine and the virtual machine are out of sync. 
Whereas in the virtual machine Thread 1 will already read @{term "42::nat"} (all non-volatile writes are already executed in the virtual machine), the non-volatile write may still be pending in the store buffer of Thread 2 and hence Thread 1 reads the old value in the store buffer machine.
This kind of issues arise when a thread has released ownership in the middle of non-volatile operations of the virtual machine, but the next volatile write of this thread has not yet made its way out of the store buffer. 
When another thread races for the released address in this situation there is always another scheduling of the virtual machine where the release has not yet taken place and we get a safety violation. 
To make these safety violations visible until the next volatile write we introduce another ghost component that keeps track of the released addresses. 
It is augmented when an ghost operation releases an address and is reset as the next volatile write is reached.
Moreover, we refine our rules for safety to take these released addresses into account. 
For example, a write to an released address of another thread is forbidden. 
We refer to these refined model as \emph{delayed releases} (as no other thread can acquire the address as long as it is still in the set of released addresses) and to our original model as \emph{free flowing releases} (as the effect of a release immediate takes place at the point of the ghost instruction). 
Note that this only affects ownership transfer due to the @{term Ghost} instruction. 
Ownership transfer together with volatile (or interlocked) writes happen simultaneously in both models.

Note that the refined rules for delayed releases are just an intermediate step in our proof. 
They do not have to be considered for the final programming discipline. As sketched above we can show in a separate theorem that a safety violation in a trace with respect to delayed releases implies a safety violation of a (potenitally other) trace with respect to free flowing releases. Both notions of safety collaps in all configurations where there are no released addresses, like the initial state. So if all reachable configurations are safe with respect to free flowing releases they are also safe with respect to delayed releases. This allows us to use the stricter policy of delayed releases for the simulation proof.
Before continuing with the coupling relation, we introduce the refined intermediate models for delayed releases and store buffers with history information. 

\<close>

subsection \<open>Intermediate models\<close>

text (in program) \<open>
We begin with the virtual machine with delayed releases, for which the memory transitions 
@{term "(is,\<theta>,(),m,\<D>,\<O>,\<R>,\<S>) \<rightarrow> (is',\<theta>',(),m',\<D>',\<O>',\<R>',\<S>')"}
are defined Figure \ref{fig:virtual-delayed-memory}.
%
\begin{figure}
\begin{center}
@{thm [mode=Axiom] DRead [where x="()",no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] DWriteNonVolatile [where x="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule,names_short] DWriteVolatile [where x="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule,names_short] DRMWReadOnly [where x="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule,names_short] DRMWWrite [where x="()",no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom,names_short] direct_memop_step.Fence [where x="()",no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] DGhost [where x="()",no_vars]}\\[0.1\baselineskip]
\end{center}
\caption{Memory transitions of the virtual machine with delayed releases\label{fig:virtual-delayed-memory}}
\end{figure}
%
The additional ghost component @{term "\<R>"} is a mapping from addresses to a Boolean flag. If an address is in the domain of @{term \<R>} it was released. The boolean flag is considered to figure out if the released address was previously shared or not. In case the flag is @{term True} it was shared otherwise not. This subtle distinction is necessary to properly handle volatile reads. A volatile read from an address owned by another thread is fine as long as it is marked as shared. The released addresses @{term \<R>} are reset at every volatile write as well as interlocked operations and the fence instruction. They are augmented at the ghost instruction taking the sharing information into account:

@{thm [display] augment_rels_def [where S="dom \<S>", no_vars]}

If an address is freshly released (@{term "a \<in> R"} and @{term "\<R> a = None"}) the flag is set according to @{term "dom \<S>"}. Otherwise the flag becomes @{term "Some False"} in case the released address is currently unshared.
Note that with this definition @{term "\<R> a = Some False"} stays stable upon every new release and we do not loose information about a release of an unshared address.

The global transition @{term "(ts, m, s) \<Rightarrow>\<^sub>d (ts',m',s')"} are analogous to the rules in Figure \ref{fig:global-virtual-step} replacing the memory transtions with the refined version for delayed releases.

The safety judgment for delayed releases @{term "\<O>s,\<R>s,i\<turnstile> (is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"} is defined in Figure \ref{fig:safe-delayed}. Note the additional component @{term \<R>s} which is the list of release maps of all threads.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] safe_delayed_direct_memop_state.Read [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] safe_delayed_direct_memop_state.WriteNonVolatile [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeDelayedWriteVolatile [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeDelayedRMWReadOnly [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SafeDelayedRMWWrite [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] safe_delayed_direct_memop_state.Fence [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] safe_delayed_direct_memop_state.Ghost [no_vars]}\\[0.1\baselineskip]
@{thm [mode=Rule] safe_delayed_direct_memop_state.Nil [no_vars]}\\[0.1\baselineskip]
\end{center}
\caption{Safe configurations of a virtual machine (delayed-releases) \label{fig:safe-delayed}}
\end{figure}
%
The rules are strict extensions of the rules in Figure \ref{fig:safe-virtual-memory}: writing or acquiring an address @{term a} is only allowed if the address is not in the release set of another thread (@{term "a \<notin> dom (\<R>s!j)"}); reading from an address is only allowed if it is not released by another thread while it was unshared (@{term "(\<R>s!j) a \<noteq> Some False"}). 

For the store buffer machine with history information we not only put writes into the store buffer but also record reads, program steps and ghost operations. 
This allows us to restore the necessary computation history of the store buffer machine and relate it to the virtual machine which may fall behind the store buffer machine during execution. 
Altogether an entry in the store buffer is either a
\begin{itemize}
\item @{term "Read\<^sub>s\<^sub>b volatile a t v"}, recording a corresponding read from address @{term "a"} which loaded the value @{term "v"} to temporary @{term "t"}, or a 
\item @{term "Write\<^sub>s\<^sub>b volatile a sop v"} for an outstanding write, where operation @{term "sop"} evaluated to value @{term "v"}, or of the form

\item @{term "Prog\<^sub>s\<^sub>b p p' is'"}, recording a program transition from @{term "p"} to @{term "p'"} which issued instructions @{term "is'"}, or of the form
\item @{term "Ghost\<^sub>s\<^sub>b A L R W"}, recording a corresponding ghost operation.
\end{itemize}
As defined in Figure \ref{fig:store-buffer-transitions} a write updates the memory when it exits the store buffer, all other store buffer entries may only have an effect on the ghost state. The effect on the ownership information is analogous to the corresponding operations in the virtual machine.
%
\begin{figure}
\begin{center}
@{thm [mode=Axiom] Write\<^sub>s\<^sub>bNonVolatile [where rs=sb, no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule, names_short] Write\<^sub>s\<^sub>bVolatile [where rs=sb,  no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] flush_step.Read\<^sub>s\<^sub>b [where rs=sb, no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] flush_step.Prog\<^sub>s\<^sub>b [where rs=sb, no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] Ghost\<^sub>s\<^sub>b [where rs=sb, no_vars]} 
\end{center}
\caption{Store buffer transitions with history\label{fig:store-buffer-transitions}}
\end{figure}
%
The memory transitions defined in Figure \ref{fig:store-buffer-history-memory} are straightforward extensions 
of the store buffer transitions of Figure \ref{fig:store-buffer-history-memory} augmented with ghost state 
and recording history information in the store buffer. Note how we deal with the ghost state. 
Only the dirty flag is updated when the instruction enters the store buffer, the ownership transfer 
takes effect when the instruction leaves the store buffer.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] SBHRead [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SBHWriteNonVolatile' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] SBHWriteVolatile' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule,names_short] SBHRMWReadOnly' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule,names_short] SBHRMWWrite' [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom,names_short] sbh_memop_step.SBHFence [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] SBHGhost' [no_vars]}
\end{center}
\caption{Memory transitions of store buffer machine with history\label{fig:store-buffer-history-memory}}
\end{figure}
%
The global transitions @{term "(ts\<^sub>s\<^sub>b\<^sub>h, m, \<S>) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h (ts\<^sub>s\<^sub>b\<^sub>h',m',\<S>')"} are analogous to the rules in Figure \ref{fig:global-transitions} replacing the memory transtions and store buffer transtiontions accordingly.
\<close>

subsection \<open>Coupling relation \label{sec:couplingrelation}\<close>

text (in program) \<open>
After this introduction of the immediate models we can proceed to the details of the coupling relation, which relates configurations of the store buffer machine with histroy and the virtual machine with delayed releases.
Remember the basic idea of the coupling relation: the state of the virtual machine is obtained from the state of the store buffer machine, by executing each store buffer until we reach the first volatile write. The remaining store buffer entries are suspended as instructions. The instructions now also include the history entries for reads, program steps and ghost operations.
The suspended reads are not yet visible in the temporaries of the virtual machine. 
Similar the ownership effects (and program steps) of the suspended operations are not yet visible in the virtual machine.
The coupling relation between the store buffer machine and the virtual machine is illustrated in Figure~\ref{fig:coupling-relation-pic}. The threads issue instructions to the store buffers from the right and the instructions emerge from the store buffers to main memory from the left. The dotted line illustrates the state of the virtual machines memory. It is obtained from the memory of the store buffer machine by executing the purely non-volatile prefixes of the store buffers. The remaining entries of the store buffer are still (suspended) instructions in the virtual machine.

\begin{figure}
\centering
\begin{tikzpicture}
\tikzstyle{sbnodel}=[shape=rectangle, draw=black, text badly centered,  outer sep=0cm]
\tikzstyle{sbnoder}=[shape=rectangle, draw=black, text ragged, outer sep=0cm]
\tikzstyle{nonvolatile}=[fill=gray!10]
\tikzstyle{virtual}=[dotted]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Store buffers and instructions %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\node (sbl0) [style=sbnodel,style=nonvolatile,text width=1.3cm] {nv};
\node (sbr0) [style=sbnoder,text width=1.7cm, right] at(sbl0.east) {v};
\node (ins0) [right] at ($ (sbr0.east) $) {thread $0$: $i_0^0$, $i_0^1$, $\dots$};

\node (sbl1) [style=sbnodel,style=nonvolatile,text width=2.0cm,below right] at ($ (sbl0.south west) -(0,0.6cm) $) {nv};
\node (sbr1) [style=sbnoder,text width=1.0cm, right] at(sbl1.east) {v};
\node (ins1) [right] at ($ (sbr1.east) $) {thread $i$: $i_i^0$, $i_i^1$, $\dots$};


\node (sbl2) [style=sbnodel,style=nonvolatile,text width=1.7cm,below right] at ($ (sbl1.south west) -(0,0.6cm) $) {nv};
\node (sbr2) [style=sbnoder,text width=1.3cm, right] at(sbl2.east) {v};
\node (ins2) [right] at ($ (sbr2.east) $) {thread $j$: $i_j^0$, $i_j^1$, $\dots$};

\node (sbl3) [style=sbnodel,style=nonvolatile,text width=1.4cm,below right] at ($ (sbl2.south west) -(0,0.6cm) $) {nv};
\node (sbr3) [style=sbnoder,text width=1.6cm, right] at(sbl3.east) {v};
\node (ins3) [right] at ($ (sbr3.east) $) {thread $n$: $i_n^0$, $i_n^1$, $\dots$};

\path (sbr1.north east) to node [near end,left] {$\vdots$} (sbr0.south east);
\path (sbr2.north east) to node [near end,left] {$\vdots$} (sbr1.south east);
\path (sbr3.north east) to node [near end,left] {$\vdots$} (sbr2.south east);

\node (sblabel)[above]  at ($ (sbr0.north west) +(0,0.6cm)$) {$\leftarrow$ store buffers};
\node (inslabel)[above]  at ($ (sbr0.north east) +(1.5cm,0.6cm)$) {$\leftarrow$ instructions};

%%%%%%%%%%
% Memory %
%%%%%%%%%%
\coordinate (memNorthWest) at ($ (sbl0.north west) -(2.0cm,0cm) $);
\coordinate (memSouthEast) at ($ (sbl3.south west) -(0.5cm,0cm) $);
\filldraw[style=nonvolatile,rounded corners]  (memNorthWest) rectangle  (memSouthEast) node [midway] {@{term "m\<^sub>s\<^sub>b\<^sub>h"}};

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Virtual memory boundaries %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\draw [style=virtual,out=90,in=-90](sbr1.north west) to (sbr0.south west);
\draw [style=virtual,out=90,in=-90](sbr2.north west) to (sbr1.south west);
\draw [style=virtual,out=90,in=-90](sbr3.north west) to (sbr2.south west);

\draw [style=virtual] ($ (memNorthWest) +(0,0.4cm) $) to ($ (sbr0.north west) + (-0.3,0.4)$)[out=0,in=90] to ($ (sbr0.north west)$);
\draw [style=virtual]($ (memNorthWest |- memSouthEast) +(0,-0.8cm) $) to node[midway,above]{@{term m}} ($ (sbr3.south west) + (-0.3,-0.8)$)[out=0,in=90]
  to ($ (sbr3.south west)$);

\node (execslabel)[below]  at ($ (sbl3.south)$) {executed};
\node (suspendslabel)[below]  at ($ (sbr3.south)$) {suspended};

\end{tikzpicture}

\caption{Illustration of coupling relation \label{fig:coupling-relation-pic}}
\end{figure}


Consider the following configuration of a thread @{term "ts\<^sub>s\<^sub>b\<^sub>h ! j"} in the store buffer machine, where @{term "i\<^sub>k"} are the instructions and @{term "s\<^sub>k"} the store buffer entries. 
Let @{term "s\<^sub>v"} be the first volatile write in the store buffer. 
Keep in mind that new store buffer entries are appended to the end of the list and entries exit the store buffer and are issued to memory from the front of the list.
%
\begin{center} 
@{term "ts\<^sub>s\<^sub>b\<^sub>h ! j = (p,[i\<^sub>1,\<dots>,i\<^sub>n], \<theta>, [s\<^sub>1,\<dots>,s\<^sub>v,s\<^sub>\<vv>,\<dots>,s\<^sub>m], \<D>, \<O>, \<R>)"}
\end{center} 
%
The corresponding configuration @{term "ts ! j"} in the virtual machine is obtained by suspending all store buffer entries beginning at @{term "s\<^sub>v"} to the front of the instructions. 
A store buffer @{term "Read\<^sub>s\<^sub>b"} / @{term "Write\<^sub>s\<^sub>b"} / @{term "Ghost\<^sub>s\<^sub>b"} is converted to a  @{term "Read"} / @{term "Write"} / @{term "Ghost"} instruction. 
We take the freedom to make this coercion implicit in the example. 
The store buffer entries preceding @{term "s\<^sub>v"} have already made their way to memory, whereas the suspended read operations are not yet visible in the temporaries @{term "\<theta>'"}. Similar, the suspended updates to the ownership sets and dirty flag are not yet recorded in @{term "\<O>'"}, @{term "\<R>'"} and @{term "\<D>'"}.
%
\begin{center} 
@{term "ts ! j =(p,[s\<^sub>v,s\<^sub>\<vv>,\<dots>,s\<^sub>m,i\<^sub>1,\<dots>,i\<^sub>n], \<theta>', (), \<D>', \<O>',\<R>')"}
\end{center} 
%
This example illustrates that the virtual machine falls behind the store buffer machine in our simulation, as store buffer instructions are suspended and reads (and ghost operations) are delayed and not yet visible in the temporaries (and the ghost state).
This delay can also propagate to the level of the programming language, which communicates with the memory system by reading the temporaries and issuing new instructions. 
For example the control flow can depend on the temporaries, which store the result of branching conditions. 
It may happen that the store buffer machine already has evaluated the branching condition by referring to the values in the store buffer, whereas the virtual machine still has to wait. 
Formally this manifests in still undefined temporaries. 
Now consider that the program in the store buffer machine makes a step from @{term "p"} to @{term "(p',is')"}, which results in a thread configuration where the program state has switched to @{term "p'"}, the instructions @{term "is'"} are appended and the program step is recorded in the store buffer:
%
\begin{center} 
@{term "ts\<^sub>s\<^sub>b\<^sub>h' ! j = (p',[i\<^sub>1,\<dots>,i\<^sub>n]@is', \<theta>, [s\<^sub>1,\<dots>,s\<^sub>v,\<dots>,s\<^sub>m,Prog\<^sub>s\<^sub>b p p' is'], \<D>, \<O>, \<R>)"}
\end{center} 
%
The virtual machine however makes no step, since it still has to evaluate the suspended instructions before making the program step. 
The instructions @{term "is'"} are not yet issued and the program state is still @{term "p"}. 
We also take these program steps into account in our final coupling relation @{thm (concl) sim_config' [no_vars]}, defined in Figure~\ref{fig:coupling-relation}.
%
\begin{figure}
\begin{center}
\begin{minipage}{10cm}
\inferrule{@{thm (prem 1) sim_config' [no_vars]}\\
           @{thm (prem 2) sim_config' [no_vars]}\\
           @{thm (prem 3) sim_config' [no_vars]}\\
           \parbox{9.8cm}{@{thm [break,mode=letnl,margin=80] (prem 4) sim_config' [simplified restrict_map_inverse, no_vars]}}}
%
          {@{thm (concl) sim_config' [no_vars]}}
\end{minipage}
\end{center}
\caption{Coupling relation \label{fig:coupling-relation}}
\end{figure}
% 
We denote the already simulated store buffer entries by @{term "Bind execs. execs"} and the suspended ones by @{term "Bind suspends. suspends"}.
The function @{term "instrs"} converts them back to instructions, which are a prefix of the instructions of the virtual machine. 
We collect the additional instructions which were issued by program instructions but still recorded in the remainder of the store buffer with function @{term "prog_instrs"}. 
These instructions have already made their way to the instructions of the store buffer machine but not yet on the virtual machine. 
This situation is formalized as @{term "Bind suspends is\<^sub>s\<^sub>b\<^sub>h is. instrs suspends @ is\<^sub>s\<^sub>b\<^sub>h = is @ prog_instrs suspends"}, where @{term "Bind is. is"} are the instructions of the virtual machine. 
The program state of the virtual machine is either the same as in the store buffer machine or the first program state recorded in the suspended part of the store buffer.
This state is selected by @{const "hd_prog"}. 
The temporaries of the virtual machine are obtained by removing the suspended reads from @{term "\<theta>"}. 
The memory is obtained by executing all store buffers until the first volatile write is hit, excluding it. Thereby only non-volatile writes are executed, which are all thread local, and hence could be executed in any order with the same result on the memory. Function @{const "flush_all_until_volatile_write"} executes them in order of appearance.
Similarly the sharing map of the virtual machine is obtained by executing all store buffers until the first volatile write via the function @{const "share_all_until_volatile_write"}. For the local ownership set @{term "\<O>\<^sub>s\<^sub>b\<^sub>h"} the auxiliary function @{term "acquire"} calculates the outstanding effect of the already simulated parts of the store buffer. Analogously @{term "release"} calculates the effect for the released addresses @{term "\<R>\<^sub>s\<^sub>b\<^sub>h"}.


\<close>

subsection \<open>Simulation \label{sec:simulation}\<close>

text (in xvalid_program_progress) \<open>
Theorem \ref{thm:simulation} is our core inductive simulation theorem. 
Provided that all reachable states of the virtual machine (with delayed releases) are safe, a step of the store buffer machine (with history) can be simulated by a (potentially empty) sequence of steps on the virtual machine, maintaining the coupling relation and an invariant on the configurations of the store buffer machine.
%
\begin{theorem}[Simulation]\label{thm:simulation}
@{thm [display,  mode=holimplnl,margin=100]  simulation_hol [no_vars]}
\end{theorem}
%
In the following we discuss the invariant @{term [names_short] "invariant ts\<^sub>s\<^sub>b\<^sub>h S\<^sub>s\<^sub>b\<^sub>h m\<^sub>s\<^sub>b\<^sub>h"}, where we commonly refer to a thread configuration @{term "ts\<^sub>s\<^sub>b\<^sub>h!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"} for @{term "i < length ts\<^sub>s\<^sub>b\<^sub>h"}. 
By outstanding references we refer to read and write operations in the store buffer. 
The invariant is a conjunction of several sub-invariants grouped by their content:

@{thm [display, names_short, mode=compact, margin=100] invariant_grouped_def [of ts\<^sub>s\<^sub>b\<^sub>h S\<^sub>s\<^sub>b\<^sub>h m\<^sub>s\<^sub>b\<^sub>h]}
%TODO make grouping formally, hide program step in valid_history

\paragraph{Ownership.} 
\begin{inparaenum}
\item \label{inv-ownership:owned-or-read-only} For every thread all outstanding non-volatile references have to be owned or refer to read-only memory.
\item Every outstanding volatile write is not owned by any other thread. 
\item Outstanding accesses to read-only memory are not owned.
\item \label{inv-ownership:distinct-ownership} The ownership sets of every two different threads are distinct.
\end{inparaenum}

\paragraph{Sharing.}
\begin{inparaenum}
\item \label{inv-sharing:non-volatile-writes-unshared} All outstanding non volatile writes are unshared. 
\item All unowned addresses are shared.
\item No thread owns read-only memory.
\item The ownership annotations of outstanding ghost and write operations are consistent (\eg released addresses are owned at the point of release).
\item \label{inv-sharing:no-write-to-read-only-memory} There is no outstanding write to read-only memory.
\end{inparaenum}

\paragraph{Temporaries.} Temporaries are modeled as an unlimited store for temporary registers. We require certain distinctness and freshness properties for each thread.
\begin{inparaenum}
\item The temporaries referred to by read instructions are distinct.
\item The temporaries referred to by reads in the store buffer are distinct.
\item Read and write temporaries are distinct.
\item Read temporaries are fresh, \ie are not in the domain of @{term "\<theta>"}.
\end{inparaenum}

\paragraph{Data dependency.} Data dependency means that store operations may only depend on \emph{previous} read operations. For every thread we have:
\begin{inparaenum}
\item Every operation @{term "(D, f)"} in a write instruction or a store buffer write is valid according to @{term "valid_sop (D, f)"}, \ie function @{term "f"} only depends on domain @{term "D"}.
\item For every suffix of the instructions of the form @{term "Write volatile a (D,f) A L R W#is"} the domain @{term "D"} is distinct from the temporaries referred to by future read instructions in @{term "is"}.
\item The outstanding writes in the store buffer do not depend on the read temporaries still in the instruction list.
\end{inparaenum}

\paragraph{History.} The history information  of program steps and  read operations we record in the store buffer have to be consistent with the trace. For every thread:
\begin{inparaenum}
\item The value stored for a non volatile read is the same as the last write to the same address in the store buffer or the value in memory, in case there is no write in the buffer. 
\item All reads have to be clean. This results from our flushing policy. Note that the value recorded for a volatile read in the initial part of the store buffer (before the first volatile write), may become stale with respect to the memory. Remember that those parts of the store buffer are already executed in the virtual machine and thus cause no trouble.
\item For every read the recorded value coincides with the corresponding value in the temporaries.
\item For every @{term "Write\<^sub>s\<^sub>b volatile a (D,f) v A L R W"} the recorded value @{term "v"} coincides with @{term "f \<theta>"}, and domain @{term "D"} is subset of @{term "dom \<theta>"} and is distinct from the following read temporaries. Note that the consistency of the ownership annotations is already covered by the aforementioned invariants.
\item For every suffix in the store buffer of the form @{term "Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 is'#sb'"}, either @{term "p\<^sub>1 = p"} in case there is no preceding program node in the buffer or it corresponds to the last program state recorded there. 
Moreover, the program transition @{term "\<theta>|`(- read_tmps sb')\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2,is')"} is possible, \ie it was possible to execute the program transition at that point.
\item The program configuration @{term "p"} coincides with the last program configuration recorded in the store buffer.
\item As the instructions from a program step are at the one hand appended to the instruction list and on the other hand recorded in the store buffer, we have for every suffix @{term "sb'"} of the store buffer: @{term "\<exists>is'. instrs sb' @ is = is' @ prog_instrs sb'"}, \ie the remaining instructions @{term "is"} correspond to a suffix of the recorded instructions @{term "prog_instrs sb'"}.
\end{inparaenum}

\paragraph{Flushes.} If the dirty flag is unset there are no outstanding volatile writes in the store buffer.

\paragraph{Program step.} The program-transitions are still a parameter of our model. 
In order to make the proof work, we have to assume some of the invariants also for the program steps. 
We allow the program-transitions to employ further invariants on the configurations, these are modeled by the parameter @{term "valid"}. 
For example, in the instantiation later on the program keeps a counter for the temporaries, for each thread. 
We maintain distinctness of temporaries by restricting all temporaries occurring in the memory system to be below that counter, which is expressed by instantiating @{term "valid"}. 
Program steps, memory steps and store buffer steps have to maintain @{term "valid"}. 
Furthermore we assume the following properties of a program step:
\begin{inparaenum}
\item The program step generates fresh, distinct read temporaries, that are neither in @{term "\<theta>"} nor in the store buffer temporaries of the memory system.
\item The generated memory instructions respect data dependencies, and are valid according to @{term "valid_sop"}.

%TODO: maybe we can omit the formal stuff, intuition should be clear, depends on what we write on PIMP.
\end{inparaenum}

\paragraph{Proof sketch.} We do not go into details but rather first sketch the main arguments for simulation of a step in the store buffer machine by a potentially empty sequence of steps in the virtual machine, maintaining the coupling relation. Second we exemplarically focus on some cases to illustrate common arguments in the proof.
The first case distinction in the proof is on the global transitions in Figure~\ref{fig:global-transitions}. 
%
\begin{inparaenum}
\item \emph{Program step}: 
we make a case distinction whether there is an outstanding volatile write in the store buffer or not. 
If not the configuration of the virtual machine corresponds to the executed store buffer and we can make the same step. 
Otherwise the virtual machine makes no step as we have to wait until all volatile writes have exited the store buffer.
%
\item \emph{Memory step}: 
we do case distinction on the rules in Figure~\ref{fig:store-buffer-history-memory}. 
For read, non volatile write and ghost instructions we do the same case distinction as for the program step. 
If there is no outstanding volatile write in the store buffer we can make the step, otherwise we have to wait. 
When a volatile write enters the store buffer it is suspended until it exists the store buffer. Hence we do no step in the virtual machine.
The read-modify-write and the fence instruction can all be simulated immediately since the store buffer has to be empty.
%
\item \emph{Store Buffer step}:
we do case distinction on the rules in Figure~\ref{fig:store-buffer-transitions}. 
When a read, a non volatile write, a ghost operation or a program history node exits the store buffer, the virtual machine does not have to do any step since these steps are already visible. 
When a volatile write exits the store buffer, we execute all the suspended operations (including reads, ghost operations and program steps) until the next suspended volatile write is hit. This is possible since all writes are non volatile and thus memory modifications are thread local. 
\end{inparaenum}

In the following we exemplarically describe some cases in more detail to give an impression on the typical arguments in the proof.
We start with a configuration @{term "c\<^sub>s\<^sub>b\<^sub>h=(ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b\<^sub>h,\<S>\<^sub>s\<^sub>b\<^sub>h)"} of the store buffer machine, where the next instruction to be executed is a 
read of thread @{term i}: @{term "Read\<^sub>s\<^sub>b volatile a t"}. The configuration of the virtual machine is @{term "cfg=(ts,m,\<S>)"}. 
We have to simulate this step on the virtual machine and can make use of 
the coupling relations @{term "(ts\<^sub>s\<^sub>b\<^sub>h,m\<^sub>s\<^sub>b\<^sub>h,\<S>\<^sub>s\<^sub>b\<^sub>h) \<sim> (ts,m,\<S>)"},  the invariants  @{term "invariant ts\<^sub>s\<^sub>b\<^sub>h \<S>\<^sub>s\<^sub>b\<^sub>h m\<^sub>s\<^sub>b\<^sub>h"} and the safety of all reachable states of the virtual machine: @{term "safe_reach_direct_delayed (ts,m,\<S>)"}. The state of the store buffer machine and the coupling with the volatile machine is depicted in Figure~\ref{fig:coupling-i-read}. Note that if there are some suspended instructions in thread @{term i}, we cannot directly exploit the 'safety of the read', as the virtual machine has not yet reached the state where thread @{term i} is poised to do the read. But fortunately we have safety of the virtual machien of all reachable states. Hence we can just  execute all suspended instructions of thread @{term i} until we reach the read. We refer to this configuration of the virtual machine as @{term "cfg''=(ts'',m'',\<S>'')"}, which is depicted in Figure~\ref{fig:coupling-i-read-forward}.

\begin{figure}
\centering
\begin{tikzpicture}
\tikzstyle{sbnodel}=[shape=rectangle, draw=black, text badly centered,  outer sep=0cm]
\tikzstyle{sbnoder}=[shape=rectangle, draw=black, text ragged, outer sep=0cm]
\tikzstyle{nonvolatile}=[fill=gray!10]
\tikzstyle{virtual}=[dotted]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Store buffers and instructions %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\node (sbl0) [style=sbnodel,style=nonvolatile,text width=1.3cm] {nv};
\node (sbr0) [style=sbnoder,text width=1.7cm, right] at(sbl0.east) {v};
\node (ins0) [right] at ($ (sbr0.east) $) {thread $0$: $i_0^0$, $i_0^1$, $\dots$};

\node (sbl1) [style=sbnodel,style=nonvolatile,text width=2.0cm,below right] at ($ (sbl0.south west) -(0,0.6cm) $) {nv};
\node (sbr1) [style=sbnoder,text width=1.0cm, right] at(sbl1.east) {v};
\node (ins1) [right] at ($ (sbr1.east) $) {thread $i$: @{term "Read\<^sub>s\<^sub>b volatile a t"},$\dots$};


\node (sbl2) [style=sbnodel,style=nonvolatile,text width=1.7cm,below right] at ($ (sbl1.south west) -(0,0.6cm) $) {nv};
\node (sbr2) [style=sbnoder,text width=1.3cm, right] at(sbl2.east) {v};
\node (ins2) [right] at ($ (sbr2.east) $) {thread $j$: $i_j^0$, $i_j^1$, $\dots$};

\node (sbl3) [style=sbnodel,style=nonvolatile,text width=1.4cm,below right] at ($ (sbl2.south west) -(0,0.6cm) $) {nv};
\node (sbr3) [style=sbnoder,text width=1.6cm, right] at(sbl3.east) {v};
\node (ins3) [right] at ($ (sbr3.east) $) {thread $n$: $i_n^0$, $i_n^1$, $\dots$};

\path (sbr1.north east)  to node [near end,left] {$\vdots$} (sbr0.south east);
\path (sbr2.north east)  to node [near end,left] {$\vdots$} (sbr1.south east);
\path (sbr3.north east)  to node [near end,left] {$\vdots$} (sbr2.south east);

\node (sblabel)[above]  at ($ (sbr0.north west) +(0,0.6cm)$) {$\leftarrow$ store buffers};
\node (inslabel)[above]  at ($ (sbr0.north east) +(1.5cm,0.6cm)$) {$\leftarrow$ instructions};

%%%%%%%%%%
% Memory %
%%%%%%%%%%
\coordinate (memNorthWest) at ($ (sbl0.north west) -(2.0cm,0cm) $);
\coordinate (memSouthEast) at ($ (sbl3.south west) -(0.5cm,0cm) $);
\filldraw[style=nonvolatile,rounded corners]  (memNorthWest) rectangle  (memSouthEast) node [midway] {@{term "m\<^sub>s\<^sub>b\<^sub>h"}};

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Virtual memory boundaries %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\draw [style=virtual,out=90,in=-90](sbr1.north west) to (sbr0.south west);
\draw [style=virtual,out=90,in=-90](sbr2.north west) to (sbr1.south west);
\draw [style=virtual,out=90,in=-90](sbr3.north west) to (sbr2.south west);

\draw [style=virtual] ($ (memNorthWest) +(0,0.4cm) $) to ($ (sbr0.north west) + (-0.3,0.4)$)[out=0,in=90] to ($ (sbr0.north west)$);
\draw [style=virtual]($ (memNorthWest |- memSouthEast) +(0,-0.8cm) $) to node[midway,above]{@{term m}} ($ (sbr3.south west) + (-0.3,-0.8)$)[out=0,in=90]
  to ($ (sbr3.south west)$);

\node (execslabel)[below]  at ($ (sbl3.south)$) {executed};
\node (suspendslabel)[below]  at ($ (sbr3.south)$) {suspended};

\end{tikzpicture}

\caption{Thread @{term i} poised to read \label{fig:coupling-i-read}}
\end{figure}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{figure}
\centering
\begin{tikzpicture}
\tikzstyle{sbnodel}=[shape=rectangle, draw=black, text badly centered,  outer sep=0cm]
\tikzstyle{sbnoder}=[shape=rectangle, draw=black, text ragged, outer sep=0cm]
\tikzstyle{nonvolatile}=[fill=gray!10]%todo rename to executed?
\tikzstyle{virtual}=[dotted]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Store buffers and instructions %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\node (sbl0) [style=sbnodel,style=nonvolatile,text width=1.3cm] {nv};
\node (sbr0) [style=sbnoder,text width=1.7cm, right] at(sbl0.east) {v};
\node (ins0) [right] at ($ (sbr0.east) $) {thread $0$: $i_0^0$, $i_0^1$, $\dots$};

\node (sbl1) [style=sbnodel,style=nonvolatile,text width=2.0cm,below right] at ($ (sbl0.south west) -(0,0.6cm) $) {nv};
\node (sbr1) [style=sbnoder,style=nonvolatile,text width=1.0cm, right] at(sbl1.east) {v};
\node (ins1) [right] at ($ (sbr1.east) $) {thread $i$: @{term "Read\<^sub>s\<^sub>b volatile a t"},$\dots$};


\node (sbl2) [style=sbnodel,style=nonvolatile,text width=1.7cm,below right] at ($ (sbl1.south west) -(0,0.6cm) $) {nv};
\node (sbr2) [style=sbnoder,text width=1.3cm, right] at(sbl2.east) {v};
\node (ins2) [right] at ($ (sbr2.east) $) {thread $j$: $i_j^0$, $i_j^1$, $\dots$};

\node (sbl3) [style=sbnodel,style=nonvolatile,text width=1.4cm,below right] at ($ (sbl2.south west) -(0,0.6cm) $) {nv};
\node (sbr3) [style=sbnoder,text width=1.6cm, right] at(sbl3.east) {v};
\node (ins3) [right] at ($ (sbr3.east) $) {thread $n$: $i_n^0$, $i_n^1$, $\dots$};

\path (sbr1.north east)  to node [near end,left] {$\vdots$} (sbr0.south east);
\path (sbr2.north east)  to node [near end,left] {$\vdots$} (sbr1.south east);
\path (sbr3.north east)  to node [near end,left] {$\vdots$} (sbr2.south east);

\node (sblabel)[above]  at ($ (sbr0.north west) +(0,0.6cm)$) {$\leftarrow$ store buffers};
\node (inslabel)[above]  at ($ (sbr0.north east) +(1.5cm,0.6cm)$) {$\leftarrow$ instructions};

%%%%%%%%%%
% Memory %
%%%%%%%%%%
\coordinate (memNorthWest) at ($ (sbl0.north west) -(2.0cm,0cm) $);
\coordinate (memSouthEast) at ($ (sbl3.south west) -(0.5cm,0cm) $);
\filldraw[style=nonvolatile,rounded corners]  (memNorthWest) rectangle  (memSouthEast) node [midway] {@{term "m\<^sub>s\<^sub>b\<^sub>h"}};

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Virtual memory boundaries %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\draw [style=virtual,out=90,in=-90](sbr1.north east) to (sbr0.south west);
\draw [style=virtual,out=90,in=-90](sbr2.north west) to (sbr1.south east);
\draw [style=virtual,out=90,in=-90](sbr3.north west) to (sbr2.south west);

\draw [style=virtual] ($ (memNorthWest) +(0,0.4cm) $) to ($ (sbr0.north west) + (-0.3,0.4)$)[out=0,in=90] to ($ (sbr0.north west)$);
\draw [style=virtual]($ (memNorthWest |- memSouthEast) +(0,-0.8cm) $) to node[midway,above]{@{term m}} ($ (sbr3.south west) + (-0.3,-0.8)$)[out=0,in=90]
  to ($ (sbr3.south west)$);

\node (execslabel)[below]  at ($ (sbl3.south)$) {executed};
\node (suspendslabel)[below]  at ($ (sbr3.south)$) {suspended};

\end{tikzpicture}

\caption{Forwarded computation of virtual machine  \label{fig:coupling-i-read-forward}}
\end{figure}



For now we want to consider the case where the read goes to memory and is not forwarded from the store buffer. The value read is @{term "v=m\<^sub>s\<^sub>b\<^sub>h a"}. Moreover, we make a case distinction wheter there is an outstanding volatile write in the store buffer of thread @{term i} or not. This determines if there are suspended instructions in the virtual machine or not. We start with the case where there is no such write. This means that there are no suspended instructions in thread @{term i} and therefore @{term "cfg''=cfg"}. 
We have to show that the virtual machine reads the same value from memory: @{term "v = m a"}. So what can go wrong? When can the the memory of the virtual machine hold a different value? The memory of the virtual machine is obtained from the memory of the store buffer machine by executing all store buffers until we hit the first volatile write. So if there is a discrepancy in the value this has to come from a non-volatile write in the executed parts of another thread, let us say thread @{term j}. This write is marked as x in Figure~\ref{fig:coupling-i-read-conflict}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{figure}
\centering
\begin{tikzpicture}
\tikzstyle{sbnodel}=[shape=rectangle, draw=black, text badly centered,  outer sep=0cm]
\tikzstyle{sbnoder}=[shape=rectangle, draw=black, text ragged, outer sep=0cm]
\tikzstyle{nonvolatile}=[fill=gray!10]%todo rename to executed?
\tikzstyle{virtual}=[dotted]

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Store buffers and instructions %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\node (sbl0) [style=sbnodel,style=nonvolatile,text width=1.3cm] {nv};
\node (sbr0) [style=sbnoder,text width=1.7cm, right] at(sbl0.east) {v};
\node (ins0) [right] at ($ (sbr0.east) $) {thread $0$: $i_0^0$, $i_0^1$, $\dots$};

\node (sbl1) [style=sbnodel,style=nonvolatile,text width=2.0cm,below right] at ($ (sbl0.south west) -(0,0.6cm) $) {nv};
\node (sbr1) [style=sbnoder,style=nonvolatile,text width=1.0cm, right] at(sbl1.east) {v};
\node (ins1) [right] at ($ (sbr1.east) $) {thread $i$: @{term "Read\<^sub>s\<^sub>b volatile a t"},$\dots$};


\node (sbl2) [style=sbnodel,style=nonvolatile,text width=1.7cm,below right] at ($ (sbl1.south west) -(0,0.6cm) $) {x};
\node (sbr2) [style=sbnoder,text width=1.3cm, right] at(sbl2.east) {v};
\node (ins2) [right] at ($ (sbr2.east) $) {thread $j$: $i_j^0$, $i_j^1$, $\dots$};

\node (sbl3) [style=sbnodel,style=nonvolatile,text width=1.4cm,below right] at ($ (sbl2.south west) -(0,0.6cm) $) {nv};
\node (sbr3) [style=sbnoder,text width=1.6cm, right] at(sbl3.east) {v};
\node (ins3) [right] at ($ (sbr3.east) $) {thread $n$: $i_n^0$, $i_n^1$, $\dots$};

\path (sbr1.north east)  to node [near end,left] {$\vdots$} (sbr0.south east);
\path (sbr2.north east)  to node [near end,left] {$\vdots$} (sbr1.south east);
\path (sbr3.north east)  to node [near end,left] {$\vdots$} (sbr2.south east);

\node (sblabel)[above]  at ($ (sbr0.north west) +(0,0.6cm)$) {$\leftarrow$ store buffers};
\node (inslabel)[above]  at ($ (sbr0.north east) +(1.5cm,0.6cm)$) {$\leftarrow$ instructions};

%%%%%%%%%%
% Memory %
%%%%%%%%%%
\coordinate (memNorthWest) at ($ (sbl0.north west) -(2.0cm,0cm) $);
\coordinate (memSouthEast) at ($ (sbl3.south west) -(0.5cm,0cm) $);
\filldraw[style=nonvolatile,rounded corners]  (memNorthWest) rectangle  (memSouthEast) node [midway] {@{term "m\<^sub>s\<^sub>b\<^sub>h"}};

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Virtual memory boundaries %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\draw [style=virtual,out=90,in=-90](sbr1.north east) to (sbr0.south west);
\draw [style=virtual,out=90,in=-90](sbr2.north west) to (sbr1.south east);
\draw [style=virtual,out=90,in=-90](sbr3.north west) to (sbr2.south west);

\draw [style=virtual] ($ (memNorthWest) +(0,0.4cm) $) to ($ (sbr0.north west) + (-0.3,0.4)$)[out=0,in=90] to ($ (sbr0.north west)$);
\draw [style=virtual]($ (memNorthWest |- memSouthEast) +(0,-0.8cm) $) to node[midway,above]{@{term m}} ($ (sbr3.south west) + (-0.3,-0.8)$)[out=0,in=90]
  to ($ (sbr3.south west)$);

\node (execslabel)[below]  at ($ (sbl3.south)$) {executed};
\node (suspendslabel)[below]  at ($ (sbr3.south)$) {suspended};

\end{tikzpicture}

\caption{Conflicting write in thread j (marked x)  \label{fig:coupling-i-read-conflict}}
\end{figure}

We refer to x both for the write operation itself and to characterize the point in time in the computation of the virtual machine where the write was executed. At the point x the write was safe according to rules in Figure~\ref{fig:safe-delayed} for non-volatile writes. So it was owned by thread @{term j} and unshared. This knowledge about the safety of write x is preserved in the invariants, namely (Ownership.\ref{inv-ownership:owned-or-read-only})
and (Sharing.\ref{inv-sharing:non-volatile-writes-unshared}). Additionally from invariant (Sharing.\ref{inv-sharing:no-write-to-read-only-memory}) we know that address @{term a} was not read-only at point x. Now we combine this information with the safety of the read of thread @{term i} in the current configuration @{term "cfg"}: address @{term a} either has to be owned by thread @{term i}, or has to be read-only or the read is volatile and @{term a} is shared. Additionally there are the constraints on the released addresses which we will exploit below. Let us address all cases step by step.
First, we consider that address @{term a} is currently owned by thread @{term i}. As it was owned by thread @{term j} at time x there has to be an release of @{term a} in the executed prefix of the store buffer of thread @{term j}. This release is recorded in the release set, 
so we know @{term "a \<in> dom (\<R>s!j)"}. This contradicts the safety of the read. Second, we consider that address @{term a} is currently read-only.
At time x address @{term a} was owned by thread @{term j}, unshared and not read-only. Hence there was a release of address @{term a} in the executed prefix of the store buffer of @{term j}, where it made a transition unshared and owned to shared. With the monotonicity of the release sets this means 
@{term "a \<in> dom (\<R>s!j)"}, even more precisely @{term "(\<R>s!j) a = Some False"}. Hence there is no chance to get the read safe (neiter a volatile nor a non-volatile). Third, consider a volatile read and that address @{term a} is currently shared. This is ruled out by the same line of reasoning as in the previous case.
So ultimately we have ruled out all races that could destroy the value at address @{term a} and have shown that we can simulate the step on the virtual machine.
This completes the simulation of the case where there is no store buffer forwarding and no volatile write in the store buffer of thread @{term i}. The other cases are handled similar. The main arguments are obtained by arguing about safety of configuration @{term cfg''} and exploiting the invariants to rule out conflicting operations in other store buffers. When there is a volatile write in he store buffer of thread @{term i} there are still pending suspended instructions in the virtual machine. Hence the virtual machine makes no step and we have to argue that the simulation relation as well as all invariants still hold.

Up to now we have focused on how to simulate the read and in particular on how to argue that the value read in the store buffer machine is the same as the value read in the virtual machine. Besided these simulation properties another major part of the proof is to show that all invariants are maintained. For example if the non-volatile read enters the store buffer we have to argue that this new entry is either owned or refers to an read-only address (Ownership.\ref{inv-ownership:owned-or-read-only}). As for the simulation above this follows from safety of the virtual machine in configuration @{term "cfg''"}. However, consider an ghost operation that acquires an address @{term a}. From safety of the configuration @{term "cfg''"} we can only infer that there is no conflicting acquire in the non-volaitle prefixes of the other store buffers. In case an conflicting acquire is in the suspended part of a store buffer of thread @{term j} safety of configuration @{term "cfg''"} is not enough. But as we have safety of all reachable states we can forward the computation of thread @{term j} until the conflicting acquire is about to be executed and construct an unsafe state which rules out the conflict.

Last we want to comment on the case where the store buffer takes a step. The major case destinction is wheter a volatile write leaves the store buffer or not. In the former case the virtual machine has to simulate a whole bunch of instructions at once to simulate the store buffer machine up to the next volatile write in the store buffer. In the latter case the virtual machine does no step at all, since the instruction leaving the store buffer is already simulated. In both cases one key argument is commutativity of non-volatile operations with respect to global effects on the memory or the sharing map. Consider a non-volatile store buffer step of thread @{term i}. In the configuration of the virtual machine before the store buffer step of thread @{term i}, the simulation relation applies the update to the memory and the sharing map of the store buffer machine, within the operations @{term "flush_all_until_volatile_write"} and @{term "share_all_until_volatile_write"} `somewhere in the middle' to obtain the memory and the sharing map of the virtual machine. After the store buffer step however, when the non-volatile operations has left the store buffer, the effect is applied to the memory and the sharing map right in the beginning. The invariants and safety sideconditions for non-volatile operations guarantee `locality' of the operation which manifests in commutativity properties. For example, a non-volatile write is thread local. There is no conflicting write in any other store buffer and hence the write can be safely moved to the beginning.

This conludes the discussion on the proof of Theorem~\ref{thm:simulation}.\qed
\<close>

text (in xvalid_program_progress) \<open>
\bigskip
The simulation theorem for a single step is inductive and can therefor be extended to arbitrary long computations.
Moreover, the coupling relation as well as the invariants become trivial for a initial configuration where all store buffers are empty and the ghost state is setup appropriately. To arrive at our final Theorem \ref{thm:reduction} we need the following steps:
\begin{enumerate}
\item \label{sim:sb-sbh} simulate the computation of the store buffer machine @{term "(ts\<^sub>s\<^sub>b,m,()) \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* (ts\<^sub>s\<^sub>b',m',())"} by a computation of a store buffer machine with history @{term "(ts\<^sub>s\<^sub>b\<^sub>h,m,\<S>) \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* (ts\<^sub>s\<^sub>b\<^sub>h',m',\<S>')"},

\item \label{sim:sbh-delayed} simulate the computation of the store buffer machine with history by a computation of the virtual machine 
 with delayed releases @{term "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')"} by Theorem \ref{thm:simulation} (extended to the reflexive transitive closure),
\item \label{sim:delayed-free-flowing} simulate the computation of the virtual machine with delayed releases by a computation of the virtual machine with free flowing releases @{term "(ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (ts',m',\<S>')"}\footnote{Here we are sloppy with @{term ts}; strictly we would have to distinguish the thread configurations without the @{term \<R>} component form the ones with the @{term \<R>} component used for delayed releases}.
\end{enumerate} 

Step \ref{sim:sb-sbh} is trivial since the bookkeeping within the additional ghost and history state does not affect the control flow of the transition systems and can be easily removed. Similar the additional @{term \<R>} ghost component can be ignored in Step \ref{sim:delayed-free-flowing}. However, to apply Theorem \ref{thm:simulation} in Step \ref{sim:sbh-delayed} we have to convert from @{term [names_short] "safe_reach_virtual_free_flowing (ts, m, \<S>)"} provided by the preconditions of Theorem \ref{thm:reduction} to the required @{term [names_short] "safe_reach_direct_delayed (ts, m, \<S>)"}. This argument is more involved and we only give a short sketch here. 
The other direction is trival as every single case for delayed releases (cf. Figure \ref{fig:safe-delayed}) immediately implies the corresponding case for free flowing releases (cf. Figure \ref{fig:safe-virtual-memory}).

First keep in mind that the predicates ensure that \emph{all} reachable configurations starting from @{term "(ts,m,\<S>)"} are safe, according to the rules for free flowing releases or delayed releases respectively. We show the theorem by contraposition and start with a computation which reaches a configuration @{term c} that is unsafe according to the rules for delayed releases and want to show that there has to be a (potentially other) computation (starting from the same initial state) that leads to an unsafe configuration @{term c'} accroding to free flowing releases. 
If @{term c} is already unsafe according to free flowing releases we have @{term "c'=c"} and are finished. 
Otherwise we have to find another unsafe configuration. 
Via induction on the length of the global computation we can also assume that for all shorter computations both safety notions coincide. 
A configuration can only be unsafe with respect to delayed releases and safe with respect to free flowing releases if there is a race between two distinct Threads @{term i} and @{term j} on an address @{term a} that is in the release set @{term "\<R>"} of one of the threads, lets say Thread @{term i}. 
For example Thread @{term j} attempts to write to an address @{term a} which is in the release set of Thread @{term i}. 
If the release map would be empty there cannot be such an race (it would simulataneously be unsafe with respect to free flowing releases). 
Now we aim to find a configuration @{term c'} that is also reachable from the initial configuration and is unsafe with respect to free flowing releases. 
Intuitively this is a configuration where Thread @{term i} is rewinded to the state just before the release of address @{term a} and Thread @{term j} is in the same state as in configuration @{term c}. 
Before the release of @{term a} the address has to be owned by Thread @{term i}, which is unsafe according to free flowing releases as well as delayed releases.
So we can argue that either Thread @{term j} can reach the same state although Thread @{term i} is rewinded or we even hit an unsafe configuration before. 
What kind of steps can Thread @{term i} perform between between the free flowing release point (point of the ghost instruction) and the delayed release point (point of next volatile write, interlocked operation or fence at which the release map is emptied)? How can these actions affect Thread @{term j}? 
Note that the delayed release point is not yet reached as this would empty the release map (which we know not to be empty). 
Thus Thread @{term i} does only perform reads, ghost instructions, program steps or non-volatile writes.
All of these instructions of Thread @{term i} either have no influence on the computation of Thread @{term j} at all (e.g. a read, program step, non-volatile write or irrelevant ghost operation) or may cause a safety violation already in a shorter computation (e.g. acquiring an address that another thread holds). This is fine for our inductive argument. So either we can replay every step of Thread @{term j} and reach 
the final configuration @{term c'} which is now also unsafe according to free flowing releases, or we hit a configuration @{term c''} in a shorter computation which violates the rules of delayed as well as free flowing releases (using the induction hypothesis).
\<close>

section \<open>PIMP \label{sec:pimp}\<close>
text \<open>
PIMP is a parallel version of IMP\cite{Nipkow-FSTTCS-96}, a canonical WHILE-language. 


An expression @{term "e"} is either 
\begin{inparaenum}
\item @{term "Const v"}, a constant value,
\item @{term "Mem volatile a"}, a (volatile) memory lookup at address @{term "a"},
\item @{term "Tmp sop"}, reading from the temporaries with a operation @{term "sop"} which is an intermediate expression occurring in the transition rules for statements,
\item @{term "Unop f e"}, a unary operation where @{term "f"} is a unary function on values, and finally
\item @{term "Binop f e\<^sub>1 e\<^sub>2"}, a binary operation where @{term "f"} is a binary function on values.
\end{inparaenum}

 
A statement @{term "s"} is either
\begin{inparaenum}
\item @{term "Skip"}, the empty statement,
\item @{term "Assign volatile a e A L R W"}, a (volatile) assignment of expression @{term "e"} to address expression @{term "a"},
\item @{term "CAS a c\<^sub>e s\<^sub>e A L R W"}, atomic compare and swap at address expression @{term "a"} with compare expression 
  @{term "c\<^sub>e"} and swap expression @{term "s\<^sub>e"},
\item @{term "Seq s\<^sub>1 s\<^sub>2"}, sequential composition,
\item @{term "Cond e s\<^sub>1 s\<^sub>2"}, the if-then-else statement,
\item @{term "While e s"}, the loop statement with condition @{term "e"},
\item @{term "SGhost"}, and @{term "SFence"} as stubs for the corresponding memory instructions.
\end{inparaenum}

The key idea of the semantics is the following: expressions are evaluated by issuing instructions to the memory system, then the program waits until the memory system has made all necessary results available in the temporaries, which allows the program to make another step. Figure~\ref{fig:expression-evaluation} defines expression evaluation.
%
\begin{figure}
\begin{tabularx}{\textwidth}{l@ {~~\<open>=\<close>~~}X}
@{thm (lhs) issue_expr.simps (1) [no_vars]} & @{thm (rhs) issue_expr.simps (1) [no_vars]}\\
@{thm (lhs) issue_expr.simps (2) [no_vars]} & @{thm (rhs) issue_expr.simps (2) [no_vars]}\\
@{thm (lhs) issue_expr.simps (3) [where sop="(D,f)", no_vars]} & @{thm (rhs) issue_expr.simps (3) [where sop="(D,f)", no_vars]}\\
@{thm (lhs) issue_expr.simps (4) [no_vars]} & @{thm (rhs) issue_expr.simps (4) [no_vars]}\\
@{thm (lhs) issue_expr.simps (5) [no_vars]} & @{thm [break,margin=50] (rhs) issue_expr.simps (5) [no_vars]}\\
\end{tabularx}\\[2pt]

\begin{tabularx}{\textwidth}{l@ {~~\<open>=\<close>~~}X}
@{thm (lhs) eval_expr.simps (1) [no_vars]} & @{thm (rhs) eval_expr.simps (1) [no_vars]}\\
@{thm (lhs) eval_expr.simps (2) [no_vars]} & @{thm (rhs) eval_expr.simps (2) [no_vars]}\\
@{thm (lhs) eval_expr.simps (3) [where sop="(D,f)", no_vars]} & @{thm (rhs) eval_expr.simps (3) [where sop="(D,f)",simplified fst_conv snd_conv, no_vars]}\\
@{thm (lhs) eval_expr.simps (4) [no_vars]} & @{thm (rhs) eval_expr.simps (4) [no_vars]}\\
@{thm (lhs) eval_expr.simps (5) [no_vars]} & @{thm [break,margin=50] (rhs) eval_expr.simps (5) [no_vars]}
\end{tabularx}
\caption{Expression evaluation\label{fig:expression-evaluation}}
\end{figure}
%
The function @{term "used_tmps e"} calculates the number of temporaries that are necessary to evaluate expression @{term "e"}, where every @{term "Mem"} expression accounts to one temporary. 
With @{term "issue_expr t e"} we obtain the instruction list for expression @{term "e"} starting at temporary @{term "t"}, whereas @{term "eval_expr t e"} constructs the operation as a pair of the domain and a function on the temporaries.

The program transitions are defined in Figure~\ref{fig:program-transitions}. We instantiate the program state by a tuple @{term "(s,t)"} containing the statement @{term "s"} and the temporary counter @{term "t"}.
%
\begin{figure}
\begin{center}
@{thm [mode=Rule] AssignAddr' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] Assign' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] CASAddr' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] CASComp' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] CAS' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] stmt_step.Seq [no_vars]}\\[-0.3\baselineskip] 
@{thm [mode=Axiom] stmt_step.SeqSkip [no_vars]} \\[0.5\baselineskip]
@{thm [mode=Rule] SCond' [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] stmt_step.CondTrue [no_vars]}\\[0.5\baselineskip]
@{thm [mode=Rule] stmt_step.CondFalse [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] While [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] SGhost [no_vars]}\\[-0.3\baselineskip]
@{thm [mode=Axiom] SFence [no_vars]}\\[0.1\baselineskip]
\end{center}
\caption{Program transitions\label{fig:program-transitions}}
\end{figure}
%
To assign an expression @{term "e"} to an address(-expression) @{term "a"} we first create the memory instructions for evaluation the address @{term "a"} and transforming the expression to an operation on temporaries. The temporary counter is incremented accordingly. 
When the value is available in the temporaries we continue by
creating the memory instructions for evaluation of expression @{term "e"} followed by the corresponding store operation.
Note that the ownership annotations can depend on the temporaries and thus can take the calculated address into account.

Execution of compare and swap @{term "CAS"} involves evaluation of three expressions, the address @{term "a"} the compare value @{term "c\<^sub>e"} and the swap value @{term "s\<^sub>e"}. 
It is finally mapped to the read-modify-write instruction @{term "RMW"} of the memory system. 
Recall that execution of @{term "RMW"} first stores the memory content at address @{term "a"} to the specified temporary. 
The condition compares this value with the result of evaluating @{term "c\<^sub>e"} and writes swap value @{term "s\<^sub>a"} if successful. 
In either case the temporary finally returns the old value read.
 
Sequential composition is straightforward. An if-then-else is computed by first issuing the memory instructions for evaluation of condition @{term "e"} and transforming the condition to an operation on temporaries. 
When the result is available the transition to the first or second statement is made, depending on the result of @{const "isTrue"}.
Execution of the loop is defined by stepwise unfolding.
Ghost and fence statements are just propagated to the memory system.
%

To instantiate Theorem~\ref{thm:simulation} with PIMP we define the invariant parameter @{term "valid"}, which has to be maintained by all transitions of PIMP, the memory system and the store buffer. 
Let @{term "\<theta>"} be the valuation of temporaries in the current configuration, for every thread configuration @{term "ts\<^sub>s\<^sub>b!i = ((s,t),is,\<theta>,sb,\<D>,\<O>)"} where @{term "i < length ts\<^sub>s\<^sub>b"} we require:
%
\begin{inparaenum}
\item The domain of all intermediate @{term "Tmp (D,f)"} expressions in statement @{term "s"} is below counter @{term "t"}.
\item All temporaries in the memory system including the store buffer are below counter @{term "t"}.
\item All temporaries less than counter @{term "t"} are either already defined in the temporaries @{term "\<theta>"} or are outstanding read temporaries in the memory system.
\end{inparaenum}

For the PIMP transitions we prove these invariants by rule induction on the semantics.
For the memory system (including the store buffer steps) the invariants are straightforward. 
The memory system does not alter the program state and does not create new temporaries, only the PIMP transitions create new ones in strictly  ascending order. 
\<close>



(*<*)
end
(*>*) 
