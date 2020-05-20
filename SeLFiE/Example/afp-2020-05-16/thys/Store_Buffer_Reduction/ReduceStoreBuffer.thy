(* Copyright (C) 2007--2010 Norbert Schirmer
 * All rights reserved, DFKI GmbH 
 *)
theory ReduceStoreBuffer
imports Main
begin
(*
Basic access policy:
shared + owned by some thread (only the owner is allowed to write): 
 - owner: LMS, volatile writes and arbitrary reads; 
 - others: volatile reads

shared + not owned by any thread:
 - read/write: LMS, volatile writes and volatile reads
 - read-only: arbitrary reads

The core argument in the simulation proof is to show that all reads can be executed in the
virtual machine, preserving the values they have seen in the store-buffer machine.

 * Non volatile reads *

non-volatile means that the tread knows everything about the evolution of the value. It is thread local
or read only. Writes in other store buffers may not interfere with non-volatile reads.
Complicated case:
i: [Load (read-only) a (m a)]
j: [Acq {a}, Write a v]

This may only be sceduled such that i comes first and then j. If Acq {a} already happend, safety of
the Load would be violated.
So when i is poised to Load, and j has already executed on the virtual machine we have a safety
violation.
On the other hand, if i has already executed on the virtual machine ("m a" has ben seen) and the
Acq of j is fine.

Not that read-only loads (before the first volatile store) in the store buffer may become stale before 
they hit memory.
 
 * volatile reads *

The value seen can depend on writes of other threads. That is why the flushing policy enforces the
store-buffer to be empty, if there is an outstanding volatile write in the store-buffer.
The volatile reads must be executed in the virtual machine at the time
they are issued to the store-buffer, to ensure that both machines see the same value.
It is perfectly valid that volatile reads in the store buffer become stale, e.g.
i: [VLoad a (m a)]
j: [VWrite a v]

As j's write is committed to memory the (history-)entry in i's store-buffer becomes stale. But as the
virtual machine has also already executed the load this is fine.

Complicated case:
i: [VLoad a (m a)]
j: [Write a v, Release {a}]

As i sees (m a) and not v it has to come first. 
But if j has already executed and released a, there is no
safety-violation when i is poised to execute the VLoad afterwards. This would lead to the wrong value (v instead of "m a", but we cannot rule out the scheduling by a safety argument.

Currently we avoid this situation, by coupling Releases to volatile Writes. Hence the Release is
not yet executed in the virtual machine and thus VLoad of i is unsafe.

Another solution would be to go back in time, to the state before Release {a} is executed, and argue
that this scheduling is also valid and would lead to a safeness violation and thus must be disregarded.


Some thoughts.:

I think some key to free-flowing release story is the following:

    flushed      suspended
   /       \ /               \
i: [\<dots>, \<dots>  , Write True,\<dots>,\<dots>]
j: [\<dots>, \<dots>  , Write True,\<dots>,\<dots>]
   \       / \               /
     races     races ruled 
      ok         out by 
                 safety

Races in the flushed part are ok, since they are already simulated in the virtual machine.
The problem is how to formulate the invariants and all the stuff that this works out in the
proof. E.g. 

i: [Write a v, Release {a}]
j: poised: Rread a

So the idea doesn't seem to work. It may only work as long as no write is involved. (i.e. Release / Acq)

FIXME: 
shared: does not seem to buy anything right now, as owner has to do volatile reads and writes.
(It should be possible that the owner does non-volatile reads, but as he is the only writer reading makes no
sense)
LMS: maybe store restriction could be relayed to owned + shared, if there is no sharing anymore there are no restrictions.

What could be better is read-only memory which can be read accessed non-volatily.

a: either owned by some thread;
   either unowned by any thread and read/write;
   either unowned by any thread and read-only:a

but how does memory become read-only?

Free-Flowing releases:
Take proof as is, and augment machnes with set of released since last flush state.
xsafety: nobody is allowed to acquire / write to released things:

Second: proof that safety ==> xsafety for virtual machine (by induction on ->*, and an initial configuration).
*)

(*
FIXME, think about this:
Introduce additional control state for the direct-machine to keep track of whether
there is an outstanding volatile store, and the set of acquired variables since the
last flush. Add this protocol to the 'good'-stuff. This should make the 
enough-flushs invariant unnecessary, and it would make it more straightforward to introduce
state-dependencies to A,L,R (maybe from the temporaries and ghost state?). If state dependencies make sense depends on the integration into PIMP.   


A stricter separation of ghost and ordinary state would be nice.
shared: global ghost state
owned: local ghost state.

SB-Machine independent of ghost state.
D-Machine uses all of it.
SBH-Machine uses it only as history information 


## notes: ernie 3. July 2009
#################################################################


final theorem:
 safe-free-flowing \<Longrightarrow> sb-machine is sequential consistent

we basically have (modulo dummy delay) :
 safe-delayed \<Longrightarrow> sb-machine is sequential consistent


need theorem
safe-free-flowing \<Longrightarrow> safe-dalayed

prf by contraposition and induction on execution:

S unsafe-dalayed \<Longrightarrow> S unsafe free-flowing
induction on S:
let t be last step of T (owning the disuputed address)

by Lemma: \<exists>S'. |S'| < |S| and
   S' \<circ> t \<sim> S and S' reachable

   case: t = release (L) then S' is unsafe free flowing \<Longrightarrow> S unsafe free flowing
   otherwise: S' unsafe delayed by induction S' unsafe free flowing \<Longrightarrow> S unsafe free flowing



Lemma:

S is reachable and 
last step of thread T is t, which is not a volatile write
then

\<exists>S' reachable. |S'| < |S| \<and> S' \<circ> t \<sim> S   (\<sim>: states are equal modulo stuff owned by T)
proof

 * S = <>, tivial.
 * S = S\<^sub>1 \<circ> t, trivial.
 * S = S\<^sub>1 \<circ> u,  (u \<noteq> t)
    (induction): \<exists>S\<^sub>1' \<sim> S\<^sub>1 \<circ> t
      moreover: t \<circ> u \<sim> u \<circ> t
    
      ultimately: S = S\<^sub>1 \<circ> u \<sim> S\<^sub>1' \<circ> t \<circ> u \<sim> S\<^sub>1' \<circ> u \<circ> t \<sim> S\<^sub>1 \<circ> t
   
6.10.2009: 
I don't think this proof works. The problem are volatile reads. We cannot just reschedule them
to the end, since the memory content may well be changed by intermediate volatile writes of other
threads.

It might be possible to come up with another lemma that says that we can delete the
last action thread T (if its not a volatile write), since this operation should not
have an effect on the following ops of the other threads.   
*)

(* ****************** 2.10.2009 *************************** *)
(*
Some new thoughts to introduce free-flowing releases in current proof scheme:

* introduce safety notion on store-buffer machine as well: safe_sb
* safe_sb takes also store-buffer content into accout, e.g. 
  I'm not allowed to acquire what is acquired in someone elses sb.
* make safe_sb a part of invariant on sb machine.
* to show that safe_sb is preserved builds on safe_reach of virtual machine

* safe_sb makes it possible to deal with releases in prefixes:
     
aforementioned complicated case is not safe_sb, as a is still owned (and not shared) by j
i: [VLoad a (m a)]
j: [Write a v, Release {a}]

what about:
i: [VLoad a (m a)]
j: [VWrite a v, Release {a}] (a is owned by j but is also shared)

j's sb is suspended. Hence v has not yet made it to memory. Hence i sees (m a) as expected.

Examples: preservation of safe_sb
config 1
i: Acq a 
j: Acq a   

  is safe_sb (if nowbody owns a)

config 2:
i: Acq a
j: [Acq a]

  should not be safe_sb.
  
  rule out by safe_reach on config 1.
  fast-forward either sb of i or j and execute the Acq a. Then the remaining Acq a is unsafe.

Important for safe_sb is, that for the current thread, the ghost-state (on ownership) is after executing its sb!
Otherwise one has problems with quite simple things, e.g. a step 
(1) i: Acq a; Write a;    owns = {}
(2) i: Write a; [Acq a]   owns = {}

assume (1) is safe_sb; Why should (2) be safe_sb?
It is if we consider acquire [Acq a] owns = {a} instead. And we know that it has to be acquired somewhere
in the store-buffer by exploiting safe_reach.

Maybe its better not to use safe_sb on the sb-state but on the state of the virtual machine.
Better in the sense that it is easier to connect it with safe_reach.


### 5.10 ###
Can't get safe_sb inductive.

consider:
i: [Rel a]
j: someting; Acq a; []
this is still safe_sb; but after one step where something is executed I have
i: [Rel a]
j: Acq a; []
this should not be safe_sb; but I have no arguments at hand.

### next idea ###
The control flow (and the reads) of a thread do not depend on the 'flush' parts of *other* threads, but can depend
on their own flush parts.

Moreover the information of the store buffer machine is not enough to construct a virtual execution that will
violate safety. We have to go back in time even further. An virtual machine that just suspends everything is not
inductive according to the rules of virtual machine steps: e.g.
State 1)
m
i: [VRead a (m a)]
j: [VWrite a 5]

State 2)
m(a:=5)
i: [VRead a (m a)]
j: []

State 1 could still be executed on a virtual machine that has i and j suspended, but State 2 not 
(since a is already visible).

What could help is we just take an extra starting config for the virtual machine for which we have:

c\<^sub>s\<^sub>b \<sim> c\<^sub>v
c\<^sub>s\<^sub>b \<sim>i c\<^sub>i; (we get virtual config c\<^sub>i by flushing (only) store buffer i until first volatile write, 
            all other buffers are suspended)

c \<rightarrow>* c\<^sub>v
\<forall>i. c \<rightarrow>* c\<^sub>i
safe_reach c;

we show: c\<^sub>s\<^sub>b \<rightarrow> c\<^sub>s\<^sub>b' \<Longrightarrow> c\<^sub>v \<rightarrow>* c\<^sub>v'

(hence we immediately have inductivity of c with respect to steps from c\<^sub>v : c \<rightarrow>* c\<^sub>v \<rightarrow>* c\<^sub>v')
What about c\<^sub>i \<rightarrow> c\<^sub>i'

  * for thread c\<^sub>i it should work similar as for c\<^sub>v'
  * if thread i takes a step then we also have to justify c\<^sub>j \<rightarrow> c\<^sub>j'. 
    when something enters the storebuffer i it is just stuttering (as i is just suspended)
    when something of thread i leaves the store-buffer it is also in the front of
    the instructions in i (since suspended) and may only depend on volatile writes
    in thread j, but those are also suspended.


The next question is can we instantiate the theorem with some kind of initial state?
For a state where the store-buffers are all empty we should have:
c\<^sub>s\<^sub>b == c\<^sub>v == c == c\<^sub>i 

Hence we trivially have all reachability constraints, and safe_reach c == safe_reach c\<^sub>v

Problem with this approach: just suspending all other threads does not work.
consider justification of thread i for step c\<^sub>i \<rightarrow> c\<^sub>i', where thread j takes a step, namely a volatile read.
volatile read can become stale in the store buffer (e.g. by a volatile write in thread i). Hence
we cannot simulate this read. (Thats why we flush all store-buffers until first volatile write in c\<^sub>v).
i: [VWrite a 5]
j: [VRead a 0]

i's virtual view:
i: VWrite a 5
j: VRead a 0

if i takes a step with Write a 5, we have a problem simulating j's stale read.

j's virtual view:
i: VWrite a 5
j: (Read has already happened)




Other problem:
i: [VWrite b 5] Acq a
j: [Rel a; VRead b 0]

Thread j has to execute before i to justify the read. But intuitively in c\<^sub>i, we wanted to delay the 'Rel a' such that
we can say 'Acq a' in thread i is unsafe.

#### 08.10.2009 ##################################
### Refined Approach for Free Flowing Releases ###
##################################################

  General setup
  -------------

Two safety predicates: 
 * safe_free_flowing: free flowing ghost releases in instruction stream
 * safe_delayed: release is delayed until next volatile write

safe_delayed is a variant of our current model, where 'Ghost' can only acquire, 
and releases are coupled with volatile (or interlocked) writes. However we don't 
want to introduce 2 different instruction streams (one with releases
and one without but with a proper annotation at the next volatile write). 
Instead we attempt to model safe-delayed with additional ghost state. 
Mainly a thread local set 'rel' of releases addresses (since the last volatile write). 
A volatile write resets this set, and a ghost release adds to this set, 
and safe_delayed may check these sets, whereas safe_free_flowing ignores these sets. 
Example: thread i poised for "Acquire A"

safe_free_flowing: 

  \<forall>j \<noteq> i. A \<inter> owns\<^sub>j = {}  ("A not owned by others")

safe_delayed:

  \<forall>j \<noteq> i. A \<inter> (owns\<^sub>j \<union> rel\<^sub>j)= {}  ("A not owned by others, 
                                   or release not yet committed")

(sanity check: safe_delayed is more restrictive than safe_free_flowing, i.e. 
  safe_delayed c \<Longrightarrow> safe_free_flowing c)

safe_reach safe c \<equiv> \<forall>c'. c \<Rightarrow>\<^sup>* c' \<Longrightarrow> safe c'
safe_reach\<^sup>n safe c \<equiv> \<forall>c'. c \<Rightarrow>\<^sup>n c' \<Longrightarrow> safe c'

Then we show two main theorems:

Theorem 1 (Simulation):
[|c\<^sub>s\<^sub>b \<Rightarrow>\<^sub>s\<^sub>b c\<^sub>s\<^sub>b'; c\<^sub>s\<^sub>b \<sim> c; safe_reach safe_delayed c|]
\<Longrightarrow>
\<exists>c'. c\<^sub>s\<^sub>b' \<sim> c' \<and> c\<^sub>s\<^sub>b \<Rightarrow>\<^sup>* c'

Proof.
  Hopefully straightforward adoption of current proof.
Qed. 
Theorem 1 can easily be extended to many steps c\<^sub>s\<^sub>b \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* c\<^sub>s\<^sub>b'

Definition: init c ("initial state")
  Intuition: state where safe_delayed and safe_free_flowing are in-sync
  That is: all rel\<^sub>i = {};

Fact:
init c \<Longrightarrow> safe_free_flowing c \<longrightarrow> safe_delayed c;


Theorem 2 (Safety):
[|safe_reach safe_free_flowing c; init c|]
\<Longrightarrow>
safe_reach safe_delayed c
Proof.

One basic ingredient is contraposition: 
from an unsafe_delayed computation we attempt to construct an unsafe_free_flowing computation.

Scenario for intuition:

  thread i:  \<dots>    Rel {a} \<dots>    |   \<dots> VWrite 
  thread j:  \<dots>       |    \<dots> Acq {a} 

thread i is somewhere in the computation between its release and the next volatile write.
thread j tries to Acq {a} inbetween.

This is safe_free_flowing (as the release has already happened), but not safe_delayed.
We want to argue that there is another scheduling of the global computation 
such that we also get a violation of safe_free_flowing.

For thread i we know that there are no volatile writes after the release until 
we hit the violation of safe_delayed. Intuitively this means that the other 
threads 'do not depend' on what is computed inside thread i after the release.
Note that the opposite is not the case. There can be volatile reads in thread i, 
which depend on (volatile) writes of 
other threads.

e.g.

  thread i:  \<dots>    Rel {a} \<dots>            \<dots> VRead b 5 \<dots>    |  \<dots> VWrite 
  thread j:  \<dots>       |    \<dots> VWrite b 6 \<dots>          \<dots>  Acq {a} 

This means that Read b 5 must come before VWrite b 6.

In general this implies that we cannot just reorder all steps of thread i 
(beginning from Rel {a}) after the Acq {a} in thread j to construct an 
unsafe_free_flowing state. 

It suggests that we instead try to *remove* all steps from thread i 
(beginning from and including Rel {a}) from the global computation, 
and argue that the other threads (especially j) can still do their 
computations until we reach a violation of safe_free_flowing 
(at latest at the Acq {a}).

There can be other violations before (but that is also fine) e.g.
  

  thread i:  \<dots>    Rel {a} \<dots>   Acq {b}; Write b 10; Rel {b}  \<dots>    |  \<dots> VWrite 
  thread j:  \<dots>       |    \<dots> VRead b 20     \<dots>              \<dots>   Acq {a}

We attempt to construct an unsafe_free_flowing state for the conflict 
with respect to a. But while we remove instructions from thread i, we 
encounter the violation with respect to b. As any violation of safe_free_flowing
is fine, this still fits into the proof.

The proof in more detail.
We do induction on the length of the computation.

[|safe_reach\<^sup>n safe_free_flowing c; init c|]
\<Longrightarrow>
safe_reach\<^sup>n safe_delayed c

  Case n=0
  --------

From fact on "init c" we know that safe_free_flowing c \<Longrightarrow> safe_delayed c;
safe_reach\<^sup>0 safe_free_flowing c <=> safe_free_flowing c \<Longrightarrow> safe_delayed c <=> safe_reach\<^sup>0 safe_delayed c

  Case n \<rightarrow> n+1
  -------------

Consider a trace: c(i) where c(0) = c; c(i) \<Rightarrow> c(i+1) for i <= n;
if there would be an k \<le> n for which \<not> safe_delayed c(k) we have \<not> safe_reach\<^sup>n safe_delayed c and by induction hypothesis
also \<not> safe_reach\<^sup>n safe_free_flowing c.

So we have:

\<forall>k \<le> n. safe_delayed c(k)

\<not> safe_delayed c(n+1)

Moreover we assume

\<forall>k \<le> n + 1. safe_free_flowing c(k)

(if we have  \<not> safe_free_flowing c(k) we have \<not> safe_reach\<^sup>n safe_free_flowing c and are finished)

We do case distinction on '\<not> safe_delayed c(n+1)'.
Some cases are trivially ruled out because of 'safe_free_flowing c(n+1)'.

Let us consider the case of 'safety violation due to an Acq A'

We get two racing threads i,j. Let j be the one issuing the 'Acq A'.

From \<not> safe_delayed c(n+1):

  A \<inter> (owns\<^sub>i \<union> rel\<^sub>i) \<noteq> {}

From safe_free_flowing c(n+1):

 A \<inter> (owns\<^sub>i) = {}

hence there is an a \<in> A and a \<in> rel\<^sub>i.

Let k < n+1 be the index where thread i did its last step in the transition from : c(k) \<Rightarrow> c(k+1).
So for c(k+1) \<dots> c(n+1) the thread configuration of i does not change.


                            last step of thread i
                                    |
c(0) \<Rightarrow> \<dots>            \<Rightarrow> c(k-1) \<Rightarrow> c(k) \<Rightarrow> c(k+1) \<Rightarrow> c(k+2) \<Rightarrow> \<dots> \<Rightarrow> c(n+1) 
  
c(k) \<Rightarrow> c(k+1) can't be a volatile or interlocked write of thread i. 
Otherwise rel\<^sub>i would be {} beginning at c(k+1) and thus there would be no a \<in> rel\<^sub>i. (in general only ops, where we cannot assert rel={} in the post state,i.e. reads, non-volatile writes and ghost ops)

We want to remove the step c(k) \<Rightarrow> c(k+1) from the computation (by undoing tread i's last step) and argue on 
replaying the rest of the computation:

c(0) \<Rightarrow> \<dots>            \<Rightarrow> c(k-1) \<Rightarrow> c'(k+1) \<Rightarrow> \<dots> \<Rightarrow> c'(n+1) 

At latest when we reach c'(n+1) we encounter a violation of safe_delayed c'(k) (from our initial race)
This requires a LEMMA!
As the length of the trace is now \<le> n (since step k is removed) we can 
use the induction hypothesis to obtain \<not> safe_reach\<^sup>n safe_free_flowing c 
and hence \<not> safe_reach\<^sup>n\<^sup>+\<^sup>1 safe_free_flowing c.

On the LEMMA:
We want to argue on the step's like c(k-1) \<Rightarrow> c'(k+1) and then 
continuing c'(k+1) \<Rightarrow> c'(k+2).
We can always do case distinction on 'safe_delayed'. If 'not safe_delayed' 
of any config we are fine with the main proof. So for the lemma we can 
assume "safe_delayed" of the initial state. 

Consider:

* (ts,S,m) \<Rightarrow> (ts',S',m')
* ts\<^sub>i = ts'\<^sub>i  (thread i does not change)
* safe_delayed (ts,S,m)
* (uts,uS,um) is obtained from ts by "undoing tread i's last step"
  - uts\<^sub>j = ts\<^sub>j (for j\<noteq>i)
  (- (uts,uS,um) \<Rightarrow> (ts,S,m) (by a step of thread i))
  - safe_delayed (uts,uS,um)
  - \<forall>a \<notin> uowns\<^sub>i. um(a) = m(a)
show:
  (uts,uS,um) \<Rightarrow> (uts',uS',um')

where
* uts\<^sub>i = uts'\<^sub>i
* uts'\<^sub>j = ts'\<^sub>j  (for j\<noteq>i)
* \<forall>a \<in> uowns\<^sub>i. um'(a) = um(a) ( this may not be necessary to know (since i only care about steps of other threads )
* \<forall>a \<notin> uowns\<^sub>i. um'(a) = m'(a)

We want to extend this simulation to a trace c(0)\<dots> c(k)
We either can simulate with a trace c'(0) \<dots> c'(k) and have safe_delayed c'(k) or 
we encounter an intermediate config \<not> safe_delayed c'(i)  for (i \<le> k) 
(from which simulation may no longer be possible).

LEMMA:
Assume:
* trace c(0) \<Rightarrow> \<dots> \<Rightarrow> c(k)
* \<forall>l,m \<le> k. ts(l)\<^sub>i = ts(m)\<^sub>i   (tread i does not change)
* undo config for thread i: ut\<^sub>i, uS, um (initial new configuration)

Show:
\<exists>trace c', x \<le> k. 
(c' simulate c up to step x, and all reached states are safe_delayed)
* \<forall>i \<le> x. safe_delayed c'(i)
* x < k \<longrightarrow> \<not> safe_delayed c'(x+1)
* \<forall>l \<le> x. ts'(l)\<^sub>i = ut\<^sub>i       (tread i does not change)
* S'(0) = uS
* m'(0) = um

* \<forall>l \<le> x. \<forall>j\<noteq>i. ts'(l)\<^sub>j = ts(l)\<^sub>j            (tread j is simulated)
* \<forall>l \<le> x. \<forall>a \<notin> uowns\<^sub>i. m'(l)(a) = m(l)(a) 
* \<forall>l \<le> x. \<forall>a \<notin> uowns\<^sub>i. S'(l)(a) = S(l)(a) 
* \<forall>l,o \<le> x. \<forall>a \<in> uowns\<^sub>i. S'(l)(a) = S'(o)(a)  (sharing of thread i stays constant)

(In case we reach the final state k, we know enough about preservation of the 
ownership and sharing ghost state to (re)construct the initial race in our main proof).




######################################################################
### Thoughts on extensions ###########################################
######################################################################

There is a common ideom for concurrency control that we currently
cannot deal with properly within our programming discipline, typically for
acquiring like ops (like acquiring a lock) and releases:

Acquire
Barrier

Barrier
Release

The Acquire is an interlocked write (or a volatile write followed by a barrier)
but the release is an ordinary volatile write, where maybe there is a barrier in front of it
(I think the reason for this is to prohibit certain compiler optimizations) but there is no
barrier after it. That means in our model, that the release leaves the store-buffer-state dirty.
And we would have to insert a flush before the next volatile read.
This extra flush is currently not done. The intuitive reason behind this is, that it is
totally ok if other threads can only observe the release with a delay, since they don't do any
harm by waiting for the release (typically they just wait in an polling loop).
Ideally what we would like in our model is:

1. We want to allow releasing writes (like lock release or leave-turnstile) to leave the store-buffer-state clean, 
such that subsequent volatile reads do not require a flush.

2. The idea why this works is that other threads that may depend on the release but have not yet seen the releasing write do nothing bad, but are basically in a polling - loop (like lock acquire or wait-for-turnstile). So when the releasing write is not yet out of the store-buffer the store-buffer machine my take an extra polling loop (compared to an sequential consistent execution, where the write is considered immediately flushed to memory). But any final state (where all store-buffers are empty) should still be reachable by an sequential consistent execution.

For simulation 2. suggests that the waiting thread of the virtual machine should just stay in the same state as long as the 
sb-machine is captured in the polling loop. So the sb-machine takes extra turns, whereas the virtual machine does nothing. Formally, this is an issue for our model, since the sb-machine may read a lot of temporaries during the idle loop, all of which are not at all
read in the virtual machine. So expressing the simulation relation seems quite odd.
Another viewpoint is to introduce an intermediate (nondeterministic) program in the virtual machine, that always can descide and take an extra polling loop (without reading anything). This simulates the sb-program (modulo the extra reads to temporaries in the sb-program). In a second step we can argue that we can refine the intermediate program to the real program (all in the virtual machine) and still calculate the same *result*.

For wait-for-turnstile the pooling loop is even harder to justify being irrelevant compared to a spin-lock-acquire.
Wait-for-turnstile takes 2 samples and compares if they have changed. If not it waits and takes another sample, otherwise it continues.
So we really have to be able to compare the 2 values and deduce something from it. So they can't be just regarded as arbitrary values.

Spinlock-example:

Thread i: (release l in sb)
[l := 0 (release l)]

Thread j: (trying to acquire)
while (test&set l)...

If we maintain our flushing policy, and treat the l:=0 as nonvolatile (to keep the status clean), the release is already visible
in the virtual machine and thus the test&set succeeds emmediately, whereas in the sb-machine thraed j has to spin.

Idea:
1. Releasing writes are treated akin to non-volatile writes with respect to flushing policy 
(maybe we give them an extra name at some point)
2. To justify the non-volatile status when we want to write to them they have to be owned and *unshared*
   => This currently prohibits other threads to even read from them, which is bad for a memory cell that is used
   for synchronisation.
3. To compensate for that we relax the safety restriction for volatile reads.
   => Besides the 'shared' info we introduce a 'last' info (or maybe it is somehow merged with the shared info)  
       
      last:: address => value option

   With 'last' we store the last value written at the point we acquired the address in there (e.g. the 1 when acquiring a lock)
   Note that our ownership model hopefully guarantees that this is unique. There may be only one thread
   waking on the lock as long as the release is in its store-buffer.

   acquiring-write:
   l := 1; shared = old(shared)(l := None); owns = old(owns) + {l}; last = old(last)(l:=Some 1)
   releasing-write:
   l := 0; shared = old(shared)(l := Some True); owns = old(owns) - {l}; last=old(last)

   Volatile read's are now always allowed according to safety (maybe we introduce a flag to distinguish
   those liberated volatile reads from the things we allowed before (owned or shared)).

   


   The semantics of a volatile read is also changed to nondeterministically choose between either reading
   from memory or the last-info. Note that the semantics is *only* changed in the virtual machine. The sb machine
   stays the same.

   -------------------------
   read a t \<rightarrow> tmps(t := m a)

   last a = Some v
   -------------------------
   read a t \<rightarrow> tmps(t := v)

   (nondeterminism ensures that a program that always reads from memory is a refinement of our program)


By reading from last we attempt to be able to simulate the sb machine taking extra loops at program points where
the virtual machine could already proceed.

Spin-Lock example:
invariant i.  m l = 0 ==> lock is free
invariant ii. last l = Some v ==> v = 1
The virtual machine may always decide to take an extra loop (in case the lock was acquired at least once), alltough m l = 0;

Note:
* Values stored in last are always values that actually where (or will be) in memory at some point.


Turnstiles:
  enter-turnstile
  x := x + 1; shared = old(shared)(x:= None); owns = old(owns) + {x}; last = old(last)(x := Some (m x + 1));
  leave-turnstile
  x := x + 1; shared = old(shared)(x:= Some True); owns = old(owns) - {x}; last = old(last);

  wait-for turnstile
  takes a sample of x and when it is odd waits until x changes (by taking at least one other sample of x)

invariant i. even (m x) ==> not in turnstile
invariant ii. last x = Some v ==> odd(v)
Note that for turnstiles we know that only one thread will increment the counter;
(What do we need to know as invariants about the relation of last x and m x?)

To see if a turnstile is cautious enough we have various cases:
1. both samples are from memory: should be safe (if turnstiles make sense at all)
2. first sample from last, second sample from memory:
   * first sample from last: we think thread is in turnstile as it is always odd
   * second sample from memory: if its the same as the first sample we continue waiting (safe)
                                if not last was either outdated and we werent in the turnstile at all, 
                                or we have really left ts at least once (safe)
3. first sample from memory, second sample from last:
   * as there is only one writer to the ts, the sample from last is always at least the counter we have seen by the first sample (safe)
4. both samples from last
   * both sample are the same, we continue waiting (safe)
   * samples are different: As only one thread writes the ts, the 'last' samples also follow the program order, hence the
     thread has left the ts at least once (safe).



Think-tank

One might try to update 'last' not only on acquire, but simply every time a write actually hits memory.
Thinking of this 'last' actually just is the memory of the store-buffer machine. To correctly update 'last' in the
virtual machine is then difficult. Currently we maintain two values: the last one (being made interlocked or with a barrier)
and the (most actual) one in the virtual machine.
What about making last a set? Storing everything what happens between the acquire and the release (or flush)?
It seems to be a history.
So the general thing seems to be:
history: address \<Rightarrow> value list;
keeping track of all values (and their order) between two flushes (or interlocked things).
A volatile read has to be able to deal with any value in the histroy, starting from the one the
thread has read last.

If we would introduce a history for each thread, we would kind of explicitely model store-buffers.
This would be the 'ultimate solution' for TSO.: 

A histroy that should work:

history:: address \<Rightarrow> (lower-bound,upper-bound,(cnt,value) set)
history a = (lb,ub,V); (n,v) \<in> V \<Longrightarrow> lb \<le> ub \<and> lb \<le> n \<and> n \<le> ub; 

* every write increases the upper-bound and adds the value;
* every read increases the lower-bound (and removes all lower values)
* every flush empties the set;

write a v: 
  h a = (lb,ub,V) \<Longrightarrow> h'=h(a:=(lb,ub+1,V \<union> {(ub+1,v)}))

read a v: 
  h a = (lb,ub,V); (n,v) \<in> V; lb \<le> n \<and> n \<le> ub  \<Longrightarrow> h'=h(a:=(lb+1,ub,V ))

flush a
 h'=h(a:=(0,0,{}))

            read a v    
(syntax: h ----------> h')
   

The single global histroy should be fine for our case, since there is only one writer, and the reads are ordered (as they are volatile) and are in sync between the sb and the virtual machine.

26.11.2009
More thoughts on history:
Currently we see 4 operations on the history:

Read (for stale reads), Write (non-volatile) , Commit (fence), WriteCommit (volatile write and LMS)

1. A read of a thread that has an outstanding write to the same address in the store buffer, always gets this value and
  should not have influence on the lb of the history for other threads.

2. In the concurrency control we thought of up to now (spinlocks release, turnstiles, versioning writer) 
   the only use of the lb for reads is to guarantee an order in which a thread sees updates when it really
   issues multiple reads. We currently do not need arguments across threads like (if thread i has already seen a
   certain value than thread j has to see a newer one).

1 and 2 suggest that it might be a good idea to make the lb's thread local. This gives us some nice properties:
* a read only effects the thread local lb (and neiter the lb of another thread nor the history)
* a write, commit, writecommit only effects the history and no lb.
* write, commite,writecommit are completely deterministic

* To easily model fences we take the thread id into the history.

history:: address => (hb,i,V :: timestamp \<Rightarrow> value option)
lb (per thread): address \<Rightarrow> lb


selectors: 
* top (hb,i,V) = hb
* thread (hb,i,V) = i
* vals (hb,i,V) = V 

invariants:
* \<forall>a hb x V. h a = (hb,x,V) \<longrightarrow> \<forall>t \<in> dom V. t \<le> hb

* \<forall>a hb x V. h a = (hb,x,V) \<longrightarrow> hb \<in> dom V 

* for all threads: \<forall>a. lb a \<le> top (h a)

* the memory value of the sb-machine and all the values in takeWhile (Not \<circ> is_volatile_Write) are in the history of the virtual machine.
  * m\<^sub>s\<^sub>b a \<in> range (vals (h a))
  * Write False a v \<in> set (takeWhile (Not \<circ> is_volatile_Write)) sb \<Longrightarrow> v \<in> range (vals (h a))

* The top-value in the history of the virtual machine is the memory value in the virtual machine:
  vals (h a) (top (h a)) = Some (m a)

* Commit preserves top value
  
 

h'=\<lambda>a. let (hb,j,V) = h a 
       in if i=j then (hb,i,V|`{hb})
          else h a
---------------------------------------
        Commit i h h'


h a = (hb,j,V)      h'=h(a:= (hb+1,i,V(hb+1 \<mapsto> v))) 
----------------------------------------------------------
        Write i a v h h'

WriteCommit is simply first Write then Commit (in this order, to make sure that there is only one value in V)
After a WriteCommit the value read is determined.

(* not a transition just a read *)
h a = (hb,j,V)      V t = Some v    lb \<le> t
----------------------------------------------
         Read a v t lb h h
The thread updates his lb: lb(a:=t);




*)

(* 

(\([^,]*\),\([^,]*\),\([^,]*\),\([^,]*\),\([^,]*\),\([^,]*\),\([^,]*\),\([^,]*?\))

(\([^()]*\),\([^()]*\),\([^()]*\),\([^()]*\),\([^()]*\),\([^()]*\),\([^()]*\),\([^()]*\))
(\1,\2,\3,\4,\5,\6,\8)
*)

subsection \<open>Memory Instructions\<close>

type_synonym addr = nat 
type_synonym val = nat
type_synonym tmp = nat


type_synonym tmps = "tmp \<Rightarrow> val option" 
type_synonym sop = "tmp set \<times> (tmps \<Rightarrow> val)" \<comment> \<open>domain and function\<close>

locale valid_sop =
fixes sop :: "sop"
assumes valid_sop: "\<And>D f \<theta>. 
          \<lbrakk>sop=(D,f); D \<subseteq> dom \<theta>\<rbrakk> 
          \<Longrightarrow> 
          f \<theta> = f (\<theta>|`D)"

type_synonym memory = "addr \<Rightarrow> val"
type_synonym owns = "addr set"
type_synonym rels = "addr \<Rightarrow> bool option"
type_synonym shared = "addr \<Rightarrow> bool option" 
type_synonym acq = "addr set"
type_synonym rel = "addr set"
type_synonym lcl = "addr set"
type_synonym wrt = "addr set"
type_synonym cond = "tmps \<Rightarrow> bool"
type_synonym ret = "val \<Rightarrow> val \<Rightarrow> val"

datatype instr = Read bool addr tmp 
               | Write bool addr sop acq lcl rel wrt
               | RMW addr tmp sop cond ret acq lcl rel wrt  
               | Fence 
               | Ghost acq lcl rel wrt

type_synonym instrs = "instr list"


type_synonym ('p,'sb,'dirty,'owns,'rels) thread_config = 
  "'p \<times> instrs \<times> tmps \<times> 'sb \<times> 'dirty \<times> 'owns \<times> 'rels"
type_synonym ('p,'sb,'dirty,'owns,'rels,'shared) global_config = 
  "('p,'sb,'dirty,'owns,'rels) thread_config list \<times> memory \<times> 'shared "

definition "owned t = (let (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = t in \<O>)" 

lemma owned_simp [simp]: "owned (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = (\<O>)"
  by (simp add: owned_def)

definition "\<O>_sb t = (let (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = t in (\<O>,sb))" 

lemma \<O>_sb_simp [simp]: "\<O>_sb (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = (\<O>,sb)"
  by (simp add: \<O>_sb_def)

definition "released t = (let (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = t in \<R>)" 

lemma released_simp [simp]: "released (p,instrs,\<theta>,sb,\<D>,\<O>,\<R>) = (\<R>)"
  by (simp add: released_def)

lemma list_update_id': "v = xs ! i \<Longrightarrow> xs[i := v] = xs"
  by simp

lemmas converse_rtranclp_induct5 = 
converse_rtranclp_induct [where a="(m,sb,\<O>,\<R>,\<S>)" and b="(m',sb',\<O>',\<R>',\<S>')", split_rule,consumes 1, case_names refl step]

subsection \<open>Abstract Program Semantics\<close>

locale memory_system = 
  fixes
  memop_step ::  "(instrs \<times> tmps \<times> 'sb \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> 
                  (instrs \<times> tmps \<times> 'sb \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sub>m _" [60,60] 100) and
  
  storebuffer_step:: "(memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> (memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>s\<^sub>b _" [60,60] 100)


locale program =
  fixes
  program_step :: "tmps \<Rightarrow> 'p \<Rightarrow> 'p \<times> instrs \<Rightarrow> bool" ("_\<turnstile> _ \<rightarrow>\<^sub>p _" [60,60,60] 100) 
  \<comment> \<open>A program only accesses the shared memory indirectly, it can read the temporaries
        and can output a sequence of memory instructions\<close>

locale computation = memory_system + program +
  constrains
  \<comment> \<open>The constrains are only used to name the types @{typ "'sb"} and  @{typ "'p"}\<close>
  storebuffer_step:: "(memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> (memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> bool" and
  memop_step :: "
                  (instrs \<times> tmps \<times> 'sb \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> 
                  (instrs \<times> tmps \<times> 'sb \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> bool" 
                     and
  program_step :: "tmps \<Rightarrow> 'p \<Rightarrow> 'p \<times> instrs \<Rightarrow> bool" 
  fixes
  "record" :: "'p \<Rightarrow> 'p \<Rightarrow> instrs \<Rightarrow> 'sb \<Rightarrow> 'sb"
begin

inductive concurrent_step :: 
  "('p,'sb,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> ('p,'sb,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> bool"
                               ("_ \<Rightarrow> _" [60,60] 100)
where
  Program: 
   "\<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
     \<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is') \<rbrakk> \<Longrightarrow> 
     (ts,m,\<S>) \<Rightarrow> (ts[i:=(p',is@is',\<theta>,record p p' is' sb,\<D>,\<O>,\<R>)],m,\<S>)"

| Memop:
   "\<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
      (is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>m (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>') \<rbrakk> 
     \<Longrightarrow> 
     (ts,m,\<S>) \<Rightarrow> (ts[i:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')],m',\<S>')"


| StoreBuffer: 
   "\<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
     (m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b (m',sb',\<O>',\<R>',\<S>') \<rbrakk> \<Longrightarrow> 
     (ts,m,\<S>) \<Rightarrow> (ts[i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')],m',\<S>')"

definition final:: "('p,'sb,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> bool"
where
 "final c = (\<not> (\<exists>c'. c \<Rightarrow> c'))"


lemma store_buffer_steps:
assumes sb_step: "storebuffer_step^** (m,sb,\<O>,\<R>,\<S>) (m',sb',\<O>',\<R>',\<S>')"
shows "\<And>ts. i < length ts \<Longrightarrow> ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<Longrightarrow> 
         concurrent_step^** (ts,m,\<S>) (ts[i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')],m',\<S>')"
using sb_step 
proof (induct rule: converse_rtranclp_induct5)
  case refl then show ?case 
    by (simp add: list_update_id')
next
  case (step m sb \<O> \<R> \<S> m'' sb'' \<O>'' \<R>'' \<S>'')
  note i_bound = \<open>i < length ts\<close>
  note ts_i = \<open>ts ! i = (p, is, \<theta>, sb, \<D>, \<O>, \<R>)\<close>
  note step = \<open>(m, sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b (m'', sb'',\<O>'',\<R>'',\<S>'')\<close>
  let ?ts' = "ts[i := (p, is, \<theta>, sb'',\<D>, \<O>'',\<R>'')]"
  from StoreBuffer [OF i_bound ts_i step] 
  have "(ts, m, \<S>) \<Rightarrow> (?ts', m'', \<S>'')".
  also
  from i_bound have i_bound': "i < length ?ts'" by simp
  from i_bound have ts'_i: "?ts'!i = (p,is,\<theta>,sb'',\<D>,\<O>'',\<R>'')"
    by simp
  from step.hyps (3) [OF i_bound' ts'_i] i_bound
  have "concurrent_step\<^sup>*\<^sup>* (?ts', m'', \<S>'') (ts[i := (p, is, \<theta>, sb',\<D>, \<O>',\<R>')], m', \<S>')"
    by (simp)
  finally
  show ?case .
qed

lemma step_preserves_length_ts: 
  assumes step: "(ts,m,\<S>) \<Rightarrow> (ts',m',\<S>')"
  shows "length ts' = length ts"
using step
apply (cases)
apply auto
done
end

lemmas concurrent_step_cases = computation.concurrent_step.cases 
[cases set, consumes 1, case_names Program Memop StoreBuffer]

definition augment_shared:: "shared \<Rightarrow> addr set \<Rightarrow> addr set \<Rightarrow> shared" ("_ \<oplus>\<^bsub>_\<^esub> _" [61,1000,60] 61)
where
"\<S> \<oplus>\<^bsub>W\<^esub> S \<equiv> (\<lambda>a. if a \<in> S then Some (a \<in> W) else \<S> a)"

definition restrict_shared:: "shared \<Rightarrow> addr set \<Rightarrow> addr set \<Rightarrow> shared" ("_ \<ominus>\<^bsub>_\<^esub> _" [51,1000,50] 51)
where
"\<S> \<ominus>\<^bsub>A\<^esub> L \<equiv> (\<lambda>a. if a \<in> L then None 
                     else (case \<S> a of None \<Rightarrow> None
                            | Some writeable \<Rightarrow> Some (a \<in> A \<or> writeable)))"
                      
definition read_only :: "shared \<Rightarrow> addr set"
where
"read_only \<S> \<equiv> {a. (\<S> a = Some False)}"

definition shared_le:: "shared \<Rightarrow> shared \<Rightarrow> bool" (infix "\<subseteq>\<^sub>s" 50)
where 
"m\<^sub>1 \<subseteq>\<^sub>s m\<^sub>2 \<equiv> m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2 \<and> read_only m\<^sub>1 \<subseteq> read_only m\<^sub>2"

lemma shared_leD: "m\<^sub>1 \<subseteq>\<^sub>s m\<^sub>2 \<Longrightarrow> m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2 \<and> read_only m\<^sub>1 \<subseteq> read_only m\<^sub>2"
  by (simp add: shared_le_def)

lemma shared_le_map_le: "m\<^sub>1 \<subseteq>\<^sub>s m\<^sub>2 \<Longrightarrow> m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2"
  by (simp add: shared_le_def)

lemma shared_le_read_only_le: "m\<^sub>1 \<subseteq>\<^sub>s m\<^sub>2 \<Longrightarrow> read_only m\<^sub>1 \<subseteq> read_only m\<^sub>2"
  by (simp add: shared_le_def)

lemma dom_augment [simp]: "dom (m \<oplus>\<^bsub>W\<^esub> S) = dom m \<union> S"
  by (auto simp add: augment_shared_def)

lemma augment_empty [simp]: "S  \<oplus>\<^bsub>x\<^esub> {} = S"
  by (simp add: augment_shared_def)


lemma inter_neg [simp]: "X \<inter> - L = X - L"
  by blast

lemma dom_restrict_shared [simp]: "dom (m \<ominus>\<^bsub>A\<^esub> L) = dom m - L"
  by (auto simp add: restrict_shared_def split: option.splits)

lemma restrict_shared_UNIV [simp]: "(m \<ominus>\<^bsub>A\<^esub> UNIV) = Map.empty"
  by (auto simp add: restrict_shared_def split: if_split_asm option.splits)

lemma restrict_shared_empty [simp]: "(Map.empty \<ominus>\<^bsub>A\<^esub> L) = Map.empty"
  apply (rule ext)
  by (auto simp add: restrict_shared_def split: if_split_asm option.splits)

lemma restrict_shared_in [simp]: "a \<in> L \<Longrightarrow> (m \<ominus>\<^bsub>A\<^esub> L) a = None"
  by (auto simp add: restrict_shared_def split: if_split_asm option.splits)

lemma restrict_shared_out: "a \<notin> L \<Longrightarrow> (m \<ominus>\<^bsub>A\<^esub> L) a = 
  map_option (\<lambda>writeable. (a \<in> A \<or> writeable)) (m a)"
  by (auto simp add: restrict_shared_def split: if_split_asm option.splits)

lemma restrict_shared_out'[simp]: 
  "a \<notin> L \<Longrightarrow> m a = Some writeable \<Longrightarrow> (m \<ominus>\<^bsub>A\<^esub> L) a = Some (a \<in> A \<or> writeable)"
  by (simp add: restrict_shared_out)

lemma augment_mono_map': "A \<subseteq>\<^sub>m B \<Longrightarrow> (A \<oplus>\<^bsub>x\<^esub> C) \<subseteq>\<^sub>m (B \<oplus>\<^bsub>x\<^esub> C)"
  by (auto simp add: augment_shared_def map_le_def domIff)

lemma augment_mono_map: "A \<subseteq>\<^sub>s B \<Longrightarrow> (A \<oplus>\<^bsub>x\<^esub> C) \<subseteq>\<^sub>s (B \<oplus>\<^bsub>x\<^esub> C)"
  by (auto simp add:  augment_shared_def shared_le_def map_le_def read_only_def dom_def split: option.splits if_split_asm)

lemma restrict_mono_map: "A \<subseteq>\<^sub>s B \<Longrightarrow>  (A \<ominus>\<^bsub>x\<^esub> C) \<subseteq>\<^sub>s (B \<ominus>\<^bsub>x\<^esub> C)"
  by (auto simp add:  restrict_shared_def shared_le_def map_le_def read_only_def dom_def split: option.splits if_split_asm)

lemma augment_mono_aux: "dom A \<subseteq> dom B \<Longrightarrow> dom (A \<oplus>\<^bsub>x\<^esub> C) \<subseteq> dom (B \<oplus>\<^bsub>x\<^esub> C)"
  by auto

lemma restrict_mono_aux: "dom A \<subseteq> dom B \<Longrightarrow> dom (A \<ominus>\<^bsub>x\<^esub> C) \<subseteq> dom (B \<ominus>\<^bsub>x\<^esub> C)"
  by auto

lemma read_only_mono: "S \<subseteq>\<^sub>m S' \<Longrightarrow> a \<in> read_only S \<Longrightarrow> a \<in> read_only S'"
    by (auto simp add:  map_le_def domIff read_only_def dest!: bspec)

lemma in_read_only_restrict_conv: 
  "a \<in> read_only (\<S> \<ominus>\<^bsub>A\<^esub> L) = (a \<in> read_only \<S> \<and> a \<notin> L \<and> a \<notin> A)"
  by (auto simp add: read_only_def restrict_shared_def split: option.splits if_split_asm)



lemma in_read_only_augment_conv: "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R) = (if a \<in> R then a \<notin> W else a \<in> read_only \<S>)"
  by (auto simp add: read_only_def augment_shared_def)

lemmas in_read_only_convs = in_read_only_restrict_conv in_read_only_augment_conv

lemma read_only_dom: "read_only \<S> \<subseteq> dom \<S>"
  by (auto simp add: read_only_def dom_def)

lemma read_only_empty [simp]: "read_only Map.empty = {}"
  by (auto simp add: read_only_def)

lemma restrict_shared_fuse: "S \<ominus>\<^bsub>A\<^esub> L \<ominus>\<^bsub>B\<^esub> M = (S \<ominus>\<^bsub>(A \<union> B)\<^esub> (L \<union> M))"
apply (rule ext)
apply (auto simp add: restrict_shared_def split: option.splits if_split_asm)
done

lemma restrict_shared_empty_set [simp]: "S \<ominus>\<^bsub>{}\<^esub> {} = S"
  apply (rule ext)
  apply (auto simp add: restrict_shared_def split: option.splits if_split_asm)
  done

definition augment_rels:: "addr set \<Rightarrow> addr set \<Rightarrow> rels \<Rightarrow> rels"
where
"augment_rels S R \<R> = (\<lambda>a. if a \<in> R
                             then (case \<R> a of 
                                     None \<Rightarrow> Some (a \<in> S)
                                   | Some s \<Rightarrow> Some (s \<and> (a \<in> S)))
                             else \<R> a)"

declare domIff [iff del]

subsection \<open>Memory Transitions\<close>

locale gen_direct_memop_step = 
fixes emp::'rels and aug::"owns \<Rightarrow> rel \<Rightarrow> 'rels \<Rightarrow> 'rels"
begin
inductive gen_direct_memop_step :: "(instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> 'rels \<times> shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> 'rels \<times> shared ) \<Rightarrow> bool" 
                    ("_ \<rightarrow> _" [60,60] 100)
where
  Read: "(Read volatile a t # is,\<theta>, x, m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>
               (is, \<theta> (t\<mapsto>m a), x, m, \<D>, \<O>, \<R>, \<S>)"

| WriteNonVolatile:
  "(Write False a (D,f) A L R W#is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> 
          (is, \<theta>, x, m(a := f \<theta>), \<D>, \<O>, \<R>, \<S>)"

| WriteVolatile:
  "(Write True a (D,f) A L R W# is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>
         (is, \<theta>,  x, m(a:=f \<theta>), True, \<O> \<union> A - R, emp, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"

| Fence:
  "(Fence # is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is, \<theta>,x, m, False, \<O>, emp, \<S>)"

| RMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W # is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is, \<theta>(t\<mapsto>m a),x,m, False, \<O>, emp, \<S>)"

| RMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> 
         (is, \<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a)))),x, m(a:= f(\<theta>(t\<mapsto>m a))), False,\<O> \<union> A - R, emp, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"

| Ghost:
  "(Ghost A L R W # is, \<theta>, x, m, \<D>, \<O>, \<R>,  \<S>) \<rightarrow>
         (is, \<theta>, x, m, \<D>, \<O> \<union> A - R, aug (dom \<S>) R \<R> , \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
end

interpretation direct_memop_step: gen_direct_memop_step Map.empty augment_rels .

term direct_memop_step.gen_direct_memop_step
abbreviation direct_memop_step :: "(instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared ) \<Rightarrow> bool" 
                    ("_ \<rightarrow> _" [60,60] 100)
where
"direct_memop_step \<equiv> direct_memop_step.gen_direct_memop_step"

term "x \<rightarrow> Y"

abbreviation direct_memop_steps :: "
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared )  
                   \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sup>* _" [60,60] 100)
where 
"direct_memop_steps == (direct_memop_step)^**"

term "x \<rightarrow>\<^sup>* Y"

interpretation virtual_memop_step: gen_direct_memop_step "()" "(\<lambda>S R \<R>. ())" .

abbreviation virtual_memop_step :: "(instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> unit \<times> shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> unit \<times> shared ) \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sub>v _" [60,60] 100)
where
"virtual_memop_step \<equiv> virtual_memop_step.gen_direct_memop_step"

term "x \<rightarrow>\<^sub>v Y"

abbreviation virtual_memop_steps :: "
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> unit \<times> shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> unit \<times> memory \<times> bool \<times> owns \<times> unit \<times> shared )  
                   \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sub>v\<^sup>* _" [60,60] 100)
where 
"virtual_memop_steps == (virtual_memop_step)^**"

term "x \<rightarrow>\<^sup>* Y"



lemma virtual_memop_step_simulates_direct_memop_step: 
  assumes step:
  "(is, \<theta>, x, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', x', m', \<D>', \<O>', \<R>', \<S>')"
  shows "(is, \<theta>, x, m, \<D>, \<O>, (), \<S>) \<rightarrow>\<^sub>v (is', \<theta>', x', m', \<D>', \<O>', (), \<S>')"
using step
apply (cases)
apply (auto intro: virtual_memop_step.gen_direct_memop_step.intros)
done

subsection \<open>Safe Configurations of Virtual Machines\<close>

inductive safe_direct_memop_state :: "owns list \<Rightarrow> nat \<Rightarrow>  
                  (instrs \<times> tmps \<times> memory \<times> bool \<times> owns \<times> shared) \<Rightarrow> bool " 
                    ("_,_\<turnstile> _ \<surd>" [60,60,60] 100)
where
  Read: "\<lbrakk>a \<in> \<O> \<or> a \<in> read_only \<S> \<or> (volatile \<and> a \<in> dom \<S>);
          volatile \<longrightarrow> \<not> \<D> \<rbrakk>
        \<Longrightarrow>
        \<O>s,i\<turnstile>(Read volatile a t # is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| WriteNonVolatile:
  "\<lbrakk>a \<in> \<O>; a \<notin> dom \<S>\<rbrakk> 
   \<Longrightarrow>
   \<O>s,i\<turnstile>(Write False a (D,f) A L R W#is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| WriteVolatile:
  "\<lbrakk>\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> \<O>s!j;     
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter>  \<O>s!j = {};
   a \<notin> read_only \<S>\<rbrakk>
   \<Longrightarrow> 
   \<O>s,i\<turnstile>(Write True a (D,f) A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Fence:
  "\<O>s,i\<turnstile>(Fence # is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Ghost:
  "\<lbrakk>A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter> \<O>s!j = {}\<rbrakk>
   \<Longrightarrow> 
   \<O>s,i\<turnstile>(Ghost A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| RMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); a \<in> \<O> \<or> a \<in> dom \<S>\<rbrakk> \<Longrightarrow> 
   \<O>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| RMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a));  
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> \<O>s!j;
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> A \<inter> \<O>s!j  = {};
    a \<notin> read_only \<S>\<rbrakk> 
   \<Longrightarrow> 
   \<O>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Nil:   "\<O>s,i\<turnstile>([], \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

inductive safe_delayed_direct_memop_state :: "owns list \<Rightarrow> rels list \<Rightarrow> nat \<Rightarrow>  
                  (instrs \<times> tmps \<times> memory \<times> bool \<times> owns \<times> shared) \<Rightarrow> bool " 
                    ("_,_,_\<turnstile> _ \<surd>" [60,60,60,60] 100)
where
  Read: "\<lbrakk>a \<in> \<O> \<or> a \<in> read_only \<S> \<or> (volatile \<and> a \<in> dom \<S>);
          \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> (\<R>s!j) a \<noteq> Some False; \<comment> \<open>no release of unshared address\<close>
          \<not> volatile \<longrightarrow> (\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> dom (\<R>s!j));
          volatile \<longrightarrow> \<not> \<D> \<rbrakk>
        \<Longrightarrow>
        \<O>s,\<R>s,i\<turnstile>(Read volatile a t # is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| WriteNonVolatile:
  "\<lbrakk>a \<in> \<O>; a \<notin> dom \<S>; \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> dom (\<R>s!j)\<rbrakk> 
   \<Longrightarrow>
   \<O>s,\<R>s,i\<turnstile>(Write False a (D,f) A L R W#is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| WriteVolatile:
  "\<lbrakk>\<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> (\<O>s!j \<union> dom (\<R>s!j));     
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter>  (\<O>s!j \<union> dom (\<R>s!j)) = {};
   a \<notin> read_only \<S>\<rbrakk>
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(Write True a (D,f) A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Fence:
  "\<O>s,\<R>s,i\<turnstile>(Fence # is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Ghost:
  "\<lbrakk>A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow>  A \<inter> (\<O>s!j \<union> dom (\<R>s!j)) = {}\<rbrakk>
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(Ghost A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| RMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a)); a \<in> \<O> \<or> a \<in> dom \<S>; 
   \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> (\<R>s!j) a \<noteq> Some False \<comment> \<open>no release of unshared address\<close>\<rbrakk>
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| RMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a));  a \<in> \<O> \<or> a \<in> dom \<S>; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> a \<notin> (\<O>s!j \<union> dom (\<R>s!j));
    A \<subseteq> dom \<S> \<union> \<O>; L \<subseteq> A; R \<subseteq> \<O>; A \<inter> R = {}; 
    \<forall>j < length \<O>s. i\<noteq>j \<longrightarrow> A \<inter> (\<O>s!j \<union> dom (\<R>s!j))  = {};
    a \<notin> read_only \<S>\<rbrakk> 
   \<Longrightarrow> 
   \<O>s,\<R>s,i\<turnstile>(RMW a t (D,f) cond ret A L R W# is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

| Nil:   "\<O>s,\<R>s,i\<turnstile>([], \<theta>, m, \<D>, \<O>, \<S>)\<surd>"

lemma memop_safe_delayed_implies_safe_free_flowing: 
  assumes safe_delayed: "\<O>s,\<R>s,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
  shows "\<O>s,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
using safe_delayed
proof (cases)
  case Read thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.intros)
next
  case WriteNonVolatile thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.intros)
next
  case WriteVolatile thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.intros)
next
  case Fence thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.intros)
next
  case Ghost thus ?thesis
  by (fastforce intro!: safe_direct_memop_state.Ghost)
next
  case RMWReadOnly thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.intros)
next
  case RMWWrite thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.RMWWrite)
next
  case Nil thus ?thesis
    by (fastforce intro!: safe_direct_memop_state.Nil)
qed

lemma memop_empty_rels_safe_free_flowing_implies_safe_delayed: 
  assumes safe: "\<O>s,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>" 
  assumes empty: "\<forall>\<R> \<in> set \<R>s. \<R> = Map.empty"
  assumes leq: "length \<O>s = length \<R>s"
  assumes unowned_shared: "(\<forall>a. (\<forall>i < length \<O>s. a \<notin> (\<O>s!i)) \<longrightarrow> a \<in> dom \<S>)"
  assumes Os_i: "\<O>s!i = \<O>"
  shows "\<O>s,\<R>s,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>"
using safe
proof (cases)
  case Read thus ?thesis
    using leq empty
    by (fastforce intro!: safe_delayed_direct_memop_state.Read dest: nth_mem)
next
  case WriteNonVolatile thus ?thesis
    using leq empty
    by (fastforce intro!: safe_delayed_direct_memop_state.intros dest: nth_mem)
next
  case WriteVolatile thus ?thesis
  using leq empty
    apply clarsimp
    apply (rule safe_delayed_direct_memop_state.WriteVolatile)
    apply (auto)
    apply  (drule nth_mem)
    apply  fastforce
    apply (drule nth_mem)
    apply fastforce
    done
next
  case Fence thus ?thesis
    by (fastforce intro!: safe_delayed_direct_memop_state.intros)
next
  case Ghost thus ?thesis
  using leq empty
    apply clarsimp
    apply (rule safe_delayed_direct_memop_state.Ghost)
    apply (auto)
    apply (drule nth_mem)
    apply fastforce
    done
next
  case RMWReadOnly thus ?thesis
  using leq empty
    by (fastforce intro!: safe_delayed_direct_memop_state.intros dest: nth_mem)
next
  case (RMWWrite cond t a A L R D f ret W) thus ?thesis
  using leq empty unowned_shared [rule_format, where a=a] Os_i
    apply clarsimp
    apply (rule safe_delayed_direct_memop_state.RMWWrite)
    apply (auto)
    apply  (drule nth_mem)
    apply  fastforce
    apply (drule nth_mem)
    apply fastforce
    done
next
  case Nil thus ?thesis
    by (fastforce intro!: safe_delayed_direct_memop_state.Nil)
qed


inductive id_storebuffer_step:: 
  "(memory \<times> unit \<times> owns \<times> rels \<times> shared) \<Rightarrow> (memory \<times> unit \<times> owns \<times> rels \<times> shared) \<Rightarrow> bool" ("_ \<rightarrow>\<^sub>I _" [60,60] 100)
where
  Id: "(m,x,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>I (m,x,\<O>,\<R>,\<S>)"

definition empty_storebuffer_step:: "(memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> (memory \<times> 'sb \<times> 'owns \<times> 'rels \<times> 'shared) \<Rightarrow> bool"
where
"empty_storebuffer_step c c' = False"

context program
begin

abbreviation direct_concurrent_step ::
  "('p,unit,bool,owns,rels,shared) global_config \<Rightarrow> ('p,unit,bool,owns,rels,shared) global_config \<Rightarrow> bool"
   ("_ \<Rightarrow>\<^sub>d _" [100,60] 100)
where
  "direct_concurrent_step \<equiv> 
     computation.concurrent_step direct_memop_step.gen_direct_memop_step empty_storebuffer_step program_step
      (\<lambda>p p' is sb. sb)"

abbreviation direct_concurrent_steps::  
  "('p,unit,bool,owns,rels,shared) global_config \<Rightarrow> ('p,unit,bool,owns,rels,shared) global_config \<Rightarrow> bool" 
    ("_ \<Rightarrow>\<^sub>d\<^sup>* _" [60,60] 100)
where
"direct_concurrent_steps == direct_concurrent_step^**"  

abbreviation virtual_concurrent_step ::
  "('p,unit,bool,owns,unit,shared) global_config \<Rightarrow> ('p,unit,bool,owns,unit,shared) global_config \<Rightarrow> bool"
   ("_ \<Rightarrow>\<^sub>v _" [100,60] 100)
where
  "virtual_concurrent_step \<equiv> 
     computation.concurrent_step virtual_memop_step.gen_direct_memop_step empty_storebuffer_step program_step
      (\<lambda>p p' is sb. sb)"

abbreviation virtual_concurrent_steps::  
  "('p,unit,bool,owns,unit,shared) global_config \<Rightarrow> ('p,unit,bool,owns,unit,shared) global_config \<Rightarrow> bool" 
    ("_ \<Rightarrow>\<^sub>v\<^sup>* _" [60,60] 100)
where
"virtual_concurrent_steps == virtual_concurrent_step^**"  

(* check if abbreviations work in both directions *)
term "x \<Rightarrow>\<^sub>v Y"
term "x \<Rightarrow>\<^sub>d Y"

term "x \<Rightarrow>\<^sub>d\<^sup>* Y"
term "x \<Rightarrow>\<^sub>v\<^sup>* Y"

end

definition
 "safe_reach step safe cfg \<equiv> 
       \<forall> cfg'. step^** cfg cfg' \<longrightarrow> safe cfg'"

lemma safe_reach_safe_refl: "safe_reach step safe cfg \<Longrightarrow> safe cfg"       
  apply (auto simp add: safe_reach_def)
  done

lemma safe_reach_safe_rtrancl: "safe_reach step safe cfg \<Longrightarrow> step^** cfg cfg' \<Longrightarrow> safe cfg'"       
  by (simp only: safe_reach_def)

lemma safe_reach_steps: "safe_reach step safe cfg \<Longrightarrow> step^** cfg cfg' \<Longrightarrow> safe_reach step safe  cfg'" 
  apply (auto simp add: safe_reach_def intro: rtranclp_trans)
  done
  
lemma safe_reach_step: "safe_reach step safe cfg \<Longrightarrow> step cfg cfg' \<Longrightarrow> safe_reach step safe cfg'"
  apply (erule safe_reach_steps)
  apply (erule r_into_rtranclp)
  done

context program
begin

abbreviation
 "safe_reach_direct \<equiv> safe_reach direct_concurrent_step"

lemma safe_reac_direct_def':
 "safe_reach_direct safe cfg \<equiv> 
       \<forall> cfg'. cfg \<Rightarrow>\<^sub>d\<^sup>* cfg' \<longrightarrow> safe cfg'"
  by( simp add: safe_reach_def)

abbreviation
 "safe_reach_virtual \<equiv> safe_reach virtual_concurrent_step"

lemma safe_reac_virtual_def':
 "safe_reach_virtual safe cfg \<equiv> 
       \<forall> cfg'. cfg \<Rightarrow>\<^sub>v\<^sup>* cfg' \<longrightarrow> safe cfg'"
  by( simp add: safe_reach_def)
end

definition
 "safe_free_flowing cfg \<equiv> let (ts,m,\<S>) = cfg 
             in (\<forall>i < length ts. let (p,is,\<theta>,x,\<D>,\<O>,\<R>) = ts!i in 
                 map owned ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd>)"

lemma safeE: "\<lbrakk>safe_free_flowing (ts,m,\<S>);i<length ts; ts!i=(p,is,\<theta>,x,\<D>,\<O>,\<R>)\<rbrakk>
              \<Longrightarrow> map owned ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd>"
  by (auto simp add: safe_free_flowing_def)

definition
 "safe_delayed cfg \<equiv> let (ts,m,\<S>) = cfg 
             in (\<forall>i < length ts. let (p,is,\<theta>,x,\<D>,\<O>,\<R>) = ts!i in 
                 map owned ts,map released ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd>)"

lemma safe_delayedE: "\<lbrakk>safe_delayed (ts,m,\<S>);i<length ts; ts!i=(p,is,\<theta>,x,\<D>,\<O>,\<R>)\<rbrakk>
              \<Longrightarrow> map owned ts,map released ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd>"
  by (auto simp add: safe_delayed_def)

definition "remove_rels  \<equiv> map (\<lambda>(p,is,\<theta>,sb,\<D>,\<O>,\<R>). (p,is,\<theta>,sb,\<D>,\<O>,()))"

theorem (in program) virtual_simulates_direct_step:
  assumes step: "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts',m',\<S>')"
  shows "(remove_rels ts,m,\<S>) \<Rightarrow>\<^sub>v (remove_rels ts',m',\<S>')"
using step
proof -
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  interpret virtual_computation:
    computation virtual_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from step show ?thesis
  proof (cases)
    case (Program j p "is" \<theta> sb \<D> \<O> \<R> p' is')
    then obtain
      ts': "ts' = ts[j:=(p',is@is',\<theta>,sb,\<D>,\<O>,\<R>)]" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')"
      by auto
    from ts_j j_bound have 
      vts_j: "remove_rels ts!j = (p,is,\<theta>,sb,\<D>,\<O>,())" by (auto simp add: remove_rels_def)
    
    from virtual_computation.Program [OF _ vts_j prog_step, of m \<S>] j_bound ts'
    show ?thesis
      by (clarsimp simp add: \<S>' m' remove_rels_def map_update)
  next
    case (Memop j p "is" \<theta> sb \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[j:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"  and
      mem_step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', sb',m', \<D>',  \<O>', \<R>', \<S>')"
      by auto

    from ts_j j_bound have 
      vts_j: "remove_rels ts!j = (p,is,\<theta>,sb,\<D>,\<O>,())" by (auto simp add: remove_rels_def)

    from virtual_computation.Memop[OF _ vts_j virtual_memop_step_simulates_direct_memop_step [OF mem_step]] j_bound ts'
    show ?thesis
      by (clarsimp simp add: remove_rels_def map_update)
  next
    case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
    hence False 
      by (auto simp add: empty_storebuffer_step_def)
    thus ?thesis ..
  qed
qed

lemmas converse_rtranclp_induct_sbh_steps = converse_rtranclp_induct
[of _ "(ts,m,\<S>)" "(ts',m',\<S>')", split_rule,
   consumes 1, case_names refl step]


theorem (in program) virtual_simulates_direct_steps:
  assumes steps: "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* (ts',m',\<S>')"
  shows "(remove_rels ts,m,\<S>) \<Rightarrow>\<^sub>v\<^sup>* (remove_rels ts',m',\<S>')"
using steps
proof (induct rule: converse_rtranclp_induct_sbh_steps)
  case refl thus ?case by auto
next
  case (step ts m \<S> ts'' m'' \<S>'')
  then obtain 
    first: "(ts, m, \<S>) \<Rightarrow>\<^sub>d (ts'', m'', \<S>'')" and
    hyp: "(remove_rels ts'', m'', \<S>'') \<Rightarrow>\<^sub>v\<^sup>* (remove_rels ts', m', \<S>')"
    by blast
  note virtual_simulates_direct_step [OF first] also note hyp
  finally
  show ?case by blast
qed

locale simple_ownership_distinct =
fixes ts::"('p,'sb,'dirty,owns,'rels) thread_config list"
assumes simple_ownership_distinct:
   "\<And>i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j. 
      \<lbrakk>i < length ts; j < length ts; i \<noteq> j; 
    ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i); ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)
      \<rbrakk> \<Longrightarrow> \<O>\<^sub>i \<inter> \<O>\<^sub>j = {}"

lemma (in simple_ownership_distinct)
  simple_ownership_distinct_nth_update:
 "\<And>i p is \<theta> \<O> \<R> \<D> xs sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
    \<forall>j < length ts. i\<noteq>j \<longrightarrow> (let (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j) = ts!j 
          in (\<O>') \<inter> (\<O>\<^sub>j) ={}) \<rbrakk> \<Longrightarrow> 
     simple_ownership_distinct (ts[i := (p',is',\<theta>',sb',\<D>',\<O>',\<R>')])"
  apply (unfold_locales)
  apply (clarsimp simp add: nth_list_update split: if_split_asm)
  apply   (force dest: simple_ownership_distinct simp add: Let_def)
  apply  (fastforce dest: simple_ownership_distinct simp add: Let_def)
  apply (fastforce dest: simple_ownership_distinct simp add: Let_def)
  done

locale read_only_unowned =
fixes \<S>::shared and ts::"('p,'sb,'dirty,owns,'rels) thread_config list"
assumes read_only_unowned:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   \<O> \<inter> read_only \<S> = {}"

lemma (in read_only_unowned)
  read_only_unowned_nth_update:
 "\<And>i p is \<O> \<R> \<D> acq \<theta> sb. 
   \<lbrakk>i < length ts; \<O> \<inter> read_only \<S>  = {}\<rbrakk> \<Longrightarrow> 
     read_only_unowned \<S> (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
  apply (unfold_locales)
  apply   (auto dest: read_only_unowned
       simp add:  nth_list_update split: if_split_asm)
  done

locale unowned_shared =
fixes \<S>::shared and ts::"('p,'sb,'dirty,owns,'rels) thread_config list"
assumes unowned_shared: "- \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts) \<subseteq> dom \<S>"

lemma (in unowned_shared)
  unowned_shared_nth_update:
  assumes i_bound: "i < length ts" 
  assumes ith: "ts!i=(p,is,xs,sb,\<D>,\<O>,\<R>)" 
  assumes subset: "\<O>  \<subseteq> \<O>'"
  shows "unowned_shared \<S> (ts[i := (p',is',xs',sb',\<D>',\<O>',\<R>')])"
proof -
  from i_bound ith subset
  have "\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts) \<subseteq> 
        \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set (ts[i := (p',is',xs',sb',\<D>',\<O>',\<R>')]))"

    apply (auto simp add: in_set_conv_nth nth_list_update split: if_split_asm)
    subgoal for x p'' is'' xs'' sb'' \<D>''  \<O>'' \<R>'' j
    apply (case_tac "j=i")
    apply  (rule_tac x="(p',is',xs',sb',\<D>',\<O>',\<R>')" in bexI)
    apply   fastforce
    apply  (fastforce simp add: in_set_conv_nth)
    apply (rule_tac x="(p'',is'',xs'',sb'',\<D>'',\<O>'',\<R>'')" in bexI)
    apply  fastforce
    apply (fastforce simp add: in_set_conv_nth)
    done 
    done
  hence "- \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set (ts[i := (p',is',xs',sb',\<D>',\<O>',\<R>')])) \<subseteq> 
         - \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts)"
    by blast
  also note unowned_shared
  finally
  show ?thesis
    by (unfold_locales)
qed

lemma (in unowned_shared) a_unowned_by_others_owned_or_shared:
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_unowned_others:
        "\<forall>j<length (map owned ts). i \<noteq> j \<longrightarrow> 
          (let \<O>\<^sub>j = (map owned ts)!j in a \<notin> \<O>\<^sub>j)" 

  shows "a \<in> \<O> \<or> a \<in> dom \<S>"
proof -
  {
    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
    assume a_unowned: "a \<notin> \<O>"
    assume j_bound: "j < length ts"
    assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j,\<R>\<^sub>j)"
    have "a \<notin> \<O>\<^sub>j"
    proof (cases "i=j")
      case True with a_unowned ts_i jth
      show ?thesis
	by auto
    next
      case False
      from a_unowned_others [rule_format, of j] j_bound jth False
      show ?thesis
	by auto
    qed
  } note lem = this
  {
    assume "a \<notin> \<O>"
    from lem [OF this]
    have "a \<in>  - \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts)"
      by (fastforce simp add: in_set_conv_nth)
    with unowned_shared have "a \<in> dom \<S>"
      by auto
  } 
  then
  show ?thesis
    by auto
qed

lemma (in unowned_shared) unowned_shared': 
  assumes notin: "\<forall>i < length ts. a \<notin> owned (ts!i)"
  shows "a \<in> dom \<S>"
proof -
  from notin  have "a \<in> - \<Union>((\<lambda>(_, _, _, _, _, \<O>, _). \<O>) ` set ts)"
    by (force simp add: in_set_conv_nth)
  with unowned_shared show ?thesis by blast
qed

lemma unowned_shared_def': "unowned_shared \<S> ts = (\<forall>a. (\<forall>i < length ts. a \<notin> owned (ts!i)) \<longrightarrow> a \<in> dom \<S>)"
apply rule
apply  clarsimp
apply (rule unowned_shared.unowned_shared')
apply   fastforce
apply  fastforce
apply (unfold unowned_shared_def)
apply clarsimp
subgoal for x
apply (drule_tac x=x in spec)
apply (erule impE)
apply  clarsimp
apply  (case_tac "(ts!i)")
apply  (drule nth_mem)
apply auto
done
done 

definition
 "initial cfg \<equiv> let (ts,m,\<S>) = cfg 
             in unowned_shared \<S> ts \<and>
                (\<forall>i < length ts. let (p,is,\<theta>,x,\<D>,\<O>,\<R>) = ts!i in 
                  \<R> = Map.empty )"

lemma initial_empty_rels: "initial (ts,m,\<S>) \<Longrightarrow> \<forall>\<R> \<in> set (map released ts). \<R> = Map.empty"
  by (fastforce simp add: initial_def simp add: in_set_conv_nth)

lemma initial_unowned_shared: "initial (ts,m,\<S>) \<Longrightarrow> unowned_shared \<S> ts"
  by (fastforce simp add: initial_def )

lemma initial_safe_free_flowing_implies_safe_delayed:
assumes init: "initial c" 
assumes safe: "safe_free_flowing c"
shows "safe_delayed c"
proof -
  obtain ts \<S> m where c: "c=(ts,m,\<S>)" by (cases c)
  from initial_empty_rels [OF init [simplified c]]
  have rels_empty: "\<forall>\<R>\<in>set (map released ts). \<R> = Map.empty".
  from initial_unowned_shared [OF init [simplified c]] have "unowned_shared \<S> ts"
    by auto
  hence us:"(\<forall>a. (\<forall>i < length (map owned ts). a \<notin> (map owned ts!i)) \<longrightarrow> a \<in> dom \<S>)"
    by (simp add:unowned_shared_def')
  {
    fix i p "is" \<theta> x \<D> \<O> \<R>
    assume i_bound: "i < length ts"
    assume ts_i: "ts!i = (p,is,\<theta>,x,\<D>,\<O>,\<R>)"
    have "map owned ts,map released ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd>"
    proof -
      from safeE [OF safe [simplified c] i_bound ts_i] 
      have "map owned ts,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>".
      from memop_empty_rels_safe_free_flowing_implies_safe_delayed [OF this rels_empty _ us] i_bound ts_i
      show ?thesis
        by simp
    qed
  }
  then show ?thesis 
    by (fastforce simp add: c safe_delayed_def)
qed


locale program_progress = program +
assumes progress: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p',is') \<Longrightarrow> p' \<noteq> p \<or> is' \<noteq> []"
text \<open>The assumption `progress' could be avoided if we introduce stuttering steps in lemma \<open>undo_local_step\<close>
or make the scheduling of threads explicit, such that we can directly express that `thread i does not make a step'.
\<close>

lemma (in program_progress) undo_local_step:
assumes step: "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts',m',\<S>')"
assumes i_bound: "i < length ts"
assumes unchanged: "ts!i = ts'!i"
assumes safe_delayed_undo: "safe_delayed (u_ts,u_m,u_shared)" \<comment> \<open>proof should also work with weaker @{const safe_free_flowing}\<close>
assumes leq: "length u_ts = length ts"
assumes others_same: "\<forall>j < length ts. j\<noteq>i \<longrightarrow> u_ts!j = ts!j"
assumes u_ts_i: "u_ts!i=(u_p,u_is,u_tmps,u_x,u_dirty,u_owns,u_rels)"
assumes u_m_other: "\<forall>a. a \<notin> u_owns \<longrightarrow> u_m a = m a"
assumes u_m_shared: "\<forall>a. a \<in> u_owns \<longrightarrow> a \<in> dom u_shared \<longrightarrow> u_m a = m a"
assumes u_shared: "\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts!i) \<longrightarrow> u_shared a = \<S> a"
assumes dist: "simple_ownership_distinct u_ts"
assumes dist_ts: "simple_ownership_distinct ts"
shows "\<exists>u_ts' u_shared' u_m'. (u_ts,u_m,u_shared) \<Rightarrow>\<^sub>d (u_ts',u_m',u_shared') \<and>
         \<comment> \<open>thread i is unchanged\<close>
         u_ts'!i = u_ts!i \<and>
         (\<forall>a \<in> u_owns. u_shared' a = u_shared a) \<and>
         (\<forall>a \<in> u_owns. \<S>' a = \<S> a) \<and>
         (\<forall>a \<in> u_owns. u_m' a = u_m a) \<and>
         (\<forall>a \<in> u_owns. m' a = m a) \<and>

         \<comment> \<open>other threads are simulated\<close>
         (\<forall>j < length ts. j\<noteq>i \<longrightarrow> u_ts'!j = ts'!j) \<and>
         (\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts!i) \<longrightarrow> u_shared' a = \<S>' a) \<and>
         (\<forall>a. a \<notin> u_owns \<longrightarrow> u_m' a = m' a)"
proof -
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from dist interpret simple_ownership_distinct u_ts .
  from step
  show ?thesis
  proof (cases)
    case (Program j p "is" \<theta> sb \<D> \<O> \<R> p' is')
    then obtain
      ts': "ts' = ts[j:=(p',is@is',\<theta>,sb,\<D>,\<O>,\<R>)]" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')"
      by auto

    from progress [OF prog_step] i_bound unchanged ts_j ts'
    have neq_j_i: "j\<noteq>i"
      by auto


    from others_same [rule_format, OF j_bound neq_j_i] ts_j
    have u_ts_j: "u_ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    from leq j_bound have j_bound': "j < length u_ts"
      by simp
    from leq i_bound have i_bound': "i < length u_ts"
      by simp

    from direct_computation.Program [OF j_bound' u_ts_j prog_step]
    have ustep:" (u_ts,u_m, u_shared) \<Rightarrow>\<^sub>d (u_ts[j := (p', is @ is', \<theta>, sb, \<D>, \<O>, \<R>)], u_m, u_shared)".  show ?thesis
      apply -
      apply (rule exI)
      apply (rule exI)
      apply (rule exI)
      apply (rule conjI)
      apply (rule ustep)
      using neq_j_i others_same u_m_other u_shared j_bound leq ts_j 
      apply (auto simp add: nth_list_update ts' \<S>' m')
      done
  next
    case (Memop j p "is" \<theta> sb \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[j:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"  and
      mem_step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', sb',m', \<D>',  \<O>', \<R>', \<S>')"
      by auto

    from mem_step i_bound unchanged ts_j
    have neq_j_i: "j\<noteq>i"
      by cases (auto simp add: ts')

    from others_same [rule_format, OF j_bound neq_j_i] ts_j
    have u_ts_j: "u_ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    from leq j_bound have j_bound': "j < length u_ts"
      by simp
    from leq i_bound have i_bound': "i < length u_ts"
      by simp
    from safe_delayedE [OF safe_delayed_undo j_bound' u_ts_j]
    have safe_j: "map owned u_ts,map released u_ts,j\<turnstile>(is, \<theta>, u_m, \<D>, \<O>, u_shared)\<surd>".
    from simple_ownership_distinct [OF j_bound' i_bound' neq_j_i u_ts_j u_ts_i]
    have owns_u_owns: "\<O> \<inter> u_owns = {}" .
    from mem_step
    show ?thesis
    proof (cases)
      case (Read volatile a t)
      then obtain
        "is": "is = Read volatile a t # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain 
        access_cond: "a \<in> \<O> \<or> a \<in> read_only u_shared \<or> 
                   (volatile \<and> a \<in> dom u_shared)" 
      
        and
        clean: "volatile \<longrightarrow> \<not> \<D>"
        by cases auto
      have u_m_a_eq: "u_m a = m a"
      proof (cases "a \<in> u_owns")
        case True
        with simple_ownership_distinct [OF j_bound' i_bound' neq_j_i u_ts_j u_ts_i]
        have "a \<notin> \<O>" by auto
        with access_cond read_only_dom [of u_shared] have "a \<in> dom u_shared"
          by auto
        from u_m_shared [rule_format, OF True this] 
        show ?thesis .
      next
        case False
        from u_m_other [rule_format, OF this]
        show ?thesis .
      qed
      note Read' = direct_memop_step.Read [of volatile a t "is'" \<theta> sb u_m \<D> \<O> \<R> u_shared]
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Read' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d (u_ts[j := (p, is', \<theta>(t \<mapsto> u_m a), sb, \<D>, \<O>, \<R>)], u_m, u_shared)".
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j 
        by (auto simp add: nth_list_update ts' eqs' u_m_a_eq)
    next
      case (WriteNonVolatile a D f A L R W)
      then obtain
        "is": "is = Write False a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        owned: "a \<in> \<O>" and unshared: "a \<notin> dom u_shared"
        by cases auto

      from simple_ownership_distinct [OF j_bound' i_bound' neq_j_i u_ts_j u_ts_i] owned
      have a_unowned_i: "a \<notin> u_owns"
        by auto
      note Write' = direct_memop_step.WriteNonVolatile [of a D f A L R W is' \<theta> sb u_m \<D> \<O> \<R> u_shared]
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Write' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d (u_ts[j := (p, is', \<theta>, sb, \<D>, \<O>, \<R>)], u_m (a := f \<theta>), u_shared)".
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j a_unowned_i
        apply (auto simp add: nth_list_update ts' eqs')
        done
    next
      case (WriteVolatile a D f A L R W)
      then obtain
        "is": "is = Write True a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=True" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        a_unowned_others: "\<forall>k < length u_ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned u_ts!k \<union> dom (map released u_ts!k))" and
        A: "A \<subseteq> dom u_shared \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length u_ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned u_ts!k \<union> dom (map released u_ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only u_shared"
        by cases auto

      note Write' = direct_memop_step.WriteVolatile [of a D f A L R W is' \<theta> sb u_m \<D> \<O> \<R> u_shared]
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Write' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d 
                   (u_ts[j := (p, is', \<theta>, sb, True, \<O> \<union> A - R, Map.empty)], u_m (a := f \<theta>), u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      from A_unowned_others [rule_format, OF i_bound' neq_j_i] u_ts_i i_bound' 
      have A_u_owns: "A \<inter> u_owns = {}" by auto
      {
        fix a
        assume a_u_owns: "a \<in> u_owns"
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = u_shared a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_owned_shared = this
      from a_unowned_others [rule_format, OF i_bound' neq_j_i] u_ts_i i_bound'  have a_u_owns: "a \<notin> u_owns" by auto
      {
        fix a
        assume a_u_owns: "a \<notin> u_owns"
        assume a_u_owns_orig: "a \<notin> owned (ts!i)"
        from u_shared [rule_format, OF a_u_owns a_u_owns_orig]
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        using R_owns A_R L_A A_u_owns owns_u_owns 
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_unowned_shared = this
      {
        fix a
        assume a_u_owns: "a \<in> u_owns"

        have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note \<S>'_shared = this

      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j u_owned_shared a_u_owns u_unowned_shared \<S>'_shared
        apply (auto simp add: nth_list_update ts' eqs')
        done
    next      
      case Fence
      then obtain
        "is": "is = Fence # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      note Fence' = direct_memop_step.Fence [of is' \<theta> sb u_m \<D> \<O> \<R> u_shared]
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Fence' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d (u_ts[j := (p, is', \<theta>, sb, False, \<O>, Map.empty)], u_m, u_shared)".
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j 
        by (auto simp add: nth_list_update ts' eqs' )
    next
      case (RMWReadOnly cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t\<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>" and
        cond: "\<not> cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from safe_j [simplified "is"] owns_u_owns u_ts_i i_bound' neq_j_i
      obtain 
        access_cond: "a \<notin> u_owns \<or> (a \<in> dom u_shared \<and> a \<in> u_owns)"
        by cases auto
        
      from u_m_other u_m_shared access_cond
      have u_m_a_eq: "u_m a = m a"
        by auto
      from cond u_m_a_eq have cond': "\<not> cond (\<theta>(t \<mapsto> u_m a))"
        by auto
      note RMWReadOnly' = direct_memop_step.RMWReadOnly [of cond \<theta> t u_m a D f ret A L R W is' sb \<D> \<O> \<R> u_shared, 
        OF cond']
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF RMWReadOnly' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d (u_ts[j := (p, is', \<theta>(t \<mapsto> u_m a), sb, False, \<O>, Map.empty)], u_m, u_shared)".
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j
        by (auto simp add: nth_list_update ts' eqs' u_m_a_eq)
    next
      case (RMWWrite cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> m a))))" and
        sb': "sb'=sb" and
        m': "m'=m(a := f (\<theta>(t \<mapsto> m a)))" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
        cond: "cond (\<theta>(t \<mapsto> m a))"
        by auto

      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from safe_j [simplified "is"] owns_u_owns u_ts_i i_bound' neq_j_i
      obtain 
        access_cond: "a \<notin> u_owns \<or> (a \<in> dom u_shared \<and> a \<in> u_owns)"
        by cases auto
        
      from u_m_other u_m_shared access_cond
      have u_m_a_eq: "u_m a = m a"
        by auto
      from cond u_m_a_eq have cond': "cond (\<theta>(t \<mapsto> u_m a))"
        by auto
      from safe_j [simplified "is"] cond'
      obtain
        a_unowned_others: "\<forall>k < length u_ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned u_ts!k \<union> dom (map released u_ts!k))" and
        A: "A \<subseteq> dom u_shared \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length u_ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned u_ts!k \<union> dom (map released u_ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only u_shared"
        by cases auto

      note Write' = direct_memop_step.RMWWrite [of cond \<theta> t u_m a D f ret A L R W is' sb \<D> \<O> \<R> u_shared, 
        OF cond']
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Write' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d 
                   (u_ts[j := (p, is', \<theta>(t \<mapsto> ret (u_m a) (f (\<theta>(t \<mapsto> u_m a)))), sb, False, \<O> \<union> A - R, Map.empty)], u_m(a := f (\<theta>(t \<mapsto> u_m a))), 
                    u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      from A_unowned_others [rule_format, OF i_bound' neq_j_i] u_ts_i i_bound' 
      have A_u_owns: "A \<inter> u_owns = {}" by auto
      {
        fix a
        assume a_u_owns: "a \<in> u_owns"
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = u_shared a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_owned_shared = this
      from a_unowned_others [rule_format, OF i_bound' neq_j_i] u_ts_i i_bound'  have a_u_owns: "a \<notin> u_owns" by auto
      {
        fix a
        assume a_u_owns: "a \<notin> u_owns"
        assume a_u_owns_orig: "a \<notin> owned (ts!i)"
        from u_shared [rule_format, OF a_u_owns this]
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        using R_owns A_R L_A A_u_owns owns_u_owns 
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_unowned_shared = this
      {
        fix a
        assume a_u_owns: "a \<in> u_owns"

        have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note \<S>'_shared = this
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j u_owned_shared a_u_owns u_unowned_shared \<S>'_shared
        apply (auto simp add: nth_list_update ts' eqs')
        done
    next
      case (Ghost A L R W) 
      then obtain
        "is": "is = Ghost A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=augment_rels (dom \<S>) R \<R>" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        A: "A \<subseteq> dom u_shared \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length u_ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned u_ts!k \<union> dom (map released u_ts!k)) = {}" 
        by cases auto

      note Ghost' = direct_memop_step.Ghost [of A L R W is' \<theta> sb u_m \<D> \<O> \<R> u_shared]
      from direct_computation.Memop [OF j_bound' u_ts_j, simplified "is", OF Ghost' ] 
      have ustep: "(u_ts, u_m, u_shared) \<Rightarrow>\<^sub>d 
                   (u_ts[j := (p, is', \<theta>, sb, \<D>, \<O> \<union> A - R, augment_rels (dom u_shared) R \<R> )], u_m, 
                          u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      from A_unowned_others [rule_format, OF i_bound' neq_j_i] u_ts_i i_bound' 
      have A_u_owns: "A \<inter> u_owns = {}" by auto
      {
        fix a
        assume a_u_owns: "a \<in> u_owns"
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = u_shared a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_owned_shared = this
      {
        fix a
        assume a_u_owns: "a \<notin> u_owns"
        assume "a \<notin> owned (ts!i)"
        from u_shared [rule_format, OF a_u_owns this]
        have "(u_shared \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        using R_owns A_R L_A A_u_owns owns_u_owns 
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note u_unowned_shared = this

      {
        fix a
        assume a_u_owns: "a \<in> u_owns"

        have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
        using R_owns A_R L_A A_u_owns owns_u_owns a_u_owns
          by (auto simp add: restrict_shared_def augment_shared_def split: option.splits)
      }
      note \<S>'_shared = this

      from dist_ts
      interpret dist_ts_inter: simple_ownership_distinct ts .
      from dist_ts_inter.simple_ownership_distinct [OF j_bound i_bound neq_j_i ts_j] 
      have "\<O> \<inter> owned (ts!i) = {}"
        apply (cases "ts!i")
        apply fastforce+
        done
      
      with simple_ownership_distinct [OF j_bound' i_bound' neq_j_i u_ts_j u_ts_i] R_owns u_shared

      have augment_eq: "augment_rels (dom u_shared) R \<R> = augment_rels (dom \<S>) R \<R>"
        apply -
        apply (rule ext)
        apply (fastforce simp add: augment_rels_def split: option.splits simp add: domIff)        
        done
        
        
      show ?thesis
        apply -
        apply (rule exI)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
        apply (rule ustep)
        using neq_j_i others_same u_m_other u_shared j_bound leq ts_j u_owned_shared u_unowned_shared \<S>'_shared
        apply (auto simp add: nth_list_update ts' eqs' augment_eq)
        done
    qed
  next
    case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
    hence False 
      by (auto simp add: empty_storebuffer_step_def)
    thus ?thesis ..
  qed
qed


theorem (in program) safe_step_preserves_simple_ownership_distinct:
  assumes step: "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts',m',\<S>')"
  assumes safe: "safe_delayed (ts,m,\<S>)"
  assumes dist: "simple_ownership_distinct ts"
  shows "simple_ownership_distinct ts'"
proof -
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from dist interpret simple_ownership_distinct ts .
  from step
  show ?thesis
  proof (cases)
    case (Program j p "is" \<theta> sb \<D> \<O> \<R> p' is')
    then obtain
      ts': "ts' = ts[j:=(p',is@is',\<theta>,sb,\<D>,\<O>,\<R>)]" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')"
      by auto

    from simple_ownership_distinct [OF j_bound _ _ ts_j]
    show "simple_ownership_distinct ts'"
      apply (simp only: ts')
      apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
      apply force
      done
  next
    case (Memop j p "is" \<theta> sb \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[j:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"  and
      mem_step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', sb',m', \<D>',  \<O>', \<R>', \<S>')"
      by auto

    from safe_delayedE [OF safe j_bound ts_j]
    have safe_j: "map owned ts,map released ts,j\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>".
    from mem_step
    show ?thesis
    proof (cases)
      case (Read volatile a t)
      then obtain
        "is": "is = Read volatile a t # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from simple_ownership_distinct [OF j_bound _ _ ts_j]
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done

    next
      case (WriteNonVolatile a D f A L R W)
      then obtain
        "is": "is = Write False a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from simple_ownership_distinct [OF j_bound _ _ ts_j]
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done

    next
      case (WriteVolatile a D f A L R W)
      then obtain
        "is": "is = Write True a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=True" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto
      from simple_ownership_distinct [OF j_bound _ _ ts_j] R_owns A_R A_unowned_others
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done
    next      
      case Fence
      then obtain
        "is": "is = Fence # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from simple_ownership_distinct [OF j_bound _ _ ts_j]
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done
    next
      case (RMWReadOnly cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t\<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>" and
        cond: "\<not> cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from simple_ownership_distinct [OF j_bound _ _ ts_j]
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done
    next
      case (RMWWrite cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> m a))))" and
        sb': "sb'=sb" and
        m': "m'=m(a := f (\<theta>(t \<mapsto> m a)))" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
        cond: "cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from safe_j [simplified "is"] cond
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto

      from simple_ownership_distinct [OF j_bound _ _ ts_j] R_owns A_R A_unowned_others
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done
    next
      case (Ghost A L R W) 
      then obtain
        "is": "is = Ghost A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=augment_rels (dom \<S>) R \<R>" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" 
        by cases auto

      from simple_ownership_distinct [OF j_bound _ _ ts_j] R_owns A_R A_unowned_others
      show "simple_ownership_distinct ts'"
        apply (simp only: ts' eqs')
        apply (rule simple_ownership_distinct_nth_update [OF j_bound ts_j])
        apply force
        done
    qed
  next
    case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
    hence False 
      by (auto simp add: empty_storebuffer_step_def)
    thus ?thesis ..
  qed
qed

theorem (in program) safe_step_preserves_read_only_unowned:
  assumes step: "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts',m',\<S>')"
  assumes safe: "safe_delayed (ts,m,\<S>)"
  assumes dist: "simple_ownership_distinct ts"
  assumes ro_unowned: "read_only_unowned \<S> ts"
  shows "read_only_unowned \<S>' ts'"
proof -
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from dist interpret simple_ownership_distinct ts .
  from ro_unowned interpret read_only_unowned \<S> ts .
  from step
  show ?thesis
  proof (cases)
    case (Program j p "is" \<theta> sb \<D> \<O> \<R> p' is')
    then obtain
      ts': "ts' = ts[j:=(p',is@is',\<theta>,sb,\<D>,\<O>,\<R>)]" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')"
      by auto

    from read_only_unowned [OF j_bound ts_j]
    show "read_only_unowned \<S>' ts'"
      apply (simp only: ts' \<S>')
      apply (rule read_only_unowned_nth_update [OF j_bound])
      apply force
      done
  next
    case (Memop j p "is" \<theta> sb \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[j:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"  and
      mem_step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', sb',m', \<D>',  \<O>', \<R>', \<S>')"
      by auto

    from safe_delayedE [OF safe j_bound ts_j]
    have safe_j: "map owned ts,map released ts,j\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>".
    from mem_step
    show ?thesis
    proof (cases)
      case (Read volatile a t)
      then obtain
        "is": "is = Read volatile a t # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from read_only_unowned [OF j_bound ts_j]
      show "read_only_unowned \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule read_only_unowned_nth_update [OF j_bound])
        apply force
        done

    next
      case (WriteNonVolatile a D f A L R W)
      then obtain
        "is": "is = Write False a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from read_only_unowned [OF j_bound ts_j]
      show "read_only_unowned \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule read_only_unowned_nth_update [OF j_bound])
        apply force
        done

    next
      case (WriteVolatile a D f A L R W)
      then obtain
        "is": "is = Write True a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=True" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto

      show "read_only_unowned \<S>' ts'"
      proof (unfold_locales)
        fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
        assume i_bound: "i < length ts'"
        assume ts'_i: "ts'!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i,\<R>\<^sub>i)"
        show "\<O>\<^sub>i \<inter> read_only \<S>' = {}"
        proof (cases "i=j")
          case True
          with read_only_unowned [OF j_bound ts_j] ts'_i A L_A R_owns A_R j_bound 
          show ?thesis
            by (auto simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        next
          case False
          from simple_ownership_distinct [OF j_bound _ False [symmetric] ts_j] ts'_i i_bound j_bound False
          have "\<O> \<inter> \<O>\<^sub>i = {}"
            by (fastforce simp add: ts')
          with A L_A R_owns A_R j_bound A_unowned_others [rule_format, of i] 
          read_only_unowned [of i p\<^sub>i is\<^sub>i \<theta>\<^sub>i sb\<^sub>i \<D>\<^sub>i \<O>\<^sub>i \<R>\<^sub>i]
            False i_bound ts'_i False
          show ?thesis
            by (force simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        qed
      qed
    next      
      case Fence
      then obtain
        "is": "is = Fence # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from read_only_unowned [OF j_bound ts_j]
      show "read_only_unowned \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule read_only_unowned_nth_update [OF j_bound])
        apply force
        done
    next
      case (RMWReadOnly cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t\<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>" and
        cond: "\<not> cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from read_only_unowned [OF j_bound ts_j]
      show "read_only_unowned \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule read_only_unowned_nth_update [OF j_bound])
        apply force
        done
    next
      case (RMWWrite cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> m a))))" and
        sb': "sb'=sb" and
        m': "m'=m(a := f (\<theta>(t \<mapsto> m a)))" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
        cond: "cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from safe_j [simplified "is"] cond
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto

      show "read_only_unowned \<S>' ts'"
      proof (unfold_locales)
        fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
        assume i_bound: "i < length ts'"
        assume ts'_i: "ts'!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i,\<R>\<^sub>i)"
        show "\<O>\<^sub>i \<inter> read_only \<S>' = {}"
        proof (cases "i=j")
          case True
          with read_only_unowned [OF j_bound ts_j] ts'_i A L_A R_owns A_R j_bound 
          show ?thesis
            by (auto simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        next
          case False
          from simple_ownership_distinct [OF j_bound _ False [symmetric] ts_j] ts'_i i_bound j_bound False
          have "\<O> \<inter> \<O>\<^sub>i = {}"
            by (fastforce simp add: ts')
          with A L_A R_owns A_R j_bound A_unowned_others [rule_format, of i] 
          read_only_unowned [of i p\<^sub>i is\<^sub>i \<theta>\<^sub>i sb\<^sub>i \<D>\<^sub>i \<O>\<^sub>i \<R>\<^sub>i]
            False i_bound ts'_i False
          show ?thesis
            by (force simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        qed
      qed
    next
      case (Ghost A L R W) 
      then obtain
        "is": "is = Ghost A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=augment_rels (dom \<S>) R \<R>" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" 
        by cases auto

      show "read_only_unowned \<S>' ts'"
      proof (unfold_locales)
        fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
        assume i_bound: "i < length ts'"
        assume ts'_i: "ts'!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i, sb\<^sub>i, \<D>\<^sub>i, \<O>\<^sub>i,\<R>\<^sub>i)"
        show "\<O>\<^sub>i \<inter> read_only \<S>' = {}"
        proof (cases "i=j")
          case True
          with read_only_unowned [OF j_bound ts_j] ts'_i A L_A R_owns A_R j_bound 
          show ?thesis
            by (auto simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        next
          case False
          from simple_ownership_distinct [OF j_bound _ False [symmetric] ts_j] ts'_i i_bound j_bound False
          have "\<O> \<inter> \<O>\<^sub>i = {}"
            by (fastforce simp add: ts')
          with A L_A R_owns A_R j_bound A_unowned_others [rule_format, of i] 
          read_only_unowned [of i p\<^sub>i is\<^sub>i \<theta>\<^sub>i sb\<^sub>i \<D>\<^sub>i \<O>\<^sub>i \<R>\<^sub>i]
            False i_bound ts'_i False
          show ?thesis
            by (force simp add: eqs' ts' read_only_def augment_shared_def restrict_shared_def domIff split: option.splits)
        qed
      qed
    qed
  next
    case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
    hence False 
      by (auto simp add: empty_storebuffer_step_def)
    thus ?thesis ..
  qed
qed


theorem (in program) safe_step_preserves_unowned_shared:
  assumes step: "(ts,m,\<S>) \<Rightarrow>\<^sub>d (ts',m',\<S>')"
  assumes safe: "safe_delayed (ts,m,\<S>)"
  assumes dist: "simple_ownership_distinct ts"
  assumes unowned_shared: "unowned_shared \<S> ts"
  shows "unowned_shared \<S>' ts'"
proof -
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from dist interpret simple_ownership_distinct ts .
  from unowned_shared interpret unowned_shared \<S> ts .
  from step
  show ?thesis
  proof (cases)
    case (Program j p "is" \<theta> sb \<D> \<O> \<R> p' is')
    then obtain
      ts': "ts' = ts[j:=(p',is@is',\<theta>,sb,\<D>,\<O>,\<R>)]" and
      \<S>': "\<S>'=\<S>" and
      m': "m'=m" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      prog_step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', is')"
      by auto

    show "unowned_shared \<S>' ts'"
      apply (simp only: ts' \<S>')
      apply (rule unowned_shared_nth_update [OF j_bound ts_j] )
      apply force
      done
  next
    case (Memop j p "is" \<theta> sb \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>')
    then obtain
      ts': "ts' = ts[j:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]" and
      j_bound: "j < length ts" and
      ts_j: "ts!j = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"  and
      mem_step: "(is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow> (is', \<theta>', sb',m', \<D>',  \<O>', \<R>', \<S>')"
      by auto

    from safe_delayedE [OF safe j_bound ts_j]
    have safe_j: "map owned ts,map released ts,j\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>".
    from mem_step
    show ?thesis
    proof (cases)
      case (Read volatile a t)
      then obtain
        "is": "is = Read volatile a t # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      show "unowned_shared \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule unowned_shared_nth_update [OF j_bound ts_j])
        apply force
        done

    next
      case (WriteNonVolatile a D f A L R W)
      then obtain
        "is": "is = Write False a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=\<R>" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      
      show "unowned_shared \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule unowned_shared_nth_update [OF j_bound ts_j])
        apply force
        done

    next
      case (WriteVolatile a D f A L R W)
      then obtain
        "is": "is = Write True a (D, f) A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m(a:=f \<theta>)" and
        \<D>': "\<D>'=True" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto


      show "unowned_shared \<S>' ts'"
      apply (clarsimp simp add: unowned_shared_def')
      using A R_owns L_A A_R A_unowned_others ts_j j_bound
      apply (auto simp add: \<S>' ts' \<O>')
      apply  (rule  unowned_shared')
      apply  clarsimp
      apply  (drule_tac x=i in spec)
      apply  (case_tac "i=j")
      apply   clarsimp
      apply  clarsimp
      apply (drule_tac x=j in spec)
      apply auto
      done
    next      
      case Fence
      then obtain
        "is": "is = Fence # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      
      show "unowned_shared \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule unowned_shared_nth_update [OF j_bound ts_j])
        apply force
        done
    next
      case (RMWReadOnly cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t\<mapsto> m a)" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O>" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S>" and
        cond: "\<not> cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      show "unowned_shared \<S>' ts'"
        apply (simp only: ts' eqs')
        apply (rule unowned_shared_nth_update [OF j_bound ts_j])
        apply force
        done
    next
      case (RMWWrite cond t a D f ret A L R W)
      then obtain
        "is": "is = RMW a t (D, f) cond ret A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>(t \<mapsto> ret (m a) (f (\<theta>(t \<mapsto> m a))))" and
        sb': "sb'=sb" and
        m': "m'=m(a := f (\<theta>(t \<mapsto> m a)))" and
        \<D>': "\<D>'=False" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=Map.empty" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
        cond: "cond (\<theta>(t \<mapsto> m a))"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'
      from safe_j [simplified "is"] cond
      obtain
        a_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow> a \<notin> (map owned ts!k \<union> dom (map released ts!k))" and
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" and
        a_not_ro: "a \<notin> read_only \<S>"
        by cases auto

      show "unowned_shared \<S>' ts'"
      apply (clarsimp simp add: unowned_shared_def')
      using A R_owns L_A A_R A_unowned_others ts_j j_bound
      apply (auto simp add: \<S>' ts' \<O>')
      apply  (rule  unowned_shared')
      apply  clarsimp
      apply  (drule_tac x=i in spec)
      apply  (case_tac "i=j")
      apply   clarsimp
      apply  clarsimp
      apply (drule_tac x=j in spec)
      apply auto
      done
    next
      case (Ghost A L R W) 
      then obtain
        "is": "is = Ghost A L R W # is'" and
        \<theta>': "\<theta>' = \<theta>" and
        sb': "sb'=sb" and
        m': "m'=m" and
        \<D>': "\<D>'=\<D>" and
        \<O>': "\<O>'=\<O> \<union> A - R" and
        \<R>': "\<R>'=augment_rels (dom \<S>) R \<R>" and
        \<S>': "\<S>'=\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
        by auto
      note eqs' = \<theta>' sb' m' \<D>' \<O>' \<R>' \<S>'

      from safe_j [simplified "is"]
      obtain
        A: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>" and A_R: "A \<inter> R = {}" and
        A_unowned_others: "\<forall>k < length ts. j\<noteq>k \<longrightarrow>  A \<inter>  (map owned ts!k \<union> dom (map released ts!k)) = {}" 
        by cases auto
      show "unowned_shared \<S>' ts'"
      apply (clarsimp simp add: unowned_shared_def')
      using A R_owns L_A A_R A_unowned_others ts_j j_bound
      apply (auto simp add: \<S>' ts' \<O>')
      apply  (rule  unowned_shared')
      apply  clarsimp
      apply  (drule_tac x=i in spec)
      apply  (case_tac "i=j")
      apply   clarsimp
      apply  clarsimp
      apply (drule_tac x=j in spec)
      apply auto
      done
    qed
  next
    case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
    hence False 
      by (auto simp add: empty_storebuffer_step_def)
    thus ?thesis ..
  qed
qed

locale program_trace = program +
fixes c       \<comment> \<open>enumeration of configurations: @{text "c n  \<Rightarrow>\<^sub>d c (n + 1) ... \<Rightarrow>\<^sub>d c (n + k)"}\<close> 
fixes n::nat  \<comment> \<open>starting index\<close>
fixes k::nat  \<comment> \<open>steps\<close>

assumes step: "\<And>l. l < k \<Longrightarrow> c (n+l) \<Rightarrow>\<^sub>d c (n + (Suc l))"

abbreviation (in program)
"trace \<equiv> program_trace program_step"

lemma (in program) trace_0 [simp]: "trace c n 0"
apply (unfold_locales)
apply auto
done

lemma split_less_Suc: "(\<forall>x<Suc k. P x) =  (P k \<and> (\<forall>x<k. P x))"
  apply rule
  apply  clarsimp
  apply clarsimp
  apply (case_tac "x = k") 
  apply auto
  done
  
lemma split_le_Suc: "(\<forall>x\<le>Suc k. P x) =  (P (Suc k) \<and> (\<forall>x\<le>k. P x))"
  apply rule
  apply  clarsimp
  apply clarsimp
  apply (case_tac "x = Suc k") 
  apply auto
  done

lemma (in program) steps_to_trace: 
assumes steps: "x \<Rightarrow>\<^sub>d\<^sup>* y"
shows "\<exists>c k. trace c 0 k \<and> c 0 = x \<and> c k = y" 
using steps
proof (induct)
  case base
  thus ?case
    apply (rule_tac x="\<lambda>k. x" in exI)
    apply (rule_tac x=0 in exI)
    by (auto simp add: program_trace_def)
next
  case (step y z)
  have first: "x \<Rightarrow>\<^sub>d\<^sup>* y" by fact
  have last: "y \<Rightarrow>\<^sub>d z" by fact
  from step.hyps obtain c k where
    trace: "trace c 0 k" and c_0: "c 0 = x" and c_k: "c k = y"
    by auto
  define c' where "c' == \<lambda>i. (if i \<le> k then c i else z)"
  from trace last c_k have "trace c' 0 (k + 1)"
    apply (clarsimp simp add: c'_def program_trace_def)
    apply (subgoal_tac "l=k")
    apply  (simp)
    apply (simp)
    done
  with c_0 
  show ?case
    apply -
    apply (rule_tac x="c'" in exI)
    apply (rule_tac x="k + 1" in exI)
    apply (auto simp add: c'_def)
    done
qed


lemma (in program) trace_preserves_length_ts: 
  "\<And>l x. trace c n k \<Longrightarrow> l \<le> k \<Longrightarrow> x \<le> k \<Longrightarrow> length (fst (c (n + l))) = length (fst (c (n + x)))"
proof (induct k)
  case 0
  thus ?case by auto
next
  case (Suc k)
  then obtain trace_suc: "trace c n (Suc k)" and
    l_suc: "l \<le> Suc k" and
    x_suc: "x \<le> Suc k"
    by simp
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .

  from trace_suc obtain
    trace_k: "trace c n k" and
    last_step: "c (n + k) \<Rightarrow>\<^sub>d c (n + (Suc k)) "
    by (clarsimp simp add: program_trace_def)
  obtain ts \<S> m where c_k: "c (n + k) = (ts, m, \<S>)" by (cases "c (n + k)") 
  obtain ts' \<S>' m' where c_suc_k: "c (n + (Suc k)) = (ts', m', \<S>')" by (cases "c (n + (Suc k))") 
  from direct_computation.step_preserves_length_ts [OF last_step [simplified c_k c_suc_k]] c_k c_suc_k
  have leq: "length (fst (c (n + Suc k))) = length (fst (c (n + k)))"
    by simp

  show ?case
  proof (cases "l = Suc k") 
    case True
    note l_suc = this
    show ?thesis
    proof (cases "x = Suc k") 
      case True with l_suc show ?thesis by simp
    next
      case False
      with x_suc have "x \<le> k" by simp
      from Suc.hyps [OF trace_k this, of k]
      have "length (fst (c (n + x))) = length (fst (c (n + k)))"
        by simp
      with leq show ?thesis using l_suc by simp
    qed
  next
    case False
    with l_suc have l_k: "l \<le> k"
      by auto
    show ?thesis
    proof (cases "x = Suc k") 
      case True
      from Suc.hyps [OF trace_k l_k, of k]
      have "length (fst (c (n + l))) = length (fst (c (n + k)))" by simp
      with leq True show ?thesis by simp
    next
      case False
      with x_suc have "x \<le> k" by simp
      from Suc.hyps [OF trace_k l_k this]
      show ?thesis by simp
    qed
  qed
qed

lemma (in program) trace_preserves_simple_ownership_distinct: 
  assumes dist: "simple_ownership_distinct (fst (c n))"
  shows "\<And>l. trace c n k \<Longrightarrow> (\<forall>x < k. safe_delayed (c (n + x))) \<Longrightarrow>  
           l \<le> k \<Longrightarrow>   simple_ownership_distinct (fst (c (n + l)))"
proof (induct k)
  case 0 thus ?case using dist by auto
next
  case (Suc k)
  then obtain 
    trace_suc: "trace c n (Suc k)" and
    safe_suc: "\<forall>x<Suc k. safe_delayed (c (n + x))" and
    l_suc: "l \<le> Suc k"
    by simp

  from trace_suc obtain
    trace_k: "trace c n k" and
    last_step: "c (n + k) \<Rightarrow>\<^sub>d c (n + (Suc k)) "
    by (clarsimp simp add: program_trace_def)

  obtain ts \<S> m where c_k: "c (n + k) = (ts, m, \<S>)" by (cases "c (n + k)") 
  obtain ts' \<S>' m' where c_suc_k: "c (n + (Suc k)) = (ts', m', \<S>')" by (cases "c (n + (Suc k))") 

  from safe_suc c_suc_k c_k
  obtain 
    safe_up_k: "\<forall>x<k. safe_delayed (c (n + x))" and
    safe_k: "safe_delayed (ts,m,\<S>)" 
    by (auto simp add: split_le_Suc) 
  from Suc.hyps [OF trace_k safe_up_k] 
  have hyp: "\<forall>l \<le> k. simple_ownership_distinct (fst (c (n + l)))"
    by simp

  from Suc.hyps [OF trace_k safe_up_k, of k] c_k
  have "simple_ownership_distinct ts"
    by simp

  from safe_step_preserves_simple_ownership_distinct [OF last_step[simplified c_k c_suc_k] safe_k this]
  have "simple_ownership_distinct ts'".
  then show ?case
  using c_suc_k hyp l_suc
    apply (cases "l=Suc k")
    apply (auto simp add: split_less_Suc)
    done
qed

lemma (in program) trace_preserves_read_only_unowned: 
  assumes dist: "simple_ownership_distinct (fst (c n))"
  assumes ro: "read_only_unowned (snd (snd (c n))) (fst (c n))"
  shows "\<And>l. trace c n k \<Longrightarrow> (\<forall>x < k. safe_delayed (c (n + x))) \<Longrightarrow>  
           l \<le> k \<Longrightarrow>   read_only_unowned (snd (snd (c (n + l)))) (fst (c (n + l)))"
proof (induct k)
  case 0 thus ?case using ro by auto
next
  case (Suc k)
  then obtain 
    trace_suc: "trace c n (Suc k)" and
    safe_suc: "\<forall>x<Suc k. safe_delayed (c (n + x))" and
    l_suc: "l \<le> Suc k"
    by simp

  from trace_suc obtain
    trace_k: "trace c n k" and
    last_step: "c (n + k) \<Rightarrow>\<^sub>d c (n + (Suc k)) "
    by (clarsimp simp add: program_trace_def)

  obtain ts \<S> m where c_k: "c (n + k) = (ts, m, \<S>)" by (cases "c (n + k)") 
  obtain ts' \<S>' m' where c_suc_k: "c (n + (Suc k)) = (ts', m', \<S>')" by (cases "c (n + (Suc k))") 

  from safe_suc c_suc_k c_k
  obtain 
    safe_up_k: "\<forall>x<k. safe_delayed (c (n + x))" and
    safe_k: "safe_delayed (ts,m,\<S>)" 
    by (auto simp add: split_le_Suc) 
  from Suc.hyps [OF trace_k safe_up_k] 
  have hyp: "\<forall>l \<le> k. read_only_unowned (snd (snd (c (n + l)))) (fst (c (n + l)))"
    by simp

  from Suc.hyps [OF trace_k safe_up_k, of k] c_k
  have ro': "read_only_unowned \<S> ts"
    by simp

  from trace_preserves_simple_ownership_distinct [where c=c and n=n, OF dist trace_k safe_up_k, of k] c_k
  have dist': "simple_ownership_distinct ts" by simp

  from safe_step_preserves_read_only_unowned [OF last_step[simplified c_k c_suc_k] safe_k dist' ro']
  have "read_only_unowned \<S>' ts'".
  then show ?case
  using c_suc_k hyp l_suc
    apply (cases "l=Suc k")
    apply (auto simp add: split_less_Suc)
    done
qed

lemma (in program) trace_preserves_unowned_shared: 
  assumes dist: "simple_ownership_distinct (fst (c n))"
  assumes ro: "unowned_shared (snd (snd (c n))) (fst (c n))"
  shows "\<And>l. trace c n k \<Longrightarrow> (\<forall>x < k. safe_delayed (c (n + x))) \<Longrightarrow>  
           l \<le> k \<Longrightarrow>   unowned_shared (snd (snd (c (n + l)))) (fst (c (n + l)))"
proof (induct k)
  case 0 thus ?case using ro by auto
next
  case (Suc k)
  then obtain 
    trace_suc: "trace c n (Suc k)" and
    safe_suc: "\<forall>x<Suc k. safe_delayed (c (n + x))" and
    l_suc: "l \<le> Suc k"
    by simp

  from trace_suc obtain
    trace_k: "trace c n k" and
    last_step: "c (n + k) \<Rightarrow>\<^sub>d c (n + (Suc k)) "
    by (clarsimp simp add: program_trace_def)

  obtain ts \<S> m where c_k: "c (n + k) = (ts, m, \<S>)" by (cases "c (n + k)") 
  obtain ts' \<S>' m' where c_suc_k: "c (n + (Suc k)) = (ts', m', \<S>')" by (cases "c (n + (Suc k))") 

  from safe_suc c_suc_k c_k
  obtain 
    safe_up_k: "\<forall>x<k. safe_delayed (c (n + x))" and
    safe_k: "safe_delayed (ts,m,\<S>)" 
    by (auto simp add: split_le_Suc) 
  from Suc.hyps [OF trace_k safe_up_k] 
  have hyp: "\<forall>l \<le> k. unowned_shared (snd (snd (c (n + l)))) (fst (c (n + l)))"
    by simp

  from Suc.hyps [OF trace_k safe_up_k, of k] c_k
  have ro': "unowned_shared \<S> ts"
    by simp

  from trace_preserves_simple_ownership_distinct [where c=c and n=n, OF dist trace_k safe_up_k, of k] c_k
  have dist': "simple_ownership_distinct ts" by simp

  from safe_step_preserves_unowned_shared [OF last_step[simplified c_k c_suc_k] safe_k dist' ro']
  have "unowned_shared \<S>' ts'".
  then show ?case
  using c_suc_k hyp l_suc
    apply (cases "l=Suc k")
    apply (auto simp add: split_less_Suc)
    done
qed


theorem (in program_progress) undo_local_steps:
assumes steps: "trace c n k"
assumes c_n: "c n = (ts,m,\<S>)"
assumes unchanged: "\<forall>l \<le> k. (\<forall>ts\<^sub>l \<S>\<^sub>l m\<^sub>l . c (n + l) = (ts\<^sub>l,m\<^sub>l,\<S>\<^sub>l) \<longrightarrow> ts\<^sub>l!i=ts!i)"
assumes safe: "safe_delayed (u_ts, u_m, u_shared)"
assumes leq: "length u_ts = length ts"
assumes i_bound: "i < length ts"
assumes others_same: "\<forall>j < length ts. j\<noteq>i \<longrightarrow> u_ts!j = ts!j"
assumes u_ts_i: "u_ts!i=(u_p,u_is,u_tmps,u_sb,u_dirty,u_owns,u_rels)"
assumes u_m_other: "\<forall>a. a \<notin> u_owns \<longrightarrow> u_m a = m a"
assumes u_m_shared: "\<forall>a. a \<in> u_owns \<longrightarrow> a \<in> dom u_shared \<longrightarrow> u_m a = m a"
assumes u_shared: "\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts!i) \<longrightarrow> u_shared a = \<S> a"
assumes dist: "simple_ownership_distinct u_ts"
assumes dist_ts: "simple_ownership_distinct ts"
assumes safe_orig: "\<forall>x.  x < k \<longrightarrow> safe_delayed (c (n + x))" 
shows "\<exists>c' l. l \<le> k \<and> trace c' n l \<and>

        c' n = (u_ts, u_m, u_shared) \<and>
        (\<forall>x \<le> l. length (fst (c' (n + x))) = length (fst (c (n + x)))) \<and>

        (\<forall>x < l. safe_delayed (c' (n + x))) \<and>
        (l < k \<longrightarrow> \<not> safe_delayed (c' (n + l))) \<and> 
       
        (\<forall>x \<le> l. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x' . c (n + x) = (ts\<^sub>x,m\<^sub>x,\<S>\<^sub>x) \<longrightarrow> c' (n+ x) = (ts\<^sub>x',m\<^sub>x',\<S>\<^sub>x') \<longrightarrow> 
          ts\<^sub>x'!i=u_ts!i \<and>
          (\<forall>a \<in> u_owns. \<S>\<^sub>x' a = u_shared a) \<and>
          (\<forall>a \<in> u_owns. \<S>\<^sub>x a = \<S> a) \<and>
          (\<forall>a \<in> u_owns. m\<^sub>x' a = u_m a) \<and>
          (\<forall>a \<in> u_owns. m\<^sub>x a = m a)) \<and>
        
        (\<forall>x \<le> l. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'. c (n + x) = (ts\<^sub>x,m\<^sub>x,\<S>\<^sub>x) \<longrightarrow> c' (n + x) = (ts\<^sub>x',m\<^sub>x',\<S>\<^sub>x') \<longrightarrow> 
         (\<forall>j < length ts\<^sub>x. j\<noteq>i \<longrightarrow> ts\<^sub>x'!j = ts\<^sub>x!j) \<and>
         (\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts!i) \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
         (\<forall>a. a \<notin> u_owns \<longrightarrow> m\<^sub>x' a = m\<^sub>x a))
"
using steps unchanged safe_orig
proof (induct k)
  case 0
  show ?case
    apply (rule_tac x="\<lambda> l. (u_ts, u_m, u_shared)" in exI)
    apply (rule_tac x=0 in exI)
    thm c_n
    apply (simp add: c_n)
    apply (clarsimp simp add: 0 leq others_same u_m_other u_shared)
    done
next
  case (Suc k)
  then obtain  
    trace_suc: "trace c n (Suc k)" and
    unchanged_suc: "\<forall>l\<le>Suc k. \<forall>ts\<^sub>l \<S>\<^sub>l m\<^sub>l. c (n + l) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l) \<longrightarrow> ts\<^sub>l ! i = ts ! i" and
    safe_orig: "\<forall>x<k. safe_delayed (c (n + x))"
    by simp

  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  from trace_suc obtain
    trace_k: "trace c n k" and
    last_step: "c (n + k) \<Rightarrow>\<^sub>d c (n + (Suc k)) "
    by (clarsimp simp add: program_trace_def)

  from unchanged_suc obtain
    unchanged_k: "\<forall>l\<le>k. \<forall>ts\<^sub>l \<S>\<^sub>l m\<^sub>l. c (n + l) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l) \<longrightarrow> ts\<^sub>l ! i = ts ! i" and
    unchanged_suc_k: "\<forall>ts\<^sub>l \<S>\<^sub>l m\<^sub>l. c (n + (Suc k)) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l) \<longrightarrow> ts\<^sub>l ! i = ts ! i"
    apply -
    apply (rule that)
    apply auto
    apply (drule_tac x=l in spec) (* Why the hack doesn't Isabelle try this *)
    apply simp
    done
  

  from Suc.hyps [OF trace_k unchanged_k safe_orig] obtain c' l where
    l_k: "l \<le> k" and
    trace_c'_l: "trace c' n l" and
    safe_l: "(\<forall>x<l. safe_delayed (c' (n + x)))" and
    unsafe_l: "(l < k \<longrightarrow> \<not> safe_delayed (c' (n + l)))" and
    c'_n: "c' n = (u_ts, u_m, u_shared)" and
    leq_l: "(\<forall>x\<le>l. length (fst (c' (n + x))) = length (fst (c (n + x))))" and
    unchanged_i: "(\<forall>x\<le>l. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                   c (n + x) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   c' (n + x) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                   ts\<^sub>x' ! i = u_ts ! i \<and>
                   (\<forall>a\<in>u_owns. \<S>\<^sub>x' a = u_shared a) \<and>
                   (\<forall>a\<in>u_owns. \<S>\<^sub>x a = \<S> a) \<and>
                   (\<forall>a\<in>u_owns. m\<^sub>x' a = u_m a) \<and>
                   (\<forall>a\<in>u_owns. m\<^sub>x a = m a))" and
     sim: "(\<forall>x\<le>l. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                   c (n + x) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   c' (n + x) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                   (\<forall>j<length ts\<^sub>x. j \<noteq> i \<longrightarrow> ts\<^sub>x' ! j = ts\<^sub>x ! j) \<and>
                   (\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts!i) \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
                   (\<forall>a. a \<notin> u_owns \<longrightarrow> m\<^sub>x' a = m\<^sub>x a))"
      by auto
    show ?case
    proof (cases "l < k")
      case True
      with True trace_c'_l safe_l unsafe_l unchanged_i sim leq_l c'_n
      show ?thesis
        apply -
        apply (rule_tac x="c'" in exI)
        apply (rule_tac x="l" in exI)
        apply auto
        done
    next
      case False
      with l_k have l_k: "l=k" by auto
      show ?thesis
      proof (cases "safe_delayed (c' (n + k))")
        case False
        with False l_k trace_c'_l safe_l unsafe_l unchanged_i sim leq_l c'_n
        show ?thesis
          apply -
          apply (rule_tac x="c'" in exI)
          apply (rule_tac x="k" in exI)
          apply auto
          done
      next
        case True
        note safe_k = this

        obtain ts\<^sub>k \<S>\<^sub>k m\<^sub>k where c_k: "c (n + k) = (ts\<^sub>k,m\<^sub>k,\<S>\<^sub>k)"
          by (cases "c (n + k)")

        obtain ts\<^sub>k' \<S>\<^sub>k' m\<^sub>k' where c_suc_k: "c (n + (Suc k)) = (ts\<^sub>k',m\<^sub>k',\<S>\<^sub>k')"
          by (cases "c (n + (Suc k))")

        obtain u_ts\<^sub>k u_shared\<^sub>k u_m\<^sub>k where c'_k: "c' (n + k) = (u_ts\<^sub>k, u_m\<^sub>k, u_shared\<^sub>k)"
          by (cases "c' (n + k)")

        from trace_preserves_length_ts [OF trace_k, of k 0] c_n c_k i_bound
        have i_bound_k: "i < length ts\<^sub>k"
          by simp

        from leq_l [rule_format, simplified l_k, of k] c_k c'_k
        have leq: "length u_ts\<^sub>k = length ts\<^sub>k"
          by simp
        
        note last_step = last_step [simplified c_k c_suc_k]
        from unchanged_suc_k c_suc_k
        have "ts\<^sub>k'!i = ts!i"
          by auto
        moreover from unchanged_k [rule_format, of k] c_k
        have unch_k_i: "ts\<^sub>k!i=ts!i"
          by auto
        ultimately have ts_eq: "ts\<^sub>k!i=ts\<^sub>k'!i"
          by simp

        from unchanged_i [simplified l_k, rule_format, OF _ c_k c'_k]
        obtain 
          u_ts_eq: "u_ts\<^sub>k ! i = u_ts ! i" and
          unchanged_shared: "\<forall>a\<in>u_owns. u_shared\<^sub>k a = u_shared a"  and
          unchanged_shared_orig: "\<forall>a\<in>u_owns. \<S>\<^sub>k a = \<S> a" and
          unchanged_owns: "\<forall>a\<in>u_owns. u_m\<^sub>k a = u_m a" and
          unchanged_owns_orig: "\<forall>a\<in>u_owns. m\<^sub>k a = m a"
          by fastforce

        from u_ts_eq u_ts_i
        have u_ts\<^sub>k_i: "u_ts\<^sub>k!i=(u_p,u_is,u_tmps,u_sb,u_dirty,u_owns,u_rels)"
          by auto
        from sim [simplified l_k, rule_format, of k, OF _ c_k c'_k]  
        obtain
          ts_sim: "(\<forall>j<length ts\<^sub>k. j \<noteq> i \<longrightarrow> u_ts\<^sub>k ! j = ts\<^sub>k ! j)" and
          shared_sim: "(\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts\<^sub>k!i) \<longrightarrow> u_shared\<^sub>k a = \<S>\<^sub>k a)" and
          mem_sim: "(\<forall>a. a \<notin> u_owns \<longrightarrow> u_m\<^sub>k a = m\<^sub>k a)"
          by (auto simp add: unch_k_i)

        

        from unchanged_owns_orig unchanged_owns u_m_shared unchanged_shared
        have unchanged_owns_shared: "\<forall>a. a \<in> u_owns \<longrightarrow> a \<in> dom u_shared\<^sub>k \<longrightarrow> u_m\<^sub>k a = m\<^sub>k a"
          by (auto simp add: simp add: domIff)

        from safe_l l_k safe_k
        have safe_up_k: "\<forall>x<k. safe_delayed (c' (n + x))"
          apply clarsimp
          done
        from trace_preserves_simple_ownership_distinct [OF _ trace_c'_l [simplified l_k] safe_up_k, 
          simplified c'_n, simplified, OF dist, of k] c'_k
        have dist': "simple_ownership_distinct u_ts\<^sub>k"
          by simp
        

        from trace_preserves_simple_ownership_distinct [OF _ trace_k, simplified c_n, simplified, OF dist_ts safe_orig, of k] 
        c_k
        have dist_orig': "simple_ownership_distinct ts\<^sub>k"
          by simp

        from undo_local_step [OF last_step i_bound_k ts_eq safe_k [simplified c'_k] leq ts_sim u_ts\<^sub>k_i mem_sim 
          unchanged_owns_shared shared_sim dist' dist_orig']
        obtain u_ts' u_shared' u_m' where
           step': "(u_ts\<^sub>k, u_m\<^sub>k, u_shared\<^sub>k) \<Rightarrow>\<^sub>d (u_ts', u_m', u_shared')" and
           ts_eq': "u_ts' ! i = u_ts\<^sub>k ! i" and
           unchanged_shared': "(\<forall>a\<in>u_owns. u_shared' a = u_shared\<^sub>k a)" and
           unchanged_shared_orig': "(\<forall>a\<in>u_owns. \<S>\<^sub>k' a = \<S>\<^sub>k a)" and
           unchanged_owns': "(\<forall>a\<in>u_owns. u_m' a = u_m\<^sub>k a)" and
           unchanged_owns_orig': "(\<forall>a\<in>u_owns. m\<^sub>k' a = m\<^sub>k a)" and
           sim_ts': "(\<forall>j<length ts\<^sub>k. j \<noteq> i \<longrightarrow> u_ts' ! j = ts\<^sub>k' ! j)" and
           sim_shared': "(\<forall>a. a \<notin> u_owns \<longrightarrow> a \<notin> owned (ts\<^sub>k ! i) \<longrightarrow> u_shared' a = \<S>\<^sub>k' a)" and
           sim_m': "(\<forall>a. a \<notin> u_owns \<longrightarrow> u_m' a = m\<^sub>k' a)"
          by auto

        define c'' where "c'' == \<lambda>l. if l \<le> n + k then c' l else (u_ts', u_m', u_shared')"
        have [simp]: "\<forall>x \<le> n + k. c'' x = c' x"
          by (auto simp add: c''_def)
        have [simp]: "c'' (Suc (n + k)) = (u_ts', u_m', u_shared')"
          by (auto simp add: c''_def)

        from trace_c'_l l_k step' c'_k  have trace': "trace c'' n (Suc k)"
         apply (simp add: program_trace_def)
         apply (clarsimp simp add: split_less_Suc)
         done

        from direct_computation.step_preserves_length_ts [OF last_step]
        have leq_ts\<^sub>k': "length ts\<^sub>k' = length ts\<^sub>k".

        with direct_computation.step_preserves_length_ts [OF step'] leq
        have leq': "length u_ts' = length ts\<^sub>k"
          by simp
        show ?thesis
          apply (rule_tac x=c'' in exI)
          apply (rule_tac x="Suc k" in exI)
          using safe_l l_k unchanged_i sim c_suc_k leq_l c'_n leq'
          apply (clarsimp simp add: split_less_Suc split_le_Suc safe_k trace' leq_ts\<^sub>k' sim_ts' sim_shared' sim_m' unch_k_i
            
            ts_eq' u_ts_eq
            unchanged_shared' unchanged_shared unchanged_shared_orig unchanged_shared_orig'
            unchanged_owns' unchanged_owns
            unchanged_owns_orig' unchanged_owns_orig )
          done
    qed (* FIXME: indentation *)
  qed         
qed


locale program_safe_reach_upto = program +
  fixes n fixes safe fixes c\<^sub>0
  assumes safe_config: "\<lbrakk>k \<le> n; trace c 0 k; c 0 = c\<^sub>0; l \<le> k \<rbrakk> \<Longrightarrow> safe (c l)"

abbreviation (in program)
  "safe_reach_upto \<equiv> program_safe_reach_upto program_step"

lemma (in program) safe_reach_upto_le:
  assumes safe: "safe_reach_upto n safe c\<^sub>0"
  assumes m_n: "m \<le> n"
  shows "safe_reach_upto m safe c\<^sub>0"
using safe m_n
apply (clarsimp simp add: program_safe_reach_upto_def)
  subgoal for k c
    apply (subgoal_tac "k \<le> n")
     apply blast
    apply simp
  done
done


lemma (in program) last_action_of_thread:
assumes trace: "trace c 0 k"
shows 
  "\<comment> \<open>thread i never executes\<close>  
  (\<forall>l \<le> k. fst (c l)!i = fst (c k)!i)  \<or>
  \<comment> \<open>thread i has a last step in the trace\<close>
  (\<exists>last <  k.  
    fst (c last)!i \<noteq> fst (c (Suc last))!i \<and>
    (\<forall>l. last < l \<longrightarrow> l \<le> k \<longrightarrow> fst (c l)!i = fst (c k)!i)) "
using trace
proof (induct k)    
  case 0 thus ?case
    by auto
next
  case (Suc k)
  hence "trace c 0 (Suc k)" by simp
  then
  obtain
    trace_k: "trace c 0 k" and
    last_step: "c k \<Rightarrow>\<^sub>d c (Suc k) "
    by (clarsimp simp add: program_trace_def)  
  
  show ?case
  proof (cases "fst (c k)!i = fst (c (Suc k))!i")
    case False
    then show ?thesis
      apply -
      apply (rule disjI2)
      apply (rule_tac x=k in exI)
      apply clarsimp
      apply (subgoal_tac "l=Suc k")
      apply auto
      done
  next
    case True
    note idle_i = this


    {
      assume same: "(\<forall>l\<le>k. fst (c l) ! i = fst (c k) ! i)"
      have ?thesis
        apply -
        apply (rule disjI1)
        apply clarsimp
        apply (case_tac "l=Suc k")
        apply  (simp add: idle_i)
        apply (rule same [simplified idle_i, rule_format])
        apply simp
        done
    }
    moreover
    {
      fix last
      assume last_k: "last < k"
      assume last_step: "fst (c last) ! i \<noteq> fst (c (Suc last)) ! i"
      assume idle: "(\<forall>l>last. l \<le> k \<longrightarrow> fst (c l) ! i = fst (c k) ! i)"
      have ?thesis
        apply -
        apply (rule disjI2)
        apply (rule_tac x=last in exI)
        using last_k 
        apply (simp add:  last_step)
        using idle [simplified idle_i] 
        apply clarsimp
        apply (case_tac "l=Suc k")
        apply  clarsimp
        apply clarsimp
        done
    }
    moreover note Suc.hyps [OF trace_k]
    ultimately
    show ?thesis
      by blast
  qed
qed

lemma (in program) sequence_traces:
assumes trace1: "trace c\<^sub>1 0 k"
assumes trace2: "trace c\<^sub>2 m l"
assumes seq: "c\<^sub>2 m = c\<^sub>1 k"
assumes c_def: "c = (\<lambda>x. if x  \<le> k then c\<^sub>1 x else (c\<^sub>2 (m + x -k)))"
shows "trace c 0 (k + l)"
proof -
  from trace1
  interpret trace1: program_trace program_step c\<^sub>1 0 k .
  from trace2
  interpret trace2: program_trace program_step c\<^sub>2 m l .
  {
    fix x
    assume x_bound: "x < (k + l)" 
    have "c x \<Rightarrow>\<^sub>d c (Suc x)"
    proof (cases "x < k")
      case True
      from trace1.step [OF True] True
      show ?thesis
        by (simp add: c_def)
    next
      case False
      hence k_x: "k \<le> x"
        by auto
      with x_bound have bound: "x - k < l"
        by auto
      from k_x have eq: "(Suc (m + x) - k) = Suc (m + x - k)"
        by simp
      from trace2.step [OF bound] k_x seq
      show ?thesis
        by (auto simp add: c_def eq)
    qed
  }
  thus ?thesis
    by (auto simp add: program_trace_def)
qed
      
theorem (in program_progress) safe_free_flowing_implies_safe_delayed:
  assumes init: "initial c\<^sub>0"
  assumes dist: "simple_ownership_distinct (fst c\<^sub>0)"
  assumes read_only_unowned: "read_only_unowned (snd (snd c\<^sub>0)) (fst c\<^sub>0)"
  assumes unowned_shared: "unowned_shared (snd (snd c\<^sub>0)) (fst c\<^sub>0)"
  assumes safe_reach_ff: "safe_reach_upto n safe_free_flowing c\<^sub>0"
  shows "safe_reach_upto n safe_delayed c\<^sub>0"
using safe_reach_ff 
proof (induct n)
  case 0
  hence "safe_reach_upto 0 safe_free_flowing c\<^sub>0" by simp
  hence "safe_free_flowing c\<^sub>0"
    by (auto simp add: program_safe_reach_upto_def)
  from initial_safe_free_flowing_implies_safe_delayed [OF init this]
  have "safe_delayed c\<^sub>0".
  then show ?case
    by (simp add: program_safe_reach_upto_def)
next
  case (Suc n)
  hence safe_reach_suc: "safe_reach_upto (Suc n) safe_free_flowing c\<^sub>0" by simp
  then interpret safe_reach_suc_inter: program_safe_reach_upto program_step "(Suc n)" safe_free_flowing c\<^sub>0 .
  from safe_reach_upto_le [OF safe_reach_suc ]  
  have safe_reach_n: "safe_reach_upto n safe_free_flowing c\<^sub>0" by simp
  from Suc.hyps [OF this]
  have safe_delayed_reach_n: "safe_reach_upto n safe_delayed c\<^sub>0".
  then interpret safe_delayed_reach_inter: program_safe_reach_upto program_step "n" safe_delayed c\<^sub>0 .
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb" .
  show ?case
  proof (cases "safe_reach_upto (Suc n) safe_delayed c\<^sub>0")
    case True thus ?thesis .
  next
    case False
    from safe_delayed_reach_n False
    obtain c where
      trace: "trace c 0 (Suc n)" and
      c_0: "c 0 = c\<^sub>0" and
      safe_delayed_upto_n: "\<forall>k\<le>n. safe_delayed (c k)" and
      violation_delayed_suc: "\<not> safe_delayed (c (Suc n))"
    proof -
      from False
      obtain c k l where 
        k_suc: "k \<le> Suc n" and
        trace_k: "trace c 0 k" and 
        l_k: "l \<le> k" and
        violation: "\<not> safe_delayed (c l)" and
        start: "c 0 = c\<^sub>0"
        by (clarsimp simp add: program_safe_reach_upto_def)
    
      show ?thesis
      proof (cases "k = Suc n")
        case False
        with k_suc have "k \<le> n"
          by auto
        from safe_delayed_reach_inter.safe_config [where c=c, OF this trace_k start l_k]
        have "safe_delayed (c l)".
        with violation have False by simp
        thus ?thesis ..
      next
        case True
        note k_suc_n = this
        from trace_k True have trace_n: "trace c 0 n"
          by (auto simp add: program_trace_def)
        show ?thesis
        proof (cases "l=Suc n") 
          case False
          with k_suc_n l_k have "l \<le> n" by simp
          from safe_delayed_reach_inter.safe_config [where c=c, OF _ trace_n start this ]
          have "safe_delayed (c l)" by simp
          with violation have False by simp
          thus ?thesis ..
        next
          case True
          from safe_delayed_reach_inter.safe_config [where c=c, OF _ trace_n start]
          have "\<forall>k\<le>n. safe_delayed (c k)" by simp
          with True k_suc_n trace_k start violation
          show ?thesis
            apply -
            apply (rule that)
            apply auto
            done
        qed    
      qed
    qed

    from trace
    interpret trace_inter: program_trace program_step c 0 "Suc n" .

    from safe_reach_suc_inter.safe_config [where c=c, OF _ trace c_0]
    have safe_suc: "safe_free_flowing (c (Suc n))"
      by auto
    
    obtain ts \<S> m where c_suc: "c (Suc n) = (ts,m,\<S>)" by (cases "c (Suc n)")
    from violation_delayed_suc c_suc
    obtain i p "is" \<theta> sb \<D> \<O> \<R> where
      i_bound: "i < length ts" and
      ts_i: "ts ! i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
      violation_i: "\<not> map owned ts,map released ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd> "
      by (fastforce simp add: safe_free_flowing_def safe_delayed_def)

    from trace_preserves_unowned_shared [where c=c and n=0 and l="Suc n", 
          simplified c_0, OF dist unowned_shared trace] safe_delayed_upto_n  c_suc
    have "unowned_shared \<S> ts" by auto
    then interpret unowned_shared \<S> ts .

    
    from violation_i obtain ins is' where "is": "is = ins#is'"
      by (cases "is") (auto simp add: safe_delayed_direct_memop_state.Nil)
    from safeE [OF safe_suc [simplified c_suc] i_bound ts_i]
    have safe_i: "map owned ts,i\<turnstile>(is, \<theta>, m, \<D>, \<O>, \<S>)\<surd>".

    define races where "races == \<lambda>\<R>. (case ins of
         Read volatile a t \<Rightarrow> (\<R> a = Some False) \<or> (\<not> volatile \<and> a \<in> dom \<R>)
       | Write volatile a sop A L R W \<Rightarrow> (a \<in> dom \<R> \<or> (volatile \<and> A \<inter> dom \<R> \<noteq> {}))
       | Ghost A L R W \<Rightarrow> (A \<inter> dom \<R> \<noteq> {})
       | RMW a t (D,f) cond ret A L R W \<Rightarrow> (if cond (\<theta>(t \<mapsto> m a)) 
                                           then a \<in> dom \<R> \<or> A \<inter> dom \<R> \<noteq> {}
                                           else \<R> a = Some False)
       | _ \<Rightarrow> False)"



    {
      assume no_race: 
        "\<forall> j. j < length ts \<longrightarrow> j\<noteq>i \<longrightarrow> \<not> races (released (ts!j))"
      from safe_i 
      have "map owned ts,map released ts,i \<turnstile>(is,\<theta>,m,\<D>,\<O>,\<S>)\<surd> "
      proof cases
        case Read
        thus ?thesis
          using "is" no_race
          by (auto simp add: races_def intro: safe_delayed_direct_memop_state.intros)
      next
        case WriteNonVolatile
        thus ?thesis
          using "is" no_race
          by (auto simp add: races_def intro: safe_delayed_direct_memop_state.intros)
      next
        case WriteVolatile
        thus ?thesis
          using "is" no_race
          apply (clarsimp simp add: races_def) 
          apply (rule safe_delayed_direct_memop_state.intros)
          apply auto
          done
      next
        case Fence
        thus ?thesis
          using "is" no_race
          by (auto simp add: races_def intro: safe_delayed_direct_memop_state.intros)
      next
        case Ghost
        thus ?thesis
          using "is" no_race
          apply (clarsimp simp add: races_def) 
          apply (rule safe_delayed_direct_memop_state.intros)
          apply auto
          done
      next
        case RMWReadOnly
        thus ?thesis
          using "is" no_race
          by (auto simp add: races_def intro: safe_delayed_direct_memop_state.intros)
      next
        case (RMWWrite cond t a _ _ A _ \<O>)
        thus ?thesis
          using "is" no_race unowned_shared' [rule_format, of a] ts_i
          apply (clarsimp simp add: races_def) 
          apply (rule safe_delayed_direct_memop_state.RMWWrite)
          apply auto
          apply force
          done
      next
        case Nil with "is" show ?thesis by auto
      qed
    }
    with violation_i
    obtain j where
      j_bound: "j < length ts" and
      neq_j_i: "j \<noteq> i" and
      race: "races (released (ts!j))"
      by auto
    
    obtain p\<^sub>j "is\<^sub>j" \<theta>\<^sub>j sb\<^sub>j \<D>\<^sub>j \<O>\<^sub>j \<R>\<^sub>j where
      ts_j: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
      apply (cases "ts!j")
      apply force
      done

    from race 
    have \<R>\<^sub>j_non_empty: "\<R>\<^sub>j \<noteq> Map.empty"
      by (auto simp add: ts_j races_def split: instr.splits if_split_asm)

    {
      assume idle_j: "\<forall>l\<le>Suc n. fst (c l) ! j = fst (c (Suc n)) ! j"
      have ?thesis
      proof -
        from idle_j [rule_format, of 0] c_suc  c_0 ts_j
        have c\<^sub>0_j: "fst c\<^sub>0 ! j = ts!j"
          by clarsimp
        from trace_preserves_length_ts [OF trace, of 0 "Suc n"] c_0 c_suc
        have "length (fst c\<^sub>0) = length ts"
          by clarsimp
        with j_bound have "j < length (fst c\<^sub>0)"
          by simp
        with nth_mem [OF this] init c\<^sub>0_j ts_j 
        have "\<R>\<^sub>j = Map.empty"
          by (auto simp add: initial_def)
        with \<R>\<^sub>j_non_empty have False
          by simp
        thus ?thesis ..
      qed
    }
    moreover
    {
      fix last
      assume last_bound: "last<Suc n" 
      assume last_step_changed_j: "fst (c last) ! j \<noteq> fst (c (Suc last)) ! j"
      assume idle_rest: "\<forall>l>last. l \<le> Suc n \<longrightarrow> fst (c l) ! j = fst (c (Suc n)) ! j"
      have ?thesis
      proof -
        obtain ts\<^sub>l \<S>\<^sub>l m\<^sub>l where
           c_last: "c last = (ts\<^sub>l,m\<^sub>l,\<S>\<^sub>l)"
          by (cases "c last")
        obtain ts\<^sub>l' \<S>\<^sub>l' m\<^sub>l' where
           c_last': "c (Suc last) = (ts\<^sub>l',m\<^sub>l',\<S>\<^sub>l')"
          by (cases "c (Suc last)")
        from idle_rest [rule_format, of "Suc last" ] c_suc c_last' last_bound
        have ts\<^sub>l'_j: "ts\<^sub>l'!j = ts!j"
          by auto

        from last_step_changed_j c_last c_last'
        have j_changed: "ts\<^sub>l!j \<noteq> ts\<^sub>l'!j"
           by auto

        from trace_inter.step [OF last_bound] c_last c_last'
        have last_step: "(ts\<^sub>l,m\<^sub>l,\<S>\<^sub>l) \<Rightarrow>\<^sub>d (ts\<^sub>l',m\<^sub>l',\<S>\<^sub>l')"
          by simp

        obtain p\<^sub>l "is\<^sub>l" \<theta>\<^sub>l sb\<^sub>l \<D>\<^sub>l \<O>\<^sub>l \<R>\<^sub>l where
          ts\<^sub>l_j: "ts\<^sub>l!j = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
          apply (cases "ts\<^sub>l!j")
          apply force
          done
(*
        obtain p\<^sub>l' "is\<^sub>l'" \<theta>\<^sub>l' sb\<^sub>l' \<D>\<^sub>l' \<O>\<^sub>l' \<R>\<^sub>l' where
          ts\<^sub>l'_j: "ts\<^sub>l'!j = (p\<^sub>l',is\<^sub>l',\<theta>\<^sub>l',sb\<^sub>l',\<D>\<^sub>l',\<O>\<^sub>l',\<R>\<^sub>l')"
          apply (cases "ts\<^sub>l'!j")
          apply force
          done
*)      
        from trace_preserves_length_ts [OF trace, of last "Suc n"] c_last c_suc last_bound
        have leq\<^sub>l: "length ts\<^sub>l = length ts"
          by simp
        with j_bound have j_bound\<^sub>l: "j < length ts\<^sub>l"
          by simp

        from trace have trace_n: "trace c 0 n"
          by (auto simp add: program_trace_def)
        
        from safe_delayed_reach_inter.safe_config [where k=n and c=c and l=last, OF _ trace_n c_0] last_bound c_last
        have safe_delayed_last: "safe_delayed (ts\<^sub>l,m\<^sub>l,\<S>\<^sub>l)"
          by auto
        
        from safe_delayed_reach_inter.safe_config [where c=c, OF _ trace_n c_0] 
        have safe_delayed_upto_n: "\<forall>x<n. safe_delayed (c (0 + x))"
          by auto
        from trace_preserves_simple_ownership_distinct [where c=c and n=0 and l=last, 
          simplified c_0, OF dist trace_n safe_delayed_upto_n]
          last_bound c_last
        have dist_last: "simple_ownership_distinct ts\<^sub>l" 
          by auto

        from trace_preserves_read_only_unowned [where c=c and n=0 and l=last, 
          simplified c_0, OF dist read_only_unowned trace_n safe_delayed_upto_n]
          last_bound c_last
        have ro_last_last: "read_only_unowned \<S>\<^sub>l ts\<^sub>l" 
          by auto


        
        from safe_delayed_reach_inter.safe_config [where c=c, OF _ trace_n c_0] 
        have safe_delayed_upto_suc_n: "\<forall>x<Suc n. safe_delayed (c (0 + x))"
          by auto

        from trace_preserves_simple_ownership_distinct [where c=c and n=0 and l="Suc last", 
          simplified c_0, OF dist trace safe_delayed_upto_suc_n]
          last_bound c_last'
        have dist_last': "simple_ownership_distinct ts\<^sub>l'" 
          by auto
        from trace last_bound have trace_last: "trace c 0 last"
          by (auto simp add: program_trace_def)

        from trace last_bound have trace_rest: "trace c (Suc last) (n - last)"
          by (auto simp add: program_trace_def)

        from idle_rest last_bound
        have idle_rest':
            "\<forall>l\<le>n - last.
                      \<forall>ts\<^sub>l \<S>\<^sub>l m\<^sub>l. c (Suc last + l) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l) \<longrightarrow> ts\<^sub>l ! j = ts\<^sub>l' ! j"
          apply clarsimp
          apply (drule_tac x="Suc (last + l)" in spec)
          apply (auto simp add: c_last' c_suc ts\<^sub>l'_j)
          done

        from safe_delayed_upto_suc_n [rule_format, of last] last_bound 
        have safe_delayed_last: "safe_delayed (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l)"
          by (auto simp add: c_last)
        from safe_delayedE [OF this j_bound\<^sub>l ts\<^sub>l_j] 
        have safe\<^sub>l: "map owned ts\<^sub>l,map released ts\<^sub>l,j\<turnstile>(is\<^sub>l, \<theta>\<^sub>l, m\<^sub>l, \<D>\<^sub>l, \<O>\<^sub>l, \<S>\<^sub>l)\<surd>".
        
        from safe_delayed_reach_inter.safe_config [where c=c, OF _ trace_n c_0] 
        have safe_delayed_upto_last: "\<forall>x<n - last. safe_delayed (c (Suc (last + x)))"
          by auto

        from last_step
        show ?thesis
        proof (cases)
          case (Program i' _ _ _ _ _ _ _ p' is')
          with j_changed j_bound\<^sub>l ts\<^sub>l_j 
          obtain
            ts\<^sub>l': "ts\<^sub>l' = ts\<^sub>l[j:=(p',is\<^sub>l@is',\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)]" and
            \<S>\<^sub>l': "\<S>\<^sub>l'=\<S>\<^sub>l" and
            m\<^sub>l': "m\<^sub>l'=m\<^sub>l" and
            prog_step: "\<theta>\<^sub>l\<turnstile> p\<^sub>l \<rightarrow>\<^sub>p (p', is')"
            by (cases "i'=j") auto
          from ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l
          obtain eqs: "p'=p\<^sub>j" "is\<^sub>l@is'=is\<^sub>j" "\<theta>\<^sub>l=\<theta>\<^sub>j" "\<D>\<^sub>l=\<D>\<^sub>j" "\<O>\<^sub>l=\<O>\<^sub>j" "\<R>\<^sub>l=\<R>\<^sub>j"
            by auto


          from undo_local_steps [where c=c, OF trace_rest c_last' idle_rest' safe_delayed_last, simplified ts\<^sub>l', 
            simplified,
            OF j_bound\<^sub>l ts\<^sub>l_j [simplified], simplified m\<^sub>l' \<S>\<^sub>l', simplified, OF dist_last  
            dist_last' [simplified ts\<^sub>l',simplified] safe_delayed_upto_last]
          obtain c' k where
            k_bound: "k \<le> n - last" and
            trace_c': "trace c' (Suc last) k" and
            c'_first: "c' (Suc last) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l)" and
            c'_leq: "(\<forall>x\<le>k. length (fst (c' (Suc (last + x)))) = length (fst (c (Suc (last + x)))))" and
            c'_safe: "(\<forall>x<k. safe_delayed (c' (Suc (last + x))))" and
            c'_unsafe: "(k < n - last \<longrightarrow> \<not> safe_delayed (c' (Suc (last + k))))" and
            c'_unch: 
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       ts\<^sub>x' ! j = ts\<^sub>l ! j \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x' a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x' a = m\<^sub>l a) \<and> (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x a = m\<^sub>l a)))" and
            c'_sim:
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       (\<forall>ja<length ts\<^sub>x. ja \<noteq> j \<longrightarrow> ts\<^sub>x' ! ja = ts\<^sub>x ! ja) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> m\<^sub>x' a = m\<^sub>x a)))"
            by auto

          obtain c_undo where c_undo:  "c_undo = (\<lambda>x. if x \<le> last then c x else c' (Suc last + x - last))"
            by blast
          have c_undo_0: "c_undo 0 = c\<^sub>0"
            by (auto simp add: c_undo c_0)
          from sequence_traces [OF trace_last trace_c', simplified c_last, OF c'_first c_undo]
          have trace_undo: "trace c_undo 0 (last + k)" .
          obtain u_ts u_shared u_m where 
            c_undo_n: "c_undo n = (u_ts,u_m, u_shared)"
            by (cases "c_undo n") 
          with last_bound c'_first c_last
          have c'_suc: "c' (Suc n) = (u_ts,u_m, u_shared)"
            apply (auto simp add: c_undo split: if_split_asm)
            apply (subgoal_tac "n=last")
            apply auto
            done

          
          show ?thesis  
          proof (cases "k < n - last")
            case True
            with c'_unsafe have unsafe: "\<not> safe_delayed (c_undo (last + k))"
              by (auto simp add: c_undo c_last c'_first)
            from True have "last + k \<le> n"
              by auto
            from safe_delayed_reach_inter.safe_config [OF this trace_undo, of "last + k"]
            have "safe_delayed (c_undo (last + k))"
              by (auto simp add: c_undo c_0)
            with unsafe have False by simp
            thus ?thesis ..
          next
            case False
            with k_bound have k: "k = n - last"
              by auto
            have eq': "Suc (last + (n - last)) = Suc n"
              using last_bound
              by simp
            from c'_unch [rule_format, of k, simplified k eq', OF _ c_suc c'_suc]
            obtain u_ts_j: "u_ts!j = ts\<^sub>l!j" and
              shared_unch: "\<forall>a\<in>\<O>\<^sub>l. u_shared a = \<S>\<^sub>l a" and
              shared_orig_unch: "\<forall>a\<in>\<O>\<^sub>l. \<S> a = \<S>\<^sub>l a" and
              mem_unch: "\<forall>a\<in>\<O>\<^sub>l. u_m a = m\<^sub>l a" and 
              mem_unch_orig: "\<forall>a\<in>\<O>\<^sub>l. m a = m\<^sub>l a"
              by auto

            from c'_sim [rule_format, of k, simplified k eq', OF _ c_suc c'_suc] i_bound neq_j_i
            obtain u_ts_i: "u_ts!i = ts!i" and
               shared_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_shared a = \<S> a" and
               mem_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_m a = m a"
              by auto
          
            from c'_leq [rule_format, of k] c'_suc c_suc
            have leq_u_ts: "length u_ts = length ts"
              by (auto simp add: eq' k)

            from j_bound leq_u_ts
            have j_bound_u: "j < length u_ts"
              by simp
            from i_bound leq_u_ts
            have i_bound_u: "i < length u_ts"
              by simp
            from k last_bound have l_k_eq: "last + k = n"
              by auto
            from safe_delayed_reach_inter.safe_config [OF _ trace_undo, simplified l_k_eq] 
              k c_0 last_bound
            have safe_delayed_c_undo': "\<forall>x\<le> n. safe_delayed (c_undo x)"
              by (auto simp add: c_undo split: if_split_asm)
            hence safe_delayed_c_undo: "\<forall>x<n. safe_delayed (c_undo x)"
              by (auto)
            from trace_preserves_simple_ownership_distinct [OF _ trace_undo, 
              simplified l_k_eq c_undo_0, simplified, OF dist this, of n] dist c_undo_n
            have dist_u_ts: "simple_ownership_distinct u_ts"
              by auto
            then interpret dist_u_ts_inter: simple_ownership_distinct u_ts .
          
            {
              fix a
              have "u_m a = m a"
              proof (cases "a \<in> \<O>\<^sub>l") 
                case True with mem_unch
                have "u_m a = m\<^sub>l a"
                  by auto
                moreover
                from True mem_unch_orig
                have "m a = m\<^sub>l a" 
                  by auto
                ultimately show ?thesis by simp
              next
                case False
                with mem_sim
                show ?thesis
                  by auto
              qed
            } hence u_m_eq: "u_m = m" by - (rule ext, auto) 

            {
              fix a
              have "u_shared a = \<S> a"
              proof (cases "a \<in> \<O>\<^sub>l") 
                case True with shared_unch
                have "u_shared a = \<S>\<^sub>l a"
                  by auto
                moreover
                from True shared_orig_unch
                have "\<S> a = \<S>\<^sub>l a" 
                  by auto
                ultimately show ?thesis by simp
              next
                case False
                with shared_sim
                show ?thesis
                  by auto
              qed
            } hence u_shared_eq: "u_shared = \<S>" by - (rule ext, auto) 

            {
              assume safe: "map owned u_ts,map released u_ts,i \<turnstile>(is,\<theta>,u_m,\<D>,\<O>,u_shared)\<surd> "
              then have False
              proof cases
                case Read
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  by (auto simp add:eqs races_def split: if_split_asm)
              next
                case WriteNonVolatile
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  by (auto simp add:eqs races_def split: if_split_asm)
              next
                case WriteVolatile
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  apply (auto simp add:eqs races_def split: if_split_asm)
                  apply fastforce
                  done
              next
                case Fence
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  by (auto simp add:eqs races_def split: if_split_asm)
              next
                case Ghost
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  apply (auto simp add:eqs races_def split: if_split_asm)
                  apply fastforce
                  done
              next
                case (RMWReadOnly cond t a D f ret A L R W)
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  by (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
              next
                case RMWWrite
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  apply (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
                  apply fastforce+
                  done
              next
                case Nil
                then show ?thesis
                using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                  by (auto simp add:eqs races_def split: if_split_asm)
              qed
            }
            hence "\<not> safe_delayed (u_ts, u_m, u_shared)"
              apply (clarsimp simp add: safe_delayed_def)
              apply (rule_tac x=i in exI)
              using u_ts_i ts_i i_bound_u
              apply auto
              done
            moreover
            from safe_delayed_c_undo' [rule_format, of n] c_undo_n
            have "safe_delayed (u_ts, u_m, u_shared)"
              by simp
            ultimately have False
              by simp
            thus ?thesis 
              by simp
          qed
        next
          case (Memop i' _ _ _ _ _ _ _ "is\<^sub>l'" \<theta>\<^sub>l' sb\<^sub>l' \<D>\<^sub>l' \<O>\<^sub>l' \<R>\<^sub>l')
          with j_changed j_bound\<^sub>l ts\<^sub>l_j 
          obtain             
            ts\<^sub>l': "ts\<^sub>l' = ts\<^sub>l[j:=(p\<^sub>l,is\<^sub>l',\<theta>\<^sub>l',sb\<^sub>l',\<D>\<^sub>l',\<O>\<^sub>l',\<R>\<^sub>l')]" and
            mem_step: "(is\<^sub>l, \<theta>\<^sub>l, sb\<^sub>l, m\<^sub>l, \<D>\<^sub>l, \<O>\<^sub>l, \<R>\<^sub>l,\<S>\<^sub>l) \<rightarrow> 
              (is\<^sub>l', \<theta>\<^sub>l', sb\<^sub>l', m\<^sub>l', \<D>\<^sub>l', \<O>\<^sub>l', \<R>\<^sub>l', \<S>\<^sub>l')"
              by (cases "i'=j") auto

          from mem_step  
          show ?thesis
          proof (cases)
            case (Read volatile a t)
            then obtain
              "is\<^sub>l": "is\<^sub>l = Read volatile a t # is\<^sub>l'" and
              \<theta>\<^sub>l': "\<theta>\<^sub>l' = \<theta>\<^sub>l(t \<mapsto> m\<^sub>l a)"  and
              sb\<^sub>l': "sb\<^sub>l'=sb\<^sub>l" and
              \<D>\<^sub>l': "\<D>\<^sub>l'=\<D>\<^sub>l" and
              \<O>\<^sub>l': "\<O>\<^sub>l' = \<O>\<^sub>l" and
              \<R>\<^sub>l': "\<R>\<^sub>l'= \<R>\<^sub>l" and
              \<S>\<^sub>l': "\<S>\<^sub>l'=\<S>\<^sub>l" and
              m\<^sub>l': "m\<^sub>l' = m\<^sub>l"
              by auto
            note eqs' = \<theta>\<^sub>l' sb\<^sub>l' \<D>\<^sub>l' \<O>\<^sub>l' \<R>\<^sub>l' \<S>\<^sub>l' m\<^sub>l'
            from ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l eqs'
            obtain eqs: "p\<^sub>l=p\<^sub>j" "is\<^sub>l'=is\<^sub>j" "\<theta>\<^sub>l(t \<mapsto> m\<^sub>l a)=\<theta>\<^sub>j" "\<D>\<^sub>l=\<D>\<^sub>j" "\<O>\<^sub>l=\<O>\<^sub>j" "\<R>\<^sub>l=\<R>\<^sub>j"
              by auto

            (* FIXME: now the same proof as for Program step *)
            from undo_local_steps [where c=c, OF trace_rest c_last' idle_rest' safe_delayed_last, simplified ts\<^sub>l', 
            simplified,
            OF j_bound\<^sub>l ts\<^sub>l_j [simplified], simplified m\<^sub>l' \<S>\<^sub>l', simplified, OF dist_last 
              dist_last' [simplified ts\<^sub>l',simplified] safe_delayed_upto_last]
            obtain c' k where
              k_bound: "k \<le> n - last" and
              trace_c': "trace c' (Suc last) k" and
              c'_first: "c' (Suc last) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l)" and
              c'_leq: "(\<forall>x\<le>k. length (fst (c' (Suc (last + x)))) = length (fst (c (Suc (last + x)))))" and
              c'_safe: "(\<forall>x<k. safe_delayed (c' (Suc (last + x))))" and
              c'_unsafe: "(k < n - last \<longrightarrow> \<not> safe_delayed (c' (Suc (last + k))))" and
              c'_unch: 
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       ts\<^sub>x' ! j = ts\<^sub>l ! j \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x' a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x' a = m\<^sub>l a) \<and> (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x a = m\<^sub>l a)))" and
              c'_sim:
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       (\<forall>ja<length ts\<^sub>x. ja \<noteq> j \<longrightarrow> ts\<^sub>x' ! ja = ts\<^sub>x ! ja) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> m\<^sub>x' a = m\<^sub>x a)))"
              by (clarsimp simp add: \<O>\<^sub>l')
            obtain c_undo where c_undo:  "c_undo = (\<lambda>x. if x \<le> last then c x else c' (Suc last + x - last))"
              by blast
            have c_undo_0: "c_undo 0 = c\<^sub>0"
              by (auto simp add: c_undo c_0)
            from sequence_traces [OF trace_last trace_c', simplified c_last, OF c'_first c_undo]
            have trace_undo: "trace c_undo 0 (last + k)" .
            obtain u_ts u_shared u_m where 
              c_undo_n: "c_undo n = (u_ts,u_m, u_shared)"
              by (cases "c_undo n") 
            with last_bound c'_first c_last
            have c'_suc: "c' (Suc n) = (u_ts,u_m, u_shared)"
              apply (auto simp add: c_undo split: if_split_asm)
              apply (subgoal_tac "n=last")
              apply auto
              done

          
            show ?thesis  
            proof (cases "k < n - last")
              case True
              with c'_unsafe have unsafe: "\<not> safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_last c'_first)
              from True have "last + k \<le> n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF this trace_undo, of "last + k"]
              have "safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_0)
              with unsafe have False by simp
              thus ?thesis ..
            next
              case False
              with k_bound have k: "k = n - last"
                by auto
              have eq': "Suc (last + (n - last)) = Suc n"
                using last_bound
                by simp
              from c'_unch [rule_format, of k, simplified k eq', OF _ c_suc c'_suc]
              obtain u_ts_j: "u_ts!j = ts\<^sub>l!j" and
                shared_unch: "\<forall>a\<in>\<O>\<^sub>l. u_shared a = \<S>\<^sub>l a" and
                shared_orig_unch: "\<forall>a\<in>\<O>\<^sub>l. \<S> a = \<S>\<^sub>l a" and
                mem_unch: "\<forall>a\<in>\<O>\<^sub>l. u_m a = m\<^sub>l a" and 
                mem_unch_orig: "\<forall>a\<in>\<O>\<^sub>l. m a = m\<^sub>l a"
                by auto

              from c'_sim [rule_format, of k, simplified k eq', OF _ c_suc c'_suc] i_bound neq_j_i
              obtain u_ts_i: "u_ts!i = ts!i" and
                 shared_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_shared a = \<S> a" and
                 mem_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_m a = m a"
                by auto
          
              from c'_leq [rule_format, of k] c'_suc c_suc
              have leq_u_ts: "length u_ts = length ts"
                by (auto simp add: eq' k)

              from j_bound leq_u_ts
              have j_bound_u: "j < length u_ts"
                by simp
              from i_bound leq_u_ts
              have i_bound_u: "i < length u_ts"
                by simp
              from k last_bound have l_k_eq: "last + k = n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF _ trace_undo, simplified l_k_eq] 
                k c_0 last_bound
              have safe_delayed_c_undo': "\<forall>x\<le>n. safe_delayed (c_undo x)"
                by (auto simp add: c_undo split: if_split_asm)
              hence safe_delayed_c_undo: "\<forall>x<n. safe_delayed (c_undo x)"
                by (auto)
              from trace_preserves_simple_ownership_distinct [OF _ trace_undo, 
                simplified l_k_eq c_undo_0, simplified, OF dist this, of n] dist c_undo_n
              have dist_u_ts: "simple_ownership_distinct u_ts"
                by auto
              then interpret dist_u_ts_inter: simple_ownership_distinct u_ts .

              
              {
                fix a
                have "u_m a = m a"
                proof (cases "a \<in> \<O>\<^sub>l") 
                  case True with mem_unch
                  have "u_m a = m\<^sub>l a"
                    by auto
                  moreover
                  from True mem_unch_orig
                  have "m a = m\<^sub>l a" 
                    by auto
                  ultimately show ?thesis by simp
                next
                  case False
                  with mem_sim
                  show ?thesis
                    by auto
                qed
              } hence u_m_eq: "u_m = m" by - (rule ext, auto) 

              {
                fix a
                have "u_shared a = \<S> a"
                proof (cases "a \<in> \<O>\<^sub>l") 
                  case True with shared_unch
                  have "u_shared a = \<S>\<^sub>l a"
                    by auto
                  moreover
                  from True shared_orig_unch
                  have "\<S> a = \<S>\<^sub>l a" 
                    by auto
                  ultimately show ?thesis by simp
                next
                  case False
                  with shared_sim
                  show ?thesis
                    by auto
                qed
              } hence u_shared_eq: "u_shared = \<S>" by - (rule ext, auto) 

              {
                assume safe: "map owned u_ts,map released u_ts,i \<turnstile>(is,\<theta>,u_m,\<D>,\<O>,u_shared)\<surd> "
                then have False
                proof cases
                  case Read
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case WriteNonVolatile
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case WriteVolatile
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def split: if_split_asm)
                    apply fastforce
                    done
                next
                  case Fence
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case Ghost
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def split: if_split_asm)
                    apply fastforce
                    done
                next
                  case (RMWReadOnly cond t a D f ret A L R W)
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
                next
                  case RMWWrite
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
                    apply fastforce+
                    done
                next
                  case Nil
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                qed
              }
              hence "\<not> safe_delayed (u_ts, u_m, u_shared)"
                apply (clarsimp simp add: safe_delayed_def)
                apply (rule_tac x=i in exI)
                using u_ts_i ts_i i_bound_u
                apply auto
                done
              moreover
              from safe_delayed_c_undo' [rule_format, of n] c_undo_n
              have "safe_delayed (u_ts, u_m, u_shared)"
                by simp
              ultimately have False
                by simp
              thus ?thesis 
                by simp
            qed
          next
            case (WriteNonVolatile  a D f A L R W)
            then obtain
              "is\<^sub>l": "is\<^sub>l = Write False a (D, f) A L R W # is\<^sub>l'" and
              \<theta>\<^sub>l': "\<theta>\<^sub>l' = \<theta>\<^sub>l"  and
              sb\<^sub>l': "sb\<^sub>l'=sb\<^sub>l" and
              \<D>\<^sub>l': "\<D>\<^sub>l'=\<D>\<^sub>l" and
              \<O>\<^sub>l': "\<O>\<^sub>l' = \<O>\<^sub>l" and
              \<R>\<^sub>l': "\<R>\<^sub>l'= \<R>\<^sub>l" and
              \<S>\<^sub>l': "\<S>\<^sub>l'=\<S>\<^sub>l" and
              m\<^sub>l': "m\<^sub>l' = m\<^sub>l(a:=f \<theta>\<^sub>l)"
              by auto
            note eqs' = \<theta>\<^sub>l' sb\<^sub>l' \<D>\<^sub>l' \<O>\<^sub>l' \<R>\<^sub>l' \<S>\<^sub>l' m\<^sub>l'
            from ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l eqs'
            obtain eqs: "p\<^sub>l=p\<^sub>j" "is\<^sub>l'=is\<^sub>j" "\<theta>\<^sub>l=\<theta>\<^sub>j" "\<D>\<^sub>l=\<D>\<^sub>j" "\<O>\<^sub>l=\<O>\<^sub>j" 
              "\<R>\<^sub>l=\<R>\<^sub>j"
              by auto

            from safe\<^sub>l [simplified "is\<^sub>l"]
            obtain a_owned: "a \<in> \<O>\<^sub>l" and a_unshared: "a \<notin> dom \<S>\<^sub>l"
              by cases auto
            have m\<^sub>l_unch_unowned: "\<forall>a'. a' \<notin> \<O>\<^sub>l \<longrightarrow> m\<^sub>l a' = (m\<^sub>l(a := f \<theta>\<^sub>l)) a'" 
            using a_owned by auto

            have m\<^sub>l_unch_unshared: "\<forall>a'. a' \<in> \<O>\<^sub>l \<longrightarrow> a' \<in> dom \<S>\<^sub>l \<longrightarrow> m\<^sub>l a' = (m\<^sub>l(a := f \<theta>\<^sub>l)) a'" 
            using a_unshared by auto
            
            from undo_local_steps [where c=c, OF trace_rest c_last' idle_rest' safe_delayed_last, simplified ts\<^sub>l', 
              simplified,
              OF j_bound\<^sub>l ts\<^sub>l_j [simplified], simplified m\<^sub>l' \<S>\<^sub>l',OF  m\<^sub>l_unch_unowned m\<^sub>l_unch_unshared, simplified, 
              OF dist_last dist_last' [simplified ts\<^sub>l',simplified] safe_delayed_upto_last]

            obtain c' k where
              k_bound: "k \<le> n - last" and
              trace_c': "trace c' (Suc last) k" and
              c'_first: "c' (Suc last) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l)" and
              c'_leq: "(\<forall>x\<le>k. length (fst (c' (Suc (last + x)))) = length (fst (c (Suc (last + x)))))" and
              c'_safe: "(\<forall>x<k. safe_delayed (c' (Suc (last + x))))" and
              c'_unsafe: "(k < n - last \<longrightarrow> \<not> safe_delayed (c' (Suc (last + k))))" and
              c'_unch: 
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       ts\<^sub>x' ! j = ts\<^sub>l ! j \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x' a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x' a = m\<^sub>l a) \<and> (\<forall>a'\<in>\<O>\<^sub>l. m\<^sub>x a' = (m\<^sub>l(a := f \<theta>\<^sub>l)) a')))" and
              c'_sim:
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       (\<forall>ja<length ts\<^sub>x. ja \<noteq> j \<longrightarrow> ts\<^sub>x' ! ja = ts\<^sub>x ! ja) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> m\<^sub>x' a = m\<^sub>x a)))"
              by (clarsimp simp add: \<O>\<^sub>l')

            obtain c_undo where c_undo:  "c_undo = (\<lambda>x. if x \<le> last then c x else c' (Suc last + x - last))"
              by blast
            have c_undo_0: "c_undo 0 = c\<^sub>0"
              by (auto simp add: c_undo c_0)
            from sequence_traces [OF trace_last trace_c', simplified c_last, OF c'_first c_undo]
            have trace_undo: "trace c_undo 0 (last + k)" .
            obtain u_ts u_shared u_m where 
              c_undo_n: "c_undo n = (u_ts,u_m, u_shared)"
              by (cases "c_undo n") 
            with last_bound c'_first c_last
            have c'_suc: "c' (Suc n) = (u_ts,u_m, u_shared)"
              apply (auto simp add: c_undo split: if_split_asm)
              apply (subgoal_tac "n=last")
              apply auto
              done

          
            show ?thesis  
            proof (cases "k < n - last")
              case True
              with c'_unsafe have unsafe: "\<not> safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_last c'_first)
              from True have "last + k \<le> n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF this trace_undo, of "last + k"]
              have "safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_0)
              with unsafe have False by simp
              thus ?thesis ..
            next
              case False
              with k_bound have k: "k = n - last"
                by auto
              have eq': "Suc (last + (n - last)) = Suc n"
                using last_bound
                by simp
              from c'_unch [rule_format, of k, simplified k eq', OF _ c_suc c'_suc]
              obtain u_ts_j: "u_ts!j = ts\<^sub>l!j" and
                shared_unch: "\<forall>a\<in>\<O>\<^sub>l. u_shared a = \<S>\<^sub>l a" and
                shared_orig_unch: "\<forall>a\<in>\<O>\<^sub>l. \<S> a = \<S>\<^sub>l a" and
                mem_unch: "\<forall>a\<in>\<O>\<^sub>l. u_m a = m\<^sub>l a" and 
                mem_unch_orig: "\<forall>a'\<in>\<O>\<^sub>l. m a' = (m\<^sub>l(a := f \<theta>\<^sub>l)) a'"
                by auto

              from c'_sim [rule_format, of k, simplified k eq', OF _ c_suc c'_suc] i_bound neq_j_i
              obtain u_ts_i: "u_ts!i = ts!i" and
                 shared_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_shared a = \<S> a" and
                 mem_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_m a = m a"
                by auto
          
              from c'_leq [rule_format, of k] c'_suc c_suc
              have leq_u_ts: "length u_ts = length ts"
                by (auto simp add: eq' k)

              from j_bound leq_u_ts
              have j_bound_u: "j < length u_ts"
                by simp
              from i_bound leq_u_ts
              have i_bound_u: "i < length u_ts"
                by simp
              from k last_bound have l_k_eq: "last + k = n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF _ trace_undo, simplified l_k_eq] 
                k c_0 last_bound
              have safe_delayed_c_undo': "\<forall>x\<le>n. safe_delayed (c_undo x)"
                by (auto simp add: c_undo split: if_split_asm)              
              hence safe_delayed_c_undo: "\<forall>x<n. safe_delayed (c_undo x)"
                by auto
              from trace_preserves_simple_ownership_distinct [OF _ trace_undo, 
                simplified l_k_eq c_undo_0, simplified, OF dist this, of n] dist c_undo_n
              have dist_u_ts: "simple_ownership_distinct u_ts"
                by auto
              then interpret dist_u_ts_inter: simple_ownership_distinct u_ts .
          (* FIXME delete
              {
                fix a
                have "u_m a = m a"
                proof (cases "a \<in> \<O>\<^sub>l") 
                  case True with mem_unch
                  have "u_m a = m\<^sub>l a"
                    by auto
                  moreover
                  from True mem_unch_orig
                  have "m a = m\<^sub>l a" 
                    by auto
                  ultimately show ?thesis by simp
                next
                  case False
                  with mem_sim
                  show ?thesis
                    by auto
                qed
              } hence u_m_eq: "u_m = m" by - (rule ext, auto) 
*)
              {
                fix a
                have "u_shared a = \<S> a"
                proof (cases "a \<in> \<O>\<^sub>l") 
                  case True with shared_unch
                  have "u_shared a = \<S>\<^sub>l a"
                    by auto
                  moreover
                  from True shared_orig_unch
                  have "\<S> a = \<S>\<^sub>l a" 
                    by auto
                  ultimately show ?thesis by simp
                next
                  case False
                  with shared_sim
                  show ?thesis
                    by auto
                qed
              } hence u_shared_eq: "u_shared = \<S>" by - (rule ext, auto) 

              {
                assume safe: "map owned u_ts,map released u_ts,i \<turnstile>(is,\<theta>,u_m,\<D>,\<O>,u_shared)\<surd> "
                then have False
                proof cases
                  case Read
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case WriteNonVolatile
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case WriteVolatile
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def split: if_split_asm)
                    apply fastforce
                    done
                next
                  case Fence
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case Ghost
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def split: if_split_asm)
                    apply fastforce
                    done
                next
                  case (RMWReadOnly cond t a' D f ret A L R W)
                  with ts_i "is" obtain
                    ins: "ins = RMW a' t (D, f) cond ret A L R W" and
                    owned_or_shared: "a' \<in> \<O> \<or> a' \<in> dom u_shared" and
                    cond: "\<not> cond (\<theta>(t \<mapsto> u_m a'))" and
                    rels_race: "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> ((map released u_ts) ! j) a' \<noteq> Some False"
                    by auto
                  from dist_u_ts_inter.simple_ownership_distinct [OF j_bound_u i_bound_u neq_j_i u_ts_j [simplified ts\<^sub>l_j] 
                    u_ts_i [simplified ts_i]] 
                  have dist: "\<O>\<^sub>l \<inter> \<O> = {}"
                    by auto
                  from owned_or_shared dist a_owned a_unshared shared_orig_unch
                  have a'_a: "a'\<noteq>a"
                    by (auto simp add: u_shared_eq domIff)
                  have u_m_eq: "u_m a' = m a'"
                  proof (cases "a' \<in> \<O>\<^sub>l") 
                    case True with mem_unch
                    have "u_m a' = m\<^sub>l a'"
                      by auto
                    moreover
                    from True mem_unch_orig a'_a
                    have "m a' = m\<^sub>l a'" 
                      by auto
                    ultimately show ?thesis by simp
                  next
                    case False
                    with mem_sim
                    show ?thesis
                      by auto
                  qed
                  with ins cond rels_race show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
                next
                  case (RMWWrite cond t a' A L R D f ret W)
                  with ts_i "is" obtain
                    ins: "ins = RMW a' t (D, f) cond ret A L R W" and
                    cond: "cond (\<theta>(t \<mapsto> u_m a'))" and
                    a': "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> a' \<notin> (map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)" and
                    safety:
                      "A \<subseteq> dom u_shared \<union> \<O>" "L \<subseteq> A" "R \<subseteq> \<O>" "A \<inter> R = {}"
                      "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> A \<inter> ((map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)) = {}"
                      "a' \<notin> read_only u_shared"
                    by auto
                  from a'[rule_format, of j] j_bound_u u_ts_j ts\<^sub>l_j neq_j_i
                  have "a' \<notin> \<O>\<^sub>l"
                    by auto
                  from mem_sim [rule_format, OF this]
                  have u_m_eq: "u_m a' = m a'"
                    by auto
                  
                  with ins cond safety a' show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    apply (auto simp add:eqs races_def u_shared_eq u_m_eq split: if_split_asm)
                    apply fastforce
                    done
                next
                  case Nil
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                qed
              }
              hence "\<not> safe_delayed (u_ts, u_m, u_shared)"
                apply (clarsimp simp add: safe_delayed_def)
                apply (rule_tac x=i in exI)
                using u_ts_i ts_i i_bound_u
                apply auto
                done
              moreover
              from safe_delayed_c_undo' [rule_format, of n] c_undo_n
              have "safe_delayed (u_ts, u_m, u_shared)"
                by simp
              ultimately have False
                by simp
              thus ?thesis 
                by simp
            qed
          next
            case WriteVolatile
            with ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l have "\<R>\<^sub>j = Map.empty"
              by auto
            with \<R>\<^sub>j_non_empty have False by auto
            thus ?thesis ..
          next
            case Fence
            with ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l have "\<R>\<^sub>j = Map.empty"
              by auto
            with \<R>\<^sub>j_non_empty have False by auto
            thus ?thesis ..
          next
            case RMWReadOnly
            with ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l have "\<R>\<^sub>j = Map.empty"
              by auto
            with \<R>\<^sub>j_non_empty have False by auto
            thus ?thesis ..
          next
            case RMWWrite
            with ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l have "\<R>\<^sub>j = Map.empty"
              by auto
            with \<R>\<^sub>j_non_empty have False by auto
            thus ?thesis ..
          next
            case (Ghost A L R W)
            then obtain
              "is\<^sub>l": "is\<^sub>l = Ghost A L R W # is\<^sub>l'" and
              \<theta>\<^sub>l': "\<theta>\<^sub>l' = \<theta>\<^sub>l"  and
              sb\<^sub>l': "sb\<^sub>l'=sb\<^sub>l" and
              \<D>\<^sub>l': "\<D>\<^sub>l'=\<D>\<^sub>l" and
              \<O>\<^sub>l': "\<O>\<^sub>l' = \<O>\<^sub>l \<union> A - R" and
              \<R>\<^sub>l': "\<R>\<^sub>l'= augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l" and
              \<S>\<^sub>l': "\<S>\<^sub>l'=\<S>\<^sub>l \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and
              m\<^sub>l': "m\<^sub>l' = m\<^sub>l"
              by auto
            note eqs' = \<theta>\<^sub>l' sb\<^sub>l' \<D>\<^sub>l' \<O>\<^sub>l' \<R>\<^sub>l' \<S>\<^sub>l' m\<^sub>l'
            from ts\<^sub>l'_j ts\<^sub>l' ts_j j_bound\<^sub>l eqs'
            obtain eqs: "p\<^sub>l=p\<^sub>j" "is\<^sub>l'=is\<^sub>j" "\<theta>\<^sub>l=\<theta>\<^sub>j" "\<D>\<^sub>l=\<D>\<^sub>j" "\<O>\<^sub>l \<union> A - R = \<O>\<^sub>j" 
              "augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l=\<R>\<^sub>j"
              by auto

            from safe\<^sub>l [simplified "is\<^sub>l"]
            obtain
            A_shared_owned: "A \<subseteq> dom \<S>\<^sub>l \<union> \<O>\<^sub>l" and L_A: "L \<subseteq> A" and R_owns: "R \<subseteq> \<O>\<^sub>l" and A_R: "A \<inter> R = {}" and
            "\<forall>j' < length (map owned ts\<^sub>l). j\<noteq>j' \<longrightarrow>  A \<inter> ((map owned ts\<^sub>l)!j' \<union> dom ((map released ts\<^sub>l)!j')) = {}"
              by cases auto


            from A_shared_owned L_A R_owns A_R
            have shared_eq: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> a \<notin> \<O>\<^sub>l' \<longrightarrow> \<S>\<^sub>l a = (\<S>\<^sub>l \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
              by (auto simp add: restrict_shared_def augment_shared_def \<O>\<^sub>l' split: option.splits)
            
            from undo_local_steps [where c=c, OF trace_rest c_last' idle_rest' safe_delayed_last, simplified ts\<^sub>l', 
              simplified,
              OF j_bound\<^sub>l ts\<^sub>l_j [simplified], simplified m\<^sub>l' \<S>\<^sub>l', simplified, 
              OF  shared_eq dist_last dist_last' [simplified ts\<^sub>l',simplified] safe_delayed_upto_last]

            obtain c' k where
              k_bound: "k \<le> n - last" and
              trace_c': "trace c' (Suc last) k" and
              c'_first: "c' (Suc last) = (ts\<^sub>l, m\<^sub>l, \<S>\<^sub>l)" and
              c'_leq: "(\<forall>x\<le>k. length (fst (c' (Suc (last + x)))) = length (fst (c (Suc (last + x)))))" and
              c'_safe: "(\<forall>x<k. safe_delayed (c' (Suc (last + x))))" and
              c'_unsafe: "(k < n - last \<longrightarrow> \<not> safe_delayed (c' (Suc (last + k))))" and
              c'_unch: 
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       ts\<^sub>x' ! j = ts\<^sub>l ! j \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x' a = \<S>\<^sub>l a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. \<S>\<^sub>x a = (\<S>\<^sub>l \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a) \<and>
                       (\<forall>a\<in>\<O>\<^sub>l. m\<^sub>x' a = m\<^sub>l a) \<and> (\<forall>a'\<in>\<O>\<^sub>l. m\<^sub>x a' = (m\<^sub>l) a')))" and
              c'_sim:
               "(\<forall>x\<le>k. \<forall>ts\<^sub>x \<S>\<^sub>x m\<^sub>x.
                   c (Suc (last + x)) = (ts\<^sub>x, m\<^sub>x, \<S>\<^sub>x) \<longrightarrow>
                   (\<forall>ts\<^sub>x' \<S>\<^sub>x' m\<^sub>x'.
                       c' (Suc (last + x)) = (ts\<^sub>x', m\<^sub>x', \<S>\<^sub>x') \<longrightarrow>
                       (\<forall>ja<length ts\<^sub>x. ja \<noteq> j \<longrightarrow> ts\<^sub>x' ! ja = ts\<^sub>x ! ja) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> a \<notin> \<O>\<^sub>l' \<longrightarrow> \<S>\<^sub>x' a = \<S>\<^sub>x a) \<and>
                       (\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> m\<^sub>x' a = m\<^sub>x a)))"

              by (clarsimp )
            obtain c_undo where c_undo:  "c_undo = (\<lambda>x. if x \<le> last then c x else c' (Suc last + x - last))"
              by blast
            have c_undo_0: "c_undo 0 = c\<^sub>0"
              by (auto simp add: c_undo c_0)
            from sequence_traces [OF trace_last trace_c', simplified c_last, OF c'_first c_undo]
            have trace_undo: "trace c_undo 0 (last + k)" .
            obtain u_ts u_shared u_m where 
              c_undo_n: "c_undo n = (u_ts,u_m, u_shared)"
              by (cases "c_undo n") 
            with last_bound c'_first c_last
            have c'_suc: "c' (Suc n) = (u_ts,u_m, u_shared)"
              apply (auto simp add: c_undo split: if_split_asm)
              apply (subgoal_tac "n=last")
              apply auto
              done

          
            show ?thesis  
            proof (cases "k < n - last")
              case True
              with c'_unsafe have unsafe: "\<not> safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_last c'_first)
              from True have "last + k \<le> n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF this trace_undo, of "last + k"]
              have "safe_delayed (c_undo (last + k))"
                by (auto simp add: c_undo c_0)
              with unsafe have False by simp
              thus ?thesis ..
            next
              case False
              with k_bound have k: "k = n - last"
                by auto
              have eq': "Suc (last + (n - last)) = Suc n"
                using last_bound
                by simp
              from c'_unch [rule_format, of k, simplified k eq', OF _ c_suc c'_suc]
              obtain u_ts_j: "u_ts!j = ts\<^sub>l!j" and
                shared_unch: "\<forall>a\<in>\<O>\<^sub>l. u_shared a = \<S>\<^sub>l a" and
                shared_orig_unch: "\<forall>a\<in>\<O>\<^sub>l. \<S> a = (\<S>\<^sub>l \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a" and
                mem_unch: "\<forall>a\<in>\<O>\<^sub>l. u_m a = m\<^sub>l a" and 
                mem_unch_orig: "\<forall>a'\<in>\<O>\<^sub>l. m a' = m\<^sub>l a'"
                by auto

              from c'_sim [rule_format, of k, simplified k eq', OF _ c_suc c'_suc] i_bound neq_j_i
              obtain u_ts_i: "u_ts!i = ts!i" and
                 shared_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> a \<notin> \<O>\<^sub>l' \<longrightarrow> u_shared a = \<S> a" and
                 mem_sim: "\<forall>a. a \<notin> \<O>\<^sub>l \<longrightarrow> u_m a = m a"
                by auto
          
              from c'_leq [rule_format, of k] c'_suc c_suc
              have leq_u_ts: "length u_ts = length ts"
                by (auto simp add: eq' k)

              from j_bound leq_u_ts
              have j_bound_u: "j < length u_ts"
                by simp
              from i_bound leq_u_ts
              have i_bound_u: "i < length u_ts"
                by simp
              from k last_bound have l_k_eq: "last + k = n"
                by auto
              from safe_delayed_reach_inter.safe_config [OF _ trace_undo, simplified l_k_eq] 
                k c_0 last_bound
              have safe_delayed_c_undo': "\<forall>x\<le>n. safe_delayed (c_undo x)"
                by (auto simp add: c_undo split: if_split_asm)              
              hence safe_delayed_c_undo: "\<forall>x<n. safe_delayed (c_undo x)"
                by auto
              from trace_preserves_simple_ownership_distinct [OF _ trace_undo, 
                simplified l_k_eq c_undo_0, simplified, OF dist this, of n] dist c_undo_n
              have dist_u_ts: "simple_ownership_distinct u_ts"
                by auto
              then interpret dist_u_ts_inter: simple_ownership_distinct u_ts .
              {
                fix a
                have "u_m a = m a"
                proof (cases "a \<in> \<O>\<^sub>l") 
                  case True with mem_unch
                  have "u_m a = m\<^sub>l a"
                    by auto
                  moreover
                  from True mem_unch_orig
                  have "m a = m\<^sub>l a" 
                    by auto
                  ultimately show ?thesis by simp
                next
                  case False
                  with mem_sim
                  show ?thesis
                    by auto
                qed
              } hence u_m_eq: "u_m = m" by - (rule ext, auto) 
              {
                assume safe: "map owned u_ts,map released u_ts,i \<turnstile>(is,\<theta>,u_m,\<D>,\<O>,u_shared)\<surd> "
                then have False
                proof cases
                  case (Read a volatile t)
                  with ts_i "is" obtain
                    ins: "ins = Read volatile a t"  and
                    access_cond: "a \<in> \<O> \<or> a \<in> read_only u_shared \<or> volatile \<and> a \<in> dom u_shared" and
                    rels_cond: "\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> ((map released u_ts) ! j) a \<noteq> Some False" and
                    rels_non_volatile_cond: "\<not> volatile \<longrightarrow> (\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> a \<notin> dom ((map released u_ts) ! j) )" and
                    clean: "volatile \<longrightarrow> \<not> \<D>"
                    by auto

                  from race ts_j
                  have rc: "augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l a = Some False \<or> 
                            (\<not> volatile \<and> a \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l))"
                    by (auto simp add: races_def ins eqs)
                  from rels_cond [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  have \<R>\<^sub>l_a: "\<R>\<^sub>l a \<noteq> Some False"
                    by auto
                  from dist_u_ts_inter.simple_ownership_distinct [OF j_bound_u i_bound_u neq_j_i u_ts_j [simplified ts\<^sub>l_j] 
                    u_ts_i [simplified ts_i]] 
                  have dist: "\<O>\<^sub>l \<inter> \<O> = {}"
                    by auto

                  show ?thesis 
                  proof (cases volatile)
                    case True
                    note volatile=this
                    show ?thesis
                    proof (cases "a \<in> R")
                      case False 
                      with rc \<R>\<^sub>l_a show False
                        by (auto simp add: augment_rels_def volatile)
                    next
                      case True
                      with R_owns
                      have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                        by auto
                      from shared_unch [rule_format, OF a_owns\<^sub>l]
                      have u_shared_eq: "u_shared a = \<S>\<^sub>l a"
                        by auto
                      from a_owns\<^sub>l dist have "a \<notin> \<O>"
                        by auto
                      moreover
                      {
                        assume "a \<in> read_only u_shared"
                        with u_shared_eq have "\<S>\<^sub>l a = Some False"
                          by (auto simp add: read_only_def)
                        with rc True \<R>\<^sub>l_a have False
                          by (auto simp add: augment_rels_def split: option.splits simp add: domIff volatile)
                      }
                      moreover
                      {
                        assume "a \<in> dom u_shared"
                        with u_shared_eq rc True \<R>\<^sub>l_a have False
                          by (auto simp add: augment_rels_def split: option.splits simp add: domIff volatile)
                      }
                      ultimately show False
                      using access_cond 
                        by auto
                    qed
                  next
                    case False
                    note non_volatile = this
                    from rels_non_volatile_cond [rule_format, OF False j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                    have \<R>\<^sub>l_a: "\<R>\<^sub>l a = None"
                      by (auto simp add: domIff)
                    show ?thesis
                    proof (cases "a \<in> R")
                      case False 
                      with rc \<R>\<^sub>l_a show False
                        by (auto simp add: augment_rels_def non_volatile domIff)
                    next
                      case True
                      with R_owns
                      have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                        by auto
                      from shared_unch [rule_format, OF a_owns\<^sub>l]
                      have u_shared_eq: "u_shared a = \<S>\<^sub>l a"
                        by auto
                      from a_owns\<^sub>l dist have a_unowned: "a \<notin> \<O>"
                        by auto
                      moreover
                      from ro_last_last interpret
                      read_only_unowned \<S>\<^sub>l ts\<^sub>l .
                      from read_only_unowned [OF j_bound\<^sub>l ts\<^sub>l_j] a_owns\<^sub>l have a_unsh: "a \<notin>  read_only \<S>\<^sub>l" by auto
                      {
                        assume "a \<in> read_only u_shared"
                        with u_shared_eq have sh: "\<S>\<^sub>l a = Some False"
                          by (auto simp add: read_only_def)
                        
                        with rc True \<R>\<^sub>l_a access_cond u_shared_eq a_unowned sh a_owns\<^sub>l a_unsh have False
                          by (auto simp add: augment_rels_def split: option.splits simp add: domIff non_volatile read_only_def)
                      }
                      moreover
                      {
                        assume "a \<in> dom u_shared"
                        with u_shared_eq rc True \<R>\<^sub>l_a a_owns\<^sub>l a_unsh access_cond dist have False
                          by (auto simp add: augment_rels_def split: option.splits simp add: domIff non_volatile read_only_def)
                      }
                      ultimately show False
                      using access_cond 
                        by (auto)
                    qed
                  qed
                next
                  case (WriteNonVolatile a D f A' L' R' W')
                  with ts_i "is" obtain
                    ins: "ins = Write False a (D, f) A' L' R' W'"  and
                    a_owned: "a \<in> \<O>" and a_unshared: "a \<notin> dom u_shared" and
                    a_unreleased: "\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> a \<notin> dom ((map released u_ts) ! j)"
                    by auto
                  from dist_u_ts_inter.simple_ownership_distinct [OF j_bound_u i_bound_u neq_j_i u_ts_j [simplified ts\<^sub>l_j] 
                    u_ts_i [simplified ts_i]] 
                  have dist: "\<O>\<^sub>l \<inter> \<O> = {}"
                    by auto
                  from race ts_j
                  have rc: "a \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                    by (auto simp add: races_def ins eqs)
                  from a_unreleased [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  have \<R>\<^sub>l_a: "a \<notin> dom \<R>\<^sub>l"
                    by auto
                  show False
                  proof (cases "a \<in> R")
                    case False 
                    with rc \<R>\<^sub>l_a show False
                      by (auto simp add: augment_rels_def domIff)
                  next
                    case True
                    with R_owns
                    have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                      by auto
                    with a_owned dist show False
                      by auto
                  qed
                next
                  case (WriteVolatile a A' L' R' D f W')
                  with ts_i "is" obtain
                    ins: "ins = Write True a (D, f) A' L' R' W'"  and
                    a_un_owned_released: "\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> 
                      a \<notin> ((map owned u_ts) ! j) \<and> a \<notin> dom ((map released u_ts) ! j)" and
                    A'_owns_shared: "A' \<subseteq> dom u_shared \<union> \<O>" and
                    L'_A': "L' \<subseteq> A'" and
                    R'_owned: "R' \<subseteq> \<O>" and
                    A'_R': "A' \<inter> R' = {}" and
                    acq_ok: "\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> A' \<inter> ((map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)) = {}" and
                   
                    writeable: "a \<notin> read_only u_shared"
                    by auto
                  from a_un_owned_released [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  obtain \<O>\<^sub>l_a: "a \<notin> \<O>\<^sub>l" and \<R>\<^sub>l_a: "a \<notin> dom (\<R>\<^sub>l)"
                    by auto
                  from acq_ok [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  obtain \<O>\<^sub>l_A': "A' \<inter> \<O>\<^sub>l = {}" and \<R>\<^sub>l_A': "A' \<inter> dom (\<R>\<^sub>l) = {}"
                    by auto
                  {
                    assume rc: "a \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                    have False
                    proof (cases "a \<in> R")
                      case False 
                      with rc \<R>\<^sub>l_a show False
                        by (auto simp add: augment_rels_def domIff)
                    next
                      case True
                      with R_owns
                      have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                        by auto
                      with \<O>\<^sub>l_a show False
                        by auto
                    qed
                  }
                  moreover 
                  {
                    assume rc: "A' \<inter> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l) \<noteq> {}"
                    then obtain a' where a'_A': "a' \<in> A'" and a'_aug: "a' \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                      by auto
                    have False
                    proof (cases "a' \<in> R")
                      case False 
                      with a'_aug a'_A' \<R>\<^sub>l_A' show False
                        by (auto simp add: augment_rels_def domIff)
                    next
                      case True
                      with R_owns have a'_owns\<^sub>l: "a' \<in> \<O>\<^sub>l"
                        by auto
                      with \<O>\<^sub>l_A' a'_A' show False
                        by auto
                    qed
                  }
                  ultimately show False
                  using race ts_j 
                    by (auto simp add: races_def ins eqs)
                next
                  case Fence
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                next
                  case (Ghost A' L' R' W')
                  with ts_i "is" obtain
                    ins: "ins = Ghost A' L' R' W'"  and
                    A'_owns_shared: "A' \<subseteq> dom u_shared \<union> \<O>" and
                    L'_A': "L' \<subseteq> A'" and
                    R'_owned: "R' \<subseteq> \<O>" and
                    A'_R': "A' \<inter> R' = {}" and
                    acq_ok: "\<forall>j<length u_ts. i \<noteq> j \<longrightarrow> A' \<inter> ((map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)) = {}" 
                    by auto
                  from acq_ok [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  obtain \<O>\<^sub>l_A': "A' \<inter> \<O>\<^sub>l = {}" and \<R>\<^sub>l_A': "A' \<inter> dom (\<R>\<^sub>l) = {}"
                    by auto
                  
                  from race ts_j 
                  obtain a'  where a'_A': "a' \<in> A'" and 
                    a'_aug: "a' \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                    by (auto simp add: races_def ins eqs)
                  show False
                  proof (cases "a' \<in> R")
                    case False 
                    with a'_aug a'_A' \<R>\<^sub>l_A' show False
                      by (auto simp add: augment_rels_def domIff)
                  next
                    case True
                    with R_owns have a'_owns\<^sub>l: "a' \<in> \<O>\<^sub>l"
                      by auto
                    with \<O>\<^sub>l_A' a'_A' show False
                      by auto
                  qed
                next
                  case (RMWReadOnly cond t a D f ret A' L' R' W')
                  with ts_i "is" obtain
                    ins: "ins = RMW a t (D, f) cond ret A' L' R' W'" and
                    owned_or_shared: "a \<in> \<O> \<or> a \<in> dom u_shared" and
                    cond: "\<not> cond (\<theta>(t \<mapsto> u_m a))" and
                    rels_race: "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> ((map released u_ts) ! j) a \<noteq> Some False"
                    by auto
                  from dist_u_ts_inter.simple_ownership_distinct [OF j_bound_u i_bound_u neq_j_i u_ts_j [simplified ts\<^sub>l_j] 
                    u_ts_i [simplified ts_i]] 
                  have dist: "\<O>\<^sub>l \<inter> \<O> = {}"
                    by auto
                  from race ts_j cond
                  have rc: "augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l a = Some False"
                    by (auto simp add: races_def ins eqs u_m_eq)

                  from rels_race [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] 
                    u_ts_j ts\<^sub>l_j j_bound_u
                  have \<R>\<^sub>l_a: "\<R>\<^sub>l a \<noteq> Some False"
                    by auto

                  show ?thesis
                  proof (cases "a \<in> R")
                    case False 
                    with rc \<R>\<^sub>l_a show False
                      by (auto simp add: augment_rels_def)
                  next
                    case True
                    with R_owns
                    have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                      by auto
                    from shared_unch [rule_format, OF a_owns\<^sub>l]
                    have u_shared_eq: "u_shared a = \<S>\<^sub>l a"
                      by auto
                    from a_owns\<^sub>l dist have "a \<notin> \<O>"
                      by auto
                    with u_shared_eq rc True \<R>\<^sub>l_a owned_or_shared show False
                      by (auto simp add: augment_rels_def split: option.splits simp add: domIff)
                  qed
                next
                  case (RMWWrite cond t a A' L' R' D f ret W')
                  with ts_i "is" obtain
                    ins: "ins = RMW a t (D, f) cond ret A' L' R' W'" and
                    cond: "cond (\<theta>(t \<mapsto> u_m a))" and
                    a_un_owned_released: "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> a \<notin> (map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)" and
                    A'_owns_shared:"A' \<subseteq> dom u_shared \<union> \<O>" and
                    L'_A': "L' \<subseteq> A'" and
                    R'_owned: "R' \<subseteq> \<O>" and
                    A'_R': "A' \<inter> R' = {}" and
                    acq_ok: "\<forall>j<length (map owned u_ts). i \<noteq> j \<longrightarrow> A' \<inter> ((map owned u_ts) ! j \<union> dom ((map released u_ts) ! j)) = {}" and 
                    writeable: "a \<notin> read_only u_shared"
                    by auto


                  from a_un_owned_released [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  obtain \<O>\<^sub>l_a: "a \<notin> \<O>\<^sub>l" and \<R>\<^sub>l_a: "a \<notin> dom (\<R>\<^sub>l)"
                    by auto
                  from acq_ok [rule_format, simplified, OF j_bound_u neq_j_i [symmetric]] u_ts_j ts\<^sub>l_j j_bound_u
                  obtain \<O>\<^sub>l_A': "A' \<inter> \<O>\<^sub>l = {}" and \<R>\<^sub>l_A': "A' \<inter> dom (\<R>\<^sub>l) = {}"
                    by auto
                  {
                    assume rc: "a \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                    have False
                    proof (cases "a \<in> R")
                      case False 
                      with rc \<R>\<^sub>l_a show False
                        by (auto simp add: augment_rels_def domIff)
                    next
                      case True
                      with R_owns
                      have a_owns\<^sub>l: "a \<in> \<O>\<^sub>l"
                        by auto
                      with \<O>\<^sub>l_a show False
                        by auto
                    qed
                  }
                  moreover 
                  {
                    assume rc: "A' \<inter> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l) \<noteq> {}"
                    then obtain a' where a'_A': "a' \<in> A'" and a'_aug: "a' \<in> dom (augment_rels (dom \<S>\<^sub>l) R \<R>\<^sub>l)"
                      by auto
                    have False
                    proof (cases "a' \<in> R")
                      case False 
                      with a'_aug a'_A' \<R>\<^sub>l_A' show False
                        by (auto simp add: augment_rels_def domIff)
                    next
                      case True
                      with R_owns have a'_owns\<^sub>l: "a' \<in> \<O>\<^sub>l"
                        by auto
                      with \<O>\<^sub>l_A' a'_A' show False
                        by auto
                    qed
                  }
                  ultimately show False
                  using race ts_j cond
                    by (auto simp add: races_def ins eqs u_m_eq)
                next
                next
                  case Nil
                  then show ?thesis
                  using  ts_i ts\<^sub>l_j race "is" j_bound i_bound u_ts_i u_ts_j leq_u_ts neq_j_i ts_j
                    by (auto simp add:eqs races_def split: if_split_asm)
                qed
              }
              hence "\<not> safe_delayed (u_ts, u_m, u_shared)"
                apply (clarsimp simp add: safe_delayed_def)
                apply (rule_tac x=i in exI)
                using u_ts_i ts_i i_bound_u
                apply auto
                done
              moreover
              from safe_delayed_c_undo' [rule_format, of n] c_undo_n
              have "safe_delayed (u_ts, u_m, u_shared)"
                by simp
              ultimately have False
                by simp
              thus ?thesis 
                by simp
            qed
          qed
        next
          case (StoreBuffer _ p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
          hence False 
            by (auto simp add: empty_storebuffer_step_def)
          thus ?thesis ..
        qed
      qed
      } (* FIXME indentation *)
      ultimately show ?thesis
      using last_action_of_thread [where i=j, OF trace]
         by blast
   qed
 qed(* FIXME indentation *)

datatype 'p memref = 
   Write\<^sub>s\<^sub>b bool addr sop val acq lcl rel wrt
 | Read\<^sub>s\<^sub>b bool addr tmp val 
 | Prog\<^sub>s\<^sub>b 'p 'p "instrs"
 | Ghost\<^sub>s\<^sub>b acq lcl rel wrt

type_synonym 'p store_buffer = "'p memref list"
inductive flush_step:: "memory \<times> 'p store_buffer \<times> owns \<times> rels \<times> shared \<Rightarrow> memory \<times> 'p store_buffer \<times> owns \<times> rels \<times> shared \<Rightarrow> bool" 
  ("_ \<rightarrow>\<^sub>f _" [60,60] 100)
where
  Write\<^sub>s\<^sub>b: "\<lbrakk>\<O>' = (if volatile then \<O> \<union> A - R else \<O>);
           \<S>' = (if volatile then \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L else \<S>);
          \<R>'=(if volatile then Map.empty else \<R>)\<rbrakk>
          \<Longrightarrow>
          (m, Write\<^sub>s\<^sub>b volatile a sop v A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m(a := v), rs,\<O>',\<R>',\<S>')"
| Read\<^sub>s\<^sub>b: "(m, Read\<^sub>s\<^sub>b volatile a t v#rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m, rs,\<O>,\<R>, \<S>)"
| Prog\<^sub>s\<^sub>b: "(m, Prog\<^sub>s\<^sub>b p p' is#rs,\<O>,\<R>, \<S>) \<rightarrow>\<^sub>f (m, rs,\<O>,\<R>, \<S>)"
| Ghost: "(m, Ghost\<^sub>s\<^sub>b A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m, rs,\<O> \<union> A - R, augment_rels (dom \<S>) R \<R>, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L )"

abbreviation flush_steps::"memory \<times> 'p store_buffer \<times> owns \<times> rels \<times> shared \<Rightarrow> memory \<times> 'p store_buffer \<times> owns \<times> rels \<times> shared\<Rightarrow> bool" 
  ("_ \<rightarrow>\<^sub>f\<^sup>* _" [60,60] 100)
where
"flush_steps == flush_step^**"

term "x \<rightarrow>\<^sub>f\<^sup>* Y"

lemmas flush_step_induct =  
  flush_step.induct [split_format (complete),
  consumes 1, case_names Write\<^sub>s\<^sub>b Read\<^sub>s\<^sub>b Prog\<^sub>s\<^sub>b Ghost]

inductive store_buffer_step:: "memory \<times> 'p store_buffer \<times> 'owns \<times> 'rels \<times> 'shared \<Rightarrow> memory \<times> 'p memref list \<times> 'owns \<times> 'rels \<times> 'shared \<Rightarrow> bool" 
  ("_ \<rightarrow>\<^sub>w _" [60,60] 100)
where
  SBWrite\<^sub>s\<^sub>b: "
          (m, Write\<^sub>s\<^sub>b volatile a sop v A L R W# rs,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>w (m(a := v), rs,\<O>,\<R>,\<S>)"

abbreviation store_buffer_steps::"memory \<times> 'p store_buffer \<times> 'owns \<times> 'rels \<times> 'shared \<Rightarrow> memory \<times> 'p store_buffer \<times> 'owns \<times> 'rels \<times> 'shared\<Rightarrow> bool" 
  ("_ \<rightarrow>w\<^sup>* _" [60,60] 100)
where
"store_buffer_steps == store_buffer_step^**"

term "x \<rightarrow>w\<^sup>* Y"

fun buffered_val :: "'p memref list \<Rightarrow> addr \<Rightarrow> val option"
where
  "buffered_val [] a = None"
| "buffered_val (r # rs) a' = 
   (case r of
      Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _ \<Rightarrow> (case buffered_val rs a' of 
                               None \<Rightarrow> (if a'=a then Some v else None)
                             | Some v' \<Rightarrow> Some v')
     | _ \<Rightarrow> buffered_val rs a')"

definition address_of :: "'p memref \<Rightarrow> addr set"
where
"address_of r = (case r of Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _ \<Rightarrow> {a} | Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> {a} |
                  _ \<Rightarrow> {})"

lemma address_of_simps [simp]: 
"address_of (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = {a}"
"address_of (Read\<^sub>s\<^sub>b volatile a t v) = {a}"
"address_of (Prog\<^sub>s\<^sub>b p p' is) = {}"
"address_of (Ghost\<^sub>s\<^sub>b A L R W) = {}"
  by (auto simp add: address_of_def)

definition is_volatile :: "'p memref \<Rightarrow> bool"
where
"is_volatile r = (case r of Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _\<Rightarrow> volatile | Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> volatile
 | _ \<Rightarrow> False)"

lemma is_volatile_simps [simp]: 
"is_volatile (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = volatile"
"is_volatile (Read\<^sub>s\<^sub>b volatile a t v) = volatile"
"is_volatile (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_volatile (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_volatile_def)

definition is_Write\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_Write\<^sub>s\<^sub>b r = (case r of Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _\<Rightarrow> True | _ \<Rightarrow> False)"

definition is_Read\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_Read\<^sub>s\<^sub>b r = (case r of Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_Prog\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_Prog\<^sub>s\<^sub>b r = (case r of Prog\<^sub>s\<^sub>b _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_Ghost\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_Ghost\<^sub>s\<^sub>b r = (case r of Ghost\<^sub>s\<^sub>b _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

lemma is_Write\<^sub>s\<^sub>b_simps [simp]: 
"is_Write\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = True"
"is_Write\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = False"
"is_Write\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_Write\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_Write\<^sub>s\<^sub>b_def)

lemma is_Read\<^sub>s\<^sub>b_simps [simp]: 
"is_Read\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = True"
"is_Read\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = False"
"is_Read\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_Read\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_Read\<^sub>s\<^sub>b_def)

lemma is_Prog\<^sub>s\<^sub>b_simps [simp]: 
"is_Prog\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = False"
"is_Prog\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = False"
"is_Prog\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = True"
"is_Prog\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_Prog\<^sub>s\<^sub>b_def)

lemma is_Ghost\<^sub>s\<^sub>b_simps [simp]: 
"is_Ghost\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = False"
"is_Ghost\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = False"
"is_Ghost\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_Ghost\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = True"
  by (auto simp add: is_Ghost\<^sub>s\<^sub>b_def)

definition is_volatile_Write\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_volatile_Write\<^sub>s\<^sub>b r = (case r of Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _\<Rightarrow> volatile | _ \<Rightarrow> False)"

lemma is_volatile_Write\<^sub>s\<^sub>b_simps [simp]: 
"is_volatile_Write\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = volatile"
"is_volatile_Write\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = False"
"is_volatile_Write\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_volatile_Write\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_volatile_Write\<^sub>s\<^sub>b_def)

lemma is_volatile_Write\<^sub>s\<^sub>b_address_of [simp]: "is_volatile_Write\<^sub>s\<^sub>b x \<Longrightarrow> address_of x \<noteq> {}"
  by (cases x) auto

definition is_volatile_Read\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_volatile_Read\<^sub>s\<^sub>b r = (case r of Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> volatile | _ \<Rightarrow> False)"

lemma is_volatile_Read\<^sub>s\<^sub>b_simps [simp]: 
"is_volatile_Read\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = volatile"
"is_volatile_Read\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = False"
"is_volatile_Read\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_volatile_Read\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_volatile_Read\<^sub>s\<^sub>b_def)

definition is_non_volatile_Write\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_non_volatile_Write\<^sub>s\<^sub>b r = (case r of Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _\<Rightarrow> \<not> volatile | _ \<Rightarrow> False)"

lemma is_non_volatile_Write\<^sub>s\<^sub>b_simps [simp]: 
"is_non_volatile_Write\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = (\<not> volatile)"
"is_non_volatile_Write\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = False"
"is_non_volatile_Write\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_non_volatile_Write\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_non_volatile_Write\<^sub>s\<^sub>b_def)

definition is_non_volatile_Read\<^sub>s\<^sub>b:: "'p memref \<Rightarrow> bool"
where
"is_non_volatile_Read\<^sub>s\<^sub>b r = (case r of Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> \<not> volatile | _ \<Rightarrow> False)"

lemma is_non_volatile_Read\<^sub>s\<^sub>b_simps [simp]: 
"is_non_volatile_Read\<^sub>s\<^sub>b (Read\<^sub>s\<^sub>b volatile a t v) = (\<not> volatile)"
"is_non_volatile_Read\<^sub>s\<^sub>b (Write\<^sub>s\<^sub>b volatile a sop v A L R W) = False"
"is_non_volatile_Read\<^sub>s\<^sub>b (Prog\<^sub>s\<^sub>b p p' is) = False"
"is_non_volatile_Read\<^sub>s\<^sub>b (Ghost\<^sub>s\<^sub>b A L R W) = False"
  by (auto simp add: is_non_volatile_Read\<^sub>s\<^sub>b_def)

lemma is_volatile_split: "is_volatile r = 
  (is_volatile_Read\<^sub>s\<^sub>b r \<or> is_volatile_Write\<^sub>s\<^sub>b r)"
  by (cases r) auto

lemma is_non_volatile_split: 
  "\<not> is_volatile r = (is_non_volatile_Read\<^sub>s\<^sub>b r \<or> is_non_volatile_Write\<^sub>s\<^sub>b r \<or> is_Prog\<^sub>s\<^sub>b r \<or> is_Ghost\<^sub>s\<^sub>b r)"
  by (cases r) auto

fun outstanding_refs:: "('p memref \<Rightarrow> bool) \<Rightarrow> 'p memref list \<Rightarrow> addr set"
where
  "outstanding_refs P [] = {}"
| "outstanding_refs P (r#rs) = (if P r then (address_of r) \<union> (outstanding_refs P rs)
                                else outstanding_refs P rs)"

lemma outstanding_refs_conv: "outstanding_refs P sb = \<Union>(address_of ` {r. r \<in> set sb \<and> P r})"
  by (induct sb) auto

lemma outstanding_refs_append: 
  "\<And>ys. outstanding_refs vol (xs@ys) = outstanding_refs vol xs \<union> outstanding_refs vol ys"
  by (auto simp add: outstanding_refs_conv)

(*
lemma outstanding_refs_empty_conv:
"(outstanding_refs P sb = {}) = (\<forall>r \<in> set sb. \<not> (P r))"
  by (auto simp add: outstanding_refs_conv)
*)

lemma outstanding_refs_empty_negate: "(outstanding_refs P sb = {}) \<Longrightarrow> 
       (outstanding_refs (Not \<circ> P) sb = \<Union>(address_of ` set sb))"
  by (auto simp add: outstanding_refs_conv)

lemma outstanding_refs_mono_pred:
  "\<And>sb sb'. 
     \<forall>r. P r \<longrightarrow> P' r \<Longrightarrow> outstanding_refs P sb \<subseteq> outstanding_refs P' sb"
  by (auto simp add: outstanding_refs_conv)

lemma outstanding_refs_mono_set:
  "\<And>sb sb'. 
     set sb \<subseteq> set sb' \<Longrightarrow> outstanding_refs P sb \<subseteq> outstanding_refs P sb'"
  by (auto simp add: outstanding_refs_conv)

lemma outstanding_refs_takeWhile:
"outstanding_refs P (takeWhile P' sb) \<subseteq> outstanding_refs P sb"
apply (rule outstanding_refs_mono_set)
apply (auto dest: set_takeWhileD)
done

lemma outstanding_refs_subsets:
  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
  "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb"

  "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Read\<^sub>s\<^sub>b sb"
  "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Read\<^sub>s\<^sub>b sb"

  "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile) sb"
  "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile) sb"

  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (is_volatile) sb"
  "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (is_volatile) sb"

  "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  "outstanding_refs is_Read\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
by (auto intro!:outstanding_refs_mono_pred simp add: is_volatile_Write\<^sub>s\<^sub>b_def is_non_volatile_Write\<^sub>s\<^sub>b_def 
  is_volatile_Read\<^sub>s\<^sub>b_def is_non_volatile_Read\<^sub>s\<^sub>b_def is_Read\<^sub>s\<^sub>b_def split: memref.splits)


lemma outstanding_non_volatile_refs_conv: 
  "outstanding_refs (Not \<circ> is_volatile) sb =
   outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<union> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
apply (induct sb) 
apply simp
  subgoal for a sb
    by (case_tac a, auto)
done


lemma outstanding_volatile_refs_conv: 
  "outstanding_refs is_volatile sb =
   outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<union> outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb"
apply (induct sb) 
apply simp
  subgoal for a sb
    by (case_tac a, auto)
done

lemma outstanding_is_Write\<^sub>s\<^sub>b_refs_conv: 
  "outstanding_refs is_Write\<^sub>s\<^sub>b sb =
   outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<union> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb"
apply (induct sb) 
apply simp
  subgoal for a sb
    by (case_tac a, auto)
done

lemma outstanding_is_Read\<^sub>s\<^sub>b_refs_conv: 
  "outstanding_refs is_Read\<^sub>s\<^sub>b sb =
   outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<union> outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb"
apply (induct sb) 
apply simp
  subgoal for a sb
    by (case_tac a, auto)
done

lemma outstanding_not_volatile_Read\<^sub>s\<^sub>b_refs_conv: "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) sb =
       outstanding_refs is_Write\<^sub>s\<^sub>b sb \<union> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
apply (induct sb)
apply (clarsimp)
  subgoal for a sb
    by (case_tac a, auto)
done


lemmas misc_outstanding_refs_convs = outstanding_non_volatile_refs_conv outstanding_volatile_refs_conv
outstanding_is_Write\<^sub>s\<^sub>b_refs_conv outstanding_is_Read\<^sub>s\<^sub>b_refs_conv outstanding_not_volatile_Read\<^sub>s\<^sub>b_refs_conv

lemma no_outstanding_vol_write_takeWhile_append: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> 
  takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@xs) = sb@(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs)"
apply (induct sb)
apply (auto split: if_split_asm)
done

lemma outstanding_vol_write_takeWhile_append: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {} \<Longrightarrow> 
  takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@xs) = (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply (auto split: if_split_asm)
done


lemma no_outstanding_vol_write_dropWhile_append: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> 
  dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@xs) = (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs)"
apply (induct sb)
apply (auto split: if_split_asm)
done

lemma outstanding_vol_write_dropWhile_append: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {} \<Longrightarrow> 
  dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@xs) = (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)@xs"
apply (induct sb)
apply (auto split: if_split_asm)
done

lemmas outstanding_vol_write_take_drop_appends =
no_outstanding_vol_write_takeWhile_append
outstanding_vol_write_takeWhile_append
no_outstanding_vol_write_dropWhile_append
outstanding_vol_write_dropWhile_append

lemma outstanding_refs_is_non_volatile_Write\<^sub>s\<^sub>b_takeWhile_conv:
  "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) =
       outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply  clarsimp
  subgoal for a sb
    by (case_tac a, auto)
done


lemma dropWhile_not_vol_write_empty:
  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = []"
apply (induct sb)
apply (auto split: if_split_asm)
done

lemma takeWhile_not_vol_write_outstanding_refs:
  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = {}"
apply (induct sb)
apply (auto split: if_split_asm)
done

lemma no_volatile_Write\<^sub>s\<^sub>bs_conv: "(outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}) = 
       (\<forall>r \<in> set sb. (\<forall>v' sop' a' A L R W. r \<noteq> Write\<^sub>s\<^sub>b True a' sop' v' A L R W))"
  by (force simp add: outstanding_refs_conv is_volatile_Write\<^sub>s\<^sub>b_def split: memref.splits)

lemma no_volatile_Read\<^sub>s\<^sub>bs_conv: "(outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}) = 
       (\<forall>r \<in> set sb. (\<forall>v' t' a'. r \<noteq> Read\<^sub>s\<^sub>b True a' t' v'))"
  by (force simp add: outstanding_refs_conv is_volatile_Read\<^sub>s\<^sub>b_def split: memref.splits)



inductive sb_memop_step :: "(instrs \<times> tmps \<times> 'p store_buffer \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared ) \<Rightarrow> 
                  (instrs \<times> tmps \<times> 'p store_buffer \<times> memory \<times> 'dirty \<times> 'owns \<times> 'rels \<times> 'shared ) \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sub>s\<^sub>b _" [60,60] 100)
where
  SBReadBuffered: 
  "\<lbrakk>buffered_val sb a = Some v\<rbrakk>
   \<Longrightarrow>
   (Read volatile a t # is,\<theta>, sb, m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
          (is, \<theta> (t\<mapsto>v), sb, m,\<D>, \<O>,\<R>, \<S>)"

| SBReadUnbuffered: 
  "\<lbrakk>buffered_val sb a = None\<rbrakk> 
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
          (is, \<theta> (t\<mapsto>m a), sb, m,\<D>, \<O>, \<R>, \<S>)"

| SBWriteNonVolatile:
  "(Write False a (D,f) A L R W#is, \<theta>, sb, m,\<D>,\<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
          (is, \<theta>, sb@ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W], m,\<D>, \<O>, \<R>, \<S>)"

| SBWriteVolatile:
   
   "(Write True a (D,f) A L R W# is, \<theta>, sb, m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
         (is, \<theta>, sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W], m,\<D>, \<O>, \<R>, \<S>)"

| SBFence:
  "(Fence # is, \<theta>, [], m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b (is, \<theta>, [], m,\<D>, \<O>, \<R>, \<S>)"

| SBRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b (is, \<theta>(t\<mapsto>m a),[], m,\<D>, \<O>, \<R>, \<S>)"

| SBRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
         (is, \<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a)))),[], m(a:= f(\<theta>(t\<mapsto>m a))),\<D>, \<O>, \<R>, \<S>)"

| SBGhost:
  "(Ghost A  L R W# is, \<theta>, sb, m,\<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b
         (is, \<theta>, sb, m,\<D>, \<O>, \<R>, \<S>)"


inductive sbh_memop_step :: "
                  (instrs \<times> tmps \<times> 'p store_buffer \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared ) \<Rightarrow>
                  (instrs \<times> tmps \<times> 'p store_buffer \<times> memory \<times> bool \<times> owns \<times> rels \<times> shared ) \<Rightarrow> bool" 
                    ("_ \<rightarrow>\<^sub>s\<^sub>b\<^sub>h _" [60,60] 100)
where
  SBHReadBuffered: 
  "\<lbrakk>buffered_val sb a = Some v\<rbrakk>
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta> (t\<mapsto>v), sb@[Read\<^sub>s\<^sub>b volatile a t v], m, \<D>, \<O>, \<R>, \<S>)"

| SBHReadUnbuffered: 
  "\<lbrakk>buffered_val sb a = None\<rbrakk> 
   \<Longrightarrow>
   (Read volatile a t # is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta> (t\<mapsto>m a), sb@[Read\<^sub>s\<^sub>b volatile a t (m a)], m, \<D>, \<O>, \<R>, \<S>)"

| SBHWriteNonVolatile:
  "(Write False a (D,f) A L R W#is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
          (is, \<theta>, sb@ [Write\<^sub>s\<^sub>b False a (D,f) (f \<theta>) A L R W], m, \<D>, \<O>, \<R>, \<S>)"

| SBHWriteVolatile:
  "(Write True a (D,f) A L R W# is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is, \<theta>, sb@[Write\<^sub>s\<^sub>b True a (D,f) (f \<theta>) A L R W], m, True, \<O>, \<R>, \<S>)"

| SBHFence:
  "(Fence # is, \<theta>, [], m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is, \<theta>, [], m, False, \<O>, Map.empty, \<S>)"

| SBHRMWReadOnly:
  "\<lbrakk>\<not> cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is, \<theta>(t\<mapsto>m a),[], m, False, \<O>, Map.empty, \<S>)"

| SBHRMWWrite:
  "\<lbrakk>cond (\<theta>(t\<mapsto>m a))\<rbrakk> \<Longrightarrow> 
   (RMW a t (D,f) cond ret A L R W# is, \<theta>, [], m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is, \<theta>(t\<mapsto>ret (m a) (f(\<theta>(t\<mapsto>m a)))),[], m(a:= f(\<theta>(t\<mapsto>m a))), False, \<O> \<union> A - R,Map.empty, \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"

| SBHGhost:
  "(Ghost A L R W# is, \<theta>, sb, m, \<D>, \<O>, \<R>, \<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h
         (is, \<theta>, sb@[Ghost\<^sub>s\<^sub>b A L R W], m, \<D>, \<O>, \<R>, \<S>)"


interpretation direct:  memory_system direct_memop_step id_storebuffer_step .
interpretation sb: memory_system sb_memop_step store_buffer_step .
interpretation sbh: memory_system sbh_memop_step flush_step .

primrec non_volatile_owned_or_read_only:: "bool \<Rightarrow> shared \<Rightarrow> owns \<Rightarrow> 'a memref list \<Rightarrow> bool"
where
"non_volatile_owned_or_read_only pending_write \<S> \<O> [] = True"
| "non_volatile_owned_or_read_only pending_write \<S> \<O> (x#xs) =
  (case x of
    Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> 
     (\<not>volatile \<longrightarrow> pending_write \<longrightarrow> (a \<in> \<O> \<or> a \<in> read_only \<S>)) \<and> 
      non_volatile_owned_or_read_only pending_write \<S> \<O> xs
  | Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> 
     (if volatile then non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) xs
      else a \<in> \<O> \<and> non_volatile_owned_or_read_only pending_write \<S> \<O> xs)
  | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> non_volatile_owned_or_read_only pending_write (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) xs
  | _ \<Rightarrow> non_volatile_owned_or_read_only pending_write \<S> \<O> xs)"

primrec acquired :: "bool \<Rightarrow> 'a memref list \<Rightarrow> addr set \<Rightarrow> addr set"
where
"acquired pending_write [] A = (if pending_write then A else {})"
| "acquired pending_write (x#xs) A =
  (case x of
     Write\<^sub>s\<^sub>b volatile _ _ _ A' L R W\<Rightarrow> 
        (if volatile then acquired True xs (if pending_write then (A \<union> A' - R) else (A' - R)) 
         else acquired pending_write xs A)
   | Ghost\<^sub>s\<^sub>b A' L R W \<Rightarrow> acquired pending_write xs (if pending_write then (A \<union> A' - R) else A) 
   | _ \<Rightarrow> acquired pending_write xs A)"

primrec share :: "'a memref list \<Rightarrow> shared \<Rightarrow> shared"
where
"share [] S = S"
| "share (x#xs) S =
  (case x of
     Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> (if volatile then (share xs (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) else share xs S)
   | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> share xs (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)
   | _ \<Rightarrow> share xs S)"

primrec acquired_reads :: "bool \<Rightarrow> 'a memref list \<Rightarrow> addr set \<Rightarrow> addr set"
where
"acquired_reads pending_write [] A = {}"
| "acquired_reads pending_write (x#xs) A =
  (case x of
     Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> (if pending_write \<and> \<not> volatile \<and> a \<in> A 
                             then insert a (acquired_reads pending_write xs A)
                             else acquired_reads pending_write xs A)
   | Write\<^sub>s\<^sub>b volatile _ _ _ A' L R W \<Rightarrow> 
         (if volatile then acquired_reads True xs (if pending_write then (A \<union> A' - R) else (A' - R)) 
          else acquired_reads pending_write xs A)
   | Ghost\<^sub>s\<^sub>b A' L R W \<Rightarrow> acquired_reads pending_write xs (A \<union> A' - R)
   | _ \<Rightarrow> acquired_reads pending_write xs A)"

lemma union_mono_aux: "A \<subseteq> B \<Longrightarrow> A \<union> C \<subseteq> B \<union> C"
  by blast

lemma set_minus_mono_aux: "A \<subseteq> B \<Longrightarrow> A - C \<subseteq> B - C"
  by blast

lemma acquired_mono: "\<And>A B pending_write. A \<subseteq> B \<Longrightarrow> acquired pending_write xs A \<subseteq> acquired pending_write xs B"
apply (induct xs)
apply  simp
subgoal for a xs A B pending_write
apply (case_tac a ) 
apply    clarsimp 
         subgoal for volatile a1 D f v A' L R W x
           apply (drule_tac C=A' in union_mono_aux)
           apply (drule_tac C="R" in set_minus_mono_aux)
           apply blast
           done 
apply   clarsimp
apply  clarsimp
apply clarsimp
subgoal for A' L R W x
  apply (drule_tac C=A' in union_mono_aux)
  apply (drule_tac C="R" in set_minus_mono_aux)
  apply blast
  done
done
done


lemma acquired_mono_in: 
  assumes x_in: "x \<in> acquired pending_write xs A" 
  assumes sub: "A \<subseteq> B" 
  shows "x \<in> acquired pending_write xs B"
using acquired_mono [OF sub, of pending_write xs] x_in
by blast

lemma acquired_no_pending_write:"\<And>A B. acquired False xs A = acquired False xs B"
  by (induct xs) (auto split: memref.splits)

lemma acquired_no_pending_write_in:
  "x \<in> acquired False xs A \<Longrightarrow> x \<in> acquired False xs B"
  apply (subst acquired_no_pending_write)
  apply auto
  done

lemma acquired_pending_write_mono_in: "\<And>A B. x \<in> acquired False xs A \<Longrightarrow> x \<in> acquired True xs B"
apply (induct xs)
apply (auto split: memref.splits if_split_asm intro: acquired_mono_in)
done

lemma acquired_pending_write_mono: "acquired False xs A \<subseteq> acquired True xs B"
  by (auto intro: acquired_pending_write_mono_in)

lemma acquired_append: "\<And>A pending_write. acquired pending_write (xs@ys) A = 
 acquired (pending_write \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<noteq> {}) ys (acquired pending_write xs A)"
  apply (induct xs)
  apply (auto split: memref.splits intro: acquired_no_pending_write_in)
  done

lemma acquired_take_drop: 
  "acquired (pending_write \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (takeWhile P xs) \<noteq> {}) 
      (dropWhile P xs) (acquired pending_write (takeWhile P xs) A) = 
   acquired pending_write xs A"
proof -
  have "acquired pending_write xs A = acquired pending_write ((takeWhile P xs)@(dropWhile P xs)) A"
    by simp
  also
  from acquired_append [where xs="(takeWhile P xs)" and ys="(dropWhile P xs)"]
  have "\<dots> = acquired (pending_write \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (takeWhile P xs) \<noteq> {}) 
      (dropWhile P xs) (acquired pending_write (takeWhile P xs) A)"
    by simp
  finally show ?thesis
    by simp
qed

lemma share_mono: "\<And>A B. dom A \<subseteq> dom B \<Longrightarrow> dom (share xs A) \<subseteq> dom (share xs B)"
apply (induct xs)
apply  simp
subgoal for a xs A B
apply (case_tac a)
apply    (clarsimp iff del: domIff)
         subgoal for volatile a1 D f v A' L R W x
         apply (drule_tac C="R" and x="W" in augment_mono_aux)
         apply (drule_tac C="L" in restrict_mono_aux)
         apply blast
         done
apply   clarsimp
apply  clarsimp
apply (clarsimp iff del: domIff)
subgoal for A' L R W x
apply (drule_tac C="R" and x="W" in augment_mono_aux)
apply (drule_tac C="L" in restrict_mono_aux)
apply blast
done
done
done

lemma share_mono_in: 
  assumes x_in: "x \<in> dom (share xs A)" 
  assumes sub: "dom A \<subseteq> dom B" 
  shows "x \<in> dom (share xs B)"
using share_mono [OF sub, of xs] x_in
by blast

lemma acquired_reads_mono: 
  "\<And>A B pending_write. A \<subseteq> B \<Longrightarrow> acquired_reads pending_write xs A \<subseteq> acquired_reads pending_write xs B"
apply (induct xs)
apply  simp
subgoal for a xs A B pending_write
apply (case_tac a)
apply    clarsimp
         subgoal for volatile a1 D f v A' L R W x
         apply (drule_tac C="A'" in union_mono_aux)
         apply (drule_tac C="R" in set_minus_mono_aux)
         apply blast
         done 
apply   clarsimp
apply   blast
apply  clarsimp
apply clarsimp
subgoal for A' L R W x
apply (drule_tac C="A'" in union_mono_aux)
apply (drule_tac C="R" in set_minus_mono_aux)
apply blast
done
done
done

lemma acquired_reads_mono_in:
  assumes x_in: "x \<in> acquired_reads pending_write xs A" 
  assumes sub: "A \<subseteq> B" 
  shows "x \<in> acquired_reads pending_write xs B"
using acquired_reads_mono [OF sub, of pending_write xs] x_in
by blast

lemma acquired_reads_no_pending_write: "\<And>A B. acquired_reads False xs A = acquired_reads False xs B"
  by (induct xs) (auto split: memref.splits)

lemma acquired_reads_no_pending_write_in:
"x \<in> acquired_reads False xs A \<Longrightarrow> x \<in> acquired_reads False xs B"
  apply (subst acquired_reads_no_pending_write)
  apply blast
  done

lemma acquired_reads_pending_write_mono:
  "\<And>A. acquired_reads False xs A \<subseteq> acquired_reads True xs A"
  by (induct xs) (auto split: memref.splits intro: acquired_reads_mono_in )

lemma acquired_reads_pending_write_mono_in: 
  assumes x_in: "x \<in> acquired_reads False xs A" 
  shows "x \<in> acquired_reads True xs A"
using acquired_reads_pending_write_mono [of xs A] x_in
by blast

lemma acquired_reads_append: "\<And>pending_write A. acquired_reads pending_write (xs@ys) A = 
  acquired_reads pending_write xs A \<union> 
  acquired_reads (pending_write \<or> (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<noteq> {})) ys 
   (acquired pending_write xs A)"
proof (induct xs)
  case Nil thus ?case by (auto dest: acquired_reads_no_pending_write_in)
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      show ?thesis
	using Cons.hyps
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    next
      case True
      show ?thesis
	using Cons.hyps
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    show ?thesis
    proof (cases volatile)
      case False
      show ?thesis
	using Cons.hyps
	by (auto simp add: Read\<^sub>s\<^sub>b False)
    next
      case True
      show ?thesis
	using Cons.hyps
	by (auto simp add: Read\<^sub>s\<^sub>b True)
    qed
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A' L R W)
    have "(acquired False xs (A \<union> A' -R )) = (acquired False xs A)"
      by (simp add: acquired_no_pending_write)
    with Cons.hyps show ?thesis by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma in_acquired_reads_no_pending_write_outstanding_write: 
"\<And>A. a \<in> acquired_reads False xs A \<Longrightarrow> outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) xs \<noteq> {}"
  apply (induct xs)
  apply simp
  apply (auto split: memref.splits)
  apply auto 
  done

lemma augment_read_only_mono: "read_only \<S> \<subseteq> read_only \<S>' \<Longrightarrow> 
  read_only (\<S> \<oplus>\<^bsub>W\<^esub> R) \<subseteq> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R)"
  by (auto simp add: augment_shared_def read_only_def)

lemma restrict_read_only_mono: "read_only \<S> \<subseteq> read_only \<S>' \<Longrightarrow> 
  read_only (\<S> \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (\<S>' \<ominus>\<^bsub>A\<^esub> L)"
  apply (clarsimp simp add: restrict_shared_def read_only_def split: option.splits if_split_asm)
  apply (rule conjI)
  apply  blast
  apply fastforce
  done


lemma share_read_only_mono: "\<And>\<S> \<S>'. read_only \<S> \<subseteq> read_only \<S>' \<Longrightarrow>
        read_only (share sb \<S>) \<subseteq> read_only (share sb \<S>')"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      note \<open>read_only \<S> \<subseteq> read_only \<S>'\<close>
      from augment_read_only_mono [OF this]
      have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R) \<subseteq> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R)".
      from restrict_read_only_mono [OF this, of A L]
      have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
      from Cons.hyps [OF this]
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    note \<open>read_only \<S> \<subseteq> read_only \<S>'\<close>
    from augment_read_only_mono [OF this]
    have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R) \<subseteq> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R)".
    from restrict_read_only_mono [OF this, of A L]
    have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
   from Cons.hyps [OF this]
   show ?thesis
     by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


(*
lemma read_only_share_takeWhile:
  "\<And>\<S>. read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)
       \<subseteq> read_only \<S>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case Write\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto)
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    note Cons.hyps [of "\<S> \<ominus>\<^bsub>A\<^esub> L"] 
    moreover
    have "read_only (\<S> \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only \<S>"
      by (auto simp add: in_read_only_restrict_conv)
    ultimately
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma read_only_share_takeWhile_in:
"a \<in> read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) \<Longrightarrow> a \<in>  read_only \<S>"
using read_only_share_takeWhile
by blast
*)
lemma non_volatile_owned_or_read_only_append: 
"\<And>\<O> \<S> pending_write. non_volatile_owned_or_read_only pending_write \<S> \<O> (xs@ys)
         = (non_volatile_owned_or_read_only pending_write \<S> \<O> xs \<and> 
            non_volatile_owned_or_read_only (pending_write \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<noteq> {}) 
             (share xs \<S>) (acquired True xs \<O>) ys)"
apply (induct xs)
apply (auto split: memref.splits)
done

lemma non_volatile_owned_or_read_only_mono:
"\<And>\<O> \<O>' \<S> pending_write. \<O> \<subseteq> \<O>' \<Longrightarrow> non_volatile_owned_or_read_only pending_write \<S> \<O> xs 
  \<Longrightarrow> non_volatile_owned_or_read_only pending_write \<S> \<O>' xs"
  apply (induct xs)
  apply  simp
  subgoal for a xs \<O> \<O>' \<S> pending_write
  apply (case_tac a)
  apply    (clarsimp split: if_split_asm)
           subgoal for volatile a1 D f v A L R W
           apply (drule_tac C="A" in union_mono_aux)
           apply (drule_tac C="R" in set_minus_mono_aux)
           apply blast
           done
  apply    fastforce
  apply   fastforce
  apply  fastforce
  apply clarsimp
  subgoal for A L R W
  apply (drule_tac C="A" in union_mono_aux)
  apply (drule_tac C="R" in set_minus_mono_aux)
  apply blast
  done
  done
  done

lemma non_volatile_owned_or_read_only_shared_mono:
"\<And>\<S> \<S>' \<O> pending_write. \<S> \<subseteq>\<^sub>s \<S>' \<Longrightarrow> non_volatile_owned_or_read_only pending_write \<S> \<O> xs 
  \<Longrightarrow> non_volatile_owned_or_read_only pending_write \<S>' \<O> xs"
  apply (induct xs)
  apply  simp
  subgoal for a xs \<S> \<S>' \<O> pending_write
  apply (case_tac a)
  apply    (clarsimp split: if_split_asm) 
           subgoal for volatile a1 D f v A L R W
           apply (frule_tac C="R" and x="W" in augment_mono_map)
           apply (drule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and C="L" in restrict_mono_map)
           apply (fastforce dest: read_only_mono)
           done
  apply   (fastforce dest: read_only_mono shared_leD)
  apply  fastforce
  subgoal for A L R W
  apply (frule_tac C="R" and x="W" in augment_mono_map)
  apply (drule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and C="L" in restrict_mono_map)
  apply (fastforce dest: read_only_mono)
  done
  done
  done

lemma non_volatile_owned_or_read_only_pending_write_antimono:
"\<And>\<O> \<S>. non_volatile_owned_or_read_only True \<S> \<O> xs 
  \<Longrightarrow> non_volatile_owned_or_read_only False \<S> \<O> xs"
  by (induct xs) (auto split: memref.splits)

primrec all_acquired :: "'a memref list \<Rightarrow> addr set"
where 
  "all_acquired [] = {}"
|  "all_acquired (i#is) =
    (case i of
       Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> (if volatile then A \<union> all_acquired is else all_acquired is)
     | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> A \<union> all_acquired is
     | _ \<Rightarrow> all_acquired is)"

lemma all_acquired_append: "all_acquired (xs@ys) = all_acquired xs \<union> all_acquired ys"
  apply (induct xs)
  apply (auto split: memref.splits)
  done

lemma acquired_reads_all_acquired: "\<And>\<O> pending_write.
  acquired_reads pending_write sb \<O> \<subseteq> \<O> \<union> all_acquired sb"
apply (induct sb)
apply  clarsimp
apply (auto split: memref.splits)
done

(*
lemma acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b: 
  "\<And>A. (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) A) = 
         A \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
*)
lemma acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b: 
  "\<And>A. (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) A) \<subseteq> 
         A \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply  clarsimp 
subgoal for a sb A
apply (case_tac a)
apply auto
done
done

lemma acquired_False_takeWhile_non_volatile_Write\<^sub>s\<^sub>b:
  "acquired False (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) A = {}"
  apply (induct sb)
   apply simp
  subgoal for a sb
    by (case_tac a) auto
  done  

lemma outstanding_refs_takeWhile_opposite: "outstanding_refs P (takeWhile (Not \<circ> P) xs) = {}"   
apply (induct xs)
apply auto
done


lemma no_outstanding_volatile_Write\<^sub>s\<^sub>b_acquired:
  "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> acquired False sb A = {}"
  apply (induct sb)
   apply simp
  subgoal for a sb
    by (case_tac a) auto
  done

lemma acquired_all_acquired:"\<And>pending_write A. acquired pending_write xs A \<subseteq> A \<union> all_acquired xs"
  apply (induct xs)
  apply (auto split: memref.splits)
  done

lemma acquired_all_acquired_in: "x \<in> acquired pending_write xs A \<Longrightarrow> x \<in> A \<union> all_acquired xs"
  using acquired_all_acquired
  by blast



primrec sharing_consistent:: "shared \<Rightarrow> owns \<Rightarrow> 'a memref list \<Rightarrow>  bool"
where
"sharing_consistent \<S> \<O> [] = True"
| "sharing_consistent \<S> \<O> (r#rs) =
   (case r of
     Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> 
      (if volatile then A \<subseteq> dom \<S> \<union> \<O> \<and> L \<subseteq> A \<and> A \<inter> R = {} \<and> R \<subseteq> \<O> \<and> 
                       sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) rs
      else sharing_consistent \<S> \<O> rs)  
   | Ghost\<^sub>s\<^sub>b A L R W  \<Rightarrow> A \<subseteq> dom \<S> \<union> \<O> \<and> L \<subseteq> A \<and> A \<inter> R = {} \<and> R \<subseteq> \<O> \<and> 
        sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) rs
   | _ \<Rightarrow> sharing_consistent \<S> \<O> rs)"

lemma sharing_consistent_all_acquired:
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> all_acquired sb \<subseteq> dom \<S> \<union> \<O>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)       
    with Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems show ?thesis by auto
  qed
qed

lemma sharing_consistent_append:
"\<And>\<S> \<O>. sharing_consistent \<S> \<O> (xs@ys) =
     (sharing_consistent \<S> \<O> xs \<and> 
      sharing_consistent (share xs \<S>) (acquired True xs \<O>) ys)"
apply (induct xs)
apply (auto split: memref.splits)
done

primrec read_only_reads :: "owns \<Rightarrow> 'a memref list \<Rightarrow> addr set"
where
"read_only_reads \<O> [] = {}"
| "read_only_reads \<O> (x#xs) =
  (case x of
     Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> (if \<not> volatile \<and> a \<notin> \<O> 
                             then insert a (read_only_reads \<O> xs)
                             else read_only_reads \<O> xs)
   | Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> 
         (if volatile then read_only_reads (\<O> \<union> A - R) xs  
          else read_only_reads \<O> xs )
   | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> read_only_reads (\<O> \<union> A - R) xs 
   | _ \<Rightarrow> read_only_reads \<O> xs)"

lemma read_only_reads_append:
"\<And>\<O>. read_only_reads \<O> (xs@ys) = 
  read_only_reads \<O> xs \<union> read_only_reads (acquired True xs \<O>) ys"
  apply (induct xs)
   apply simp
  subgoal for a xs \<O>
    by (case_tac a) auto
  done

lemma read_only_reads_antimono:
  "\<And>\<O> \<O>'. 
  \<O> \<subseteq> \<O>' \<Longrightarrow> read_only_reads \<O>' sb \<subseteq> read_only_reads \<O> sb"
  apply (induct sb)
  apply  simp
  subgoal for a sb \<O> \<O>'
  apply (case_tac a)
  apply    (clarsimp split: if_split_asm)
           subgoal for volatile a1 D f v A L R W
           apply (drule_tac C="A" in union_mono_aux)
           apply (drule_tac C="R" in set_minus_mono_aux)
           apply blast
           done 
  apply   auto
  subgoal for A L R W x
  apply (drule_tac C="A" in union_mono_aux)
  apply (drule_tac C="R" in set_minus_mono_aux)
  apply blast
  done
  done
  done

primrec non_volatile_writes_unshared:: "shared \<Rightarrow> 'a memref list \<Rightarrow> bool"
where
"non_volatile_writes_unshared \<S> [] = True"
| "non_volatile_writes_unshared \<S> (x#xs) =
  (case x of
    Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> (if volatile then non_volatile_writes_unshared (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) xs
                                     else a \<notin> dom \<S> \<and> non_volatile_writes_unshared \<S> xs)
  | Ghost\<^sub>s\<^sub>b A L R W  \<Rightarrow> non_volatile_writes_unshared (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) xs
  | _ \<Rightarrow> non_volatile_writes_unshared \<S> xs)"


lemma non_volatile_writes_unshared_append: 
"\<And>\<S>. non_volatile_writes_unshared \<S> (xs@ys)
         = (non_volatile_writes_unshared \<S> xs \<and> non_volatile_writes_unshared (share xs \<S>) ys)"
apply (induct xs)
apply (auto split: memref.splits)
done

lemma non_volatile_writes_unshared_antimono:
"\<And>\<S> \<S>'. dom \<S> \<subseteq> dom \<S>' \<Longrightarrow> non_volatile_writes_unshared \<S>' xs 
  \<Longrightarrow> non_volatile_writes_unshared \<S> xs"
  apply (induct xs)
  apply  simp
  subgoal for a xs \<S> \<S>'
  apply (case_tac a)
  apply     (clarsimp split: if_split_asm)
            subgoal for volatile a1 D f v A L R W
            apply (drule_tac C="R" in augment_mono_aux)
            apply (drule_tac C="L" in restrict_mono_aux)
            apply blast
            done
  apply    fastforce
  apply   fastforce
  apply  fastforce
  apply (clarsimp split: if_split_asm)
  subgoal for A L R W
  apply (drule_tac C="R" in augment_mono_aux)
  apply (drule_tac C="L" in restrict_mono_aux)
  apply blast
  done
  done
  done 

primrec  no_write_to_read_only_memory:: "shared \<Rightarrow> 'a memref list \<Rightarrow> bool"
where
"no_write_to_read_only_memory \<S> [] = True"
| "no_write_to_read_only_memory \<S> (x#xs) =
  (case x of
    Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> a \<notin> read_only \<S> \<and>
                                      (if volatile then no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) xs
                                       else no_write_to_read_only_memory \<S> xs)
  | Ghost\<^sub>s\<^sub>b A L R W  \<Rightarrow> no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) xs
  | _ \<Rightarrow> no_write_to_read_only_memory \<S> xs)"

lemma no_write_to_read_only_memory_append: 
"\<And>\<S>. no_write_to_read_only_memory \<S> (xs@ys)
         = (no_write_to_read_only_memory \<S> xs \<and> no_write_to_read_only_memory (share xs \<S>) ys)"
apply (induct xs)
apply  simp
subgoal for a xs \<S>
  by (case_tac a) auto
done

lemma no_write_to_read_only_memory_antimono:
"\<And>\<S> \<S>'. \<S> \<subseteq>\<^sub>s \<S>' \<Longrightarrow> no_write_to_read_only_memory \<S>' xs 
  \<Longrightarrow> no_write_to_read_only_memory \<S> xs"
  apply (induct xs)
  apply  simp
  subgoal for a xs \<S> \<S>' 
  apply (case_tac a)
  apply    (clarsimp split: if_split_asm) 
             subgoal for volatile a1 D f v A L R W 
             apply (frule_tac C="R" and x="W" in augment_mono_map)
             apply (drule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and C="L" and x="A" in restrict_mono_map)
             apply (fastforce dest: read_only_mono shared_leD)
             done
  apply    (fastforce dest: read_only_mono shared_leD)
  apply   fastforce
  apply  fastforce
  apply (clarsimp)
  subgoal for A L R W
  apply (frule_tac C="R" and x="W" in augment_mono_map)
  apply (drule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and C="L" and x="A" in restrict_mono_map)
  apply (fastforce dest: read_only_mono shared_leD)
  done
  done
  done

locale outstanding_non_volatile_refs_owned_or_read_only =
fixes \<S>::shared
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes outstanding_non_volatile_refs_owned_or_read_only:
  "\<And>i is \<O> \<R> \<D> \<theta> sb p. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   non_volatile_owned_or_read_only False \<S> \<O> sb"

locale outstanding_volatile_writes_unowned_by_others =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes outstanding_volatile_writes_unowned_by_others: 
  "\<And>i p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j. 
   \<lbrakk>i < length ts; j < length ts; i\<noteq>j;
    ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i); ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)
   \<rbrakk>
   \<Longrightarrow>
    (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i = {}"


locale read_only_reads_unowned =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes read_only_reads_unowned: 
  "\<And>i p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j. 
   \<lbrakk>i < length ts; j < length ts; i\<noteq>j;
    ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i); ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)
   \<rbrakk>
   \<Longrightarrow>
    (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> 
     read_only_reads (acquired True 
                          (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) \<O>\<^sub>i) 
                          (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) = {}"

locale ownership_distinct =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes ownership_distinct:
   "\<And>i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j. 
      \<lbrakk>i < length ts; j < length ts; i \<noteq> j; 
    ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i); ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)
      \<rbrakk> \<Longrightarrow> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"


locale valid_ownership = 
  outstanding_non_volatile_refs_owned_or_read_only + 
  outstanding_volatile_writes_unowned_by_others + 
  read_only_reads_unowned +
  ownership_distinct

locale outstanding_non_volatile_writes_unshared =
fixes \<S>::shared and ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes outstanding_non_volatile_writes_unshared:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   non_volatile_writes_unshared \<S> sb"


locale sharing_consis =
fixes \<S>::shared and ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes sharing_consis:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   sharing_consistent \<S> \<O> sb"




locale no_outstanding_write_to_read_only_memory =
fixes \<S>::shared and ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes no_outstanding_write_to_read_only_memory:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   no_write_to_read_only_memory \<S> sb"


locale valid_sharing = 
  outstanding_non_volatile_writes_unshared +
  sharing_consis +
  read_only_unowned +
  unowned_shared +
  no_outstanding_write_to_read_only_memory

locale valid_ownership_and_sharing = valid_ownership +
  outstanding_non_volatile_writes_unshared +
  sharing_consis +
  no_outstanding_write_to_read_only_memory


lemma (in read_only_reads_unowned)
  read_only_reads_unowned_nth_update:
 "\<And>i p is \<O> \<R> \<D>  \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); 
     read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<O>') 
       (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<subseteq> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
       (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb);
     \<O>' \<union> all_acquired sb' \<subseteq> \<O> \<union> all_acquired sb\<rbrakk> \<Longrightarrow> 
     read_only_reads_unowned (ts[i := (p',is',\<theta>',sb',\<D>',\<O>',\<R>')])"
  apply (unfold_locales)
  apply (clarsimp simp add: nth_list_update split: if_split_asm)
  apply   (fastforce dest: read_only_reads_unowned)+
  done

 
lemma outstanding_non_volatile_refs_owned_or_read_only_tl: 
  "outstanding_non_volatile_refs_owned_or_read_only \<S> (t#ts) \<Longrightarrow> outstanding_non_volatile_refs_owned_or_read_only \<S> ts"
  by (force simp add: outstanding_non_volatile_refs_owned_or_read_only_def)

lemma outstanding_volatile_writes_unowned_by_others_tl: 
  "outstanding_volatile_writes_unowned_by_others (t#ts) \<Longrightarrow> outstanding_volatile_writes_unowned_by_others ts"
  apply (clarsimp simp add: outstanding_volatile_writes_unowned_by_others_def)
  apply fastforce
  done


lemma read_only_reads_unowned_tl: 
  "read_only_reads_unowned  (t # ts) \<Longrightarrow>
    read_only_reads_unowned  (ts)"
  apply (clarsimp simp add: read_only_reads_unowned_def)
  apply fastforce
  done



lemma ownership_distinct_tl:
  assumes dist: "ownership_distinct (t#ts)" 
  shows "ownership_distinct ts"
proof -
  from dist
  interpret ownership_distinct "t#ts" .
  
  show ?thesis
  proof (rule ownership_distinct.intro)
    fix i j p "is" \<O> \<R> \<D> xs sb p' is' \<O>' \<R>' \<D>' xs' sb'
    assume i_bound: "i < length ts" 
      and j_bound: "j < length ts" 
      and neq: "i \<noteq> j" 
      and ith: "ts ! i = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      and jth: "ts ! j = (p',is', xs', sb',\<D>', \<O>',\<R>')"
    from i_bound j_bound neq ith jth
    show "(\<O> \<union> all_acquired sb) \<inter> (\<O>' \<union> all_acquired sb') = {}"
      by - (rule ownership_distinct [of "Suc i" "Suc j"],auto)
  qed
qed

lemma valid_ownership_tl: "valid_ownership \<S> (t#ts) \<Longrightarrow> valid_ownership \<S> ts"
  by (auto simp add: valid_ownership_def 
    intro: outstanding_volatile_writes_unowned_by_others_tl 
    outstanding_non_volatile_refs_owned_or_read_only_tl ownership_distinct_tl
    read_only_reads_unowned_tl)


lemma sharing_consistent_takeWhile: 
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "sharing_consistent \<S> \<O> (takeWhile P sb)"
proof -
  from consis have "sharing_consistent \<S> \<O> (takeWhile P sb @ dropWhile P sb)"
    by simp
  with sharing_consistent_append [of _ _ "takeWhile P sb" "dropWhile P sb"] 
  show ?thesis
    by simp
qed
    
lemma sharing_consis_tl: "sharing_consis \<S> (t#ts) \<Longrightarrow> sharing_consis \<S> ts"
  by (auto simp add: sharing_consis_def)

lemma sharing_consis_Cons: 
  "\<lbrakk>sharing_consis \<S> ts; sharing_consistent \<S> \<O> sb\<rbrakk>
   \<Longrightarrow> sharing_consis \<S> ((p,is,\<theta>,sb,\<D>,\<O>,\<R>)#ts)"
  apply (clarsimp simp add: sharing_consis_def)
  subgoal for i pa isa \<O>' \<R>' \<D>' \<theta>' sba
    by (case_tac i) auto
  done

lemma outstanding_non_volatile_writes_unshared_tl:
  "outstanding_non_volatile_writes_unshared \<S> (t#ts) \<Longrightarrow> 
  outstanding_non_volatile_writes_unshared \<S> ts"
  by (auto simp add: outstanding_non_volatile_writes_unshared_def)

lemma no_outstanding_write_to_read_only_memory_tl:
  "no_outstanding_write_to_read_only_memory \<S> (t#ts) \<Longrightarrow>
  no_outstanding_write_to_read_only_memory \<S> ts"
  by (auto simp add: no_outstanding_write_to_read_only_memory_def)

lemma valid_ownership_and_sharing_tl: 
  "valid_ownership_and_sharing \<S> (t#ts) \<Longrightarrow> valid_ownership_and_sharing \<S> ts"
  apply (clarsimp simp add: valid_ownership_and_sharing_def)
  apply (auto intro: valid_ownership_tl
    outstanding_non_volatile_writes_unshared_tl
    no_outstanding_write_to_read_only_memory_tl
    sharing_consis_tl)
  done


lemma non_volatile_owned_or_read_only_outstanding_non_volatile_writes: 
  "\<And>\<O> \<S> pending_write. \<lbrakk>non_volatile_owned_or_read_only pending_write \<S> \<O> sb\<rbrakk>
   \<Longrightarrow>
  outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.hyps [of True "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [of pending_write "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<O> \<union> A - R)"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma (in outstanding_non_volatile_refs_owned_or_read_only) outstanding_non_volatile_writes_owned:
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  shows "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
using non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ts_i]]
by blast







lemma non_volatile_reads_acquired_or_read_only: 
  "\<And>\<O> \<S>. \<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb; sharing_consistent \<S> \<O> sb\<rbrakk>
   \<Longrightarrow>
  outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb \<union> read_only \<S>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
	A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )

      from Cons.hyps [OF non_vol consis']
      have hyp: "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb
                 \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
      with R_owns A_R L_A
      show ?thesis
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b True )
	apply (drule (1) rev_subsetD)
	apply (auto simp add: in_read_only_convs split: if_split_asm)
	done
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
      A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )

    from Cons.hyps [OF non_vol consis']
    have hyp: "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb
      \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
    with R_owns A_R L_A
    show ?thesis
      apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
      apply (drule (1) rev_subsetD)
      apply (auto simp add: in_read_only_convs split: if_split_asm)
      done
  qed
qed


lemma non_volatile_reads_acquired_or_read_only_reads: 
  "\<And>\<O> \<S> pending_write. \<lbrakk>non_volatile_owned_or_read_only pending_write \<S> \<O> sb\<rbrakk>
   \<Longrightarrow>
  outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb \<union> read_only_reads \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )

      from Cons.hyps [OF non_vol ]
      have hyp: "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb
                 \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only_reads (\<O> \<union> A - R) sb".
      then 
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True )
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only pending_write (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )

    from Cons.hyps [OF non_vol ]
    have hyp: "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb
                 \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only_reads (\<O> \<union> A - R) sb".
    then 
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b )
  qed
qed




lemma non_volatile_owned_or_read_only_outstanding_refs: 
  "\<And>\<O> \<S> pending_write. \<lbrakk>non_volatile_owned_or_read_only pending_write \<S> \<O> sb\<rbrakk>
   \<Longrightarrow>
  outstanding_refs (Not \<circ> is_volatile) sb \<subseteq> \<O> \<union> all_acquired sb \<union> read_only_reads \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.hyps [of True "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.hyps [of pending_write "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<O> \<union> A - R)"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed



lemma no_unacquired_write_to_read_only:
"\<And>\<S> \<O>. \<lbrakk>no_write_to_read_only_memory \<S> sb;sharing_consistent \<S> \<O> sb;
 a \<in> read_only \<S>; a \<notin> (\<O> \<union> all_acquired sb)\<rbrakk> 
       \<Longrightarrow> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain no_wrt: "no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and 
	A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
	a_ro: "a \<in> read_only \<S>" and
	a_A: "a \<notin> A" and a_all_acq: "a \<notin> all_acquired sb" and a_owns: "a \<notin> \<O>" and 
	a'_notin: "a' \<notin> read_only \<S>" 
	by ( simp add: Write\<^sub>s\<^sub>b True )
      
      from a'_notin a_ro have neq_a_a': "a\<noteq>a'"
	by blast

      from a_A a_all_acq a_owns
      have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
	by auto
      from a_ro L_A a_A R_owns a_owns
      have "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs split: if_split_asm)

      from Cons.hyps [OF no_wrt consis' this a_notin']
      have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb".
      with neq_a_a'
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case Prog\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain no_wrt: "no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and 
	A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	a_ro: "a \<in> read_only \<S>" and
	a_A: "a \<notin> A" and a_all_acq: "a \<notin> all_acquired sb" and a_owns: "a \<notin> \<O>" 
	by ( simp add: Ghost\<^sub>s\<^sub>b )
      
      
      from a_A a_all_acq a_owns
      have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
	by auto
      from a_ro L_A a_A R_owns a_owns
      have "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs split: if_split_asm)

      from Cons.hyps [OF no_wrt consis' this a_notin']
      have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb".
      then
      show ?thesis
	by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma read_only_reads_read_only: 
  "\<And>\<S> \<O>. \<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb;
  sharing_consistent \<S> \<O> sb\<rbrakk>
  \<Longrightarrow>
  read_only_reads \<O> sb \<subseteq> \<O> \<union> all_acquired sb \<union> read_only \<S>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
	A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )

      from Cons.hyps [OF non_vol consis']
      have hyp: "read_only_reads (\<O> \<union> A - R) sb
                 \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      {
	fix a'
	assume a'_in: "a' \<in> read_only_reads (\<O> \<union> A - R) sb"
	assume a'_unowned: "a' \<notin> \<O>"
	assume a'_unacq: "a' \<notin> all_acquired sb"
	assume a'_A: "a' \<notin> A"
	have "a' \<in> read_only \<S>"
	proof -
	  from a'_in hyp a'_unowned a'_unacq a'_A 
	  have "a' \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by auto
	  
	  with L_A R_owns a'_unowned
	  show ?thesis
	    by (auto simp add: in_read_only_convs split:if_split_asm)
	qed
      }
	
      then
	  
      show ?thesis
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b True simp del: o_apply)
	apply force
	done
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
      A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )

    from Cons.hyps [OF non_vol consis']
    have hyp: "read_only_reads (\<O> \<union> A - R) sb
                 \<subseteq> \<O> \<union> A - R \<union> all_acquired sb \<union> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

    {
      fix a'
      assume a'_in: "a' \<in> read_only_reads (\<O> \<union> A - R) sb"
      assume a'_unowned: "a' \<notin> \<O>"
      assume a'_unacq: "a' \<notin> all_acquired sb"
      assume a'_A: "a' \<notin> A"
      have "a' \<in> read_only \<S>"
      proof -
	from a'_in hyp a'_unowned a'_unacq a'_A 
	have "a' \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	  
	with L_A R_owns a'_unowned
	show ?thesis
	  by (auto simp add: in_read_only_convs split:if_split_asm)
        qed
    }
	
    then
	  
    show ?thesis
      apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b simp del: o_apply)
      apply force
      done
    
  qed
qed

lemma no_unacquired_write_to_read_only_reads:
"\<And>\<S> \<O> . \<lbrakk>no_write_to_read_only_memory \<S> sb;
non_volatile_owned_or_read_only True \<S> \<O> sb; sharing_consistent \<S> \<O> sb;
 a \<in> read_only_reads \<O> sb; a \<notin> (\<O> \<union> all_acquired sb)\<rbrakk> 
       \<Longrightarrow> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain no_wrt: "no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and 
	non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
	A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
	a_ro: "a \<in> read_only_reads (\<O> \<union> A - R) sb" and
	a_A: "a \<notin> A" and a_all_acq: "a \<notin> all_acquired sb" and a_owns: "a \<notin> \<O>" and 
	a'_notin: "a' \<notin> read_only \<S>" 
	by ( simp add: Write\<^sub>s\<^sub>b True )

      from read_only_reads_read_only [OF non_vol consis' ] a_ro a_owns a_all_acq a_A
      have "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" 
	by auto
      with a'_notin R_owns a_owns have neq_a_a': "a\<noteq>a'"
	by (auto simp add:  in_read_only_convs split: if_split_asm)
      

      from a_A a_all_acq a_owns
      have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
	by auto

      from Cons.hyps [OF no_wrt non_vol consis' a_ro a_notin'] 
      have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb".
      then 
      show ?thesis
	using neq_a_a'
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v) 
    show ?thesis
    proof (cases volatile)
      case True
      with Cons show ?thesis
	by  (auto simp add: Read\<^sub>s\<^sub>b)
    next
      case False
      note non_volatile = this
      from Cons.prems obtain no_wrt': "no_write_to_read_only_memory \<S> sb" and 
	consis':"sharing_consistent \<S> \<O> sb" and
	a_in: "a \<in> (if a' \<notin> \<O> then insert a' (read_only_reads \<O> sb)
                 else read_only_reads \<O> sb)" and
	a'_owns_shared: "a' \<in> \<O> \<or> a' \<in> read_only \<S>" and 
	non_vol': "non_volatile_owned_or_read_only True \<S> \<O> sb" and
        a_owns: "a \<notin> \<O> \<union> all_acquired sb"
	by (clarsimp simp add: Read\<^sub>s\<^sub>b False)

      show ?thesis
      proof (cases "a' \<in> \<O>")
	case True
	with a_in have "a \<in> read_only_reads \<O> sb"
	  by auto
	from Cons.hyps [OF no_wrt' non_vol' consis' this a_owns]
	show ?thesis
	  by (clarsimp simp add: Read\<^sub>s\<^sub>b)
      next
	case False
	note a'_unowned = this
	with a_in have a_in': "a \<in> insert a' (read_only_reads \<O> sb)" by auto
	from a'_owns_shared False have a'_read_only: "a' \<in> read_only \<S>" by auto
	show ?thesis
	proof (cases "a=a'")
	  case False
	  with a_in' have "a \<in> (read_only_reads \<O> sb)" by auto
	  from Cons.hyps [OF no_wrt' non_vol' consis' this a_owns]
	  show ?thesis
	    by (simp add: Read\<^sub>s\<^sub>b)
	next
	  case True
	  from no_unacquired_write_to_read_only [OF no_wrt' consis' a'_read_only] a_owns True
	  
	  have "a' \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
	    by auto
	  then show ?thesis
	    by (simp add: Read\<^sub>s\<^sub>b True)
	qed
      qed
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain no_wrt: "no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and 
      non_vol: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R)  sb" and 
      A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
      a_ro: "a \<in> read_only_reads (\<O> \<union> A - R) sb" and
      a_A: "a \<notin> A" and a_all_acq: "a \<notin> all_acquired sb" and a_owns: "a \<notin> \<O>" 
      by ( simp add: Ghost\<^sub>s\<^sub>b )

    from read_only_reads_read_only [OF non_vol consis' ] a_ro a_owns a_all_acq a_A
    have "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" 
      by auto
      

    from a_A a_all_acq a_owns
    have a_notin': "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
      by auto

    from Cons.hyps [OF no_wrt non_vol consis' a_ro a_notin'] 
    have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb".
    then 
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


lemma no_unacquired_write_to_read_only'':
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only \<S> \<inter> outstanding_refs is_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
using no_unacquired_write_to_read_only [OF no_wrt consis]
by auto

lemma no_unacquired_volatile_write_to_read_only:
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only \<S> \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
proof -
  have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
    apply (rule outstanding_refs_mono_pred)
    apply (auto simp add: is_volatile_Write\<^sub>s\<^sub>b_def split: memref.splits)
    done
  with no_unacquired_write_to_read_only'' [OF no_wrt consis]
  show ?thesis by blast
qed

lemma no_unacquired_non_volatile_write_to_read_only_reads:
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only \<S> \<inter> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
proof -
  from outstanding_refs_subsets 
  have "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb" by - assumption
  with no_unacquired_write_to_read_only'' [OF no_wrt consis]
  show ?thesis by blast
qed


lemma no_unacquired_write_to_read_only_reads':
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes non_vol: "non_volatile_owned_or_read_only True \<S> \<O> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only_reads \<O> sb \<inter> outstanding_refs is_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
using no_unacquired_write_to_read_only_reads [OF no_wrt non_vol consis]
by auto

lemma no_unacquired_volatile_write_to_read_only_reads:
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes non_vol: "non_volatile_owned_or_read_only True \<S> \<O> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only_reads \<O> sb \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
proof -
  have "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
    apply (rule outstanding_refs_mono_pred)
    apply (auto simp add: is_volatile_Write\<^sub>s\<^sub>b_def split: memref.splits)
    done
  with no_unacquired_write_to_read_only_reads [OF no_wrt non_vol consis]
  show ?thesis by blast
qed

lemma no_unacquired_non_volatile_write_to_read_only:
  assumes no_wrt: "no_write_to_read_only_memory \<S> sb"
  assumes non_vol: "non_volatile_owned_or_read_only True \<S> \<O> sb"
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "read_only_reads \<O> sb \<inter> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> \<O> \<union> all_acquired sb"
proof -
  from outstanding_refs_subsets 
  have "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<subseteq> outstanding_refs is_Write\<^sub>s\<^sub>b sb" by - assumption
  with no_unacquired_write_to_read_only_reads [OF no_wrt non_vol consis]
  show ?thesis by blast
qed



lemma set_dropWhileD: "x \<in> set (dropWhile P xs) \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma outstanding_refs_takeWhileD:
  "x \<in> outstanding_refs P (takeWhile P' sb) \<Longrightarrow> x \<in> outstanding_refs P sb"
  using outstanding_refs_takeWhile
  by blast

lemma outstanding_refs_dropWhileD:
  "x \<in> outstanding_refs P (dropWhile P' sb) \<Longrightarrow> x \<in> outstanding_refs P sb"
  by (auto dest: set_dropWhileD simp add: outstanding_refs_conv)



lemma dropWhile_ConsD: "dropWhile P xs = y#ys \<Longrightarrow> \<not> P y"
  by (simp add: dropWhile_eq_Cons_conv)


lemma non_volatile_owned_or_read_only_drop:
  "non_volatile_owned_or_read_only False \<S> \<O> sb
  \<Longrightarrow> non_volatile_owned_or_read_only True 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) 
      (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
using non_volatile_owned_or_read_only_append [of False \<S> \<O> "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"]
apply (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
apply  (clarsimp simp add: outstanding_vol_write_take_drop_appends 
  takeWhile_not_vol_write_outstanding_refs dropWhile_not_vol_write_empty)
apply(clarsimp simp add: outstanding_vol_write_take_drop_appends 
  takeWhile_not_vol_write_outstanding_refs dropWhile_not_vol_write_empty )
apply (case_tac "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)")
apply  (fastforce simp add: outstanding_refs_conv)
apply (frule dropWhile_ConsD)
apply (clarsimp split: memref.splits)
done


lemma  read_only_share: "\<And>\<S> \<O>. 
  sharing_consistent \<S> \<O> sb \<Longrightarrow> 
        read_only (share sb \<S>) \<subseteq> read_only \<S> \<union> \<O> \<union> all_acquired sb"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.prems obtain 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )
      from Cons.hyps [OF  consis']
      have "read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))
              \<subseteq> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<union> (\<O> \<union> A - R) \<union> all_acquired sb"
        by auto
      also from A_shared_owns L_A R_owns A_R
      have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<union> (\<O> \<union> A - R) \<union> all_acquired sb \<subseteq>
        read_only \<S> \<union> \<O> \<union> (A \<union> all_acquired sb)"
        by (auto simp add: read_only_def augment_shared_def restrict_shared_def split: option.splits)
      finally
      show ?thesis
        by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
    from Cons.hyps [OF  consis']
    have "read_only (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))
              \<subseteq> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<union> (\<O> \<union> A - R) \<union> all_acquired sb"
      by auto
    also from A_shared_owns L_A R_owns A_R
    have "read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<union> (\<O> \<union> A - R) \<union> all_acquired sb \<subseteq>
        read_only \<S> \<union> \<O> \<union> (A \<union> all_acquired sb)"
      by (auto simp add: read_only_def augment_shared_def restrict_shared_def split: option.splits)
    finally
    show ?thesis
      by (simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


      
lemma (in valid_ownership_and_sharing) outstanding_non_write_non_vol_reads_drop_disj:
assumes i_bound: "i < length ts"
assumes j_bound: "j < length ts"
assumes neq_i_j: "i \<noteq> j"
assumes ith: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
assumes jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
shows "outstanding_refs is_Write\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) \<inter> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)
         = {}" 
proof -

  let ?take_j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
  let ?drop_j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"

  let ?take_i = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i)"
  let ?drop_i = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i)"


  note nvo_i = outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ith]
  note nvo_j = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]
  note nro_i = no_outstanding_write_to_read_only_memory [OF i_bound ith]
  with no_write_to_read_only_memory_append [of \<S> ?take_i ?drop_i]
  have nro_drop_i: "no_write_to_read_only_memory (share ?take_i \<S>) ?drop_i"
    by simp
  note nro_j = no_outstanding_write_to_read_only_memory [OF j_bound jth]
  with no_write_to_read_only_memory_append [of \<S> ?take_j ?drop_j]
  have nro_drop_j: "no_write_to_read_only_memory (share ?take_j \<S>) ?drop_j"
    by simp
  from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound neq_i_j ith jth]
  have dist: "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i = {}".
  note own_dist = ownership_distinct [OF i_bound j_bound neq_i_j ith jth]




  from sharing_consis [OF j_bound jth]
  have consis_j: "sharing_consistent \<S> \<O>\<^sub>j sb\<^sub>j".
  with sharing_consistent_append [of \<S> \<O>\<^sub>j ?take_j ?drop_j]
  obtain
    consis_take_j: "sharing_consistent \<S> \<O>\<^sub>j ?take_j" and
    consis_drop_j: "sharing_consistent (share ?take_j \<S>) (acquired True ?take_j \<O>\<^sub>j) ?drop_j"
    by simp
    
  from sharing_consis [OF i_bound ith]
  have consis_i: "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i".
  with sharing_consistent_append [of \<S> \<O>\<^sub>i ?take_i ?drop_i]
  have consis_drop_i: "sharing_consistent (share ?take_i \<S>) (acquired True ?take_i \<O>\<^sub>i) ?drop_i"
    by simp


  {
    fix x
    assume x_in_drop_i: "x \<in> outstanding_refs is_Write\<^sub>s\<^sub>b ?drop_i"
    assume x_in_drop_j: "x \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_j"
    have False
    proof -
      from x_in_drop_i have x_in_i: "x \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i"
	using outstanding_refs_append [of is_Write\<^sub>s\<^sub>b ?take_i ?drop_i] by auto

      from x_in_drop_j have x_in_j: "x \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb\<^sub>j"
	using outstanding_refs_append [of is_non_volatile_Read\<^sub>s\<^sub>b ?take_j ?drop_j]
	by auto
      from non_volatile_owned_or_read_only_drop [OF nvo_j]
      have nvo_drop_j: "non_volatile_owned_or_read_only True (share ?take_j \<S>) (acquired True ?take_j \<O>\<^sub>j) ?drop_j".

      from non_volatile_reads_acquired_or_read_only_reads [OF nvo_drop_j ] x_in_drop_j 
        acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
      have x_j: "x \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j \<union> read_only_reads (acquired True ?take_j \<O>\<^sub>j) ?drop_j" 
	using all_acquired_append [of ?take_j ?drop_j]
	by ( auto )

      {
	assume x_in_vol_drop_i: "x \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b ?drop_i"
	hence x_in_vol_i: "x \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i"
	  using outstanding_refs_append [of is_volatile_Write\<^sub>s\<^sub>b ?take_i ?drop_i]
	  by auto

	from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound neq_i_j ith jth]
	have "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i = {}". 
	with x_in_vol_i x_j obtain  
	  x_unacq_j: "x \<notin>  \<O>\<^sub>j \<union> all_acquired sb\<^sub>j" and
	  x_ror_j: "x \<in> read_only_reads (acquired True ?take_j \<O>\<^sub>j) ?drop_j"
	  by auto
	from read_only_reads_unowned [OF j_bound i_bound neq_i_j [symmetric] jth ith] x_ror_j
	have "x \<notin> \<O>\<^sub>i \<union> all_acquired sb\<^sub>i"
	  by auto

	moreover 


	from read_only_reads_read_only [OF nvo_drop_j  consis_drop_j] x_ror_j x_unacq_j 
	  all_acquired_append [of ?take_j ?drop_j] acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb\<^sub>j \<O>\<^sub>j]
	have "x \<in> read_only (share ?take_j \<S>)"
	  by (auto)
        
        from read_only_share [OF consis_take_j] this x_unacq_j all_acquired_append [of ?take_j ?drop_j]
        have "x \<in> read_only \<S>"
	  by auto

	with no_unacquired_write_to_read_only'' [OF nro_i consis_i]  x_in_i
	have "x \<in> \<O>\<^sub>i \<union> all_acquired sb\<^sub>i"
	  by auto

	ultimately have False by auto
      }
      moreover
      {
	assume x_in_non_vol_drop_i: "x \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b ?drop_i"
	hence "x \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i"
	  using outstanding_refs_append [of is_non_volatile_Write\<^sub>s\<^sub>b ?take_i ?drop_i]
	  by auto
	with non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF nvo_i]
	have "x \<in> \<O>\<^sub>i \<union> all_acquired sb\<^sub>i" by auto

	moreover

	with x_j own_dist obtain
	  x_unacq_j: "x \<notin>  \<O>\<^sub>j \<union> all_acquired sb\<^sub>j" and
	  x_ror_j: "x \<in> read_only_reads (acquired True ?take_j \<O>\<^sub>j) ?drop_j"
	  by auto
	from read_only_reads_unowned [OF j_bound i_bound neq_i_j [symmetric] jth ith] x_ror_j
	have "x \<notin> \<O>\<^sub>i \<union> all_acquired sb\<^sub>i"
	  by auto

	ultimately have False
	  by auto
      }
      ultimately
      
      show ?thesis
	using x_in_drop_i x_in_drop_j
	by (auto simp add: misc_outstanding_refs_convs)
    qed
  }
  thus ?thesis
    by auto
qed
  
lemma (in valid_ownership_and_sharing) outstanding_non_volatile_write_disj:
assumes i_bound: "i < length ts"
assumes j_bound: "j < length ts"
assumes neq_i_j: "i \<noteq> j"
assumes ith: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
assumes jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
shows "outstanding_refs (is_non_volatile_Write\<^sub>s\<^sub>b) (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) \<inter> 
        (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) - 
          read_only_reads \<O>\<^sub>j (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) \<union> 
         (\<O>\<^sub>j \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))
        ) = {}" (is "?non_vol_writes_i \<inter> ?not_volatile_j = {}")
proof -
  note nro_i = no_outstanding_write_to_read_only_memory [OF i_bound ith]
  note nro_j = no_outstanding_write_to_read_only_memory [OF j_bound jth]
  note nvo_j = outstanding_non_volatile_refs_owned_or_read_only [OF j_bound jth]
  note nvo_i = outstanding_non_volatile_refs_owned_or_read_only [OF i_bound ith]
    
  from outstanding_volatile_writes_unowned_by_others [OF i_bound j_bound neq_i_j ith jth]
  have dist: "(\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>i = {}".
  
  from outstanding_volatile_writes_unowned_by_others [OF j_bound i_bound neq_i_j [symmetric] jth ith]
  have dist_j: "(\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) \<inter> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j = {}".
  
  note own_dist = ownership_distinct [OF i_bound j_bound neq_i_j ith jth]
  
  from sharing_consis [OF j_bound jth]
  have consis_j: "sharing_consistent \<S> \<O>\<^sub>j sb\<^sub>j".
  
  from sharing_consis [OF i_bound ith]
  have consis_i: "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i".
  
  let ?take_j = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
  let ?drop_j = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"


  { 
    fix x
    assume x_in_take_i: "x \<in> ?non_vol_writes_i"
    assume x_in_j: "x \<in> ?not_volatile_j"
    from x_in_take_i have x_in_i: "x \<in> outstanding_refs (is_non_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i"
      by (auto dest: outstanding_refs_takeWhileD)
    from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF nvo_i] x_in_i
    have x_in_owns_acq_i: "x \<in> \<O>\<^sub>i \<union> all_acquired sb\<^sub>i"
      by auto
    have False
    proof -
      {
	assume x_in_j: "x \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j" 
	with dist_j have x_notin: "x \<notin> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i)"
	  by auto
	with x_in_owns_acq_i have False
	  by auto
      }
      moreover
      {
	assume x_in_j: "x \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j"
	from non_volatile_owned_or_read_only_outstanding_non_volatile_writes [OF nvo_j] x_in_j
	have "x \<in> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	  by auto
	with x_in_owns_acq_i own_dist
	have False
	  by auto
      }
      moreover
      {
	assume x_in_j: "x \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?drop_j"
	  
	from non_volatile_owned_or_read_only_drop [OF nvo_j]
	have nvo': "non_volatile_owned_or_read_only True (share ?take_j \<S>) (acquired True ?take_j \<O>\<^sub>j) ?drop_j".

	from non_volatile_owned_or_read_only_outstanding_refs [OF nvo'] x_in_j
	have "x \<in> acquired True ?take_j \<O>\<^sub>j \<union> all_acquired ?drop_j \<union>  
	  read_only_reads (acquired True ?take_j \<O>\<^sub>j) ?drop_j"
	  by (auto simp add: misc_outstanding_refs_convs)
	
	moreover 
	from acquired_append [of True ?take_j ?drop_j \<O>\<^sub>j] acquired_all_acquired [of True ?take_j \<O>\<^sub>j]
	  all_acquired_append [of ?take_j ?drop_j]
	have "acquired True ?take_j \<O>\<^sub>j \<union> all_acquired ?drop_j \<subseteq> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
	  by auto
	ultimately 
	have "x \<in> read_only_reads (acquired True ?take_j \<O>\<^sub>j) ?drop_j"
	  using x_in_owns_acq_i own_dist
	  by auto
	
	with read_only_reads_unowned [OF j_bound i_bound neq_i_j [symmetric] jth ith] x_in_owns_acq_i
	have False
	  by auto
      }
      moreover
      {
	assume x_in_j: "x \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b ?take_j" 
	assume x_notin: "x \<notin> read_only_reads \<O>\<^sub>j ?take_j"
	from non_volatile_owned_or_read_only_append [where xs="?take_j" and ys="?drop_j"] nvo_j
	have "non_volatile_owned_or_read_only False \<S> \<O>\<^sub>j ?take_j"
	  by auto
	
	from non_volatile_owned_or_read_only_outstanding_refs [OF this]  x_in_j x_notin
	have "x \<in> \<O>\<^sub>j \<union> all_acquired ?take_j" 
	  by (auto simp add: misc_outstanding_refs_convs )
	with all_acquired_append [of ?take_j ?drop_j] x_in_owns_acq_i own_dist
	have False
	  by auto
      }
      moreover
      {
	assume x_in_j: "x \<in> \<O>\<^sub>j \<union> all_acquired ?take_j"
	moreover
	from all_acquired_append [of ?take_j ?drop_j]
	have "all_acquired ?take_j \<subseteq> all_acquired sb\<^sub>j"
	  by auto
	ultimately have False
	  using x_in_owns_acq_i own_dist
	  by auto
      }
      ultimately show ?thesis
	using x_in_take_i x_in_j
	by (auto simp add: misc_outstanding_refs_convs)
    qed
  }
  then show ?thesis
    by auto
qed

lemma (in valid_ownership_and_sharing) outstanding_non_volatile_write_not_volatile_read_disj:
assumes i_bound: "i < length ts"
assumes j_bound: "j < length ts"
assumes neq_i_j: "i \<noteq> j"
assumes ith: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
assumes jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
shows "outstanding_refs (is_non_volatile_Write\<^sub>s\<^sub>b) (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>i) \<inter> 
        outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}" 
  (is "?non_vol_writes_i \<inter> ?not_volatile_j = {}")
proof -
  have "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<subseteq> 
    outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<union>  
    outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb\<^sub>j \<union> 
    outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
    by (auto simp add: misc_outstanding_refs_convs dest: outstanding_refs_dropWhileD)
  with outstanding_non_volatile_write_disj [OF i_bound j_bound neq_i_j ith jth]
  show ?thesis
    by blast
qed



lemma (in valid_ownership_and_sharing) outstanding_refs_is_Write\<^sub>s\<^sub>b_takeWhile_disj:
        "\<forall>i < length ts. (\<forall>j < length ts. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>i,_,_,_) = ts!i;
                      (_,_,_,sb\<^sub>j,_,_,_) = ts!j
                   in outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}))"
proof -
  {
    fix i j p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
    assume i_bound: "i < length ts"
    assume j_bound: "j < length ts"
    assume neq_i_j: "i \<noteq> j"
    assume ith: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
    assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
    from outstanding_non_volatile_write_disj [OF j_bound i_bound neq_i_j[symmetric] jth ith]
    have "outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}"
      apply (clarsimp simp add: outstanding_refs_is_non_volatile_Write\<^sub>s\<^sub>b_takeWhile_conv)
      apply (auto simp add: misc_outstanding_refs_convs )
      done
  }
  thus ?thesis
    by (fastforce simp add: Let_def)
qed



fun read_tmps:: "'p store_buffer \<Rightarrow> tmp set"
where
  "read_tmps [] = {}"
| "read_tmps (r#rs) =
     (case r of 
       Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> insert t (read_tmps rs)
      | _ \<Rightarrow> read_tmps rs)"


lemma in_read_tmps_conv:
  "(t \<in> read_tmps xs) = (\<exists>volatile a v. Read\<^sub>s\<^sub>b volatile a t v \<in> set xs)"
  by (induct xs) (auto split: memref.splits)


lemma read_tmps_mono: "\<And>ys. set xs \<subseteq> set ys \<Longrightarrow> read_tmps xs \<subseteq> read_tmps ys"
  by (fastforce simp add: in_read_tmps_conv)



fun distinct_read_tmps:: "'p store_buffer \<Rightarrow> bool"
where
  "distinct_read_tmps [] = True"
| "distinct_read_tmps (r#rs) =
     (case r of 
         Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> t \<notin> (read_tmps rs) \<and> distinct_read_tmps rs
       | _ \<Rightarrow> distinct_read_tmps rs)"
 
lemma distinct_read_tmps_conv:
 "distinct_read_tmps xs = (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j \<longrightarrow>
      (case xs!i of 
         Read\<^sub>s\<^sub>b _ _ t\<^sub>i _ \<Rightarrow> case xs!j of Read\<^sub>s\<^sub>b _ _ t\<^sub>j _ \<Rightarrow> t\<^sub>i \<noteq> t\<^sub>j | _ \<Rightarrow> True
       | _ \<Rightarrow> True))"
\<comment> \<open>Nice lemma, ugly proof.\<close>
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v)
    with Cons.hyps show ?thesis
      apply -
      apply (rule iffI [rule_format]) 
      apply  clarsimp
             subgoal for i j
             apply (case_tac i)
             apply  fastforce
             apply (case_tac j)
             apply  (fastforce split: memref.splits) 
             apply (clarsimp cong: memref.case_cong)
             done
      apply clarsimp
      subgoal for i j
      apply (erule_tac x="Suc i" in allE)
      apply  clarsimp
      apply (erule_tac x="Suc j" in allE)
      apply  (clarsimp cong: memref.case_cong)
      done
      done
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    with Cons.hyps show ?thesis
      apply -
      apply (rule iffI [rule_format]) 
      apply  clarsimp
             subgoal for i j 
             apply (case_tac i)
             apply  clarsimp
             apply  (case_tac j)
             apply   clarsimp
             apply  (fastforce split: memref.splits simp add: in_read_tmps_conv dest: nth_mem)
             apply (clarsimp)
             apply (case_tac j)
             apply  (fastforce split: memref.splits simp add: in_read_tmps_conv dest: nth_mem)
             apply (clarsimp cong: memref.case_cong)
             done
      apply clarsimp
      apply (rule conjI)
      apply (clarsimp simp add: in_read_tmps_conv)
      apply  (erule_tac x="0" in allE)
      apply  (clarsimp simp add: in_set_conv_nth)
             subgoal for volatile' a' v' i
             apply  (erule_tac x="Suc i" in allE)
             apply  clarsimp
             done
      apply clarsimp
      subgoal for i j
      apply (erule_tac x="Suc i" in allE)
      apply clarsimp
      apply (erule_tac x="Suc j" in allE)
      apply (clarsimp cong: memref.case_cong)
      done
      done
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps show ?thesis
      apply -
      apply (rule iffI [rule_format]) 
      apply  clarsimp
             subgoal for i j
             apply (case_tac i)
             apply  fastforce
             apply (case_tac j)
             apply  (fastforce split: memref.splits) 
             apply (clarsimp cong: memref.case_cong)
             done
      apply clarsimp
      subgoal for i j
      apply (erule_tac x="Suc i" in allE)
      apply  clarsimp
      apply (erule_tac x="Suc j" in allE)
      apply  (clarsimp cong: memref.case_cong)
      done
      done
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons.hyps show ?thesis
      apply -
      apply (rule iffI [rule_format]) 
      apply  clarsimp
             subgoal for i j
             apply (case_tac i)
             apply  fastforce
             apply (case_tac j)
             apply  (fastforce split: memref.splits) 
             apply (clarsimp cong: memref.case_cong)
             done
      apply clarsimp
      subgoal for i j
      apply (erule_tac x="Suc i" in allE)
      apply  clarsimp
      apply (erule_tac x="Suc j" in allE)
      apply (clarsimp cong: memref.case_cong)
      done
      done
  qed
qed

fun load_tmps:: "instrs \<Rightarrow> tmp set"
where
  "load_tmps [] = {}"
| "load_tmps (i#is) =
     (case i of
        Read volatile a t \<Rightarrow> insert t (load_tmps is)
      | RMW _ t _ _ _ _ _ _ _  \<Rightarrow> insert t (load_tmps is)
      | _ \<Rightarrow> load_tmps is)"

lemma in_load_tmps_conv:
  "(t \<in> load_tmps xs) = ((\<exists>volatile a. Read volatile a t \<in> set xs) \<or>
                         (\<exists>a sop cond ret A L R W. RMW a t sop cond ret A L R W \<in> set xs))"
  by (induct xs) (auto split: instr.splits)

lemma load_tmps_mono: "\<And>ys. set xs \<subseteq> set ys \<Longrightarrow> load_tmps xs \<subseteq> load_tmps ys"
  by (fastforce simp add: in_load_tmps_conv)

fun distinct_load_tmps:: "instrs \<Rightarrow> bool"
where
  "distinct_load_tmps [] = True"
| "distinct_load_tmps (r#rs) =
     (case r of 
         Read volatile a t \<Rightarrow> t \<notin> (load_tmps rs) \<and> distinct_load_tmps rs
       | RMW a t sop cond ret A L R W \<Rightarrow> t \<notin> (load_tmps rs) \<and> distinct_load_tmps rs
       | _ \<Rightarrow> distinct_load_tmps rs)"


locale load_tmps_distinct =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes load_tmps_distinct:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   distinct_load_tmps is"

locale read_tmps_distinct =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes read_tmps_distinct:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   distinct_read_tmps sb"

locale load_tmps_read_tmps_distinct =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes load_tmps_read_tmps_distinct:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   load_tmps is \<inter> read_tmps sb = {}"

locale tmps_distinct = 
  load_tmps_distinct + 
  read_tmps_distinct + 
  load_tmps_read_tmps_distinct

lemma rev_read_tmps: "read_tmps (rev xs) = read_tmps xs"
  by (auto simp add: in_read_tmps_conv)

lemma rev_load_tmps: "load_tmps (rev xs) = load_tmps xs"
  by (auto simp add: in_load_tmps_conv)

lemma distinct_read_tmps_append: "\<And>ys. distinct_read_tmps (xs @ ys) = 
        (distinct_read_tmps xs \<and> distinct_read_tmps ys \<and>
        read_tmps xs \<inter> read_tmps ys = {})" 
by (induct xs) (auto split: memref.splits simp add: in_read_tmps_conv)

lemma distinct_load_tmps_append: "\<And>ys. distinct_load_tmps (xs @ ys) = 
        (distinct_load_tmps xs \<and> distinct_load_tmps ys \<and>
        load_tmps xs \<inter> load_tmps ys = {})" 
apply (induct xs) 
apply (auto split: instr.splits simp add: in_load_tmps_conv)
done

lemma read_tmps_append: "read_tmps (xs@ys) = (read_tmps xs \<union> read_tmps ys)"
  by (fastforce simp add: in_read_tmps_conv)

lemma load_tmps_append: "load_tmps (xs@ys) = (load_tmps xs \<union> load_tmps ys)"
  by (fastforce simp add: in_load_tmps_conv)

fun write_sops:: "'p store_buffer \<Rightarrow> sop set"
where
  "write_sops [] = {}"
| "write_sops (r#rs) =
     (case r of 
       Write\<^sub>s\<^sub>b volatile a sop v _ _ _ _\<Rightarrow> insert sop (write_sops rs)
      | _ \<Rightarrow> write_sops rs)"

lemma in_write_sops_conv:
  "(sop \<in> write_sops xs) = (\<exists>volatile a v A L R W. Write\<^sub>s\<^sub>b volatile a sop v A L R W \<in> set xs)"
  apply (induct xs) 
  apply  simp
  apply (auto split: memref.splits) 
  apply  force
  apply force
  done

lemma write_sops_mono: "\<And>ys. set xs \<subseteq> set ys \<Longrightarrow> write_sops xs \<subseteq> write_sops ys"
  by (fastforce simp add: in_write_sops_conv)

lemma write_sops_append: "write_sops (xs@ys) = write_sops xs \<union> write_sops ys"
  by (force simp add: in_write_sops_conv)

  
fun store_sops:: "instrs \<Rightarrow> sop set"
where
  "store_sops [] = {}"
| "store_sops (i#is) =
     (case i of
        Write volatile a sop _ _ _ _ \<Rightarrow> insert sop (store_sops is)
      | RMW a t sop cond ret A L R W \<Rightarrow> insert sop (store_sops is) 
      | _ \<Rightarrow> store_sops is)"

lemma in_store_sops_conv:
  "(sop \<in> store_sops xs) = ((\<exists>volatile a A L R W. Write volatile a sop A L R W \<in> set xs) \<or>
                            (\<exists>a t cond ret A L R W. RMW a t sop cond ret A L R W \<in> set xs))"
  by (induct xs) (auto split: instr.splits)

lemma store_sops_mono: "\<And>ys. set xs \<subseteq> set ys \<Longrightarrow> store_sops xs \<subseteq> store_sops ys"
  by (fastforce simp add: in_store_sops_conv)

lemma store_sops_append: "store_sops (xs@ys) = store_sops xs \<union> store_sops ys"
  by (force simp add: in_store_sops_conv)

locale valid_write_sops =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes valid_write_sops:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk> 
   \<Longrightarrow>
   \<forall>sop \<in> write_sops sb. valid_sop sop"

locale valid_store_sops =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes valid_store_sops:
  "\<And>i is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk> 
   \<Longrightarrow>
   \<forall>sop \<in> store_sops is. valid_sop sop"

locale valid_sops = valid_write_sops + valid_store_sops

text \<open>The value stored in a non-volatile @{const "Read\<^sub>s\<^sub>b"} in the store-buffer has to match the
 last value written to the same address in the store buffer 
 or the memory content if there is no corresponding write in the store buffer.
 No volatile read may follow a volatile write.
 Volatile reads in the store buffer may refer to a stale value:
  e.g. imagine one writer and multiple readers
\<close>

(* Read\<^sub>s\<^sub>b-only reads in the takeWhile part of the store buffer may become stale*)
(* FIXME: The flushing stuff: outstanding_refs is_volatile_Read\<^sub>s\<^sub>b rs = {} \<and> acquired_reads True rs (A - R) = {}
   does not fit well in this definition (it is not memory dependent).
   Maybe it would fit better to sharing_consistent.
*)
fun reads_consistent:: "bool \<Rightarrow> owns \<Rightarrow> memory \<Rightarrow> 'p store_buffer \<Rightarrow> bool"
where
  "reads_consistent pending_write \<O> m [] = True"
| "reads_consistent pending_write \<O> m (r#rs) = 
   (case r of 
      Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> (\<not> volatile \<longrightarrow> (pending_write \<or> a \<in> \<O>) \<longrightarrow> v = m a) \<and> 
                             reads_consistent pending_write \<O> m rs
    | Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> 
        (if volatile then
             outstanding_refs is_volatile_Read\<^sub>s\<^sub>b rs = {} \<and> 
             reads_consistent True (\<O> \<union> A - R) (m(a := v)) rs
         else reads_consistent pending_write \<O> (m(a := v)) rs)
    | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> reads_consistent pending_write (\<O> \<union> A - R) m rs
    | _ \<Rightarrow> reads_consistent pending_write \<O> m rs
   )"

fun volatile_reads_consistent:: "memory \<Rightarrow> 'p store_buffer \<Rightarrow> bool"
where
  "volatile_reads_consistent m [] = True"
| "volatile_reads_consistent m (r#rs) = 
   (case r of 
      Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> (volatile \<longrightarrow> v = m a) \<and> volatile_reads_consistent m rs
    | Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> volatile_reads_consistent (m(a := v)) rs 
    | _ \<Rightarrow> volatile_reads_consistent m rs
   )"

fun flush:: "'p store_buffer \<Rightarrow> memory \<Rightarrow> memory"
where
  "flush [] m = m"
| "flush (r#rs) m =
     (case r of 
        Write\<^sub>s\<^sub>b volatile a _ v _ _ _ _ \<Rightarrow> flush rs (m(a:=v))
      | _ \<Rightarrow> flush rs m)"

lemma reads_consistent_pending_write_antimono:
  "\<And>\<O> m. reads_consistent True \<O> m sb \<Longrightarrow> reads_consistent False \<O> m sb"
apply (induct sb)
apply  simp
subgoal for a sb \<O> m
  by (case_tac a) auto
done

lemma reads_consistent_owns_antimono:
  "\<And>\<O> \<O>' pending_write m.
       \<O> \<subseteq> \<O>' \<Longrightarrow> reads_consistent pending_write \<O>' m sb \<Longrightarrow> reads_consistent pending_write \<O> m sb"
apply (induct sb)
apply  simp
subgoal for a sb \<O> \<O>' pending_write m
apply (case_tac a)
apply    (clarsimp split: if_split_asm)
         subgoal for volatile a D f v A L R W
         apply (drule_tac C="A" in union_mono_aux)
         apply (drule_tac C="R" in set_minus_mono_aux)
         apply blast
         done
apply   fastforce
apply  fastforce
apply clarsimp
subgoal for A L R W 
apply (drule_tac C="A" in union_mono_aux)
apply (drule_tac C="R" in set_minus_mono_aux)
apply blast
done
done
done

lemma acquired_reads_mono': "x \<in> acquired_reads b xs A \<Longrightarrow> acquired_reads b xs B = {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> False"
apply (drule acquired_reads_mono_in [where B=B])
apply auto
done


lemma reads_consistent_append: 
  "\<And>m pending_write \<O>. reads_consistent pending_write \<O> m (xs@ys) = 
      (reads_consistent pending_write \<O> m xs \<and>
       reads_consistent (pending_write \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<noteq> {}) 
          (acquired True xs \<O>) (flush xs m) ys \<and>
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<noteq> {}
        \<longrightarrow> outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ys = {} ))"
apply (induct xs)
apply  clarsimp
subgoal for a xs m pending_write \<O>
apply (case_tac a)
apply (auto simp add: outstanding_refs_append acquired_reads_append
dest: acquired_reads_mono_in acquired_pending_write_mono_in acquired_reads_mono' acquired_mono_in)
done
done


lemma reads_consistent_mem_eq_on_non_volatile_reads:
  assumes mem_eq: "\<forall>a \<in> A. m' a = m a"
  assumes subset: "outstanding_refs (is_non_volatile_Read\<^sub>s\<^sub>b) sb \<subseteq> A"
  \<comment> \<open>We could be even more restrictive here, only the non volatile reads that are
        not buffered in @{term "sb"} have to be the same.\<close>
  assumes consis_m: "reads_consistent pending_write \<O> m sb"
  shows "reads_consistent pending_write \<O> m' sb"
using mem_eq subset consis_m 
proof (induct sb arbitrary: m' m pending_write \<O>)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  note mem_eq = \<open>\<forall>a \<in> A. m' a = m a\<close>
  note subset = \<open>outstanding_refs (is_non_volatile_Read\<^sub>s\<^sub>b) (r#sb) \<subseteq> A\<close>
  note consis_m = \<open>reads_consistent pending_write \<O> m (r#sb)\<close>

  from subset have subset': "outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> A"
    by (auto simp add: Write\<^sub>s\<^sub>b)
  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a sop v A' L R W)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A. (m'(a:=v)) a' = (m(a:=v)) a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case True
      from consis_m obtain
	consis': "reads_consistent True (\<O> \<union> A' - R) (m(a := v)) sb" and
        no_volatile_Read\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}" 
	by (simp add: Write\<^sub>s\<^sub>b True)

      from Cons.hyps [OF mem_eq' subset' consis']
      have "reads_consistent True (\<O> \<union> A' - R) (m'(a := v)) sb".
      with no_volatile_Read\<^sub>s\<^sub>b
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      from consis_m obtain consis': "reads_consistent pending_write \<O> (m(a := v)) sb" 
	by (simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF mem_eq' subset' consis']
      have "reads_consistent pending_write \<O> (m'(a := v)) sb".
      then
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A. m' a' = m a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case True
      from consis_m obtain	
	consis': "reads_consistent pending_write \<O> m sb"  
	by (simp add: Read\<^sub>s\<^sub>b True)
      from Cons.hyps [OF mem_eq' subset' consis']
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b True)
    next
      case False
      from consis_m obtain	
	consis': "reads_consistent pending_write \<O> m sb"  and v: "(pending_write \<or> a \<in> \<O>) \<longrightarrow> v=m a" 
	by (simp add: Read\<^sub>s\<^sub>b False)
      from mem_eq subset Read\<^sub>s\<^sub>b have "m' a = m a"
	by (auto simp add: False)
      with Cons.hyps [OF mem_eq' subset' consis'] v
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b False)
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed



lemma volatile_reads_consistent_mem_eq_on_volatile_reads:
  assumes mem_eq: "\<forall>a \<in> A. m' a = m a"
  assumes subset: "outstanding_refs (is_volatile_Read\<^sub>s\<^sub>b) sb \<subseteq> A"
  \<comment> \<open>We could be even more restrictive here, only the non volatile reads that are
        not buffered in @{term "sb"} have to be the same.\<close>
  assumes consis_m: "volatile_reads_consistent m sb"
  shows "volatile_reads_consistent m' sb"
using mem_eq subset consis_m 
proof (induct sb arbitrary: m' m)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  note mem_eq = \<open>\<forall>a \<in> A. m' a = m a\<close>
  note subset = \<open>outstanding_refs (is_volatile_Read\<^sub>s\<^sub>b) (r#sb) \<subseteq> A\<close>
  note consis_m = \<open>volatile_reads_consistent m (r#sb)\<close>

  from subset have subset': "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb \<subseteq> A"
    by (auto simp add: Write\<^sub>s\<^sub>b)
  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a sop v A' L R W)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A. (m'(a:=v)) a' = (m(a:=v)) a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case True
      from consis_m obtain
	consis': "volatile_reads_consistent (m(a := v)) sb"
	by (simp add: Write\<^sub>s\<^sub>b True)

      from Cons.hyps [OF mem_eq' subset' consis']
      have "volatile_reads_consistent (m'(a := v)) sb".
      then
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      from consis_m obtain consis': "volatile_reads_consistent (m(a := v)) sb" 
	by (simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF mem_eq' subset' consis']
      have "volatile_reads_consistent (m'(a := v)) sb".
      then
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A. m' a' = m a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case False
      from consis_m obtain	
	consis': "volatile_reads_consistent m sb"  
	by (simp add: Read\<^sub>s\<^sub>b False)
      from Cons.hyps [OF mem_eq' subset' consis']
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b False)
    next
      case True
      from consis_m obtain	
	consis': "volatile_reads_consistent m sb"  and v: "v=m a" 
	by (simp add: Read\<^sub>s\<^sub>b True)
      from mem_eq subset Read\<^sub>s\<^sub>b v have "v = m' a"
	by (auto simp add: True)
      with Cons.hyps [OF mem_eq' subset' consis'] 
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b True)
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed

locale valid_reads =
fixes m::"memory"  and ts::"('p, 'p store_buffer,bool,owns,rels) thread_config list" 
assumes valid_reads: "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
          \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
            reads_consistent False \<O> m sb"

lemma valid_reads_Cons: "valid_reads m (t#ts) = 
  (let (_,_,_,sb,_,\<O>,_) = t in reads_consistent False \<O> m sb \<and> valid_reads m ts)"
apply (auto simp add: valid_reads_def)
subgoal for p' is' \<theta>' sb' \<D>' \<O>' \<R>' i p "is" \<theta> sb \<D> \<O> \<R>
apply (case_tac i)
apply auto
done
done



text \<open>\<open>Read\<^sub>s\<^sub>bs\<close> and writes have in the store-buffer have to conform to the 
  valuation of temporaries.\<close>
context program
begin
fun history_consistent:: "tmps \<Rightarrow> 'p \<Rightarrow> 'p store_buffer \<Rightarrow> bool"
where
  "history_consistent \<theta> p [] = True"
| "history_consistent \<theta> p (r#rs) =
    (case r of
       Read\<^sub>s\<^sub>b vol a t v \<Rightarrow> 
         (case \<theta> t of Some v' \<Rightarrow> v=v' \<and> history_consistent \<theta> p rs | _ \<Rightarrow> False) 
     | Write\<^sub>s\<^sub>b vol a (D,f) v _ _ _ _ \<Rightarrow> 
           D \<subseteq> dom \<theta> \<and> f \<theta> = v \<and> D \<inter> read_tmps rs = {} \<and> history_consistent \<theta> p rs
     | Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 is \<Rightarrow> p\<^sub>1=p \<and> 
                           \<theta>|`(dom \<theta> - read_tmps rs)\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2,is) \<and> 
                           history_consistent \<theta> p\<^sub>2 rs
     | _ \<Rightarrow> history_consistent \<theta> p rs)"
end

fun hd_prog:: "'p \<Rightarrow> 'p store_buffer \<Rightarrow> 'p"
where
  "hd_prog p [] = p"
| "hd_prog p (i#is) = (case i of
      Prog\<^sub>s\<^sub>b p' _ _ \<Rightarrow> p'
    | _ \<Rightarrow> hd_prog p is)" 

fun last_prog:: "'p \<Rightarrow> 'p store_buffer \<Rightarrow> 'p"
where
  "last_prog p [] = p"
| "last_prog p (i#is) = (case i of
      Prog\<^sub>s\<^sub>b _ p' _ \<Rightarrow> last_prog p' is
    | _ \<Rightarrow> last_prog p is)" 

locale valid_history = program +
constrains 
  program_step :: "tmps \<Rightarrow> 'p \<Rightarrow> 'p \<times> instrs \<Rightarrow> bool"  
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list" 
assumes valid_history: "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
          \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
            program.history_consistent program_step \<theta> (hd_prog p sb) sb"

fun data_dependency_consistent_instrs:: "addr set \<Rightarrow> instrs \<Rightarrow> bool"
where
  "data_dependency_consistent_instrs T [] = True"
| "data_dependency_consistent_instrs T (i#is) =
     (case i of
        Write volatile a (D,f) _ _ _ _ \<Rightarrow> D \<subseteq> T \<and> D \<inter> load_tmps is = {} \<and> data_dependency_consistent_instrs T is
      | RMW a t (D,f) cond ret _ _ _ _ \<Rightarrow> D \<subseteq> T \<and> D \<inter> load_tmps is = {} \<and> data_dependency_consistent_instrs (insert t T) is
      | Read _ _ t \<Rightarrow> data_dependency_consistent_instrs (insert t T) is
      | _ \<Rightarrow> data_dependency_consistent_instrs T is)"

lemma data_dependency_consistent_mono:
"\<And> T T'. \<lbrakk>data_dependency_consistent_instrs T is; T \<subseteq> T'\<rbrakk> \<Longrightarrow> data_dependency_consistent_instrs T' is"
apply (induct "is")
apply clarsimp
subgoal for a "is" T T'
apply (case_tac a)
apply     clarsimp
          subgoal for volatile a' t
          apply (drule_tac a=t in insert_mono)
          apply clarsimp
          done
apply    fastforce
apply   clarsimp
        subgoal for a' t D f cond ret A L R W 
        apply (frule_tac a=t in insert_mono)
        apply fastforce
        done
apply  fastforce
apply fastforce
done
done


lemma data_dependency_consistent_instrs_append:
  "\<And>ys T . data_dependency_consistent_instrs T (xs@ys) =
       (data_dependency_consistent_instrs T xs \<and> 
        data_dependency_consistent_instrs (T \<union> load_tmps xs) ys \<and>
        load_tmps ys \<inter> \<Union>(fst ` store_sops xs) = {})"
apply (induct xs)
apply (auto split: instr.splits simp add: load_tmps_append intro: data_dependency_consistent_mono)
done

locale valid_data_dependency =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list" 
assumes data_dependency_consistent_instrs: 
  "\<And>i p is \<O> \<D> \<theta> sb. 
          \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
            data_dependency_consistent_instrs (dom \<theta>) is"
assumes load_tmps_write_tmps_distinct: 
  "\<And>i p is \<O> \<D> \<theta> sb. 
          \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
            load_tmps is \<inter> \<Union>(fst ` write_sops sb) = {}"

locale load_tmps_fresh =
fixes ts::"('p, 'p store_buffer,bool,owns,rels) thread_config list" 
assumes load_tmps_fresh: 
  "\<And>i p is \<O> \<D> \<theta> sb. 
          \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
            load_tmps is \<inter> dom \<theta> = {}"

fun acquired_by_instrs :: "instrs \<Rightarrow> addr set \<Rightarrow> addr set"
where
  "acquired_by_instrs [] A = A"
| "acquired_by_instrs (i#is) A = 
   (case i of
      Read _ _ _ \<Rightarrow> acquired_by_instrs is A
    | Write volatile _ _ A' L R W \<Rightarrow> acquired_by_instrs is (if volatile then (A \<union> A' - R) else A)
    | RMW a t sop cond ret A' L R W \<Rightarrow>  acquired_by_instrs is {}
    | Fence   \<Rightarrow> acquired_by_instrs is {}
    | Ghost A' L R W \<Rightarrow> acquired_by_instrs is (A \<union> A' - R))"

fun acquired_loads :: "bool \<Rightarrow> instrs \<Rightarrow> addr set \<Rightarrow> addr set"
where
  "acquired_loads pending_write [] A = {}"
| "acquired_loads pending_write (i#is) A =
   (case i of
      Read volatile a _ \<Rightarrow> (if pending_write \<and> \<not> volatile \<and> a \<in> A 
                            then insert a (acquired_loads pending_write is A)
                            else acquired_loads pending_write is A)
    | Write volatile _ _ A' L R W \<Rightarrow> (if volatile then acquired_loads True is (if pending_write then (A \<union> A' - R) else {})
                             else acquired_loads pending_write is A)
    | RMW a t sop cond ret A' L R W \<Rightarrow>  acquired_loads pending_write is {}
    | Fence   \<Rightarrow> acquired_loads pending_write is {}
    | Ghost A' L R W \<Rightarrow> acquired_loads pending_write is (A \<union> A' - R))"

lemma acquired_by_instrs_mono: 
  "\<And> A B. A \<subseteq> B \<Longrightarrow> acquired_by_instrs is A \<subseteq> acquired_by_instrs is B"
apply (induct "is")
apply  simp
subgoal for a "is" A B
apply (case_tac a)
apply      clarsimp
apply     clarsimp
          subgoal for volatile a' D f A' L R W x 
          apply (drule_tac C=A' in union_mono_aux)
          apply (drule_tac C="R" in set_minus_mono_aux)
          apply blast
          done
apply   clarsimp
apply  clarsimp
apply clarsimp
subgoal for A' L R W x
apply (drule_tac C=A' in union_mono_aux)
apply (drule_tac C="R" in set_minus_mono_aux)
apply blast
done
done
done

lemma acquired_by_instrs_mono_in:
  assumes x_in: "x \<in> acquired_by_instrs is A" 
  assumes sub: "A \<subseteq> B" 
  shows "x \<in> acquired_by_instrs is B"
using acquired_by_instrs_mono [OF sub, of "is"] x_in
by blast


locale enough_flushs =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list" 
assumes clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b: 
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
     \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);\<not> \<D>\<rbrakk> \<Longrightarrow> 
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {})"

fun prog_instrs:: "'p store_buffer \<Rightarrow> instrs"
where 
  "prog_instrs [] = []"
 |"prog_instrs (i#is) = (case i of
    Prog\<^sub>s\<^sub>b _ _ is' \<Rightarrow> is' @ prog_instrs is
   | _ \<Rightarrow> prog_instrs is)"

fun instrs:: "'p store_buffer \<Rightarrow> instrs"
where
  "instrs [] = []"
| "instrs (i#is) = (case i of
     Write\<^sub>s\<^sub>b volatile a sop v A L R W \<Rightarrow> Write volatile a sop A L R W# instrs is
   | Read\<^sub>s\<^sub>b volatile a t v \<Rightarrow> Read volatile a t # instrs is
   | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> Ghost A L R W# instrs is
   | _ \<Rightarrow> instrs is)"

locale causal_program_history =
fixes "is\<^sub>s\<^sub>b" and sb
assumes causal_program_history: 
  "\<And>sb\<^sub>1 sb\<^sub>2. sb=sb\<^sub>1@sb\<^sub>2 \<Longrightarrow> \<exists>is. instrs sb\<^sub>2 @ is\<^sub>s\<^sub>b = is @ prog_instrs sb\<^sub>2"

lemma causal_program_history_empty [simp]: "causal_program_history is []"
  by (rule causal_program_history.intro) simp

lemma causal_program_history_suffix:
  "causal_program_history is\<^sub>s\<^sub>b (sb@sb') \<Longrightarrow> causal_program_history is\<^sub>s\<^sub>b sb'"
  by (auto simp add: causal_program_history_def)

locale valid_program_history = 
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list" 
assumes valid_program_history: 
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
     \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
      causal_program_history is sb"

assumes valid_last_prog:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
     \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
      last_prog p sb = p"

lemma (in valid_program_history) valid_program_history_nth_update:
 "\<lbrakk>i < length ts; causal_program_history is sb; last_prog p sb = p\<rbrakk> 
  \<Longrightarrow> 
   valid_program_history (ts [i:=(p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
  by (rule valid_program_history.intro)
     (auto dest: valid_program_history valid_last_prog
    simp add: nth_list_update split: if_split_asm)

lemma (in outstanding_non_volatile_refs_owned_or_read_only)
  outstanding_non_volatile_refs_owned_instructions_read_value_independent:
 "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
     outstanding_non_volatile_refs_owned_or_read_only \<S> (ts[i := (p',is',\<theta>',sb,\<D>',\<O>,\<R>')])"
  by (unfold_locales)
     (auto dest: outstanding_non_volatile_refs_owned_or_read_only 
       simp add:  nth_list_update split: if_split_asm)

lemma (in outstanding_non_volatile_refs_owned_or_read_only)
  outstanding_non_volatile_refs_owned_or_read_only_nth_update:
 "\<And>i is \<O> \<D> \<R>  \<theta> sb. 
   \<lbrakk>i < length ts; non_volatile_owned_or_read_only False \<S> \<O> sb\<rbrakk> \<Longrightarrow> 
     outstanding_non_volatile_refs_owned_or_read_only \<S> (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
by (unfold_locales)
   (auto dest: outstanding_non_volatile_refs_owned_or_read_only 
       simp add:  nth_list_update split: if_split_asm)

lemma (in outstanding_volatile_writes_unowned_by_others)
  outstanding_volatile_writes_unowned_by_others_instructions_read_value_independent:
 "\<And>i p is \<O> \<R> \<D>  \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
     outstanding_volatile_writes_unowned_by_others (ts[i := (p',is',\<theta>',sb,\<D>',\<O>,\<R>')])"
  by (unfold_locales)
     (auto dest: outstanding_volatile_writes_unowned_by_others 
       simp add:  nth_list_update split: if_split_asm)

lemma (in read_only_reads_unowned)
  read_only_unowned_instructions_read_value_independent:
 "\<And>i p is \<O> \<R> \<D>  \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> \<Longrightarrow> 
     read_only_reads_unowned (ts[i := (p',is',\<theta>',sb,\<D>',\<O>,\<R>')])"
  by (unfold_locales)
     (auto dest: read_only_reads_unowned
       simp add:  nth_list_update split: if_split_asm)



lemma Write\<^sub>s\<^sub>b_in_outstanding_refs:
  "Write\<^sub>s\<^sub>b True a sop v A L R W \<in> set xs \<Longrightarrow> a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
  by (induct xs) (auto split:memref.splits)


lemma (in outstanding_volatile_writes_unowned_by_others)
  outstanding_volatile_writes_unowned_by_others_store_buffer:
 "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); 
    outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb' \<subseteq> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb;
    all_acquired sb' \<subseteq> all_acquired sb\<rbrakk> \<Longrightarrow> 
     outstanding_volatile_writes_unowned_by_others (ts[i := (p',is',\<theta>',sb',\<D>',\<O>,\<R>')])"
  apply (unfold_locales)
  apply (fastforce dest: outstanding_volatile_writes_unowned_by_others 
         simp add:  nth_list_update split: if_split_asm)
  done


lemma (in ownership_distinct)
  ownership_distinct_instructions_read_value_store_buffer_independent:
 "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
     all_acquired sb' \<subseteq> all_acquired sb\<rbrakk> \<Longrightarrow> 
     ownership_distinct (ts[i := (p',is',\<theta>',sb',\<D>',\<O>,\<R>')])"
  by (unfold_locales)
     (auto dest: ownership_distinct 
       simp add:  nth_list_update split: if_split_asm)


lemma (in ownership_distinct)
  ownership_distinct_nth_update:
 "\<And>i p is \<O> \<R> \<D> xs sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
    \<forall>j < length ts. i\<noteq>j \<longrightarrow> (let (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j) = ts!j 
          in (\<O>' \<union> all_acquired sb') \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) ={}) \<rbrakk> \<Longrightarrow> 
     ownership_distinct (ts[i := (p',is',\<theta>',sb',\<D>',\<O>',\<R>')])"
  apply (unfold_locales)
  apply (clarsimp simp add: nth_list_update split: if_split_asm)
  apply   (force dest: ownership_distinct simp add: Let_def)
  apply  (fastforce dest: ownership_distinct simp add: Let_def)
  apply (fastforce dest: ownership_distinct simp add: Let_def)
  done


lemma (in valid_write_sops) valid_write_sops_nth_update:
          "\<lbrakk>i < length ts; \<forall>sop \<in> write_sops sb. valid_sop sop\<rbrakk> \<Longrightarrow> 
            valid_write_sops (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold valid_write_sops_def)
     (auto dest: valid_write_sops simp add: nth_list_update split: if_split_asm)

lemma (in valid_store_sops) valid_store_sops_nth_update:
          "\<lbrakk>i < length ts; \<forall>sop \<in> store_sops is. valid_sop sop\<rbrakk> \<Longrightarrow> 
            valid_store_sops (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold valid_store_sops_def)
     (auto dest: valid_store_sops simp add: nth_list_update split: if_split_asm)

lemma (in valid_sops) valid_sops_nth_update:
          "\<lbrakk>i < length ts; \<forall>sop \<in> write_sops sb. valid_sop sop;
            \<forall>sop \<in> store_sops is. valid_sop sop\<rbrakk> \<Longrightarrow> 
            valid_sops (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold valid_sops_def valid_write_sops_def valid_store_sops_def)
     (auto dest: valid_write_sops valid_store_sops 
       simp add: nth_list_update split: if_split_asm)


lemma (in valid_data_dependency) valid_data_dependency_nth_update:
          "\<lbrakk>i < length ts; data_dependency_consistent_instrs (dom \<theta>) is; 
            load_tmps is \<inter> \<Union>(fst ` write_sops sb) = {}\<rbrakk> \<Longrightarrow> 
            valid_data_dependency (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
  by (unfold valid_data_dependency_def)
     (force dest: data_dependency_consistent_instrs load_tmps_write_tmps_distinct 
         simp add: nth_list_update split: if_split_asm)

lemma (in enough_flushs) enough_flushs_nth_update:
 "\<lbrakk>i < length ts; 
   \<not> \<D> \<longrightarrow> (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {})
  \<rbrakk> \<Longrightarrow> 
     enough_flushs (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"

  apply (unfold_locales)
  apply  (force simp add: nth_list_update split: if_split_asm dest: clean_no_outstanding_volatile_Write\<^sub>s\<^sub>b)
  done

lemma (in outstanding_non_volatile_writes_unshared) 
  outstanding_non_volatile_writes_unshared_nth_update:
          "\<lbrakk>i < length ts; non_volatile_writes_unshared \<S> sb\<rbrakk> \<Longrightarrow> 
            outstanding_non_volatile_writes_unshared \<S> (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: outstanding_non_volatile_writes_unshared 
       simp add: nth_list_update split: if_split_asm)

lemma (in sharing_consis) 
  sharing_consis_nth_update:
          "\<lbrakk>i < length ts; sharing_consistent \<S> \<O> sb\<rbrakk> \<Longrightarrow> 
            sharing_consis \<S> (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: sharing_consis 
       simp add: nth_list_update split: if_split_asm)



lemma (in no_outstanding_write_to_read_only_memory) 
  no_outstanding_write_to_read_only_memory_nth_update:
          "\<lbrakk>i < length ts; no_write_to_read_only_memory \<S> sb\<rbrakk> \<Longrightarrow> 
            no_outstanding_write_to_read_only_memory \<S> (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest:  no_outstanding_write_to_read_only_memory
       simp add: nth_list_update split: if_split_asm)

lemma in_Union_image_nth_conv: "a \<in> \<Union> (f ` set xs) \<Longrightarrow> \<exists>i. i < length xs \<and> a \<in> f (xs!i)"    
  by (auto simp add: in_set_conv_nth)

lemma in_Inter_image_nth_conv: "a \<in> \<Inter> (f ` set xs) = (\<forall>i < length xs. a \<in> f (xs!i))"    
  by (force simp add:  in_set_conv_nth)



lemma release_ownership_nth_update:
  assumes R_subset: "R \<subseteq> \<O>"
  shows "\<And>i. \<lbrakk>i < length ts; ts!i = (p,is,xs,sb,\<D>,\<O>,\<R>);
          ownership_distinct ts\<rbrakk>
   \<Longrightarrow>  \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set (ts[i:=(p',is',xs',sb',\<D>',\<O> - R,\<R>')]))
        = ((\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts))  - R )"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  note i_bound = \<open>i < length (t # ts)\<close>
  note ith = \<open>(t # ts) ! i = (p,is,xs, sb, \<D>, \<O>,\<R>)\<close>
  note dist = \<open>ownership_distinct (t#ts)\<close>
  then interpret ownership_distinct "t#ts".
  from dist
  have dist': "ownership_distinct ts"
    by (rule ownership_distinct_tl)
  show ?case
  proof (cases i)
    case 0
    from ith 0 have t: "t = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    have "R \<inter> (\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts)) = {}"
    proof -
      {
	fix x
	assume x_R: "x \<in> R"
	assume x_ls: "x \<in> (\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts))"
	then obtain j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j where
	  j_bound: "j < length ts" and
	  jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	  x_in: "x \<in> \<O>\<^sub>j"
	  by (fastforce simp add: in_set_conv_nth )
	from  j_bound jth 0 
	have "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}"
	  apply -
	  apply (rule ownership_distinct [OF i_bound _ _ ith, of "Suc j"])
	  apply clarsimp+
	  apply blast
	  done
	
	with x_R R_subset x_in have False
	  by auto
      }
      thus ?thesis
	by blast
    qed
    then
    show ?thesis
      by (auto simp add: 0 t)  
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where t: "t = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases t)

    have n_bound: "n < length ts"
      using i_bound by (simp add: Suc)
    have nth: "ts!n = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      using ith by (simp add: Suc)
    
    have "R \<inter> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l) = {}"
    proof -
      {
	fix x
	assume x_R: "x \<in> R"
	assume x_owns\<^sub>l: "x \<in> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l)"
	from t 
	have "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l)= {}"
	  apply -
	  apply (rule ownership_distinct [OF i_bound _ _ ith, of "0"])
	  apply (auto simp add: Suc)
	  done
	with x_owns\<^sub>l x_R R_subset have False
	  by auto
      }
      thus ?thesis
	by blast
    qed
    with Cons.hyps [OF n_bound nth dist']
    show ?thesis
      by (auto simp add: Suc t)
  qed
qed
   
lemma acquire_ownership_nth_update:
  shows "\<And>i. \<lbrakk>i < length ts; ts!i = (p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk>
   \<Longrightarrow>  \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set (ts[i:=(p',is',xs',sb',\<D>',\<O> \<union> A,\<R>')]))
        = ((\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts))  \<union> A )"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  note i_bound = \<open>i < length (t # ts)\<close>
  note ith = \<open>(t # ts) ! i = (p,is, xs, sb, \<D>, \<O>, \<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have t: "t = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    show ?thesis
      by (auto simp add: 0 t)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where t: "t = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases t)

    have n_bound: "n < length ts"
      using i_bound by (simp add: Suc)
    have nth: "ts!n = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      using ith by (simp add: Suc)
    from Cons.hyps [OF n_bound nth]
    show ?thesis
      by (auto simp add: Suc t)
  qed
qed

lemma acquire_release_ownership_nth_update:
  assumes R_subset: "R \<subseteq> \<O>"
  shows "\<And>i. \<lbrakk>i < length ts; ts!i = (p,is,xs,sb,\<D>,\<O>,\<R>);
          ownership_distinct ts\<rbrakk>
   \<Longrightarrow>  \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set (ts[i:=(p',is',xs',sb',\<D>',\<O> \<union> A - R,\<R>')]))
        = ((\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts))  \<union> A - R )"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  note i_bound = \<open>i < length (t # ts)\<close>
  note ith = \<open>(t # ts) ! i = (p,is, xs, sb,\<D>, \<O>,\<R>)\<close>
  note dist = \<open>ownership_distinct (t#ts)\<close>
  then interpret ownership_distinct "t#ts".
  from dist
  have dist': "ownership_distinct ts"
    by (rule ownership_distinct_tl)
  show ?case
  proof (cases i)
    case 0
    from ith 0 have t: "t = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    have "R \<inter> (\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts)) = {}"
    proof -
      {
	fix x
	assume x_R: "x \<in> R"
	assume x_ls: "x \<in> (\<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts))"
	then obtain j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j where
	  j_bound: "j < length ts" and
	  jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	  x_in: "x \<in> \<O>\<^sub>j"
	  by (fastforce simp add: in_set_conv_nth )
	from  j_bound jth 0 
	have "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j)= {}"
	  apply -
	  apply (rule ownership_distinct [OF i_bound _ _ ith, of "Suc j"])
	  apply clarsimp+
	  apply blast
	  done
	
	with x_R R_subset x_in have False
	  by auto
      }
      thus ?thesis
	by blast
    qed
    then
    show ?thesis
      by (auto simp add: 0 t)  
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where t: "t = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases t)

    have n_bound: "n < length ts"
      using i_bound by (simp add: Suc)
    have nth: "ts!n = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      using ith by (simp add: Suc)
    
    have "R \<inter> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l) = {}"
    proof -
      {
	fix x
	assume x_R: "x \<in> R"
	assume x_owns\<^sub>l: "x \<in> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l)"
	from t 
	have "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>l \<union> all_acquired sb\<^sub>l)= {}"
	  apply -
	  apply (rule ownership_distinct [OF i_bound _ _ ith, of "0"])
	  apply (auto simp add: Suc)
	  done
	with x_owns\<^sub>l x_R R_subset have False
	  by auto
      }
      thus ?thesis
	by blast
    qed
    with Cons.hyps [OF n_bound nth dist']
    show ?thesis
      by (auto simp add: Suc t)
  qed
qed



lemma (in valid_history) valid_history_nth_update:
          "\<lbrakk>i < length ts; history_consistent \<theta> (hd_prog p sb) sb \<rbrakk> \<Longrightarrow> 
            valid_history program_step (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: valid_history simp add: nth_list_update split: if_split_asm)

lemma (in valid_reads) valid_reads_nth_update:
          "\<lbrakk>i < length ts; reads_consistent False \<O> m sb \<rbrakk> \<Longrightarrow> 
            valid_reads m (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: valid_reads simp add: nth_list_update split: if_split_asm)

lemma (in load_tmps_distinct) load_tmps_distinct_nth_update:
          "\<lbrakk>i < length ts; distinct_load_tmps is\<rbrakk> \<Longrightarrow> 
            load_tmps_distinct (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: load_tmps_distinct simp add: nth_list_update split: if_split_asm)

lemma (in read_tmps_distinct) read_tmps_distinct_nth_update:
          "\<lbrakk>i < length ts; distinct_read_tmps sb\<rbrakk> \<Longrightarrow> 
            read_tmps_distinct (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: read_tmps_distinct simp add: nth_list_update split: if_split_asm)

lemma (in load_tmps_read_tmps_distinct) load_tmps_read_tmps_distinct_nth_update:
          "\<lbrakk>i < length ts; load_tmps is \<inter> read_tmps sb = {}\<rbrakk> \<Longrightarrow> 
            load_tmps_read_tmps_distinct (ts[i := (p,is,xs,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (auto dest: load_tmps_read_tmps_distinct simp add: nth_list_update split: if_split_asm)

lemma (in load_tmps_fresh) load_tmps_fresh_nth_update:
          "\<lbrakk>i < length ts; 
            load_tmps is \<inter> dom \<theta> = {}\<rbrakk> \<Longrightarrow> 
            load_tmps_fresh (ts[i := (p,is,\<theta>,sb,\<D>,\<O>,\<R>)])"
  by (unfold_locales)
     (fastforce dest: load_tmps_fresh
         simp add: nth_list_update split: if_split_asm)




fun flush_all_until_volatile_write:: 
  "('p,'p store_buffer,'dirty,'owns,'rels) thread_config list \<Rightarrow> memory \<Rightarrow> memory"
where
  "flush_all_until_volatile_write [] m = m"
| "flush_all_until_volatile_write ((_, _, _, sb,_, _)#ts) m =
     flush_all_until_volatile_write ts (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m)"

fun share_all_until_volatile_write:: 
  "('p,'p store_buffer,'dirty,'owns,'rels) thread_config list \<Rightarrow> shared \<Rightarrow> shared"
where
  "share_all_until_volatile_write [] S = S"
| "share_all_until_volatile_write ((_, _, _, sb,_,_)#ts) S =
     share_all_until_volatile_write ts (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S)"





lemma takeWhile_dropWhile_real_prefix: 
  "\<lbrakk>x \<in> set xs; \<not> P x\<rbrakk> \<Longrightarrow> \<exists>y ys. xs=takeWhile P xs @ y#ys \<and> \<not> P y \<and> dropWhile P xs = y#ys"   
  by (induct xs) auto

lemma buffered_val_witness: "buffered_val sb a = Some v \<Longrightarrow> 
  \<exists>volatile sop A L R W.  Write\<^sub>s\<^sub>b volatile a sop v A L R W \<in> set sb"
  apply (induct sb) 
  apply  simp
  apply (clarsimp split: memref.splits option.splits if_split_asm)
  apply  blast
  apply blast
  done


lemma flush_append_Read\<^sub>s\<^sub>b:
  "\<And>m. (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t v])) m)
       = flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m"
by (induct sb) (auto split: memref.splits)

lemma flush_append_write:
   "\<And>m. (flush (sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W]) m) = (flush sb m) (a:=v)"
by (induct sb) (auto split: memref.splits)

lemma flush_append_Prog\<^sub>s\<^sub>b:
"\<And>m. (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])) m) = 
       (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) "
  by (induct sb) (auto split: memref.splits)

lemma flush_append_Ghost\<^sub>s\<^sub>b:
"\<And>m. (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Ghost\<^sub>s\<^sub>b A L R W])) m) = 
       (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) "
  by (induct sb) (auto split: memref.splits)

lemma share_append: "\<And>S. share (xs@ys) S = share ys (share xs S)"
  by (induct xs) (auto split: memref.splits)

lemma share_append_Read\<^sub>s\<^sub>b:
  "\<And>S. (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Read\<^sub>s\<^sub>b volatile a t v])) S)
       = share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S"
 by (induct sb) (auto split: memref.splits)

lemma share_append_Write\<^sub>s\<^sub>b:
  "\<And>S. (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W])) S)
       = share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S"
by (induct sb) (auto split: memref.splits)

lemma share_append_Prog\<^sub>s\<^sub>b:
"\<And>S. (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])) S) = 
       (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) "
  by (induct sb) (auto split: memref.splits)

lemma in_acquired_no_pending_write_outstanding_write: 
  "a \<in> acquired False sb A \<Longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}"
apply (induct sb)
apply (auto split: memref.splits)
done

lemma flush_buffered_val_conv:
  "\<And>m. flush sb m a = (case buffered_val sb a of None \<Rightarrow> m a | Some v \<Rightarrow> v)"
  by (induct sb) (auto split: memref.splits option.splits)

(*
lemma reads_consistent_unbuffered_snoc: 
  "\<And>m. buffered_val sb a = None \<Longrightarrow> m a = v \<Longrightarrow> reads_consistent m sb \<Longrightarrow>
        volatile \<longrightarrow> 
          outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> 
        \<not> volatile \<longrightarrow> a \<notin> acquired False sb {}
  \<Longrightarrow> reads_consistent m (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
  by (simp add: reads_consistent_append flush_buffered_val_conv)
*)

lemma reads_consistent_unbuffered_snoc: 
  "\<And>m. buffered_val sb a = None \<Longrightarrow> m a = v \<Longrightarrow> reads_consistent pending_write \<O> m sb \<Longrightarrow>
        volatile \<longrightarrow> 
          outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} 
  \<Longrightarrow> reads_consistent pending_write \<O> m (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
  by (simp add: reads_consistent_append flush_buffered_val_conv)

lemma reads_consistent_buffered_snoc: 
  "\<And>m. buffered_val sb a = Some v \<Longrightarrow>  reads_consistent pending_write \<O> m sb \<Longrightarrow>
        volatile \<longrightarrow> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} 
  \<Longrightarrow> reads_consistent pending_write \<O> m (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
  by (simp add: reads_consistent_append flush_buffered_val_conv)

lemma reads_consistent_snoc_Write\<^sub>s\<^sub>b:
  "\<And>m. reads_consistent pending_write \<O> m sb \<Longrightarrow> 
  reads_consistent pending_write \<O> m (sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W])"
  by (simp add: reads_consistent_append)

lemma reads_consistent_snoc_Prog\<^sub>s\<^sub>b:
  "\<And>m. reads_consistent pending_write \<O> m sb \<Longrightarrow> reads_consistent pending_write \<O> m (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])"
  by (simp add: reads_consistent_append)

lemma reads_consistent_snoc_Ghost\<^sub>s\<^sub>b:
  "\<And>m. reads_consistent pending_write \<O> m sb \<Longrightarrow> reads_consistent pending_write \<O> m (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
  by (simp add: reads_consistent_append)

(* FIXME: move to map.thy *)
lemma restrict_map_id [simp]:"m |` dom m = m"
  apply (rule ext)
  subgoal for x
  apply (case_tac "m x")
  apply (auto simp add: restrict_map_def domIff)
  done
  done

lemma flush_all_until_volatile_write_Read_commute:
  shows "\<And>m i.  \<lbrakk>i < length ls; ls!i=(p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>,\<R>)
    \<rbrakk>  
   \<Longrightarrow> 
    flush_all_until_volatile_write 
       (ls[i := (p,is , \<theta>(t\<mapsto>v), sb @ [Read\<^sub>s\<^sub>b volatile a t v],\<D>',\<O>',\<R>')]) m =
    flush_all_until_volatile_write ls m"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 flush_append_Read\<^sub>s\<^sub>b del: fun_upd_apply )
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)
    from i_bound ith
    have "flush_all_until_volatile_write
      (ls[n := (p,is , \<theta>(t\<mapsto>v), sb @ [Read\<^sub>s\<^sub>b volatile a t v],\<D>',\<O>',\<R>') ]) 
      (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
      flush_all_until_volatile_write ls (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done
    
    then
    show ?thesis
      by (simp add: Suc l del: fun_upd_apply)
  qed
qed

lemma flush_all_until_volatile_write_append_Ghost_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p',is',\<theta>', sb@[Ghost\<^sub>s\<^sub>b A L R W], \<D>', \<O>',\<R>')]) m
       = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 flush_append_Ghost\<^sub>s\<^sub>b del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith
    have "flush_all_until_volatile_write 
              (ts[n := (p',is',\<theta>', sb@[Ghost\<^sub>s\<^sub>b A L R W], \<D>', \<O>',\<R>')])
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
         flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done

    then show ?thesis
      by (simp add: Suc l)
  qed
qed


lemma update_commute:
assumes g_unchanged: "\<forall>a m. a \<notin> G \<longrightarrow> g m a = m a"
assumes g_independent: "\<forall>a m. a \<in> G \<longrightarrow> g (f m) a = g m a"
assumes f_unchanged: "\<forall>a m. a \<notin> F \<longrightarrow> f m a = m a"
assumes f_independent: "\<forall>a m. a \<in> F \<longrightarrow> f (g m) a = f m a"
assumes disj: "G \<inter> F = {}"
shows "f (g m) = g (f m)"
proof 
  fix a
  show "f (g m) a = g (f m) a"
  proof (cases "a \<in> G")
    case True
    with disj have a_notin_F: "a \<notin> F"
      by blast
    from f_unchanged [rule_format, OF a_notin_F, of "g m"]
    have "f (g m) a = g m a" .
    also
    from g_independent [rule_format, OF True]
    have "\<dots> = g (f m) a" by simp
    finally show ?thesis .
  next
    case False
    note a_notin_G = this
    show ?thesis
    proof (cases "a \<in> F")
      case True
      from f_independent [rule_format, OF True]
      have "f (g m) a = f m a" by simp
      also
      from g_unchanged [rule_format, OF a_notin_G]
      have "\<dots> = g (f m) a"
	by simp
      finally show ?thesis .
    next
      case False
      from f_unchanged [rule_format, OF False]
      have "f (g m) a = g m a".
      also
      from g_unchanged [rule_format, OF a_notin_G]
      have "\<dots> = m a" .
      also       
      from f_unchanged [rule_format, OF False]
      have "\<dots> = f m a" by simp
      also
      from g_unchanged [rule_format, OF a_notin_G]
      have "\<dots> = g (f m) a"
	by simp
      finally show ?thesis .
    qed
  qed
qed
      
      
lemma update_commute':
assumes g_unchanged: "\<forall>a m. a \<notin> G \<longrightarrow> g m a = m a"
assumes g_independent: "\<forall>a m\<^sub>1 m\<^sub>2. a \<in> G \<longrightarrow> g m\<^sub>1 a = g m\<^sub>2 a"
assumes f_unchanged: "\<forall>a m. a \<notin> F \<longrightarrow> f m a = m a"
assumes f_independent: "\<forall>a m\<^sub>1 m\<^sub>2. a \<in> F \<longrightarrow> f m\<^sub>1 a = f m\<^sub>2 a"
assumes disj: "G \<inter> F = {}"
shows "f (g m) = g (f m)"
proof -
  from g_independent have g_ind': "\<forall>a m. a \<in> G \<longrightarrow> g (f m) a = g m a" by blast
  from f_independent have f_ind': "\<forall>a m. a \<in> F \<longrightarrow> f (g m) a = f m a" by blast
  from update_commute [OF g_unchanged g_ind' f_unchanged f_ind' disj]
  show ?thesis .
qed

lemma flush_unchanged_addresses: "\<And>m. a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb \<Longrightarrow> flush sb m a = m a"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  note a_notin = \<open>a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (r#sb)\<close>
  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a' sop v)
    from a_notin obtain neq_a_a': "a\<noteq>a'" and a_notin': "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
      by (simp add: Write\<^sub>s\<^sub>b)
    from Cons.hyps [OF a_notin', of "m(a':=v)"] neq_a_a'
    show ?thesis
      apply (simp add: Write\<^sub>s\<^sub>b del: fun_upd_apply)
      apply simp
      done
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    from a_notin obtain a_notin': "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
      by (simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF a_notin', of "m"] 
    show ?thesis
      by (simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by simp
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by simp
  qed
qed

lemma flushed_values_mem_independent:
  "\<And>m m' a. a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb \<Longrightarrow>  flush sb m' a = flush sb m a"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a' sop' v')
    have "flush sb (m'(a' := v')) a' = flush sb (m(a' := v')) a'"
    proof (cases "a' \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb")
      case True
      from Cons.hyps [OF this]
      show ?thesis .
    next
      case False
      from flush_unchanged_addresses [OF False]
      show ?thesis
	by simp
    qed
    with Cons.hyps Cons.prems
    show ?thesis
      by (auto simp add: Write\<^sub>s\<^sub>b)
  next
    case Read\<^sub>s\<^sub>b thus ?thesis using Cons
      by auto
  next
    case Prog\<^sub>s\<^sub>b thus ?thesis using Cons
      by auto
  next
    case Ghost\<^sub>s\<^sub>b thus ?thesis using Cons
      by auto
  qed
qed

lemma flush_all_until_volatile_write_unchanged_addresses:
  "\<And>m. a \<notin> \<Union>((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls) \<Longrightarrow>
       flush_all_until_volatile_write ls m a = m a"
proof (induct ls)
  case Nil thus ?case by simp
next
  case (Cons l ls)
  obtain p "is" \<O> \<R> \<D> xs sb where l: "l=(p,is,xs,sb,\<D>,\<O>,\<R>)"
    by (cases l)
  note \<open>a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set (l#ls))\<close>
  then obtain
    a_notin_sb: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" and
    a_notin_ls: "a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls)"
    by (auto simp add: l)

  
  from Cons.hyps [OF a_notin_ls]
  have "flush_all_until_volatile_write ls (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) a 
        = 
        (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) a".

  also

  from flush_unchanged_addresses [OF a_notin_sb]
  have "(flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) a = m a".
  finally
  show ?case
    by (simp add: l)
qed

lemma  notin_outstanding_non_volatile_takeWhile_lem:
  "a \<notin> outstanding_refs (Not \<circ> is_volatile) sb
        \<Longrightarrow>
        a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply (auto simp add: is_Write\<^sub>s\<^sub>b_def split: if_split_asm memref.splits)
done

lemma  notin_outstanding_non_volatile_takeWhile_lem':
  "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb
        \<Longrightarrow>
        a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply (auto simp add: is_Write\<^sub>s\<^sub>b_def split: if_split_asm memref.splits)
done

lemma notin_outstanding_non_volatile_takeWhile_Un_lem':
"a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs (Not \<circ> is_volatile) sb) ` set ls)
 \<Longrightarrow> a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls)"
proof (induct ls)
  case Nil thus ?case by simp
next
  case (Cons l ls)
  obtain p "is" \<O> \<R> \<D> xs sb where l: "l=(p,is,xs,sb,\<D>,\<O>,\<R>)"
    by (cases l)

  from Cons.prems
  obtain 
    a_notin_sb: "a \<notin> outstanding_refs (Not \<circ> is_volatile) sb" and
    a_notin_ls: "a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs (Not \<circ> is_volatile) sb) ` set ls)"
    by (force simp add: l simp del: o_apply) 
  from notin_outstanding_non_volatile_takeWhile_lem [OF a_notin_sb]
   Cons.hyps [OF a_notin_ls]
  show ?case
    by (auto simp add: l simp del: o_apply)
qed

lemma flush_all_until_volatile_write_unchanged_addresses':
  assumes  notin: "a \<notin> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs (Not \<circ> is_volatile) sb) ` set ls)"
  shows "flush_all_until_volatile_write ls m a = m a"
using notin_outstanding_non_volatile_takeWhile_Un_lem' [OF notin]
by (auto intro: flush_all_until_volatile_write_unchanged_addresses)

lemma flush_all_until_volatile_wirte_mem_independent:
  "\<And>m m'. a \<in> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                     (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls) \<Longrightarrow>
          flush_all_until_volatile_write ls m' a = flush_all_until_volatile_write ls m a"
proof (induct ls)
  case Nil thus ?case by simp
next
  case (Cons l ls)
  obtain p "is" \<O> \<R> \<D> xs sb where l: "l=(p,is,xs,sb,\<D>,\<O>,\<R>)"
    by (cases l)
  note a_in = \<open>a \<in> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                     (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set (l#ls))\<close>
  show ?case 
  proof (cases "a \<in> \<Union> ((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                     (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls)") 
    case True
    from Cons.hyps [OF this]
    show ?thesis
      by (simp add: l)
  next
    case False
    with a_in
    have "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
      by (auto simp add: l)
    from flushed_values_mem_independent [rule_format, OF this]
    have "flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m' a =
          flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m a".
    with flush_all_until_volatile_write_unchanged_addresses [OF False]
    show ?thesis
      by (auto simp add: l)
  qed
qed

lemma flush_all_until_volatile_write_buffered_val_conv: 
  assumes no_volatile_Write\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
  shows"\<And>m i. \<lbrakk>i < length ls; ls!i = (p,is,xs,sb,\<D>,\<O>,\<R>);
               
        \<forall>j < length ls. i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = ls!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) \<rbrakk> \<Longrightarrow>
      flush_all_until_volatile_write ls m a =
        (case buffered_val sb a of None \<Rightarrow> m a | Some v \<Rightarrow> v)"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,is,xs,sb,\<D>,\<O>,\<R>)\<close>
  note notin = \<open>\<forall>j < length (l#ls). i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = (l#ls)!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    from no_volatile_Write\<^sub>s\<^sub>b have take_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
      by (auto simp add: outstanding_refs_conv)

    have "a \<notin> \<Union>((\<lambda>(_,_, _, sb, _,_,_).
            outstanding_refs is_Write\<^sub>s\<^sub>b
             (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ls)" (is "a \<notin> ?LS")
    proof 
      assume "a \<in> ?LS" 
      from in_Union_image_nth_conv [OF this]
      obtain j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j "\<D>\<^sub>j" "xs\<^sub>j" "sb\<^sub>j" where 
	j_bound: "j < length ls" and
	jth: "ls!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	a_in_j: "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	by fastforce
      from a_in_j obtain v' sop' A L R W where "Write\<^sub>s\<^sub>b False a sop' v' A L R W\<in> set (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
  apply (clarsimp simp add: outstanding_refs_conv )
  subgoal for x
	apply (case_tac x)
	apply    clarsimp
	apply    (frule set_takeWhileD) 
	apply auto
	done
  done
      with notin [rule_format, of "Suc j"] j_bound jth
      show False
	by (force simp add: 0  outstanding_refs_conv is_non_volatile_Write\<^sub>s\<^sub>b_def 
	  split: memref.splits)
    qed
    from flush_all_until_volatile_write_unchanged_addresses [OF this]
    have "flush_all_until_volatile_write ls (flush sb m) a = (flush sb m) a"
      by (simp add: take_all)
    then 
    show ?thesis 
      by (simp add: 0 l take_all flush_buffered_val_conv)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l )"
      by (cases l)

    from i_bound ith notin
    have "flush_all_until_volatile_write ls
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) a
          = (case buffered_val sb a of None \<Rightarrow> 
               (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) a | Some v \<Rightarrow> v)"
      apply -
      apply (rule Cons.hyps)
      apply (force simp add: Suc Let_def simp del: o_apply)+
      done

    moreover
    from notin [rule_format, of 0] l
    have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l)"
      by (auto simp add: Let_def outstanding_refs_conv Suc )
    then
    have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l)" 
      apply (clarsimp simp add: outstanding_refs_conv is_Write\<^sub>s\<^sub>b_def split: memref.splits dest: set_takeWhileD)
      apply (frule set_takeWhileD)
      apply force
      done

    from flush_unchanged_addresses [OF this]
    have "(flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) a = m a" .

    ultimately
    show ?thesis
      by (simp add: Suc l split: option.splits)
  qed
qed


context program
begin

abbreviation sb_concurrent_step ::
  "('p,'p store_buffer,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> ('p,'p store_buffer,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> bool"
    ("_ \<Rightarrow>\<^sub>s\<^sub>b _" [60,60] 100)
where
  "sb_concurrent_step \<equiv> 
     computation.concurrent_step sb_memop_step store_buffer_step program_step (\<lambda>p p' is sb. sb)"

term "x \<Rightarrow>\<^sub>s\<^sub>b Y"

abbreviation (in program) sb_concurrent_steps::
  "('p,'p store_buffer,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> ('p,'p store_buffer,'dirty,'owns,'rels,'shared) global_config \<Rightarrow> bool"
    ("_ \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* _" [60,60] 100)
where
"sb_concurrent_steps \<equiv> sb_concurrent_step^**"

term "x \<Rightarrow>\<^sub>s\<^sub>b\<^sup>* Y"

abbreviation sbh_concurrent_step ::
  "('p,'p store_buffer,bool,owns,rels,shared) global_config \<Rightarrow> ('p,'p store_buffer,bool,owns,rels,shared) global_config \<Rightarrow> bool"
    ("_ \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h _" [60,60] 100)
where
  "sbh_concurrent_step \<equiv> 
     computation.concurrent_step sbh_memop_step flush_step program_step 
      (\<lambda>p p' is sb. sb @ [Prog\<^sub>s\<^sub>b p p' is] )"

term "x \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h Y"

abbreviation sbh_concurrent_steps::
  "('p,'p store_buffer,bool,owns,rels,shared) global_config \<Rightarrow> ('p,'p store_buffer,bool,owns,rels,shared) global_config \<Rightarrow> bool"
    ("_ \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* _" [60,60] 100)
where
"sbh_concurrent_steps \<equiv> sbh_concurrent_step^**"

term "x \<Rightarrow>\<^sub>s\<^sub>b\<^sub>h\<^sup>* Y"
end 

lemma instrs_append_Read\<^sub>s\<^sub>b:
  "instrs (sb@[Read\<^sub>s\<^sub>b volatile a t v]) = instrs sb @ [Read volatile a t]"
  by (induct sb) (auto split: memref.splits)

lemma instrs_append_Write\<^sub>s\<^sub>b:
  "instrs (sb@[Write\<^sub>s\<^sub>b volatile a sop v A L R W]) = instrs sb @ [Write volatile a sop A L R W]"
  by (induct sb) (auto split: memref.splits)

lemma instrs_append_Ghost\<^sub>s\<^sub>b:
  "instrs (sb@[Ghost\<^sub>s\<^sub>b A L R W]) = instrs sb @ [Ghost A L R W]"
  by (induct sb) (auto split: memref.splits)


lemma prog_instrs_append_Ghost\<^sub>s\<^sub>b:
  "prog_instrs (sb@[Ghost\<^sub>s\<^sub>b A L R W]) = prog_instrs sb"
  by (induct sb) (auto split: memref.splits)

lemma prog_instrs_append_Read\<^sub>s\<^sub>b:
  "prog_instrs (sb@[Read\<^sub>s\<^sub>b volatile a t v]) = prog_instrs sb "
  by (induct sb) (auto split: memref.splits)

lemma prog_instrs_append_Write\<^sub>s\<^sub>b:
  "prog_instrs (sb@[Write\<^sub>s\<^sub>b volatile a sop v A L R W]) = prog_instrs sb"
  by (induct sb) (auto split: memref.splits)

lemma hd_prog_append_Read\<^sub>s\<^sub>b:
  "hd_prog p (sb@[Read\<^sub>s\<^sub>b volatile a t v]) = hd_prog p sb"
  by (induct sb) (auto split: memref.splits)

lemma hd_prog_append_Write\<^sub>s\<^sub>b:
  "hd_prog p (sb@[Write\<^sub>s\<^sub>b volatile a sop v A L R W]) = hd_prog p sb"
  by (induct sb) (auto split: memref.splits)

lemma flush_update_other: "\<And>m. a \<notin> outstanding_refs (Not \<circ> is_volatile) sb \<Longrightarrow>
        outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {} \<Longrightarrow>
       flush sb (m(a:=v)) = (flush sb m)(a := v)"
  by (induct sb)
     (auto split: memref.splits if_split_asm simp add: fun_upd_twist)

lemma flush_update_other': "\<And>m. a \<notin> outstanding_refs (is_non_volatile_Write\<^sub>s\<^sub>b) sb \<Longrightarrow>
        outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb = {} \<Longrightarrow>
       flush sb (m(a:=v)) = (flush sb m)(a := v)"
  by (induct sb)
     (auto split: memref.splits if_split_asm simp add: fun_upd_twist)

lemma flush_update_other'': "\<And>m. a \<notin> outstanding_refs (is_non_volatile_Write\<^sub>s\<^sub>b) sb \<Longrightarrow>
        a \<notin> outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) sb \<Longrightarrow>
       flush sb (m(a:=v)) = (flush sb m)(a := v)"
  by (induct sb)
     (auto split: memref.splits if_split_asm simp add: fun_upd_twist)

lemma flush_all_until_volatile_write_update_other:     
"\<And>m. \<forall>j < length ts. 
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)) 
  \<Longrightarrow> 
  flush_all_until_volatile_write ts (m(a := v)) =
    (flush_all_until_volatile_write ts m)(a := v)"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons t ts)
  note notin = \<open>\<forall>j < length (t#ts). 
                (let (_,_,_,sb\<^sub>j,_,_,_) = (t#ts)!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<close>
  hence notin': "\<forall>j < length ts. 
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
    by auto

  obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where t: "t = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
    by (cases t)

  have no_write: 
    "outstanding_refs (is_volatile_Write\<^sub>s\<^sub>b) (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) = {}"
    by (auto simp add: outstanding_refs_conv dest: set_takeWhileD)

  from notin [rule_format, of 0] t
  have a_notin: 
    "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l)"
    by (auto )

  from flush_update_other' [OF a_notin no_write]
  have "(flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) (m(a := v))) =
          (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)(a := v)".
  with Cons.hyps [OF notin', of "(flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"]
  show ?case
    by (simp add: t del: fun_upd_apply)
qed

lemma flush_all_until_volatile_write_append_non_volatile_write_commute: 
  assumes no_volatile_Write\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}" 
  shows "\<And>m i. \<lbrakk>i < length ts; ts!i = (p,is,xs,sb,\<D>,\<O>,\<R>);
      \<forall>j < length ts. i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<rbrakk> 
   \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p',is', xs, sb @ [Write\<^sub>s\<^sub>b False a sop v A L R W],\<D>', \<O>,\<R>')]) m =
    (flush_all_until_volatile_write ts m)(a := v)"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons t ts)
  note i_bound =  \<open>i < length (t#ts)\<close>
  note ith = \<open>(t#ts)!i = (p,is,xs,sb,\<D>,\<O>,\<R>)\<close>
  note notin = \<open>\<forall>j < length (t#ts). i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = (t#ts)!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have t: "t = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    from no_volatile_Write\<^sub>s\<^sub>b have take_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
      by (auto simp add: outstanding_refs_conv)

    from no_volatile_Write\<^sub>s\<^sub>b 
    have take_all': "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Write\<^sub>s\<^sub>b False a sop v A L R W]) = 
            (sb @ [Write\<^sub>s\<^sub>b False a sop v A L R W])"
      by (auto simp add: outstanding_refs_conv)
    from notin 
    have "\<forall>j < length ts. 
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
                 in a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
      by (auto simp add: 0)

    from flush_all_until_volatile_write_update_other [OF this]
    show ?thesis 
      by (simp add: 0 t take_all' take_all flush_append_write del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where t: "t = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases t)
    from i_bound ith notin 
    have "flush_all_until_volatile_write
            (ts[n := (p',is',xs, sb @ [Write\<^sub>s\<^sub>b False a sop v A L R W], \<D>', \<O>,\<R>')])
            (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
          (flush_all_until_volatile_write ts
              (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m))
              (a := v)"
      apply -
      apply (rule Cons.hyps) 
      apply (auto simp add: Suc simp del: o_apply)
      done

    then
    show ?thesis
      by (simp add: t Suc del: fun_upd_apply)
  qed
qed

lemma flush_all_until_volatile_write_append_unflushed: 
  assumes volatile_Write\<^sub>s\<^sub>b: "\<not> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}" 
  shows "\<And>m i. \<lbrakk>i < length ts; ts!i = (p,is,xs,sb,\<D>,\<O>,\<R>)\<rbrakk> 
   \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p',is', xs, sb @ sbx,\<D>', \<O>,\<R>')]) m =
    (flush_all_until_volatile_write ts m)"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,xs,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,xs,sb,\<D>,\<O>,\<R>)"
      by simp
    from volatile_Write\<^sub>s\<^sub>b
    obtain r where r_in: "r \<in> set sb" and volatile_r: "is_volatile_Write\<^sub>s\<^sub>b r"
      by (auto simp add: outstanding_refs_conv)
    from takeWhile_append1 [OF r_in, of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" ] volatile_r

    have "(flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ sbx)) m) =
          (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb ) m)"
      by auto
    then
    show ?thesis
      by (simp add: 0 l)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from Cons.hyps [of n] i_bound ith
    show ?thesis
      by (simp add: l Suc)
  qed
qed

lemma flush_all_until_volatile_nth_update_unused: 
  shows "\<And>m i. \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk> 
   \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p',is',\<theta>', sb, \<D>', \<O>',\<R>')]) m =
    (flush_all_until_volatile_write ts m)"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    show ?thesis
      by (simp add: 0 l)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from Cons.hyps [of n] i_bound ith
    show ?thesis
      by (simp add: l Suc)
  qed
qed

lemma flush_all_until_volatile_write_append_volatile_write_commute:  
  assumes no_volatile_Write\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}" 
  shows "\<And>m i. \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk> \<Longrightarrow>
    flush_all_until_volatile_write
     (ts[i := (p',is', \<theta>, sb @ [Write\<^sub>s\<^sub>b True a sop v A L R W],\<D>', \<O>,\<R>')]) m
   = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    from no_volatile_Write\<^sub>s\<^sub>b
    have s1: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb  = sb"
      by (auto simp add: outstanding_refs_conv)

    from no_volatile_Write\<^sub>s\<^sub>b
    have s2: "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Write\<^sub>s\<^sub>b True a sop v A L R W])) = sb"
      by (auto simp add: outstanding_refs_conv)

    show ?thesis
      by (simp add: 0 l s1 s2)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from Cons.hyps [of n] i_bound ith
    show ?thesis
      by (simp add: l Suc)
  qed
qed

lemma reads_consistent_update: 
  "\<And>pending_write \<O> m. reads_consistent pending_write \<O> m sb \<Longrightarrow> 
       a \<notin> outstanding_refs (Not \<circ> is_volatile) sb \<Longrightarrow>      
       reads_consistent pending_write \<O> (m(a := v)) sb"
apply (induct sb)
apply simp
apply  (clarsimp split: memref.splits if_split_asm
         simp add: fun_upd_twist)
subgoal for sb \<O> m x11 addr val A R pending_write
apply (case_tac "a=addr")
apply simp
apply (fastforce simp add: fun_upd_twist)
done
done

lemma (in program) history_consistent_hd_prog: "\<And>p. history_consistent \<theta> p' xs
\<Longrightarrow> history_consistent \<theta> (hd_prog p xs) xs"
apply (induct xs)
apply  simp
apply (auto split: memref.splits option.splits)
done

locale valid_program = program +
  fixes valid_prog
  assumes valid_prog_inv: "\<lbrakk>\<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid_prog p\<rbrakk> \<Longrightarrow> valid_prog p'"

lemma (in valid_program) history_consistent_appendD: 
  "\<And>\<theta> ys p. \<forall>sop \<in> write_sops xs. valid_sop sop \<Longrightarrow>
                read_tmps xs \<inter> read_tmps ys = {} \<Longrightarrow> 
          history_consistent \<theta> p (xs@ys) \<Longrightarrow> 
           (history_consistent (\<theta>|` (dom \<theta> - read_tmps ys)) p xs \<and> 
            history_consistent \<theta> (last_prog p xs) ys \<and>
            read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {})" 
proof (induct xs)
  case Nil thus ?case
    by auto
next
  case (Cons x xs)
  note valid_sops = \<open>\<forall>sop\<in>write_sops (x # xs). valid_sop sop\<close>
  note read_tmps_dist = \<open>read_tmps (x#xs) \<inter> read_tmps ys = {}\<close>
  note consis = \<open>history_consistent \<theta> p ((x#xs)@ys)\<close>
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v)
    obtain D f where sop: "sop=(D,f)"
      by (cases sop) 
    from consis obtain 
      D_tmps: "D \<subseteq> dom \<theta>" and
      f_v: "f \<theta> = v" and
      D_read_tmps: "D \<inter> read_tmps (xs @ ys) = {}" and
      consis': "history_consistent \<theta> p (xs @ ys)" 
      by (simp add: Write\<^sub>s\<^sub>b sop)
    from valid_sops obtain 
      valid_Df: "valid_sop (D,f)" and
      valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Write\<^sub>s\<^sub>b sop)
    from valid_Df
    interpret valid_sop "(D,f)" .
    from read_tmps_dist have read_tmps_dist': "read_tmps xs \<inter> read_tmps ys = {}"
      by (simp add: Write\<^sub>s\<^sub>b)


    from D_read_tmps have D_ys: "D \<inter> read_tmps ys = {}"
      by (auto simp add: read_tmps_append)
    with D_tmps have D_subset: "D \<subseteq> dom \<theta> - read_tmps ys"
      by auto
    moreover
    
    from valid_sop [OF refl D_tmps]
    have "f \<theta> = f (\<theta> |` D)".
    moreover
    let ?\<theta>' = "\<theta> |` (dom \<theta> - read_tmps ys)"
    from D_subset
    have "?\<theta>' |` D = \<theta> |` D" 
      apply -
      apply (rule ext)
      by (auto simp add: restrict_map_def)
    moreover
    from D_subset
    have D_tmps': "D \<subseteq> dom ?\<theta>'"
      by auto
    ultimately 
    have f_v': "f ?\<theta>' = v"
      using valid_sop [OF refl D_tmps'] f_v
      by simp
    from D_read_tmps
    have "D \<inter> read_tmps xs = {}"
      by (auto simp add: read_tmps_append)
    with Cons.hyps [OF valid_sops' read_tmps_dist' consis'] D_tmps D_subset f_v' D_ys
    show ?thesis
      by (auto simp add: Write\<^sub>s\<^sub>b sop)
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from consis obtain 
      tmps_t: "\<theta> t = Some v" and
      consis': "history_consistent \<theta> p (xs @ ys)"
      by (simp add: Read\<^sub>s\<^sub>b split: option.splits)

    from read_tmps_dist
    obtain t_ys: "t \<notin> read_tmps ys" and read_tmps_dist': "read_tmps xs \<inter> read_tmps ys = {}"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from valid_sops have valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from t_ys tmps_t
    have "(\<theta> |` (dom \<theta> - read_tmps ys)) t = Some v"
      by (auto simp add: restrict_map_def domIff)
    with Cons.hyps [OF valid_sops' read_tmps_dist' consis']

    show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
    from consis obtain p\<^sub>1_p: "p\<^sub>1 = p" and
     prog_step: "\<theta> |` (dom \<theta> - read_tmps (xs @ ys))\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2, mis)" and
     consis': "history_consistent \<theta> p\<^sub>2 (xs @ ys)"
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    let ?\<theta>' = "\<theta> |` (dom \<theta> - read_tmps ys)"
    have eq: "?\<theta>' |` (dom ?\<theta>' - read_tmps xs) = \<theta> |` (dom \<theta> - read_tmps (xs @ ys))"
      apply (rule ext)
      apply (auto simp add: read_tmps_append restrict_map_def domIff split: if_split_asm)
      done

    from valid_sops have valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from read_tmps_dist
    obtain read_tmps_dist': "read_tmps xs \<inter> read_tmps ys = {}"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF valid_sops' read_tmps_dist' consis'] p\<^sub>1_p prog_step eq
    show ?thesis
      by (simp add: Prog\<^sub>s\<^sub>b)
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons show ?thesis
      by auto
  qed
qed

lemma (in valid_program) history_consistent_appendI: 
  "\<And>\<theta> ys p. \<forall>sop \<in> write_sops xs. valid_sop sop \<Longrightarrow>
  history_consistent (\<theta>|` (dom \<theta> - read_tmps ys)) p xs \<Longrightarrow>
 history_consistent \<theta> (last_prog p xs) ys \<Longrightarrow>
 read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {} \<Longrightarrow> valid_prog p \<Longrightarrow>
           history_consistent \<theta> p (xs@ys)" 
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note valid_sops = \<open>\<forall>sop\<in>write_sops (x # xs). valid_sop sop\<close>
  note consis_xs = \<open>history_consistent (\<theta> |` (dom \<theta> - read_tmps ys)) p (x # xs)\<close>
  note consis_ys = \<open>history_consistent \<theta> (last_prog p (x # xs)) ys\<close>
  note dist = \<open>read_tmps ys \<inter> \<Union>(fst ` write_sops (x # xs)) = {}\<close>
  note valid_p = \<open>valid_prog p\<close>
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v)
    obtain D f where sop: "sop=(D,f)"
      by (cases sop) 
    from consis_xs obtain 
      D_tmps: "D \<subseteq> dom \<theta> - read_tmps ys" and
      f_v: "f (\<theta> |` (dom \<theta> - read_tmps ys)) = v" (is "f ?\<theta> = v") and
      D_read_tmps: "D \<inter> read_tmps xs = {}" and
      consis': "history_consistent (\<theta> |` (dom \<theta> - read_tmps ys)) p xs" 
      by (simp add: Write\<^sub>s\<^sub>b sop)

    from D_tmps D_read_tmps 
    have "D \<inter> read_tmps (xs @ ys) = {}"
      by (auto simp add: read_tmps_append)
    moreover
    from D_tmps have D_tmps': "D \<subseteq> dom \<theta>"
      by auto
    moreover 
    from valid_sops obtain 
      valid_Df: "valid_sop (D,f)" and
      valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Write\<^sub>s\<^sub>b sop)
    from valid_Df
    interpret valid_sop "(D,f)" .

    from D_tmps
    have tmps_eq: "\<theta> |` ((dom \<theta> - read_tmps ys) \<inter> D) = \<theta> |` D"
      apply -
      apply (rule ext) 
      apply (auto simp add: restrict_map_def)
      done
    from D_tmps
    have "f ?\<theta> = f (?\<theta> |` D)"
      apply -
      apply (rule valid_sop [OF refl ])
      apply auto
      done
    with valid_sop [OF refl D_tmps'] f_v D_tmps

    have "f \<theta> = v"
      by (clarsimp simp add: tmps_eq)
    moreover
    from consis_ys have consis_ys': "history_consistent \<theta> (last_prog p xs) ys"
      by (auto simp add: Write\<^sub>s\<^sub>b)

    from dist have dist': "read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {}"
      by (auto simp add: Write\<^sub>s\<^sub>b)

    moreover note Cons.hyps [OF valid_sops' consis' consis_ys' dist' valid_p]

    ultimately show ?thesis
      by (simp add: Write\<^sub>s\<^sub>b sop)
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from consis_xs obtain
      t_v: "(\<theta> |` (dom \<theta> - read_tmps ys)) t = Some v" and
      consis_xs': "history_consistent (\<theta> |` (dom \<theta> - read_tmps ys)) p xs"
      by (clarsimp simp add: Read\<^sub>s\<^sub>b split: option.splits)
    from t_v have "\<theta> t = Some v"
      by (auto simp add: restrict_map_def split: if_split_asm)
    moreover
    from valid_sops obtain 
      valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from consis_ys have consis_ys': "history_consistent \<theta> (last_prog p xs) ys"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from dist have dist': "read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {}"
      by (auto simp add: Read\<^sub>s\<^sub>b)

    note Cons.hyps [OF valid_sops' consis_xs' consis_ys' dist' valid_p]
    ultimately
    show ?thesis
      by (simp add: Read\<^sub>s\<^sub>b)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis)
    let ?\<theta> = "\<theta> |` (dom \<theta> - read_tmps ys)"
    from consis_xs  obtain 
      p\<^sub>1_p: "p\<^sub>1 = p" and
      prog_step: "?\<theta> |` (dom ?\<theta> - read_tmps xs)\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2, mis)" and
      consis': "history_consistent ?\<theta> p\<^sub>2 xs"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    
    (*let ?\<theta>' = "\<theta> |` (dom \<theta> - read_tmps ys)"*)
    have eq: "?\<theta> |` (dom ?\<theta> - read_tmps xs) = \<theta> |` (dom \<theta> - read_tmps (xs @ ys))"
      apply (rule ext)
      apply (auto simp add: read_tmps_append restrict_map_def domIff split: if_split_asm)
      done

    from prog_step eq
    have "\<theta> |` (dom \<theta> - read_tmps (xs @ ys))\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2, mis)" by simp
    moreover
    from valid_sops obtain 
      valid_sops': "\<forall>sop\<in>write_sops xs. valid_sop sop"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from consis_ys have consis_ys': "history_consistent \<theta> (last_prog p\<^sub>2 xs) ys"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from dist have dist': "read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {}"
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    note Cons.hyps [OF valid_sops' consis' consis_ys' dist' valid_prog_inv [OF prog_step valid_p [simplified p\<^sub>1_p [symmetric]]]]
    ultimately
    show ?thesis
      by (simp add: Prog\<^sub>s\<^sub>b p\<^sub>1_p)
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons show ?thesis
      by auto
  qed
qed

lemma (in valid_program) history_consistent_append_conv: 
  "\<And>\<theta> ys p. \<forall>sop \<in> write_sops xs. valid_sop sop \<Longrightarrow>
                read_tmps xs \<inter> read_tmps ys = {} \<Longrightarrow> valid_prog p \<Longrightarrow>
          history_consistent \<theta> p (xs@ys) = 
           (history_consistent (\<theta>|` (dom \<theta> - read_tmps ys)) p xs \<and> 
            history_consistent \<theta> (last_prog p xs) ys \<and>
            read_tmps ys \<inter> \<Union>(fst ` write_sops xs) = {})"
apply rule
apply  (rule history_consistent_appendD,assumption+)
apply (rule history_consistent_appendI)
apply auto
done

lemma instrs_takeWhile_dropWhile_conv:
  "instrs xs = instrs (takeWhile P xs) @ instrs (dropWhile P xs)"
by (induct xs) (auto split: memref.splits)



lemma (in program) history_consistent_hd_prog_p: 
  "\<And>p. history_consistent \<theta> p xs \<Longrightarrow> p = hd_prog p xs"
  by (induct xs) (auto split: memref.splits option.splits)

lemma instrs_append: "\<And>ys. instrs (xs@ys) = instrs xs @ instrs ys"
  by (induct xs) (auto split: memref.splits)

lemma prog_instrs_append: "\<And>ys. prog_instrs (xs@ys) = prog_instrs xs @ prog_instrs ys"
  by (induct xs) (auto split: memref.splits)

lemma prog_instrs_empty: "\<forall>r \<in> set xs. \<not> is_Prog\<^sub>s\<^sub>b r \<Longrightarrow> prog_instrs xs = []"
  by (induct xs) (auto split: memref.splits)

lemma length_dropWhile [termination_simp]: "length (dropWhile P xs) \<le> length xs"
  by (induct xs) auto

lemma prog_instrs_filter_is_Prog\<^sub>s\<^sub>b: "prog_instrs (filter (is_Prog\<^sub>s\<^sub>b) xs) = prog_instrs xs"
  by (induct xs) (auto split: memref.splits)


lemma Cons_to_snoc: "\<And>x. \<exists>ys y. (x#xs) = (ys@[y])"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x1 xs)
  from Cons [of x1] obtain ys y where "x1#xs = ys @ [y]"
    by auto
  then
  show ?case
    by simp
qed

lemma causal_program_history_Read:
  assumes causal_Read: "causal_program_history (Read volatile a t # is\<^sub>s\<^sub>b) sb" 
  shows "causal_program_history is\<^sub>s\<^sub>b (sb @ [Read\<^sub>s\<^sub>b volatile a t v])"
proof
  fix sb\<^sub>1 sb\<^sub>2
  assume sb: "sb @ [Read\<^sub>s\<^sub>b volatile a t v] = sb\<^sub>1 @ sb\<^sub>2"
  from causal_Read
  interpret causal_program_history "Read volatile a t # is\<^sub>s\<^sub>b" "sb" .
  show "\<exists>is. instrs sb\<^sub>2 @ is\<^sub>s\<^sub>b = is @ prog_instrs sb\<^sub>2"
  proof (cases sb\<^sub>2)
    case Nil
    thus ?thesis
      by simp
  next
    case (Cons r sb')
    from Cons_to_snoc [of r sb'] Cons obtain ys y where sb\<^sub>2_snoc: "sb\<^sub>2=ys@[y]"
      by auto
    with sb obtain y: "y = Read\<^sub>s\<^sub>b volatile a t v" and sb: "sb = sb\<^sub>1@ys"
      by simp

    from causal_program_history [OF sb] obtain "is" where
      "instrs ys @ Read volatile a t # is\<^sub>s\<^sub>b = is @ prog_instrs ys"
      by auto
    then show ?thesis
      by (simp add: sb\<^sub>2_snoc y instrs_append prog_instrs_append)
  qed
qed


lemma causal_program_history_Write:
  assumes causal_Write: "causal_program_history (Write volatile a sop A L R W# is\<^sub>s\<^sub>b) sb"
  shows  "causal_program_history is\<^sub>s\<^sub>b (sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W])"
proof
  fix sb\<^sub>1 sb\<^sub>2
  assume sb: "sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W] = sb\<^sub>1 @ sb\<^sub>2"
  from causal_Write
  interpret causal_program_history "Write volatile a sop A L R W# is\<^sub>s\<^sub>b" "sb" .
  show "\<exists>is. instrs sb\<^sub>2 @ is\<^sub>s\<^sub>b = is @ prog_instrs sb\<^sub>2"
  proof (cases sb\<^sub>2)
    case Nil
    thus ?thesis
      by simp
  next
    case (Cons r sb')
    from Cons_to_snoc [of r sb'] Cons obtain ys y where sb\<^sub>2_snoc: "sb\<^sub>2=ys@[y]"
      by auto
    with sb obtain y: "y = Write\<^sub>s\<^sub>b volatile a sop v A L R W" and sb: "sb = sb\<^sub>1@ys"
      by simp

    from causal_program_history [OF sb] obtain "is" where
      "instrs ys @ Write volatile a sop A L R W# is\<^sub>s\<^sub>b = is @ prog_instrs ys"
      by auto
    then show ?thesis
      by (simp add: sb\<^sub>2_snoc y instrs_append prog_instrs_append)
  qed
qed

lemma causal_program_history_Prog\<^sub>s\<^sub>b:
  assumes causal_Write: "causal_program_history is\<^sub>s\<^sub>b sb"
  shows  "causal_program_history (is\<^sub>s\<^sub>b@mis) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])"
proof
  fix sb\<^sub>1 sb\<^sub>2
  assume sb: "sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis] = sb\<^sub>1 @ sb\<^sub>2"
  from causal_Write
  interpret causal_program_history "is\<^sub>s\<^sub>b" "sb" .
  show "\<exists>is. instrs sb\<^sub>2 @ (is\<^sub>s\<^sub>b@mis) = is @ prog_instrs sb\<^sub>2"
  proof (cases sb\<^sub>2)
    case Nil
    thus ?thesis
      by simp
  next
    case (Cons r sb')
    from Cons_to_snoc [of r sb'] Cons obtain ys y where sb\<^sub>2_snoc: "sb\<^sub>2=ys@[y]"
      by auto
    with sb obtain y: "y = Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis" and sb: "sb = sb\<^sub>1@ys"
      by simp

    from causal_program_history [OF sb] obtain "is" where
      "instrs ys @ (is\<^sub>s\<^sub>b @ mis) = is @ prog_instrs (ys@[Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])"
      by (auto simp add: prog_instrs_append)
    then show ?thesis
      by (simp add: sb\<^sub>2_snoc y instrs_append prog_instrs_append)
  qed
qed

lemma causal_program_history_Ghost:
  assumes causal_Ghost\<^sub>s\<^sub>b: "causal_program_history (Ghost A L R W # is\<^sub>s\<^sub>b) sb"
  shows  "causal_program_history is\<^sub>s\<^sub>b (sb @ [Ghost\<^sub>s\<^sub>b A L R W])"
proof
  fix sb\<^sub>1 sb\<^sub>2
  assume sb: "sb @ [Ghost\<^sub>s\<^sub>b A L R W] = sb\<^sub>1 @ sb\<^sub>2"
  from causal_Ghost\<^sub>s\<^sub>b
  interpret causal_program_history "Ghost A L R W # is\<^sub>s\<^sub>b" "sb" .
  show "\<exists>is. instrs sb\<^sub>2 @ is\<^sub>s\<^sub>b = is @ prog_instrs sb\<^sub>2"
  proof (cases sb\<^sub>2)
    case Nil
    thus ?thesis
      by simp
  next
    case (Cons r sb')
    from Cons_to_snoc [of r sb'] Cons obtain ys y where sb\<^sub>2_snoc: "sb\<^sub>2=ys@[y]"
      by auto
    with sb obtain y: "y = Ghost\<^sub>s\<^sub>b A L R W" and sb: "sb = sb\<^sub>1@ys"
      by simp

    from causal_program_history [OF sb] obtain "is" where
      "instrs ys @ Ghost A L R W # is\<^sub>s\<^sub>b = is @ prog_instrs ys"
      by auto
    then show ?thesis
      by (simp add: sb\<^sub>2_snoc y instrs_append prog_instrs_append)
  qed
qed

lemma hd_prog_last_prog_end: "\<lbrakk>p = hd_prog p sb ; last_prog p sb = p\<^sub>s\<^sub>b\<rbrakk> \<Longrightarrow> p = hd_prog p\<^sub>s\<^sub>b sb"
  by (induct sb) (auto split: memref.splits)

lemma hd_prog_idem: "hd_prog (hd_prog p xs) xs = hd_prog p xs"
  by (induct xs) (auto split: memref.splits)

lemma last_prog_idem: "last_prog (last_prog p sb) sb = last_prog p sb"
  by (induct sb) (auto split: memref.splits)


lemma last_prog_hd_prog_append:
  "last_prog (hd_prog p\<^sub>s\<^sub>b (sb@sb')) sb =last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb"
apply (induct sb)
apply (auto split: memref.splits)
done

lemma last_prog_hd_prog: "last_prog (hd_prog p xs) xs = last_prog p xs"
  by (induct xs) (auto split: memref.splits)


lemma last_prog_append_Read\<^sub>s\<^sub>b: 
  "\<And>p. last_prog p (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) = last_prog p sb"
  by (induct sb) (auto split: memref.splits)


lemma last_prog_append_Write\<^sub>s\<^sub>b: 
  "\<And>p. last_prog p (sb @ [Write\<^sub>s\<^sub>b volatile a sop v A L R W]) = last_prog p sb"
  by (induct sb) (auto split: memref.splits)


lemma last_prog_append_Prog\<^sub>s\<^sub>b:
  "\<And>x. last_prog x (sb@[Prog\<^sub>s\<^sub>b p p' mis]) = p'"
  by (induct sb) (auto split: memref.splits)

lemma hd_prog_append_Prog\<^sub>s\<^sub>b: "hd_prog x (sb @ [Prog\<^sub>s\<^sub>b p p' mis]) = hd_prog p sb"
  by (induct sb) (auto split: memref.splits)


lemma hd_prog_last_prog_append_Prog\<^sub>s\<^sub>b:
  "\<And>p'. hd_prog p' xs = p' \<Longrightarrow> last_prog p' xs = p\<^sub>1 \<Longrightarrow> 
       hd_prog p' (xs @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis]) = p'"
apply (induct xs)
apply (auto split: memref.splits)
done

lemma hd_prog_append_Ghost\<^sub>s\<^sub>b:
  "hd_prog p (sb@[Ghost\<^sub>s\<^sub>b A  R L W]) = hd_prog p sb"
  by (induct sb) (auto split: memref.splits)

lemma last_prog_append_Ghost\<^sub>s\<^sub>b: 
  "\<And>p. last_prog p (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) = last_prog p sb"
  by (induct sb) (auto split: memref.splits)

lemma dropWhile_all_False_conv:  
"\<forall>x \<in> set xs. \<not> P x \<Longrightarrow> dropWhile P xs = xs"
by (induct xs) auto

lemma dropWhile_append_all_False: 
"\<forall>y \<in> set ys. \<not> P y \<Longrightarrow> 
  dropWhile P (xs@ys) = dropWhile P xs @ ys"
apply (induct xs)
apply (auto simp add: dropWhile_all_False_conv)
done


lemma reads_consistent_append_first:
  "\<And>m ys. reads_consistent pending_write \<O> m (xs @ ys) \<Longrightarrow> reads_consistent pending_write \<O> m xs"
  by (clarsimp simp add: reads_consistent_append)

lemma reads_consistent_takeWhile:
assumes consis: "reads_consistent pending_write \<O> m sb" 
shows "reads_consistent pending_write \<O> m (takeWhile P sb)"
using reads_consistent_append [where xs="(takeWhile P sb)" and ys="(dropWhile P sb)"] consis
apply (simp add: reads_consistent_append)
done

lemma flush_flush_all_until_volatile_write_Write\<^sub>s\<^sub>b_volatile_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,xs,Write\<^sub>s\<^sub>b True a sop v A L R W#sb,\<D>,\<O>,\<R>);
        \<forall>i < length ts. (\<forall>j < length ts. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>i,_,_,_) = ts!i;
                      (_,_,_,sb\<^sub>j,_,_,_) = ts!j
                   in outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}));
        \<forall>j < length ts. i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j in a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<rbrakk>
       \<Longrightarrow> 
       flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)
         ((flush_all_until_volatile_write ts m)(a := v)) =
       flush_all_until_volatile_write (ts[i := (p,is,xs, sb, \<D>', \<O>',\<R>')])
         (m(a := v))"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,xs,Write\<^sub>s\<^sub>b True a sop v A L R W#sb,\<D>,\<O>,\<R>)\<close>
  note disj = \<open>\<forall>i < length (l#ts). (\<forall>j < length (l#ts). i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>i,_,_,_) = (l#ts)!i;
                      (_,_,_,sb\<^sub>j,_,_,_) = (l#ts)!j
                   in outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}))\<close>
  note a_notin = \<open>\<forall>j < length (l#ts). i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = (l#ts)!j 
                 in a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,xs,Write\<^sub>s\<^sub>b True a sop v A L R W#sb,\<D>,\<O>,\<R>)"
      by simp
    have a_notin_ts:
      "a \<notin> \<Union>((\<lambda>(_,_,_,sb,_,_,_). outstanding_refs is_Write\<^sub>s\<^sub>b 
                            (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts)" (is "a \<notin> ?U")
    proof 
      assume "a \<in> ?U"
      from in_Union_image_nth_conv [OF this]
      obtain j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j "xs\<^sub>j" "sb\<^sub>j" where 
	j_bound: "j < length ts" and
	jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	a_in_j: "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	by fastforce
      from a_notin [rule_format, of "Suc j"] j_bound 0 a_in_j
      show False
	by (auto simp add: jth)
    qed

    from a_notin_ts
    have "(flush_all_until_volatile_write ts m)(a := v) =
                flush_all_until_volatile_write ts (m(a := v))"
      apply -
      apply (rule update_commute' [where F="{a}" and G="?U" and 
	g="flush_all_until_volatile_write ts"])
      apply (auto intro: flush_all_until_volatile_wirte_mem_independent
             flush_all_until_volatile_write_unchanged_addresses)
      done
    
    moreover

    let ?SB = "outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

    have U_SB_disj: "?U \<inter> ?SB = {}"
    proof -
      {
	fix a'
	assume a'_in_U: "a' \<in> ?U"
	have "a' \<notin> ?SB"
	proof 
	  assume a'_in_SB: "a' \<in> ?SB"
	  hence a'_in_SB': "a' \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
	    apply (clarsimp simp add: outstanding_refs_conv)
	    apply (drule set_takeWhileD)
      subgoal for x
	    apply (rule_tac x=x in exI)
	    apply (auto simp add: is_Write\<^sub>s\<^sub>b_def split:memref.splits)
	    done
	    done
	  from in_Union_image_nth_conv [OF a'_in_U]
	  obtain j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j "xs\<^sub>j" "sb\<^sub>j" where 
	    j_bound: "j < length ts" and
	    jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)" and
	    a'_in_j: "a' \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    by fastforce

	  from disj [rule_format, of 0 "Suc j"] 0 j_bound a'_in_SB' a'_in_j jth l
	  show False
	    by auto
	qed
      }
      moreover
      {
	fix a'
	assume a'_in_SB: "a' \<in> ?SB"
	hence a'_in_SB': "a' \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
	    apply (clarsimp simp add: outstanding_refs_conv)
	    apply (drule set_takeWhileD)
	    subgoal for x
	    apply (rule_tac x=x in exI)
	    apply (auto simp add: is_Write\<^sub>s\<^sub>b_def split:memref.splits)
	    done
	    done
	have "a' \<notin> ?U"
	proof 
	  assume "a' \<in> ?U"
	  from in_Union_image_nth_conv [OF this]
	  obtain j p\<^sub>j "is\<^sub>j" "\<O>\<^sub>j" \<R>\<^sub>j \<D>\<^sub>j "xs\<^sub>j" "sb\<^sub>j" where 
	    j_bound: "j < length ts" and
	    jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<R>\<^sub>j,\<O>\<^sub>j)" and
	    a'_in_j: "a' \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	    by fastforce

	  from disj [rule_format, of 0 "Suc j"] j_bound a'_in_SB' a'_in_j jth  l
	  show False
	    by auto
	qed
      }
      ultimately
      show ?thesis by blast
    qed

    have "flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)
           (flush_all_until_volatile_write ts (m(a := v))) = 
          flush_all_until_volatile_write ts 
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (m(a := v)))"
      apply (rule update_commute' [where g = "flush_all_until_volatile_write ts ",
             OF _ _ _ _ U_SB_disj])
      apply (auto intro: flush_all_until_volatile_wirte_mem_independent
             flush_all_until_volatile_write_unchanged_addresses
             flush_unchanged_addresses
             flushed_values_mem_independent simp del: o_apply)
      done
      
    ultimately
    have "flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)
           ((flush_all_until_volatile_write ts m)(a := v)) =
          flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (m(a := v)))"
      by simp

    then show ?thesis 
      by (auto simp add: l 0 o_def simp del: fun_upd_apply)
  next
    case (Suc n)

    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>j xs\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>j,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith disj a_notin
    have  
      "flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)
        ((flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m))
          (a := v)) =
       flush_all_until_volatile_write (ts[n := (p,is, xs, sb,\<D>', \<O>',\<R>')])
        ((flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)(a := v))"
      apply -
      apply (rule Cons.hyps)
      apply (force simp add: Suc Let_def simp del: o_apply)+
      done

    moreover

    let ?SB = "outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l)"
    have "a \<notin> ?SB"
    proof 
      assume "a \<in> ?SB"
      with a_notin [rule_format, of 0]
      show False
	by (auto simp add: l Suc)
    qed
    then
    have "((flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)(a := v)) =
          (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) (m(a := v)))"
      apply -
      apply (rule update_commute' [where m=m and F="{a}" and G="?SB"])
      apply (auto intro: 
             flush_unchanged_addresses
             flushed_values_mem_independent simp del: o_apply)
      done

    ultimately
    show ?thesis
      by (simp add: l Suc del: fun_upd_apply o_apply)
  qed
qed



   




lemma (in program)
"\<And>sb' p. history_consistent \<theta> (hd_prog p (sb@sb')) (sb@sb') \<Longrightarrow>
          last_prog p (sb@sb') = p \<Longrightarrow> 
 last_prog (hd_prog p (sb@sb')) sb = hd_prog p sb'"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons r sb\<^sub>1)
  have consis: "history_consistent \<theta> (hd_prog p ((r # sb\<^sub>1) @ sb')) ((r # sb\<^sub>1) @ sb')" 
    by fact
  have last_prog: "last_prog p ((r # sb\<^sub>1) @ sb') = p" by fact
  show ?case
  proof (cases r)
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto split: option.splits)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 "is")
    from last_prog have last_prog_p\<^sub>2: "last_prog p\<^sub>2 (sb\<^sub>1 @ sb') = p"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from consis obtain consis': "history_consistent \<theta> p\<^sub>2 (sb\<^sub>1 @ sb')"
      by (simp add: Prog\<^sub>s\<^sub>b)

    hence "history_consistent \<theta> (hd_prog p\<^sub>2 (sb\<^sub>1 @ sb')) (sb\<^sub>1 @ sb')"
      by (rule history_consistent_hd_prog)
    from Cons.hyps [OF this ]
    have "last_prog p\<^sub>2 sb\<^sub>1 = hd_prog p sb'"
      oops

lemma last_prog_to_last_prog_same: "\<And>p'. last_prog p' sb = p \<Longrightarrow> last_prog p sb = p"
  by (induct sb) (auto split: memref.splits)

lemma last_prog_hd_prog_same: "\<lbrakk>last_prog p' sb = p; hd_prog p' sb = p'\<rbrakk> \<Longrightarrow> hd_prog p sb = p'"
  by (induct sb) (auto split : memref.splits)

lemma last_prog_hd_prog_last_prog:   
  "last_prog p' (sb@sb') = p \<Longrightarrow> hd_prog p' (sb@sb') = p' \<Longrightarrow>
   last_prog (hd_prog p sb') sb = last_prog p' sb"
apply (induct sb)
apply (simp add: last_prog_hd_prog_same)
apply (auto split : memref.splits)
done

lemma (in program) last_prog_hd_prog_append':
"\<And>sb' p. history_consistent \<theta> (hd_prog p (sb@sb')) (sb@sb') \<Longrightarrow>
          last_prog p (sb@sb') = p \<Longrightarrow> 
 last_prog (hd_prog p sb') sb = hd_prog p sb'"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons r sb\<^sub>1)
  have consis: "history_consistent \<theta> (hd_prog p ((r # sb\<^sub>1) @ sb')) ((r # sb\<^sub>1) @ sb')" 
    by fact
  have last_prog: "last_prog p ((r # sb\<^sub>1) @ sb') = p" by fact
  show ?case
  proof (cases r)
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto split: option.splits)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 "is")
    from last_prog have last_prog_p\<^sub>2: "last_prog p\<^sub>2 (sb\<^sub>1 @ sb') = p"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from last_prog_to_last_prog_same [OF this]
    have last_prog_p: "last_prog p (sb\<^sub>1 @ sb') = p".
    from consis obtain consis': "history_consistent \<theta> p\<^sub>2 (sb\<^sub>1 @ sb')"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from history_consistent_hd_prog_p [OF consis']
    have hd_prog_p\<^sub>2: "hd_prog p\<^sub>2 (sb\<^sub>1 @ sb') = p\<^sub>2" by simp
    from consis' have "history_consistent \<theta> (hd_prog p (sb\<^sub>1 @ sb')) (sb\<^sub>1 @ sb')"
      by (rule history_consistent_hd_prog)
    from Cons.hyps [OF this last_prog_p]
    have "last_prog (hd_prog p sb') sb\<^sub>1 = hd_prog p sb'".
    moreover
    from last_prog_hd_prog_last_prog [OF last_prog_p\<^sub>2 hd_prog_p\<^sub>2]
    have "last_prog (hd_prog p sb') sb\<^sub>1 = last_prog p\<^sub>2 sb\<^sub>1".
    ultimately
    have "last_prog p\<^sub>2 sb\<^sub>1 = hd_prog p sb'"
      by simp
    thus ?thesis
      by (simp add: Prog\<^sub>s\<^sub>b)
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by (auto split: option.splits)
  qed
qed

lemma flush_all_until_volatile_write_Write\<^sub>s\<^sub>b_non_volatile_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,xs,Write\<^sub>s\<^sub>b False a sop v A L R W#sb,\<D>,\<O>,\<R>);
        \<forall>i < length ts. (\<forall>j < length ts. i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>i,_,_,_) = ts!i;
                      (_,_,_,sb\<^sub>j,_,_,_) = ts!j
                   in outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}));
        \<forall>j < length ts. i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j in a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p,is, xs, sb,\<D>', \<O>,\<R>')])(m(a := v))  =
               flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,xs,Write\<^sub>s\<^sub>b False a sop v A L R W#sb,\<D>,\<O>,\<R>)\<close>
  note disj = \<open>\<forall>i < length (l#ts). (\<forall>j < length (l#ts). i \<noteq> j \<longrightarrow>
                  (let (_,_,_,sb\<^sub>i,_,_,_) = (l#ts)!i;
                      (_,_,_,sb\<^sub>j,_,_,_) = (l#ts)!j
                   in outstanding_refs is_Write\<^sub>s\<^sub>b sb\<^sub>i \<inter> 
                      outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) = {}))\<close>
  note a_notin = \<open>\<forall>j < length (l#ts). i \<noteq> j \<longrightarrow>
                (let (_,_,_,sb\<^sub>j,_,_,_) = (l#ts)!j 
    in a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,xs,Write\<^sub>s\<^sub>b False a sop v A L R W#sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l xs\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,xs\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith disj a_notin 
    have
      "flush_all_until_volatile_write (ts[n := (p,is,xs, sb, \<D>', \<O>,\<R>')])
          ((flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)(a := v)) =
       flush_all_until_volatile_write ts
          (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (force simp add: Suc Let_def simp del: o_apply)+
      done

    moreover

    let ?SB = "outstanding_refs is_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l)"
    have "a \<notin> ?SB"
    proof 
      assume "a \<in> ?SB"
      with a_notin [rule_format, of 0]
      show False
	by (auto simp add: l Suc)
    qed
    then
    have "((flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)(a := v)) =
          (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) (m(a := v)))"
      apply -
      apply (rule update_commute' [where m=m and F="{a}" and G="?SB"])
      apply (auto intro: 
             flush_unchanged_addresses
             flushed_values_mem_independent simp del: o_apply)
      done

    ultimately
    show ?thesis
      by (simp add: l Suc del: fun_upd_apply o_apply)
  qed
qed   

lemma (in program) history_consistent_access_last_read': 
  "\<And>p. history_consistent \<theta> p (sb @ [Read\<^sub>s\<^sub>b volatile a t v]) \<Longrightarrow>
        \<theta> t = Some v"
apply (induct sb)
apply (auto  split: memref.splits option.splits)
done

lemma (in program) history_consistent_access_last_read:
  "history_consistent \<theta> p (rev (Read\<^sub>s\<^sub>b volatile a t v # sb)) \<Longrightarrow> \<theta> t = Some v"
  by (simp add: history_consistent_access_last_read')

lemma flush_all_until_volatile_write_Read\<^sub>s\<^sub>b_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,\<theta>,Read\<^sub>s\<^sub>b volatile a t v#sb,\<D>,\<O>,\<R>)\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p,is,\<theta>, sb, \<D>', \<O>,\<R>')]) m
       = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,Read\<^sub>s\<^sub>b volatile a t v#sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,Read\<^sub>s\<^sub>b volatile a t v#sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith
    have "flush_all_until_volatile_write (ts[n := (p,is,\<theta>, sb, \<D>', \<O>,\<R>')])
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
         flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done

    then show ?thesis
      by (simp add: Suc l)
  qed
qed

lemma flush_all_until_volatile_write_Ghost\<^sub>s\<^sub>b_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,\<theta>,Ghost\<^sub>s\<^sub>b A L R W#sb,\<D>,\<O>,\<R>)\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p',is',\<theta>', sb, \<D>', \<O>',\<R>')]) m
       = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,Ghost\<^sub>s\<^sub>b A L R W#sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,Ghost\<^sub>s\<^sub>b A L R W#sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith
    have "flush_all_until_volatile_write (ts[n := (p',is',\<theta>', sb, \<D>', \<O>',\<R>')])
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
         flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done

    then show ?thesis
      by (simp add: Suc l)
  qed
qed

lemma flush_all_until_volatile_write_Prog\<^sub>s\<^sub>b_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,\<theta>,Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb,\<D>,\<O>,\<R>)\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p,is, \<theta>, sb,\<D>', \<O>,\<R>')]) m
       = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis#sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith
    have "flush_all_until_volatile_write (ts[n := (p,is, \<theta>, sb,\<D>', \<O>,\<R>')])
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
         flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done

    then show ?thesis
      by (simp add: Suc l)
  qed
qed


lemma flush_all_until_volatile_write_append_Prog\<^sub>s\<^sub>b_commute:
  "\<And>i m. \<lbrakk>i < length ts; ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk>
       \<Longrightarrow> flush_all_until_volatile_write (ts[i := (p\<^sub>2,is@mis, \<theta>, sb@[Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis],\<D>', \<O>,\<R>')]) m
       = flush_all_until_volatile_write ts m"
proof (induct ts)
  case Nil thus ?case
    by simp
next
  case (Cons l ts)
  note i_bound =  \<open>i < length (l#ts)\<close>
  note ith = \<open>(l#ts)!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 flush_append_Prog\<^sub>s\<^sub>b del: fun_upd_apply)
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)

    from i_bound ith
    have "flush_all_until_volatile_write 
              (ts[n := (p\<^sub>2,is@mis,\<theta>, sb@[Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis], \<D>', \<O>,\<R>')])
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m) =
         flush_all_until_volatile_write ts
           (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) m)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done

    then show ?thesis
      by (simp add: Suc l)
  qed
qed




lemma (in program) history_consistent_append_Prog\<^sub>s\<^sub>b:
  assumes step: "\<theta>\<turnstile> p \<rightarrow>\<^sub>p (p', mis)"
  shows "history_consistent \<theta> (hd_prog p xs) xs \<Longrightarrow> last_prog p xs = p \<Longrightarrow>
       history_consistent \<theta> (hd_prog p' (xs@[Prog\<^sub>s\<^sub>b p p' mis])) (xs@[Prog\<^sub>s\<^sub>b p p' mis])"
proof (induct xs)
  case Nil with step show ?case by simp
next
  case (Cons x xs)
  note consis = \<open>history_consistent \<theta> (hd_prog p (x # xs)) (x # xs)\<close>
  note last = \<open>last_prog p (x#xs) = p\<close>
  show ?case
  proof (cases x)
    case Write\<^sub>s\<^sub>b with Cons show ?thesis by (auto simp add: read_tmps_append)
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto split: option.splits)
  next
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis')
    from consis obtain
      step: "\<theta> |`(dom \<theta> - read_tmps (xs @ [Prog\<^sub>s\<^sub>b p p' mis]))\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2, mis')" and
      consis': "history_consistent \<theta> p\<^sub>2 xs"
      by (auto simp add: Prog\<^sub>s\<^sub>b read_tmps_append)
    from last have last_p\<^sub>2: "last_prog p\<^sub>2 xs = p"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from last_prog_to_last_prog_same [OF this]
    have last_prog': "last_prog p xs = p".
    from history_consistent_hd_prog [OF consis']
    have consis'': "history_consistent \<theta> (hd_prog p xs) xs".
    from Cons.hyps [OF this last_prog']
    have "history_consistent \<theta> (hd_prog p' (xs @ [Prog\<^sub>s\<^sub>b p p' mis]))
            (xs @ [Prog\<^sub>s\<^sub>b p p' mis])".
    from history_consistent_hd_prog [OF this]
    have "history_consistent \<theta> (hd_prog p\<^sub>2 (xs @ [Prog\<^sub>s\<^sub>b p p' mis])) 
           (xs @ [Prog\<^sub>s\<^sub>b p p' mis])".
    moreover
    from history_consistent_hd_prog_p [OF consis'] 
    have "p\<^sub>2 = hd_prog p\<^sub>2 xs".
    from hd_prog_last_prog_append_Prog\<^sub>s\<^sub>b [OF this [symmetric] last_p\<^sub>2]
    have "hd_prog p\<^sub>2 (xs @ [Prog\<^sub>s\<^sub>b p p' mis]) = p\<^sub>2"
      by simp
    ultimately
    have "history_consistent \<theta> p\<^sub>2 (xs @ [Prog\<^sub>s\<^sub>b p p' mis])"
      by simp
    thus ?thesis
      by (simp add: Prog\<^sub>s\<^sub>b step)
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  qed
qed


(* FIXME: consistent naming: acquired vs. acquire; released vs. release *)
(* augment_rels, really only depends on the owned part of dom \<S>. *)
primrec release :: "'a memref list \<Rightarrow> addr set \<Rightarrow> rels \<Rightarrow> rels"
where
"release [] S \<R> = \<R>"
| "release (x#xs) S \<R> =
  (case x of
     Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> 
        (if volatile then release xs (S \<union> R - L) Map.empty 
         else release xs S \<R>)
   | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> release xs (S \<union> R - L) (augment_rels S R \<R>) 
   | _ \<Rightarrow> release xs S \<R>)"


lemma augment_rels_shared_exchange: "\<forall>a \<in> R. (a \<in> S') = (a \<in> S) \<Longrightarrow> augment_rels S R \<R> = augment_rels S' R \<R>"
apply (rule ext)
apply (auto simp add: augment_rels_def split: option.splits)
done


lemma sharing_consistent_shared_exchange: 
assumes shared_eq: "\<forall>a \<in> all_acquired sb. \<S>' a = \<S> a"
assumes consis: "sharing_consistent \<S> \<O> sb" 
shows "sharing_consistent \<S>' \<O> sb"
using shared_eq consis
proof (induct sb arbitrary: \<S> \<S>' \<O>)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
        shared_eq: "\<forall>a \<in> A \<union> all_acquired sb. \<S>' a = \<S> a"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )
      from shared_eq
      have shared_eq': "\<forall>a\<in> all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by (auto simp add: augment_shared_def restrict_shared_def)
      from Cons.hyps [OF shared_eq' consis']
      have "sharing_consistent (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb".
      thus ?thesis
      using A_shared_owns L_A A_R R_owns shared_eq
        by (auto  simp add: Write\<^sub>s\<^sub>b True domIff)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
      shared_eq: "\<forall>a \<in> A \<union> all_acquired sb. \<S>' a = \<S> a"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
    from shared_eq
    have shared_eq': "\<forall>a\<in>all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by (auto simp add: augment_shared_def restrict_shared_def)
    from Cons.hyps [OF shared_eq' consis']
    have "sharing_consistent (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb".
    thus ?thesis
    using A_shared_owns L_A A_R R_owns shared_eq
      by (auto  simp add: Ghost\<^sub>s\<^sub>b domIff)
  qed
qed



lemma release_shared_exchange: 
assumes shared_eq: "\<forall>a \<in> \<O> \<union> all_acquired sb. \<S>' a = \<S> a"
assumes consis: "sharing_consistent \<S> \<O> sb" 
shows "release sb (dom \<S>') \<R> = release sb (dom \<S>) \<R>"
using shared_eq consis 
proof (induct sb arbitrary: \<S> \<S>' \<O> \<R>)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
        shared_eq: "\<forall>a \<in> \<O> \<union> A \<union> all_acquired sb. \<S>' a = \<S> a"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True )
      from shared_eq
      have shared_eq': "\<forall>a\<in>\<O> \<union> A - R \<union> all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by (auto simp add: augment_shared_def restrict_shared_def)
      from Cons.hyps [OF shared_eq' consis']
      have "release sb (dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty = release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty" .
      then show ?thesis
        by (auto  simp add: Write\<^sub>s\<^sub>b True domIff) 
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
      shared_eq: "\<forall>a \<in> \<O> \<union> A \<union> all_acquired sb. \<S>' a = \<S> a"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b )
    from shared_eq
    have shared_eq': "\<forall>a\<in>\<O> \<union> A - R \<union> all_acquired sb. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by (auto simp add: augment_shared_def restrict_shared_def)
    from A_shared_owns shared_eq R_owns have "\<forall>a\<in>R. (a \<in> dom \<S>) = (a \<in> dom \<S>')"
      by (auto simp add: domIff)
    from augment_rels_shared_exchange [OF this]
    have "(augment_rels (dom \<S>') R \<R>) = (augment_rels (dom \<S>) R \<R>)".
    
    with Cons.hyps [OF shared_eq' consis']
    have "release sb (dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>') R \<R>) = 
            release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>) R \<R>)" by simp
    then show ?thesis
      by (clarsimp  simp add: Ghost\<^sub>s\<^sub>b domIff) 
  qed
qed

lemma release_append: 
"\<And>\<S> \<R>. release (sb@xs) (dom \<S>) \<R> = release xs (dom (share sb \<S>)) (release sb (dom (\<S>)) \<R>)"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "Map.empty"]
      show ?thesis
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
   qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    with Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "augment_rels (dom \<S>) R \<R>"]
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

locale xvalid_program = valid_program +
  fixes valid
  assumes valid_implies_valid_prog:     
     "\<lbrakk>i < length ts; 
      ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); valid ts\<rbrakk> \<Longrightarrow> valid_prog p" 

  assumes valid_implies_valid_prog_hd:     
     "\<lbrakk>i < length ts; 
      ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); valid ts\<rbrakk> \<Longrightarrow> valid_prog (hd_prog p sb)" 
  assumes distinct_load_tmps_prog_step: 
    "\<lbrakk>i < length ts; 
      ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); \<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid ts\<rbrakk> 
     \<Longrightarrow>
      distinct_load_tmps is' \<and> 
      (load_tmps is' \<inter> load_tmps is = {}) \<and>
      (load_tmps is' \<inter> read_tmps sb) = {}"

  assumes valid_data_dependency_prog_step: 
    "\<lbrakk>i < length ts;
      ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); \<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid ts\<rbrakk> 
     \<Longrightarrow> 
     data_dependency_consistent_instrs (dom \<theta> \<union> load_tmps is) is' \<and> 
     load_tmps is' \<inter> \<Union>(fst ` store_sops is)  = {} \<and>
     load_tmps is' \<inter> \<Union>(fst ` write_sops sb)  = {}"

  assumes load_tmps_fresh_prog_step:
  "\<lbrakk>i < length ts;
      ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); \<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid ts\<rbrakk> 
   \<Longrightarrow> 
   load_tmps is' \<inter> dom \<theta> = {}"

  assumes valid_sops_prog_step:
      "\<lbrakk>\<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid_prog p\<rbrakk>\<Longrightarrow> \<forall>sop\<in>store_sops is'. valid_sop sop"

  assumes prog_step_preserves_valid:
      "\<lbrakk>i < length ts;
        ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); \<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is'); valid ts\<rbrakk> \<Longrightarrow>
        valid (ts[i:=(p',is@is',\<theta>,sb@[Prog\<^sub>s\<^sub>b p p' is'],\<D>,\<O>,\<R>)])"

  assumes flush_step_preserves_valid:
      "\<lbrakk>i < length ts;
        ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); (m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>f (m',sb',\<O>',\<R>',\<S>'); valid ts\<rbrakk> \<Longrightarrow>
        valid (ts[i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')])"

  assumes sbh_step_preserves_valid:
      "\<lbrakk>i < length ts;
        ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); 
        (is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b\<^sub>h (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>'); 
       valid ts\<rbrakk> 
       \<Longrightarrow>
       valid (ts[i:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')])"



lemma refl': "x = y \<Longrightarrow> r^** x y"
  by auto



lemma no_volatile_Read\<^sub>s\<^sub>b_volatile_reads_consistent:
  "\<And>m. outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {} \<Longrightarrow> volatile_reads_consistent m sb"
  apply (induct sb)
  apply  simp
  subgoal for a sb m
  apply (case_tac a)
  apply (auto split: if_split_asm)
  done
  done


theorem (in program) flush_store_buffer_append:
shows "\<And>ts p m \<theta> \<O> \<R> \<D> \<S> is  \<O>'. 
 \<lbrakk>i < length ts;
  instrs (sb@sb') @ is\<^sub>s\<^sub>b = is @ prog_instrs (sb@sb');
  causal_program_history is\<^sub>s\<^sub>b (sb@sb');
  ts!i = (p,is,\<theta> |` (dom \<theta> - read_tmps (sb@sb')),x,\<D>,\<O>,\<R>);
  p=hd_prog p\<^sub>s\<^sub>b (sb@sb');
  (last_prog p\<^sub>s\<^sub>b (sb@sb')) = p\<^sub>s\<^sub>b;
  reads_consistent True \<O>' m sb; 
  history_consistent \<theta> p (sb@sb');
  \<forall>sop \<in> write_sops sb. valid_sop sop;
  distinct_read_tmps (sb@sb');
  volatile_reads_consistent m sb
\<rbrakk>
  \<Longrightarrow>
  \<exists>is'. instrs sb' @ is\<^sub>s\<^sub>b = is' @ prog_instrs sb' \<and>
     (ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* 
     (ts[i:=(last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb,is',\<theta>|` (dom \<theta> - read_tmps sb'),x,
       (\<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}),
       acquired True sb \<O>, release sb (dom \<S>) \<R>)], flush sb m,share sb \<S>)"
proof (induct sb)
  case Nil
  thus ?case by (auto simp add: list_update_id' split: if_split_asm)
next
case (Cons r sb)
  interpret direct_computation:
    computation direct_memop_step empty_storebuffer_step program_step "\<lambda>p p' is sb. sb".
  have ts_i: 
    "ts!i = (p,is,\<theta> |` (dom \<theta> - read_tmps ((r#sb)@sb')),x,\<D>,\<O>,\<R>)"
    by fact
  have "is": "instrs ((r # sb) @ sb') @ is\<^sub>s\<^sub>b = is @ prog_instrs ((r # sb) @ sb')" by fact

 
  have i_bound: "i < length ts" by fact
  have causal: "causal_program_history is\<^sub>s\<^sub>b ((r # sb) @ sb')" by fact
  hence causal': "causal_program_history is\<^sub>s\<^sub>b (sb @ sb')" 
    by (auto simp add: causal_program_history_def)

  note reads_consis = \<open>reads_consistent True \<O>' m (r#sb)\<close>
  note p = \<open>p = hd_prog p\<^sub>s\<^sub>b ((r#sb)@sb')\<close>
  note p\<^sub>s\<^sub>b = \<open>last_prog p\<^sub>s\<^sub>b ((r # sb) @ sb') = p\<^sub>s\<^sub>b\<close>
  note hist_consis = \<open>history_consistent \<theta> p ((r#sb)@sb')\<close>
  note valid_sops = \<open>\<forall>sop \<in> write_sops (r#sb). valid_sop sop\<close>
  note dist = \<open>distinct_read_tmps ((r#sb)@sb')\<close>
  note vol_read_consis = \<open>volatile_reads_consistent m (r#sb)\<close>

  show ?case
  proof (cases r)
    case (Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 pis)

    from vol_read_consis
    have vol_read_consis': "volatile_reads_consistent m sb"
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    from hist_consis  obtain
      prog_step: "\<theta>|` (dom \<theta> - read_tmps (sb @ sb'))\<turnstile> p\<^sub>1 \<rightarrow>\<^sub>p (p\<^sub>2, pis)" and
      hist_consis': "history_consistent \<theta> p\<^sub>2 (sb @ sb')" 
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from p obtain  p: "p = p\<^sub>1" 
      by (simp add: Prog\<^sub>s\<^sub>b)

    from history_consistent_hd_prog [OF hist_consis']
    have hist_consis'': "history_consistent \<theta> (hd_prog p\<^sub>2 (sb @ sb')) (sb @ sb')" .
    from "is"
    have "is": "instrs (sb @ sb') @ is\<^sub>s\<^sub>b = (is @ pis) @ prog_instrs (sb @ sb')"
      by (simp add: Prog\<^sub>s\<^sub>b)
    
    
    from ts_i "is" have 
      ts_i: "ts!i = (p, is,\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x, \<D>, \<O>,\<R>)"
      by (simp add: Prog\<^sub>s\<^sub>b)
   
    let ?ts'= "ts[i:=(p\<^sub>2,is@pis,\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x,\<D>,\<O>,\<R>)]"
    from direct_computation.Program [OF i_bound ts_i prog_step [simplified p[symmetric]]]
    have "(ts,m,\<S>) \<Rightarrow>\<^sub>d (?ts',m,\<S>)" by simp    

    also
    from i_bound have i_bound': "i < length ?ts'"
      by auto

    from i_bound
    have ts'_i: "?ts'!i = (p\<^sub>2,is@pis,(\<theta> |` (dom \<theta> - read_tmps (sb @ sb'))),x, \<D>, \<O>,\<R>)"
      by auto

    from history_consistent_hd_prog_p [OF hist_consis'] 
    have p\<^sub>2_hd_prog: " p\<^sub>2 = hd_prog p\<^sub>2 (sb @ sb')".

    from reads_consis have reads_consis': "reads_consistent True \<O>' m sb"
      by (simp add: Prog\<^sub>s\<^sub>b)

    from valid_sops have valid_sops': "\<forall>sop \<in> write_sops sb. valid_sop sop"
      by (simp add: Prog\<^sub>s\<^sub>b)

    from dist have dist': "distinct_read_tmps (sb@sb')"
      by (simp add: Prog\<^sub>s\<^sub>b)
    

    from p\<^sub>s\<^sub>b have last_prog_p\<^sub>2: "last_prog p\<^sub>2 (sb @ sb') = p\<^sub>s\<^sub>b"
      by (simp add: Prog\<^sub>s\<^sub>b)
    from hd_prog_last_prog_end [OF p\<^sub>2_hd_prog this]
    have p\<^sub>2_hd_prog': "p\<^sub>2 = hd_prog p\<^sub>s\<^sub>b (sb @ sb')".
    from last_prog_p\<^sub>2 [symmetric] have last_prog': "last_prog p\<^sub>s\<^sub>b (sb @ sb') = p\<^sub>s\<^sub>b"
      by (simp add: last_prog_idem)
    

    from Cons.hyps [OF i_bound'  "is" causal' ts'_i p\<^sub>2_hd_prog' last_prog' reads_consis' 
      hist_consis' valid_sops' dist' vol_read_consis'] i_bound 
    obtain is' where
      is': "instrs sb' @ is\<^sub>s\<^sub>b = is' @ prog_instrs sb'" and
      step: "(?ts', m,\<S>) \<Rightarrow>\<^sub>d\<^sup>*
         (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb, is',
          \<theta> |` (dom \<theta> - read_tmps sb'), x, \<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {},
          acquired True sb \<O>,release sb (dom \<S>) \<R>)],
          flush sb m,share sb \<S> )"
      by (auto)
    from p\<^sub>2_hd_prog' 
    have last_prog_eq: "last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb = last_prog p\<^sub>2 sb"
      by (simp add: last_prog_hd_prog_append)
    note step
    finally show ?thesis
      using is' 
      by (simp add: Prog\<^sub>s\<^sub>b last_prog_eq)
  next
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    obtain D f where sop: "sop=(D,f)"
      by (cases sop)


    from vol_read_consis
    have vol_read_consis': "volatile_reads_consistent (m(a:=v)) sb"
      by (auto simp add: Write\<^sub>s\<^sub>b)

    from hist_consis obtain 
      D_tmps: "D \<subseteq> dom \<theta>" and
      f_v: "f \<theta> = v" and
      dep: "D \<inter> read_tmps (sb@sb') = {}" and
      hist_consis': "history_consistent \<theta> p (sb@sb')"
      by (simp add: Write\<^sub>s\<^sub>b sop split: option.splits)

    from dist have dist': "distinct_read_tmps (sb@sb')" by (auto simp add: Write\<^sub>s\<^sub>b)

    from valid_sops obtain "valid_sop sop" and
      valid_sops': "\<forall>sop \<in> write_sops sb. valid_sop sop" 
      by (simp add: Write\<^sub>s\<^sub>b)
    interpret valid_sop sop by fact
    from valid_sop [OF sop D_tmps]
    have "f \<theta> = f (\<theta> |` D)" .
    moreover
    from dep D_tmps have D_subset: "D \<subseteq> (dom \<theta> - read_tmps (sb@sb'))"
      by auto
    moreover from D_subset have "(\<theta>|`(dom \<theta> - read_tmps (sb@sb')) |` D) = \<theta> |` D"
      apply -
      apply (rule ext)
      apply (auto simp add: restrict_map_def)
      done
    moreover from D_subset D_tmps have "D \<subseteq> dom (\<theta> |` (dom \<theta> - read_tmps (sb@sb')))"
      by simp
    moreover
    note valid_sop [OF sop this] 
    ultimately have f_v': "f (\<theta>|`(dom \<theta> - read_tmps (sb@sb'))) = v"
      by (simp add: f_v)

    interpret causal': causal_program_history "is\<^sub>s\<^sub>b" "sb@sb'" by fact

    from "is"
    have "Write volatile a sop A L R W# instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is @ prog_instrs (sb @ sb')"
      by (simp add: Write\<^sub>s\<^sub>b)
    with causal'.causal_program_history [of "[]", simplified, OF refl]    
    obtain is' where "is": "is=Write volatile a sop A L R W#is'" and
      is': "instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is' @ prog_instrs (sb @ sb')"
      by auto

    from ts_i "is"
    have ts_i: "ts!i = (p,Write volatile a sop A L R W#is',
      \<theta> |` (dom \<theta> - read_tmps (sb@sb')),x,\<D>,\<O>,\<R>)"
      by (simp add: Write\<^sub>s\<^sub>b)
    
    from p have p': "p = hd_prog p\<^sub>s\<^sub>b (sb@sb')"
      by (auto simp add: Write\<^sub>s\<^sub>b hd_prog_idem)

    from p\<^sub>s\<^sub>b have p\<^sub>s\<^sub>b': "last_prog p\<^sub>s\<^sub>b (sb @ sb') = p\<^sub>s\<^sub>b"
      by (simp add: Write\<^sub>s\<^sub>b)

    show ?thesis
    proof (cases volatile)
      case False
      have memop_step:
	"(Write volatile a sop A L R W#is',\<theta>|`(dom \<theta> - read_tmps (sb@sb')),
                 x,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow> 
           (is',\<theta>|` (dom \<theta> - read_tmps (sb@sb')),x,m(a:=v),\<D>,\<O>,\<R>,\<S>)"
	using D_subset
	apply (simp only: sop f_v' [symmetric] False)
	apply (rule direct_memop_step.WriteNonVolatile)
	done
    
      let ?ts' = "ts[i := (p, is',\<theta> |` (dom \<theta> - read_tmps (sb @ sb')),x, \<D>, \<O>,\<R>)]"
      from direct_computation.Memop [OF i_bound ts_i  memop_step]
      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (?ts', m(a := v), \<S>)".

      also
      from reads_consis have reads_consis': "reads_consistent True \<O>' (m(a:=v)) sb"
	by (auto simp add: Write\<^sub>s\<^sub>b False)
      from i_bound have i_bound': "i < length ?ts'"
	by auto
    
      from i_bound
      have ts'_i: "?ts' ! i = (p, is',\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x, \<D>, \<O>,\<R>)"
	by simp      

      from Cons.hyps [OF i_bound' is' causal' ts'_i p' p\<^sub>s\<^sub>b' reads_consis' hist_consis' 
	valid_sops' dist' vol_read_consis'] i_bound
      obtain is'' where
	is'': "instrs sb' @ is\<^sub>s\<^sub>b = is'' @ prog_instrs sb'" and
	steps: "(?ts',m(a:=v),\<S>) \<Rightarrow>\<^sub>d\<^sup>* 
        (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb, is'',
	    \<theta> |` (dom \<theta> - read_tmps sb'), x, 
            \<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}, acquired True sb \<O>, release sb (dom \<S>) \<R>)],
         flush sb (m(a := v)),share sb \<S>)"
	by (auto simp del: fun_upd_apply)
      note steps
      finally
      show ?thesis
	using is''
	by (simp add: Write\<^sub>s\<^sub>b False)
    next
      case True
      have memop_step:
	"(Write volatile a sop A L R W#is',\<theta>|`(dom \<theta> - read_tmps (sb@sb')),
                 x,m,\<D>,\<O>,\<R>,\<S> ) \<rightarrow> 
           (is',\<theta>|` (dom \<theta> - read_tmps (sb@sb')),x,m(a:=v),True,\<O> \<union> A - R,Map.empty,\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	using D_subset
	apply (simp only: sop f_v' [symmetric] True)
	apply (rule direct_memop_step.WriteVolatile)
	done

      let ?ts' = "ts[i := (p, is', \<theta> |` (dom \<theta> - read_tmps (sb @ sb')),x, True, \<O> \<union> A - R,Map.empty)]"
      from direct_computation.Memop [OF i_bound ts_i  memop_step]
      have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (?ts', m(a := v), \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

      also
      from reads_consis have reads_consis': "reads_consistent True (\<O>' \<union> A - R)(m(a:=v)) sb"
	by (auto simp add: Write\<^sub>s\<^sub>b True)
      from i_bound have i_bound': "i < length ?ts'"
	by auto
    
      from i_bound
      have ts'_i: "?ts' ! i = (p, is',\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x, True, \<O> \<union> A - R,Map.empty)"
	by simp      

      from Cons.hyps [OF i_bound' is' causal' ts'_i p' p\<^sub>s\<^sub>b' reads_consis' hist_consis' 
	valid_sops' dist' vol_read_consis', of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"] i_bound
      obtain is'' where
	is'': "instrs sb' @ is\<^sub>s\<^sub>b = is'' @ prog_instrs sb'" and
	steps: "(?ts',m(a:=v),\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<Rightarrow>\<^sub>d\<^sup>* 
        (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb, is'',
            \<theta> |` (dom \<theta> - read_tmps sb'), x, 
	    True, acquired True sb (\<O> \<union> A - R),release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) Map.empty)],
         flush sb (m(a := v)), share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	by (auto simp del: fun_upd_apply)
      note steps
      finally
      show ?thesis
	using is''
	by (simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)

    from vol_read_consis reads_consis obtain v: "v=m a" and r_consis: "reads_consistent True \<O>' m sb" and
      vol_read_consis': "volatile_reads_consistent m sb"
      by (cases volatile) (auto simp add: Read\<^sub>s\<^sub>b)

    from valid_sops have valid_sops': "\<forall>sop \<in> write_sops sb. valid_sop sop"  
      by (simp add: Read\<^sub>s\<^sub>b)

    from hist_consis obtain \<theta>: "\<theta> t = Some v" and 
      hist_consis': "history_consistent \<theta> p (sb@sb')" 
      by (simp add: Read\<^sub>s\<^sub>b split: option.splits)
    from dist obtain t_notin: "t \<notin> read_tmps (sb@sb')" and
      dist': "distinct_read_tmps (sb@sb')" by (simp add: Read\<^sub>s\<^sub>b)
    from \<theta> t_notin have restrict_commute:
      "(\<theta>|` (dom \<theta> - read_tmps (sb@sb')))(t\<mapsto>v) =
        \<theta>|` (dom \<theta> - read_tmps (sb@sb'))"
      apply -
      apply (rule ext)
      apply (auto simp add: restrict_map_def domIff)
      done
    from \<theta> t_notin 
    have restrict_commute': 
      "((\<theta> |` (dom \<theta> - insert t (read_tmps (sb@sb'))))(t \<mapsto> v)) =
          \<theta>|` (dom \<theta> - read_tmps (sb@sb'))"
      apply -
      apply (rule ext)
      apply (auto simp add: restrict_map_def domIff)
      done

    interpret causal': causal_program_history "is\<^sub>s\<^sub>b" "sb@sb'" by fact

    from "is"
    have "Read volatile a t # instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is @ prog_instrs (sb @ sb')"
      by (simp add: Read\<^sub>s\<^sub>b)

    with causal'.causal_program_history [of "[]", simplified, OF refl]    
    obtain is' where "is": "is=Read volatile a t#is'" and
      is': "instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is' @ prog_instrs (sb @ sb')"
      by auto

    from ts_i "is"
    have ts_i: "ts!i = (p,Read volatile a t#is',
                 \<theta> |` (dom \<theta> - insert t (read_tmps (sb@sb'))),x,\<D>,\<O>,\<R>)"
      by (simp add: Read\<^sub>s\<^sub>b)

    from direct_memop_step.Read [of volatile a t "is'" "\<theta>|` (dom \<theta> - insert t (read_tmps (sb@sb')))" x m \<D> \<O> \<R> \<S>]
    have memop_step: " 
          (Read volatile a t # is',
            \<theta> |` (dom \<theta> - insert t (read_tmps (sb @ sb'))), x, m, \<D>, \<O>,\<R>,\<S>) \<rightarrow> 
          (is',
             \<theta> |` (dom \<theta> - (read_tmps (sb @ sb'))), x, m, \<D>, \<O>, \<R>,\<S>)"
      by (simp add: v [symmetric] restrict_commute restrict_commute')

    let ?ts' = "ts[i := (p, is',
                 \<theta> |` (dom \<theta> - read_tmps (sb @ sb')),x, \<D>, \<O>,\<R>)]"

    from direct_computation.Memop [OF i_bound ts_i memop_step]
    have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (?ts', m, \<S>)".

    also

    from i_bound have i_bound': "i < length ?ts'"
      by auto

    from i_bound
    have ts'_i: "?ts'!i = (p,is', (\<theta> |` (dom \<theta> - read_tmps (sb @ sb'))),x,\<D>, \<O>, \<R>)"
      by auto

    from p have p': "p = hd_prog p\<^sub>s\<^sub>b (sb@sb')"
      by (auto simp add: Read\<^sub>s\<^sub>b hd_prog_idem)

    from p\<^sub>s\<^sub>b have p\<^sub>s\<^sub>b': "last_prog p\<^sub>s\<^sub>b (sb @ sb') = p\<^sub>s\<^sub>b"
      by (simp add: Read\<^sub>s\<^sub>b)

    
    from Cons.hyps [OF i_bound' is' causal' ts'_i p' p\<^sub>s\<^sub>b' r_consis  hist_consis'
    valid_sops' dist' vol_read_consis']
    
    obtain is'' where
      is'': "instrs sb' @ is\<^sub>s\<^sub>b = is'' @ prog_instrs sb'" and
      steps: "(?ts',m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* 
          (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb, is'',
             \<theta> |` (dom \<theta> - read_tmps sb'),x, \<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}, 
             acquired True sb \<O>, release sb (dom \<S>) \<R>)],
             flush sb m,share sb \<S>)"
      by (auto simp del: fun_upd_apply)

    note steps
    finally
    show ?thesis
      using is''
      by (simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)

    from vol_read_consis
    have vol_read_consis': "volatile_reads_consistent m sb"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)

    from reads_consis have  r_consis: "reads_consistent True (\<O>' \<union> A - R) m sb"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)

    from valid_sops have valid_sops': "\<forall>sop \<in> write_sops sb. valid_sop sop"  
      by (simp add: Ghost\<^sub>s\<^sub>b)

    from hist_consis obtain 
      hist_consis': "history_consistent \<theta> p (sb@sb')" 
      by (simp add: Ghost\<^sub>s\<^sub>b)

    from dist obtain 
      dist': "distinct_read_tmps (sb@sb')" by (simp add: Ghost\<^sub>s\<^sub>b)

    interpret causal': causal_program_history "is\<^sub>s\<^sub>b" "sb@sb'" by fact

    from "is"
    have "Ghost A L R W# instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is @ prog_instrs (sb @ sb')"
      by (simp add: Ghost\<^sub>s\<^sub>b)

    with causal'.causal_program_history [of "[]", simplified, OF refl]    
    obtain is' where "is": "is=Ghost A L R W#is'" and
      is': "instrs (sb @ sb') @ is\<^sub>s\<^sub>b = is' @ prog_instrs (sb @ sb')"
      by auto

    from ts_i "is"
    have ts_i: "ts!i = (p,Ghost A L R W#is',
                 \<theta> |` (dom \<theta> - (read_tmps (sb@sb'))),x,\<D>,\<O>,\<R>)"
      by (simp add: Ghost\<^sub>s\<^sub>b)

    from direct_memop_step.Ghost [of A L R W "is'" 
      "\<theta>|` (dom \<theta> - (read_tmps (sb@sb')))" x  m \<D> "\<O>" \<R> \<S>]
    have memop_step:"
      (Ghost A L R W# is',\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x, m, \<D>, \<O>, \<R>, \<S>) 
      \<rightarrow> (is',\<theta> |` (dom \<theta> - read_tmps (sb @ sb')), x, m, \<D>, \<O> \<union> A - R , augment_rels (dom \<S>) R \<R>, 
      \<S> \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L)".

    let ?ts' = "ts[i := (p, is',
                 \<theta> |` (dom \<theta> - read_tmps (sb @ sb')),x, \<D>, \<O> \<union> A - R, augment_rels (dom \<S>) R \<R>)]"
    from direct_computation.Memop [OF i_bound ts_i memop_step]
    have "(ts, m, \<S>) \<Rightarrow>\<^sub>d (?ts', m, \<S> \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L)".

    also

    from i_bound have i_bound': "i < length ?ts'"
      by auto

    from i_bound
    have ts'_i: "?ts'!i = (p,is',(\<theta> |` (dom \<theta> - read_tmps (sb @ sb'))),x, \<D>, \<O> \<union> A - R,augment_rels (dom \<S>) R \<R> )"
      by auto

    from p have p': "p = hd_prog p\<^sub>s\<^sub>b (sb@sb')"
      by (auto simp add: Ghost\<^sub>s\<^sub>b hd_prog_idem)

    from p\<^sub>s\<^sub>b have p\<^sub>s\<^sub>b': "last_prog p\<^sub>s\<^sub>b (sb @ sb') = p\<^sub>s\<^sub>b"
      by (simp add: Ghost\<^sub>s\<^sub>b)

    from Cons.hyps [OF   i_bound' is' causal' ts'_i p' p\<^sub>s\<^sub>b' r_consis hist_consis' 
      valid_sops' dist' vol_read_consis', of "\<S> \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L"] 
    obtain is'' where
      is'': "instrs sb' @ is\<^sub>s\<^sub>b = is'' @ prog_instrs sb'" and
      steps: "(?ts',m,\<S> \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L) \<Rightarrow>\<^sub>d\<^sup>* 
          (ts[i := (last_prog (hd_prog p\<^sub>s\<^sub>b sb') sb, is'',
             \<theta> |` (dom \<theta> - read_tmps sb'),x, 
             \<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}, acquired True sb (\<O> \<union> A - R), 
              release sb (dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) (augment_rels (dom \<S>) R \<R>))],
           flush sb m,share sb (\<S> \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L))"
      by (auto simp add: list_update_overwrite simp del: fun_upd_apply)

    note steps
    finally
    show ?thesis
      using is''
      by (simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

corollary  (in program) flush_store_buffer:
  assumes i_bound: "i < length ts"
  assumes instrs: "instrs sb @ is\<^sub>s\<^sub>b = is @ prog_instrs sb"
  assumes cph: "causal_program_history is\<^sub>s\<^sub>b sb"
  assumes ts_i: "ts!i = (p,is,\<theta> |` (dom \<theta> - read_tmps sb),x,\<D>,\<O>,\<R>)"
  assumes p: "p=hd_prog p\<^sub>s\<^sub>b sb"
  assumes last_prog: "(last_prog p\<^sub>s\<^sub>b sb) = p\<^sub>s\<^sub>b"
  assumes reads_consis: "reads_consistent True \<O>' m sb"
  assumes hist_consis: "history_consistent \<theta> p sb"
  assumes valid_sops: "\<forall>sop \<in> write_sops sb. valid_sop sop"
  assumes dist: "distinct_read_tmps sb"
  assumes vol_read_consis: "volatile_reads_consistent m sb"
  shows "(ts,m,\<S>) \<Rightarrow>\<^sub>d\<^sup>* 
         (ts[i:=(p\<^sub>s\<^sub>b,is\<^sub>s\<^sub>b, \<theta>,x,
            \<D> \<or> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {},acquired True sb \<O>, release sb (dom \<S>) \<R>)],
             flush sb m,share sb \<S>)"
using flush_store_buffer_append [where sb'="[]", simplified, OF i_bound instrs cph ts_i [simplified] p last_prog reads_consis hist_consis valid_sops dist vol_read_consis] last_prog
by simp


lemma last_prog_same_append: "\<And>xs p\<^sub>s\<^sub>b. last_prog p\<^sub>s\<^sub>b (sb@xs) = p\<^sub>s\<^sub>b \<Longrightarrow> last_prog p\<^sub>s\<^sub>b xs = p\<^sub>s\<^sub>b"
  apply (induct sb)
  apply  simp
  subgoal for a sb xs p\<^sub>s\<^sub>b
  apply (case_tac a)
  apply     simp
  apply    simp
  apply   simp
  apply  (drule last_prog_to_last_prog_same)
  apply  simp
  apply simp
  done
  done


lemma reads_consistent_drop_volatile_writes_no_volatile_reads: 
  "\<And>pending_write \<O> m. reads_consistent pending_write \<O> m sb \<Longrightarrow> 
  outstanding_refs is_volatile_Read\<^sub>s\<^sub>b ((dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)) sb) = {}"
  apply (induct sb)
  apply (auto split: memref.splits)
  done

(* cf reads_consistent_append
lemma reads_consistent_flush: 
"\<And>m. reads_consistent m sb \<Longrightarrow> 
  reads_consistent (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m) 
   (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  apply (induct sb)
  apply  simp
  apply (case_tac a)
  apply auto
  done
*)


lemma reads_consistent_flush_other: 
  assumes no_volatile_Write\<^sub>s\<^sub>b_sb: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
  shows "\<And>m pending_write \<O>. 
  \<lbrakk>outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb = {};
       reads_consistent pending_write \<O> m xs\<rbrakk> \<Longrightarrow> reads_consistent pending_write \<O> (flush sb m) xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  note no_inter = \<open>outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (x # xs) \<inter> 
    outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb = {}\<close>
  hence no_inter': "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb = {}"
    by (auto)
  note consis = \<open>reads_consistent pending_write \<O> m (x # xs)\<close>
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R)
    show ?thesis
    proof (cases volatile)
      case False
      from consis obtain consis': "reads_consistent pending_write \<O> (m(a := v)) xs" 
	by (simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF no_inter' consis']
      have "reads_consistent pending_write \<O> (flush sb (m(a := v))) xs".
      moreover
      from no_inter have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by (auto simp add: Write\<^sub>s\<^sub>b split: if_split_asm)
    
      from flush_update_other' [OF this no_volatile_Write\<^sub>s\<^sub>b_sb]
      have "(flush sb (m(a := v))) = (flush sb m)(a := v)".
      ultimately
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    next
      case True
      from consis obtain consis': "reads_consistent True (\<O> \<union> A - R) (m(a := v)) xs" and
	no_read: "(outstanding_refs is_volatile_Read\<^sub>s\<^sub>b xs = {} )"
	by (simp add: Write\<^sub>s\<^sub>b True)
      from Cons.hyps [OF no_inter' consis']
      have "reads_consistent True (\<O> \<union> A - R) (flush sb (m(a := v))) xs".
      moreover
      from no_inter have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by (auto simp add: Write\<^sub>s\<^sub>b split: if_split_asm)
    
      from flush_update_other' [OF this no_volatile_Write\<^sub>s\<^sub>b_sb]
      have "(flush sb (m(a := v))) = (flush sb m)(a := v)".
      ultimately
      show ?thesis
	using no_read
	by (simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from consis obtain val: "(\<not> volatile \<longrightarrow> (pending_write \<or> a \<in> \<O>) \<longrightarrow> v = m a)" and
      consis': "reads_consistent pending_write \<O> m xs"
      by (simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF no_inter' consis']
    have hyp: "reads_consistent pending_write \<O> (flush sb m) xs"
      by simp
    show ?thesis
    proof (cases volatile)
      case False
      from no_inter False have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)
      with no_volatile_Write\<^sub>s\<^sub>b_sb 
      have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
	apply (clarsimp simp add: outstanding_refs_conv is_Write\<^sub>s\<^sub>b_def split: memref.splits)
	apply force
	done
      with hyp val flush_unchanged_addresses  [OF this]
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b)
    next
      case True
      with hyp val show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b)
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed

lemma reads_consistent_flush_independent: 
  assumes no_volatile_Write\<^sub>s\<^sub>b_sb: "outstanding_refs is_Write\<^sub>s\<^sub>b sb \<inter> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b xs = {}"
  assumes consis: "reads_consistent pending_write \<O> m xs" 
  shows "reads_consistent pending_write \<O> (flush sb m) xs"
proof -
  from flush_unchanged_addresses [where sb=sb and m=m] no_volatile_Write\<^sub>s\<^sub>b_sb
  have "\<forall>a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b xs. flush sb m a = m a"
    by auto
  from reads_consistent_mem_eq_on_non_volatile_reads [OF this subset_refl consis]
  show ?thesis .
qed


lemma reads_consistent_flush_all_until_volatile_write_aux:
  assumes no_reads: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b xs = {}" 
  shows "\<And>m pending_write \<O>'.  \<lbrakk>reads_consistent pending_write \<O>' m xs; \<forall>i < length ts. 
    let (p,is,\<theta>,sb,\<D>,\<O>,\<R>) = ts!i in
      outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> 
      outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = {}\<rbrakk> 
 \<Longrightarrow> reads_consistent pending_write \<O>' (flush_all_until_volatile_write ts m) xs"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  have consis: "reads_consistent pending_write \<O>' m xs" by fact


  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t 
    where t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  from Cons.prems t obtain
    no_inter: "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> 
      outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) = {}" and
    no_inter': "\<forall>i < length ts. 
    let (p,is,\<theta>,sb,\<D>,\<O>,\<R>) = ts!i in
      outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> 
      outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = {}"
    by (force simp add: Let_def simp del: o_apply)


  have out1: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b 
    (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) = {}"
    by (auto simp add: outstanding_refs_conv dest: set_takeWhileD)

  from no_inter have "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs \<inter> 
    outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b  (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) = {}" 
    by auto

  from reads_consistent_flush_other [OF out1 this consis]
 
  have "reads_consistent pending_write \<O>' (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) m) xs".
  from Cons.hyps [OF this no_inter']
  show ?case
    by (simp add: t)
qed

(* FIXME: delete
lemma read_only_reads_takeWhile_owns:
  "\<And>\<O>. read_only_reads \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> \<O> = {}"
apply (induct sb)
apply clarsimp
apply (case_tac a)
apply auto
done
*)

lemma reads_consistent_flush_other': 
  assumes no_volatile_Write\<^sub>s\<^sub>b_sb: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
  shows "\<And>m  \<O>. 
  \<lbrakk>outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<inter> 
     (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))  
   )  = {};
  reads_consistent False \<O> m xs;
   read_only_reads \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<subseteq> RO\<rbrakk> 
  \<Longrightarrow> reads_consistent False \<O> (flush sb m) xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)

  note no_inter = Cons.prems (1)

  note consis = \<open>reads_consistent False \<O> m (x # xs)\<close>
  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto


  note RO = \<open>read_only_reads \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (x#xs)) \<subseteq> RO\<close>


  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R)
    show ?thesis
    proof (cases volatile)
      case False
      from consis obtain consis': "reads_consistent False \<O> (m(a := v)) xs" 
	by (simp add: Write\<^sub>s\<^sub>b False)

      from no_inter
      have no_inter': "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<inter> 
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))
        ) = {}"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False aargh)


      from RO
      have RO': "read_only_reads \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<subseteq> RO" 
	by (auto simp add: Write\<^sub>s\<^sub>b False)

      from Cons.hyps [OF no_inter' consis' RO']
      have "reads_consistent False \<O> (flush sb (m(a := v))) xs".
      moreover
      from no_inter have "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by (auto simp add: Write\<^sub>s\<^sub>b split: if_split_asm)
    
      from flush_update_other' [OF this no_volatile_Write\<^sub>s\<^sub>b_sb]
      have "(flush sb (m(a := v))) = (flush sb m)(a := v)".
      ultimately
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    next
      case True
      from consis obtain consis': "reads_consistent True (\<O> \<union> A - R) (m(a := v)) xs" and
	no_read: "(outstanding_refs is_volatile_Read\<^sub>s\<^sub>b xs = {})"
	by (simp add: Write\<^sub>s\<^sub>b True)

      from no_inter obtain
	a_notin: "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb" and
	disj: "(outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) xs) \<inter>
	        outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb = {}"
	by (auto simp add: Write\<^sub>s\<^sub>b True aargh misc_outstanding_refs_convs)

      from reads_consistent_flush_other [OF no_volatile_Write\<^sub>s\<^sub>b_sb disj consis']

      have "reads_consistent True (\<O> \<union> A - R) (flush sb (m(a := v))) xs".
      moreover
      note a_notin
    
      from flush_update_other' [OF this no_volatile_Write\<^sub>s\<^sub>b_sb]
      have "(flush sb (m(a := v))) = (flush sb m)(a := v)".
      ultimately
      show ?thesis
	using no_read
	by (simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from consis obtain val: "(\<not> volatile \<longrightarrow> a \<in> \<O> \<longrightarrow> v = m a)" and
      consis': "reads_consistent False \<O> m xs"
      by (simp add: Read\<^sub>s\<^sub>b)


    from RO
    have RO': "read_only_reads \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<subseteq> RO"
      by (auto simp add: Read\<^sub>s\<^sub>b )

    from no_inter
    have no_inter': "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<inter> 
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
        outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
        outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
        (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
        (\<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))
        ) = {}"
      by (fastforce simp add: Read\<^sub>s\<^sub>b aargh)


    show ?thesis
    proof (cases volatile)
      case True

      from Cons.hyps [OF no_inter' consis' RO'] 
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b True)
    next
      case False
      note non_volatile=this

      from Cons.hyps [OF no_inter' consis' RO'] 
      have hyp: "reads_consistent False \<O> (flush sb m) xs".

      show ?thesis
      proof (cases "a \<in> \<O>")
	case False
	with hyp show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b non_volatile False)
      next
	case True
	from no_inter True have a_notin: "a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	  by blast

	with no_volatile_Write\<^sub>s\<^sub>b_sb 
	have "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b sb"
	  apply (clarsimp simp add: outstanding_refs_conv is_Write\<^sub>s\<^sub>b_def split: memref.splits)
	  apply force
	  done

	from flush_unchanged_addresses  [OF this] hyp val 
	
	show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b non_volatile True)
      qed
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from consis obtain consis': "reads_consistent False (\<O> \<union> A - R) m xs" 
      by (simp add: Ghost\<^sub>s\<^sub>b)

    from RO
    have RO': "read_only_reads (\<O> \<union> A - R) (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<subseteq> RO"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)


    from no_inter
    have no_inter': "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb  \<inter> 
      (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
        outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O> \<union> A - R \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))
        ) = {}"
      by (fastforce simp add: Ghost\<^sub>s\<^sub>b aargh)

    from Cons.hyps [OF no_inter' consis' RO' ] 
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma reads_consistent_flush_all_until_volatile_write_aux':
  assumes no_reads: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b xs = {}" 
  assumes read_only_reads_RO: "read_only_reads \<O>' (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<subseteq> RO"
  shows "\<And>m.  \<lbrakk>reads_consistent False \<O>' m xs; \<forall>i < length ts. 
    let (p,is,\<theta>,sb,\<D>,\<O>) = ts!i in
      outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> 
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O>' \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))
        )  
       = {}
\<rbrakk> 
 \<Longrightarrow> reads_consistent False \<O>' (flush_all_until_volatile_write ts m) xs"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  have consis: "reads_consistent False \<O>' m xs" by fact


  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t 
    where t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  obtain
    no_inter: "outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<inter> 
    (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O>' \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))

        )  
       = {}" and
    no_inter': "\<forall>i < length ts. 
    let (p,is,\<theta>,sb,\<D>,\<O>) = ts!i in
      outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> 
       (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union>  
         outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs \<union> 
         outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) \<union> 
         (outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs) - RO) \<union> 
         (\<O>' \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) xs))
        )  
    = {}"
  proof -
    show ?thesis
      apply (rule that)
      using  Cons.prems (2) [rule_format, of 0]
      apply  (clarsimp simp add: t)
      apply clarsimp
      using Cons.prems (2)
      apply -
      subgoal for i
      apply (drule_tac x="Suc i" in spec)
      apply (clarsimp simp add: Let_def simp del: o_apply)
      done
      done
  qed


  have out1: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b 
    (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) = {}"
    by (auto simp add: outstanding_refs_conv dest: set_takeWhileD)

  from reads_consistent_flush_other' [OF out1 no_inter consis read_only_reads_RO ] 
  have "reads_consistent False \<O>' (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) m) xs".
  from Cons.hyps [OF this no_inter']
  show ?case
    by (simp add: t)
qed





(* cf. reads_consistent_drop_volatile_writes_no_volatile_reads
lemma reads_consistent_no_volatile_Read\<^sub>s\<^sub>b_drop: "\<And>m. reads_consistent m sb \<Longrightarrow> 
   outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = {}"
apply (induct sb)
apply  simp
apply (case_tac a)
apply auto
done
*)

lemma in_outstanding_refs_cases [consumes 1, case_names Write\<^sub>s\<^sub>b Read\<^sub>s\<^sub>b]:
  "a \<in> outstanding_refs P xs \<Longrightarrow>
       (\<And>volatile sop v A L R W.  (Write\<^sub>s\<^sub>b volatile a sop v A L R W) \<in> set xs \<Longrightarrow> P (Write\<^sub>s\<^sub>b volatile a sop v A L R W) \<Longrightarrow> C) \<Longrightarrow>
       (\<And>volatile t v.  (Read\<^sub>s\<^sub>b volatile a t v) \<in> set xs \<Longrightarrow> P (Read\<^sub>s\<^sub>b volatile a t v) \<Longrightarrow> C)
       \<Longrightarrow> C"
  apply (clarsimp simp add: outstanding_refs_conv)
  subgoal for x
  apply (case_tac x)
  apply fastforce+
  done
  done

lemma dropWhile_Cons: "(dropWhile P xs) = x#ys \<Longrightarrow> \<not> P x"
apply (induct xs)
apply (auto split: if_split_asm)
done

lemma reads_consistent_dropWhile: 
  "reads_consistent pending_write \<O> m (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = 
       reads_consistent True \<O> m  (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (case_tac "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)")
apply (simp only:)
apply  simp
apply (frule dropWhile_Cons)
apply (auto split: memref.splits)
done


theorem 
  reads_consistent_flush_all_until_volatile_write: 
  "\<And>i m pending_write. \<lbrakk>valid_ownership_and_sharing \<S> ts; 
  i < length ts; ts!i = (p, is,\<theta>, sb, \<D>, \<O>,\<R>); 
  reads_consistent pending_write \<O> m sb \<rbrakk> 
  \<Longrightarrow> reads_consistent True (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>)
  (flush_all_until_volatile_write ts m) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  note i_bound = \<open>i < length (t # ts)\<close>
  note ts_i = \<open>(t # ts) ! i = (p, is,\<theta>, sb, \<D>, \<O>,\<R>)\<close>
  note consis = \<open>reads_consistent pending_write \<O> m sb\<close>
  note valid = \<open>valid_ownership_and_sharing \<S> (t#ts)\<close>
  then interpret valid_ownership_and_sharing \<S> "t#ts".
  from valid_ownership_and_sharing_tl [OF valid] have valid': "valid_ownership_and_sharing \<S> ts".
    
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t 
    where t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)
  show ?case
  proof (cases i)
    case 0
    with ts_i t have sb_eq: "sb=sb\<^sub>t"
      by simp

    let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

    from reads_consistent_append [of pending_write \<O> m ?take_sb ?drop_sb] consis
    have consis': "reads_consistent True (acquired True ?take_sb \<O>) (flush ?take_sb m) ?drop_sb"
      apply (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<noteq> {}")
      apply  clarsimp
      apply clarsimp
      apply (simp add: reads_consistent_dropWhile [of pending_write])
      done


    from reads_consistent_drop_volatile_writes_no_volatile_reads [OF consis]
    have no_vol_Read\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = {}".
    hence "outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)
           =
           outstanding_refs (\<lambda>s. True) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
      by (auto simp add: outstanding_refs_conv)

    have "\<forall>i<length ts.
     let (p, is,\<theta>, sb', \<D>, \<O>,\<R>) = ts ! i
     in outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter>
        outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') = {}"
    proof - 
      {
	fix j p\<^sub>j "is\<^sub>j" \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j x
	assume j_bound: "j < length ts"
	assume ts_j: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
	assume x_in_sb: "x \<in> outstanding_refs (Not \<circ> is_volatile_Read\<^sub>s\<^sub>b) (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	assume x_in_j: "x \<in> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
	have False
	proof -
	  from outstanding_non_volatile_write_not_volatile_read_disj [rule_format, of "Suc j" 0, simplified, OF j_bound ts_j t]
	  sb_eq x_in_sb x_in_j 
	  show ?thesis
	    by auto
	qed
      }
      thus ?thesis
	by (auto simp add: Let_def)
    qed
    from reads_consistent_flush_all_until_volatile_write_aux [OF no_vol_Read\<^sub>s\<^sub>b consis' this]
    show ?thesis
      by (simp add: t sb_eq del: o_apply)
  next
    case (Suc k)
    with i_bound have k_bound: "k < length ts"
      by auto
      
    from ts_i Suc have ts_k: "ts ! k = (p, is,\<theta>, sb, \<D>, \<O>,\<R>)"
      by simp



    have "reads_consistent False \<O> (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) m) sb"
    proof -
      have no_vW: 
	"outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) = {}"
	apply (clarsimp simp add: outstanding_refs_conv )
	apply (drule set_takeWhileD)
	apply simp
	done
      
      
      from consis have consis': "reads_consistent False \<O> m sb"
	by (cases pending_write) (auto intro: reads_consistent_pending_write_antimono)
      note disj = outstanding_non_volatile_write_disj [where i=0, OF _  i_bound [simplified Suc], simplified, OF t ts_k ]
      
      
      from reads_consistent_flush_other' [OF no_vW disj consis' subset_refl] 
      show ?thesis .
    qed
    from Cons.hyps [OF valid' k_bound ts_k this]
    show ?thesis
      by (simp add: t)
  qed
qed


lemma split_volatile_Write\<^sub>s\<^sub>b_in_outstanding_refs:
  "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<Longrightarrow> (\<exists>sop v ys zs A L R W. xs = ys@(Write\<^sub>s\<^sub>b True a sop v A L R W#zs))"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have a_in: "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b (x # xs)" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      from a_in have "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
	by (auto simp add: False Write\<^sub>s\<^sub>b)
      from Cons.hyps [OF this] obtain sop'' v'' A'' L'' R'' W'' ys zs
	where "xs=ys@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
	by auto
      hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	by blast
    next
      case True
      note volatile = this
      show ?thesis
      proof (cases "a'=a")
	case False
	with a_in have "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
	  by (auto simp add: volatile Write\<^sub>s\<^sub>b)
	from Cons.hyps [OF this] obtain sop'' v'' A'' L'' R'' W'' ys zs
	  where "xs=ys@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
	  by auto
	hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
	  by auto
	thus ?thesis
	  by blast
      next
	case True
	then have "x#xs=[]@(Write\<^sub>s\<^sub>b True a sop v A L R W#xs)"
	  by (simp add: Write\<^sub>s\<^sub>b volatile True)
	thus ?thesis
	  by blast
      qed
    qed
  next
    case Read\<^sub>s\<^sub>b 
    from a_in have "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  next
    case Prog\<^sub>s\<^sub>b
    from a_in have "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  next
    case Ghost\<^sub>s\<^sub>b
    from a_in have "a \<in> outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  qed
qed

lemma sharing_consistent_mono_shared:
"\<And>\<S> \<S>' \<O>.
  dom \<S> \<subseteq> dom \<S>' \<Longrightarrow> sharing_consistent \<S> \<O> sb \<Longrightarrow> sharing_consistent \<S>' \<O> sb"
apply (induct sb)
apply simp
subgoal for a sb \<S> \<S>' \<O>
apply (case_tac a)
apply    clarsimp
         subgoal for volatile a D f v A L R W  
         apply (frule_tac A="\<S>" and B="\<S>'" and C="R" and x="W" in augment_mono_aux)
         apply (frule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and B="\<S>' \<oplus>\<^bsub>W\<^esub>  R" and C="L" in restrict_mono_aux)
         apply blast
         done
apply   clarsimp
apply  clarsimp
apply clarsimp
subgoal for A L R W
apply (frule_tac A="\<S>" and B="\<S>'" and C="R" and x="W" in augment_mono_aux)
apply (frule_tac A="\<S> \<oplus>\<^bsub>W\<^esub> R" and B="\<S>' \<oplus>\<^bsub>W\<^esub>  R" and C="L" in restrict_mono_aux)
apply blast
done
done
done

lemma sharing_consistent_mono_owns:
"\<And>\<O> \<O>' \<S>.
  \<O> \<subseteq> \<O>' \<Longrightarrow> sharing_consistent \<S> \<O> sb \<Longrightarrow> sharing_consistent \<S> \<O>' sb"
apply (induct sb)
apply simp
subgoal for a sb \<O> \<O>' \<S>
apply (case_tac a)
apply    clarsimp
         subgoal for volatile a D f v A L R W
         apply (frule_tac A="\<O>" and B="\<O>'" and C="A" in union_mono_aux)
         apply (frule_tac A="\<O> \<union> A" and B="\<O>' \<union> A" and C="R" in set_minus_mono_aux)
         apply fastforce
         done
apply   clarsimp
apply  clarsimp
apply clarsimp
subgoal for A L R W
apply (frule_tac A="\<O>" and B="\<O>'" and C="A" in union_mono_aux)
apply (frule_tac A="\<O> \<union> A" and B="\<O>' \<union> A" and C="R" in set_minus_mono_aux)
apply fastforce
done
done
done


(* FIXME: move up *)
primrec all_shared :: "'a memref list \<Rightarrow> addr set"
where 
  "all_shared [] = {}"
| "all_shared (i#is) =
    (case i of
      Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> (if volatile then R \<union> all_shared is else all_shared is)
     | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> R \<union> all_shared is
     | _ \<Rightarrow> all_shared is)"

lemma sharing_consistent_all_shared:
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> all_shared sb \<subseteq> dom \<S> \<union> \<O>"
  apply (induct sb)
  apply  clarsimp
  subgoal for a
  apply (case_tac a) 
  apply    (fastforce split: memref.splits if_split_asm)
  apply   clarsimp
  apply  clarsimp
  apply fastforce
  done
  done

lemma sharing_consistent_share_all_shared:
  "\<And>\<S>. dom (share sb \<S>) \<subseteq> dom \<S> \<union> all_shared sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop t A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"]
      show ?thesis
        by (auto simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"]
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed




primrec all_unshared :: "'a memref list \<Rightarrow> addr set"
where 
  "all_unshared [] = {}"
| "all_unshared (i#is) =
    (case i of
      Write\<^sub>s\<^sub>b volatile _ _ _  A L R W \<Rightarrow> (if volatile then L \<union> all_unshared is else all_unshared is)
     | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> L \<union> all_unshared is
     | _ \<Rightarrow> all_unshared is)"

lemma all_unshared_append: "all_unshared (xs @ ys) = all_unshared xs \<union> all_unshared ys"
  apply (induct xs)
  apply  simp
  subgoal for a
  apply (case_tac a)
  apply auto
  done
  done


lemma freshly_shared_owned:
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> dom (share sb \<S>) - dom \<S> \<subseteq> \<O>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)       
    with Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems show ?thesis by auto
  qed
qed

lemma unshared_all_unshared:
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> dom \<S> - dom (share sb \<S>) \<subseteq> all_unshared sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)       
    with Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems show ?thesis by auto
  qed
qed

lemma unshared_acquired_or_owned: 
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> all_unshared sb \<subseteq> all_acquired sb \<union> \<O>"
  apply (induct sb)
  apply  simp
  subgoal for a
  apply (case_tac a)
  apply auto+
  done
  done

lemma all_shared_acquired_or_owned: 
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> all_shared sb \<subseteq> all_acquired sb \<union> \<O>"
  apply (induct sb)
  apply  simp
  subgoal for a
  apply (case_tac a)
  apply auto+
  done
  done

(* FIXME: replace by thm sharing_consistent_shared_exchange? *)
lemma sharing_consistent_preservation:
"\<And>\<S> \<S>' \<O>. 
\<lbrakk>sharing_consistent \<S> \<O> sb;
 all_acquired sb \<inter> dom \<S> - dom \<S>' = {};
 all_unshared sb \<inter> dom \<S>' - dom \<S> = {}\<rbrakk>
 \<Longrightarrow> sharing_consistent \<S>' \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  have consis: "sharing_consistent \<S> \<O> (x # sb)" by fact
  have removed_cond: "all_acquired (x # sb) \<inter> dom \<S> - dom \<S>' = {}" by fact
  have new_cond: "all_unshared (x # sb) \<inter> dom \<S>' - dom \<S> = {}" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False with Write\<^sub>s\<^sub>b Cons show ?thesis
	by auto
    next
      case True
      from consis obtain 
	A: "A \<subseteq> dom \<S> \<union> \<O>" and
	L: "L \<subseteq> A" and
        A_R: "A \<inter> R = {}" and
	R: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      

      from removed_cond obtain rem_cond: "(A \<union> all_acquired sb) \<inter> dom \<S> \<subseteq> dom \<S>'" by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      hence rem_cond': "all_acquired sb \<inter> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	by auto

      from new_cond obtain "(L \<union> all_unshared sb) \<inter> dom \<S>' \<subseteq> dom \<S>" by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      hence new_cond': "all_unshared sb \<inter> dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"     
	by auto
      
      from Cons.hyps [OF consis' rem_cond' new_cond']
      have "sharing_consistent (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb".
      moreover
      from A rem_cond have "A \<subseteq> dom \<S>' \<union> \<O>"
	by auto
      moreover note L A_R R
      ultimately show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from consis obtain 
      A: "A \<subseteq> dom \<S> \<union> \<O>" and
      L: "L \<subseteq> A" and
      A_R: "A \<inter> R = {}" and
      R: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      

    from removed_cond obtain rem_cond: "(A \<union> all_acquired sb) \<inter> dom \<S> \<subseteq> dom \<S>'" by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    hence rem_cond': "all_acquired sb \<inter> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by auto

    from new_cond obtain "(L \<union> all_unshared sb) \<inter> dom \<S>' \<subseteq> dom \<S>" by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    hence new_cond': "all_unshared sb \<inter> dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"     
      by auto
      
    from Cons.hyps [OF consis' rem_cond' new_cond']
    have "sharing_consistent (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb".
    moreover
    from A rem_cond have "A \<subseteq> dom \<S>' \<union> \<O>"
      by auto
    moreover note L A_R R
    ultimately show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed (insert Cons, auto)
qed 

lemma (in sharing_consis) sharing_consis_preservation:
assumes dist: 
        "\<forall>i < length ts. let (_,_,_,sb,_,_,_) = ts!i in 
          all_acquired sb \<inter> dom \<S> - dom \<S>' = {} \<and> all_unshared sb \<inter> dom \<S>' - dom \<S> = {}"   
shows "sharing_consis \<S>' ts"   
proof 
  fix i p "is" \<O> \<R> \<D> \<theta> sb
  assume i_bound: "i < length ts"
  assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  show "sharing_consistent \<S>' \<O> sb"
  proof -
    from sharing_consis [OF i_bound ts_i]
    have consis: "sharing_consistent \<S> \<O> sb".
    from dist [rule_format, OF i_bound] ts_i
    obtain 
      acq: "all_acquired sb \<inter> dom \<S> - dom \<S>' = {}" and
      uns: "all_unshared sb \<inter> dom \<S>' - dom \<S> = {}"
      by auto
    from sharing_consistent_preservation [OF consis acq uns]
    show ?thesis .
  qed
qed

lemma (in sharing_consis) sharing_consis_shared_exchange:
assumes dist: 
        "\<forall>i < length ts. let (_,_,_,sb,_,_,_) = ts!i in 
          \<forall>a \<in> all_acquired sb. \<S>' a = \<S> a"   
shows "sharing_consis \<S>' ts"   
proof 
  fix i p "is" \<O> \<R> \<D> \<theta> sb
  assume i_bound: "i < length ts"
  assume ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  show "sharing_consistent \<S>' \<O> sb"
  proof -
    from sharing_consis [OF i_bound ts_i]
    have consis: "sharing_consistent \<S> \<O> sb".
    from dist [rule_format, OF i_bound] ts_i
    obtain 
      dist_sb: "\<forall>a \<in> all_acquired sb. \<S>' a = \<S> a"
      by auto
    from sharing_consistent_shared_exchange [OF dist_sb consis]
    show ?thesis .
  qed
qed



lemma all_acquired_takeWhile: "all_acquired (takeWhile P sb) \<subseteq> all_acquired sb"
proof -
  from all_acquired_append [of "takeWhile P sb" "dropWhile P sb"] 
  show ?thesis
    by auto
qed

lemma all_acquired_dropWhile: "all_acquired (dropWhile P sb) \<subseteq> all_acquired sb"
proof -
  from all_acquired_append [of "takeWhile P sb" "dropWhile P sb"] 
  show ?thesis
    by auto
qed

lemma acquired_share_owns_shared:
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "acquired pending_write sb \<O> \<union> dom (share sb \<S>) \<subseteq> \<O> \<union> dom \<S>"
proof -
  from acquired_all_acquired have "acquired pending_write sb \<O> \<subseteq> \<O> \<union> all_acquired sb".
  moreover
  from sharing_consistent_all_acquired  [OF consis] have "all_acquired sb \<subseteq> dom \<S> \<union> \<O>".
  moreover
  from sharing_consistent_share_all_shared have "dom (share sb \<S>) \<subseteq> dom \<S> \<union> all_shared sb".
  moreover
  from sharing_consistent_all_shared [OF consis] have "all_shared sb \<subseteq> dom \<S> \<union> \<O>".
  ultimately
  show ?thesis
    by blast
qed
   
lemma acquired_owns_shared:
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "acquired True sb \<O> \<subseteq> \<O> \<union> dom \<S>"
using acquired_share_owns_shared [OF consis]
by blast

lemma share_owns_shared:
  assumes consis: "sharing_consistent \<S> \<O> sb"
  shows "dom (share sb \<S>) \<subseteq> \<O> \<union> dom \<S>"
using acquired_share_owns_shared [OF consis]
by blast

lemma all_shared_append: "all_shared (xs@ys) = all_shared xs \<union> all_shared ys"
  by (induct xs) (auto split: memref.splits)

lemma acquired_union_notin_first:
  "\<And> pending_write A B. a \<in> acquired pending_write sb (A \<union> B) \<Longrightarrow> a \<notin> A \<Longrightarrow> a \<in> acquired pending_write sb B"
proof (induct sb)
  case Nil thus ?case by (auto split: if_split_asm)
next
  case (Cons x sb)
  then obtain a_notin_A: "a \<notin> A" and
    a_acq: "a \<in> acquired pending_write (x # sb) (A \<union> B)" 
    by blast
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Write\<^sub>s\<^sub>b Cons show ?thesis by simp
    next
      case True
      note volatile = this
      show ?thesis
      proof (cases pending_write)
	case True
	from a_acq have a_acq': "a \<in> acquired True sb (A \<union> B \<union> A' - R)"
	  by (simp add: Write\<^sub>s\<^sub>b volatile True)
	have "(A \<union> B \<union> A' - R) \<subseteq>  (A \<union> (B \<union> A' - R))"
	  by auto
	from acquired_mono_in [OF a_acq' this]
	have "a \<in> acquired True sb (A \<union> (B \<union> A' - R))".
	from Cons.hyps [OF this a_notin_A]

	have "a \<in> acquired True sb (B \<union> A' - R)".
	then
	show ?thesis by (simp add: Write\<^sub>s\<^sub>b volatile True)
      next
	case False
	from a_acq have a_acq': "a \<in> acquired True sb (A' - R)"
	  by (simp add: Write\<^sub>s\<^sub>b volatile False)
	then
	show ?thesis
	  by (simp add: Write\<^sub>s\<^sub>b volatile False)
      qed
    qed
  next
    case (Ghost\<^sub>s\<^sub>b A' L R W)
    show ?thesis
    proof (cases pending_write)
      case True
      from a_acq have a_acq': "a \<in> acquired True sb (A \<union> B \<union> A' - R)"
        by (simp add: Ghost\<^sub>s\<^sub>b True)
      have "(A \<union> B \<union> A' - R) \<subseteq>  (A \<union> (B \<union> A' - R))"
        by auto
      from acquired_mono_in [OF a_acq' this]
      have "a \<in> acquired True sb (A \<union> (B \<union> A' - R))".
      from Cons.hyps [OF this a_notin_A]

      have "a \<in> acquired True sb (B \<union> A' - R)".
      then
      show ?thesis by (simp add: Ghost\<^sub>s\<^sub>b True)
    next
      case False
      from a_acq have a_acq': "a \<in> acquired False sb (A \<union> B)"
	by (simp add: Ghost\<^sub>s\<^sub>b False)
      from Cons.hyps [OF this a_notin_A]
      show ?thesis
	by (simp add: Ghost\<^sub>s\<^sub>b False)
    qed
  qed (insert Cons, auto)
qed







(* FIXME: move up *)
lemma split_all_acquired_in:
"a \<in> all_acquired xs \<Longrightarrow>
(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs \<and> a \<in> A) \<or>
 (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have a_in: "a \<in> all_acquired (x # xs)" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      from a_in have "a \<in> all_acquired xs"
	by (auto simp add: False Write\<^sub>s\<^sub>b)
      from Cons.hyps [OF this] 
      have "(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs \<and> a \<in> A) \<or>
            (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W # zs \<and> a \<in> A)" (is "?write \<or> ?ghst").
      then 
      show ?thesis
      proof 
	assume ?write
	then
	obtain sop'' a'' v'' A'' L'' R'' W'' ys zs
	  where "xs=ys@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	  by auto
	hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs"
	  by auto
	thus ?thesis
	  using a_in
	  by blast
      next
	assume ?ghst
	then obtain A'' L'' R'' W'' ys zs where
	  "xs=ys@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	  by auto
	hence "x#xs = (x#ys)@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs"
	  by auto
	thus ?thesis
	  using a_in
	  by blast
      qed
    next
      case True
      note volatile = this
      show ?thesis
      proof (cases "a \<in> A")
	case False
	with a_in have "a \<in> all_acquired xs"
	  by (auto simp add: volatile Write\<^sub>s\<^sub>b)
	from Cons.hyps [OF this] 
	have "(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and> a \<in> A) \<or>
              (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A)" (is "?write \<or> ?ghst").
	then 
	show ?thesis
	proof 
	  assume ?write
	  then
	  obtain sop'' a'' v'' A'' L'' R'' W'' ys zs
	    where "xs=ys@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W'' #zs" and a_in: "a \<in> A''"
	    by auto
	  hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs"
	    by auto
	  thus ?thesis
	    using a_in
	    by blast
	next
	  assume ?ghst
	  then obtain A'' L'' R'' W'' ys zs where
	    "xs=ys @Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	    by auto 
	  hence "x#xs  = (x#ys)@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs"
	    by auto
	  thus ?thesis
	    using a_in
	    by blast
	qed
      next
	case True
	then have "x#xs=[]@(Write\<^sub>s\<^sub>b True a' sop v A L R W#xs)"
	  by (simp add: Write\<^sub>s\<^sub>b volatile True)
	thus ?thesis
	  using True
	  by blast
      qed
    qed
  next
    case Read\<^sub>s\<^sub>b 
    from a_in have "a \<in> all_acquired xs"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] 
    have "(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs \<and> a \<in> A) \<or>
            (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A)" (is "?write \<or> ?ghst").
    then 
    show ?thesis
    proof 
      assume ?write
      then
      obtain sop'' a'' v'' A'' L'' R'' W'' ys zs
	where "xs=ys@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	by auto
      hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	using a_in
	by blast
    next
      assume ?ghst
      then obtain A'' L'' R'' W'' ys zs where
	"xs=ys@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	by auto
      hence "x#xs = (x#ys)@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	using a_in
	by blast
    qed
  next
    case Prog\<^sub>s\<^sub>b
    from a_in have "a \<in> all_acquired xs"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] 
    have "(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W# zs \<and> a \<in> A) \<or>
            (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A)" (is "?write \<or> ?ghst").
    then 
    show ?thesis
    proof 
      assume ?write
      then
      obtain sop'' a'' v'' A'' L'' R'' W'' ys zs
	where "xs=ys@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	by auto
      hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	using a_in
	by blast
    next
      assume ?ghst
      then obtain A'' L'' R'' W'' ys zs where
	"xs=ys@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	by auto
      hence "x#xs = (x#ys)@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	using a_in
	by blast
    qed
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    show ?thesis
    proof (cases "a \<in> A")
      case False
      with a_in have "a \<in> all_acquired xs"
	by (auto simp add: Ghost\<^sub>s\<^sub>b)
      from Cons.hyps [OF this] 
      have "(\<exists>sop a' v ys zs A L R W. xs = ys @ Write\<^sub>s\<^sub>b True a' sop v A L R W # zs \<and> a \<in> A) \<or>
            (\<exists>A L R W ys zs. xs = ys @ Ghost\<^sub>s\<^sub>b A L R W# zs \<and> a \<in> A)" (is "?write \<or> ?ghst").
      then 
      show ?thesis
      proof 
	assume ?write
	then
	obtain sop'' a'' v'' A'' L'' R'' W'' ys zs
	  where "xs=ys@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	  by auto
	hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b True a'' sop'' v'' A'' L'' R'' W''#zs"
	  by auto
	thus ?thesis
	  using a_in
	  by blast
      next
	assume ?ghst
	then obtain A'' L'' R'' W'' ys zs where
	  "xs=ys@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs" and a_in: "a \<in> A''"
	  by auto
	hence "x#xs = (x#ys)@Ghost\<^sub>s\<^sub>b A'' L'' R'' W''#zs"
	  by auto
	thus ?thesis
	  using a_in
	  by blast
      qed
    next
      case True
      
      then have "x#xs=[]@(Ghost\<^sub>s\<^sub>b A L R W#xs)"
	by (simp add: Ghost\<^sub>s\<^sub>b True)
      thus ?thesis
	using True
	by blast
    qed
  qed
qed


lemma split_Write\<^sub>s\<^sub>b_in_outstanding_refs:
  "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b xs \<Longrightarrow> (\<exists>sop volatile v ys zs A L R W. xs = ys@(Write\<^sub>s\<^sub>b volatile a sop v A L R W#zs))"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have a_in: "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b (x # xs)" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases "a'=a")
      case False
      with a_in have "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	by (auto simp add: Write\<^sub>s\<^sub>b)
      from Cons.hyps [OF this] obtain sop'' volatile'' v'' A'' L'' R'' W'' ys zs
	where "xs=ys@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
	by auto
      hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
	by auto
      thus ?thesis
	by blast
    next
      case True
      then have "x#xs=[]@(Write\<^sub>s\<^sub>b volatile a sop v A L R W#xs)"
	by (simp add: Write\<^sub>s\<^sub>b True)
      thus ?thesis
	by blast
    qed
  next
    case Read\<^sub>s\<^sub>b 
    from a_in have "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Read\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' volatile'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W'' #zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  next
    case Prog\<^sub>s\<^sub>b
    from a_in have "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Prog\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' volatile'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  next
    case Ghost\<^sub>s\<^sub>b
    from a_in have "a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
    from Cons.hyps [OF this] obtain sop'' volatile'' v'' A'' L'' R'' W'' ys zs
      where "xs=ys@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    hence "x#xs = (x#ys)@Write\<^sub>s\<^sub>b volatile'' a sop'' v'' A'' L'' R'' W''#zs"
      by auto
    thus ?thesis
      by blast
  qed
qed

lemma outstanding_refs_is_Write\<^sub>s\<^sub>b_union:
  "outstanding_refs is_Write\<^sub>s\<^sub>b xs = 
    (outstanding_refs is_volatile_Write\<^sub>s\<^sub>b xs \<union> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b xs)"
apply (induct xs)
apply  simp
subgoal for a
apply (case_tac a)
apply auto
done
done

  
lemma rtranclp_r_rtranclp: "\<lbrakk>r\<^sup>*\<^sup>* x y; r y z\<rbrakk> \<Longrightarrow> r\<^sup>*\<^sup>* x z"
  by auto

lemma r_rtranclp_rtranclp: "\<lbrakk>r x y; r\<^sup>*\<^sup>* y z\<rbrakk> \<Longrightarrow> r\<^sup>*\<^sup>* x z"
  by auto

lemma unshared_is_non_volatile_Write\<^sub>s\<^sub>b: "\<And>\<S>.
  \<lbrakk>non_volatile_writes_unshared \<S> sb; a \<in> dom \<S>; a \<notin> all_unshared sb\<rbrakk> \<Longrightarrow> 
  a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" ] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)       
    with Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"] Cons.prems show ?thesis by auto
  qed
qed

lemma outstanding_non_volatile_Read\<^sub>s\<^sub>b_acquired_or_read_only_reads:
  "\<And>\<O> \<S> pending_write. 
  \<lbrakk>non_volatile_owned_or_read_only pending_write \<S> \<O> sb;
 a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb\<rbrakk>
\<Longrightarrow> a \<in> acquired_reads True sb \<O> \<or> a \<in> read_only_reads \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      with Write\<^sub>s\<^sub>b Cons.hyps [of True "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<O> \<union> A - R)"] Cons.prems
      show ?thesis by auto
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v) 
    show ?thesis
    proof (cases volatile)
      case False with Read\<^sub>s\<^sub>b Cons show ?thesis by auto
    next
      case True
      with Read\<^sub>s\<^sub>b Cons show ?thesis by auto
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) with Cons.hyps [of pending_write "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "\<O> \<union> A - R"] Cons.prems
    show ?thesis
      by auto
  qed
qed

lemma acquired_reads_union: "\<And>pending_writes A B. 
  \<lbrakk>a \<in> acquired_reads pending_writes sb (A \<union> B); a \<notin> A\<rbrakk> \<Longrightarrow> a \<in> acquired_reads pending_writes sb B"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L' R' W')
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      show ?thesis
      proof (cases pending_writes)
	case True
	from Cons.prems obtain 
	  a_in: "a \<in> acquired_reads True sb (A \<union> B \<union> A' - R')" and
	  a_notin: "a \<notin> A"
	  by (simp add: Write\<^sub>s\<^sub>b volatile True)
	have "(A \<union> B \<union> A' - R') \<subseteq>  (A \<union> (B \<union> A' - R'))"
	  by auto
	from acquired_reads_mono [OF this ] a_in
	have "a \<in> acquired_reads True sb (A \<union> (B \<union> A' - R'))"
	  by auto

	from Cons.hyps [OF this a_notin]
	have "a \<in> acquired_reads True sb (B \<union> A' - R')".
	then show ?thesis
	  by (simp add: Write\<^sub>s\<^sub>b volatile True)
      next
	case False
	with Cons show ?thesis
	  by (auto simp add: Write\<^sub>s\<^sub>b volatile False)
      qed
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by (auto split: if_split_asm)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A' L' R' W')
    show ?thesis
    proof -
      from Cons.prems obtain 
	a_in: "a \<in> acquired_reads pending_writes sb (A \<union> B \<union> A' - R')" and
	a_notin: "a \<notin> A"
        by (simp add: Ghost\<^sub>s\<^sub>b )
      have "(A \<union> B \<union> A' - R') \<subseteq>  (A \<union> (B \<union> A' - R'))"
        by auto
      from acquired_reads_mono [OF this ] a_in
      have "a \<in> acquired_reads pending_writes sb (A \<union> (B \<union> A' - R'))"
        by auto

      from Cons.hyps [OF this a_notin]
      have "a \<in> acquired_reads pending_writes sb (B \<union> A' - R')".
      then show ?thesis
        by (simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed

   
lemma non_volatile_writes_unshared_no_outstanding_non_volatile_Write\<^sub>s\<^sub>b: "\<And>\<S> \<S>'. 
  \<lbrakk>non_volatile_writes_unshared \<S> sb; 
  \<forall>a \<in> dom \<S>' - dom \<S>. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb \<rbrakk>
 \<Longrightarrow> non_volatile_writes_unshared \<S>' sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
    proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.prems obtain 
	unshared_sb: "non_volatile_writes_unshared (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and
        no_refs_sb: "\<forall>a\<in>dom \<S>' - dom \<S>. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by (simp add: Write\<^sub>s\<^sub>b True)
      from no_refs_sb have "\<forall>a\<in>dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L). 
	a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
	by auto
      from Cons.hyps [OF unshared_sb this]
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by (auto)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W) 
    from Cons.prems obtain 
      unshared_sb: "non_volatile_writes_unshared (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and
      no_refs_sb: "\<forall>a\<in>dom \<S>' - dom \<S>. a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
      by (simp add: Ghost\<^sub>s\<^sub>b)
    from no_refs_sb have "\<forall>a\<in>dom (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) - dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L). 
      a \<notin> outstanding_refs is_non_volatile_Write\<^sub>s\<^sub>b sb"
      by auto
    from Cons.hyps [OF unshared_sb this]
    show ?thesis
      by (simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed



theorem sharing_consis_share_all_until_volatile_write:
  "\<And>\<S> ts'. \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts; length ts' = length ts;
        \<forall>i < length ts. 
              (let (_,_,_,sb,_,\<O>,_) = ts!i;
                   (_,_,_,sb',_,\<O>',_) = ts'!i 
               in \<O>' = acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and> 
                  sb' = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)\<rbrakk> \<Longrightarrow>
       sharing_consis (share_all_until_volatile_write ts \<S>) ts' \<and>
       dom (share_all_until_volatile_write ts \<S>) - dom \<S> \<subseteq> 
          \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts) \<and>
       dom \<S> - dom (share_all_until_volatile_write ts \<S>) \<subseteq> 
          \<Union> ((\<lambda>(_,_,_,sb,_,\<O>,_). all_acquired sb \<union> \<O>) ` set ts)"
proof (induct ts)
  case Nil thus ?case by auto
next
  case (Cons t ts)
  have leq: "length ts' = length (t#ts)" by fact
  have sim: "\<forall>i < length (t#ts). 
              (let (_,_,_,sb,_,\<O>,_) = (t#ts)!i;
                   (_,_,_,sb',_,\<O>',_) = ts'!i 
               in \<O>' = acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and> 
                  sb' = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
    by fact
  obtain p "is" \<O> \<R> \<D> \<theta> sb 
    where t: "t = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)

  from leq obtain t' ts'' where ts': "ts'=t'#ts''" and leq': "length ts'' = length ts"
    by (cases ts') force+
  
  obtain p' "is'" \<O>' \<R>' \<D>' \<theta>' sb' 
    where t': "t' = (p',is',\<theta>',sb',\<D>',\<O>',\<R>')"
    by (cases t')

  from sim [rule_format, of 0] t t' ts'
  obtain \<O>': "\<O>' = acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>" and
         sb': "sb' = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
    by auto

  from sim ts'
  have sim': "\<forall>i < length ts. 
              (let (_,_,_,sb,_,\<O>,\<R>) = ts!i;
                   (_,_,_,sb',_,\<O>',\<R>) = ts''!i 
               in \<O>' = acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and> 
                  sb' = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by auto
    

  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "(t#ts)".
  from sharing_consis [of 0] t
  have consis_sb: "sharing_consistent \<S> \<O> sb"
    by fastforce
  from sharing_consistent_takeWhile [OF this]
  have consis': "sharing_consistent \<S> \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by simp
  
  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
  from freshly_shared_owned [OF consis']
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>".
  from unshared_all_unshared [OF consis'] unshared_acquired_or_owned [OF consis']
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> \<O>"
    by simp

    
  have dist: "ownership_distinct (t#ts)" by fact
  from ownership_distinct_tl [OF this]
  have dist': "ownership_distinct ts" .

  
  from sharing_consis_tl [OF consis]
  interpret consis': sharing_consis \<S> "ts".
    

  from dist interpret ownership_distinct "(t#ts)".

  (* FIXME: this proof appears in several times. Maybe make a lemma *)
  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

      
      
  from consis'.sharing_consis_preservation [OF sep]
  have consis_ts: "sharing_consis ?\<S>' ts".


  from Cons.hyps [OF dist' this leq' sim']
  obtain consis_ts'':
    "sharing_consis (share_all_until_volatile_write ts ?\<S>') ts''" and

    fresh: "dom (share_all_until_volatile_write ts ?\<S>') - dom ?\<S>' \<subseteq> 
           \<Union> ((\<lambda>(_,_,_,_,_,\<O>,\<R>).  \<O>) ` set ts)" and
    unshared: "dom ?\<S>' - dom (share_all_until_volatile_write ts ?\<S>') \<subseteq> 
          \<Union> ((\<lambda>(_,_,_,sb,_,\<O>,\<R>). all_acquired sb \<union> \<O>)` set ts)"
    by auto


  from sharing_consistent_append [of _ _ "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"] consis_sb
  have consis_t': "sharing_consistent ?\<S>' \<O>' sb'"
    by (simp add: \<O>' sb')


  have fresh_dist: "all_acquired sb' \<inter> dom ?\<S>' - dom (share_all_until_volatile_write ts ?\<S>') = {}"
  proof -
    have "all_acquired sb' \<inter> \<Union> ((\<lambda>(_,_,_,sb,_,\<O>,_). all_acquired sb \<union> \<O>)` set ts) = {}"
    proof -
      {
	fix x
	assume x_sb': "x \<in> all_acquired sb'"
	assume x_ts: "x \<in> \<Union> ((\<lambda>(_,_,_,sb,_,\<O>,_). all_acquired sb \<union> \<O>)` set ts)"
	have False
	proof -
	  from x_ts
	  obtain i p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i where 
	    i_bound: "i < length ts" and
            ts_i: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)" and
	    x_in: "x \<in> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i"
	    by (force simp add:  in_set_conv_nth)
	  from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	  have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	    by force
	  with x_sb' x_in all_acquired_dropWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" "sb"] show False
	    by (auto simp add: sb')
	qed
      }
      thus ?thesis by blast
    qed
    with unshared show ?thesis
      by blast
  qed

  have unshared_dist: "all_unshared sb' \<inter> dom (share_all_until_volatile_write ts ?\<S>') - dom ?\<S>' = {}"
  proof -
    from unshared_acquired_or_owned [OF consis_t']
    have "all_unshared sb' \<subseteq> all_acquired sb' \<union> \<O>'".
    also
    from all_acquired_dropWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" "sb"]
    acquired_all_acquired [of True "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb" \<O>]
    all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" "sb"]
    have "all_acquired sb' \<union> \<O>' \<subseteq> all_acquired sb \<union> \<O>"
      by (auto simp add: sb' \<O>')
    finally
    have "all_unshared sb' \<subseteq> (all_acquired sb \<union> \<O>)".

    moreover

    have "(all_acquired sb \<union> \<O>) \<inter> \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts) = {}"
    proof -
      {
	fix x
	assume x_sb': "x \<in> all_acquired sb \<union> \<O>"
	assume x_ts: "x \<in> \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_). \<O>)` set ts)"
	have False
	proof -
	  from x_ts
	  obtain i p\<^sub>i is\<^sub>i \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i where 
	    i_bound: "i < length ts" and
            ts_i: "ts!i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)" and
	    x_in: "x \<in> \<O>\<^sub>i"
	    by (force simp add:  in_set_conv_nth)
	  from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	  have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	    by force
	  with x_sb' x_in show False
	    by (auto simp add: sb')
	qed
      }
      thus ?thesis by blast
    qed
    ultimately show ?thesis
      using fresh by fastforce
  qed

  from sharing_consistent_preservation [OF consis_t' fresh_dist unshared_dist]
  have consis_ts: "sharing_consistent (share_all_until_volatile_write ts ?\<S>') \<O>' sb'".
  note sharing_consis_Cons [OF consis_ts'' consis_ts, of p' is' \<theta>' \<D>' ]
  moreover
  from fresh fresh_owned
  have "dom (share_all_until_volatile_write ts ?\<S>') - dom \<S> \<subseteq> 
          \<O> \<union> \<Union> ((\<lambda>(_,_,_,_,_,\<O>,_).  \<O>) ` set ts)"  
    by auto
  moreover
  from unshared unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb]
  have "dom \<S> - dom (share_all_until_volatile_write ts ?\<S>') \<subseteq> 
          all_acquired sb \<union> \<O> \<union> \<Union> ((\<lambda>(_,_,_,sb,_,\<O>,_). all_acquired sb \<union> \<O>) ` set ts)"
    by auto
  ultimately

  show ?case
    by (auto simp add: t ts' t')
qed


corollary sharing_consistent_share_all_until_volatile_write: 
assumes dist: "ownership_distinct ts" 
assumes consis: "sharing_consis \<S> ts" 
assumes i_bound: "i < length ts" 
assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" 
shows "sharing_consistent (share_all_until_volatile_write ts \<S>) 
                          (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
                          (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof -
  define ts' where "ts' == map (\<lambda>(p,is,\<theta>,sb,\<D>,\<O>,\<R>).  
                    (p,is,\<theta>,
                          dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb,\<D>,acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>,\<R>)) ts"
  have leq: "length ts' = length ts"
    by (simp add: ts'_def)

  have flush: "\<forall>i < length ts. 
              (let (_,_,_,sb,_,\<O>,_) = ts!i;
                   (_,_,_,sb',_,\<O>',_) = ts'!i 
               in \<O>' = acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<and> 
                  sb' = dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by (auto simp add: ts'_def Let_def)

  from sharing_consis_share_all_until_volatile_write [OF dist consis leq flush]
  interpret sharing_consis "(share_all_until_volatile_write ts \<S>)" "ts'" by simp
  from i_bound leq ts_i sharing_consis [of i]
  show ?thesis
    by (force simp add: ts'_def)
qed



lemma restrict_map_UNIV [simp]: "S |` UNIV = S"
  by (auto simp add: restrict_map_def)

(*
lemma share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b: 
  "\<And>S.  (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) =
  S \<ominus>\<^bsub>(all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb))\<^esub> (all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb))"
apply (induct sb)
apply  simp
apply (case_tac a)
apply (auto intro: share_mono_in simp add: restrict_shared_fuse)
done
*)

(*
lemma dom_share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b: 
  "dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) = dom S - all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  apply (auto simp add: share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
  done
*)
(*
lemma dom_share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b: 
  "\<And>S.  dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) \<subseteq> dom S - all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply  simp
apply (case_tac a)
apply (auto intro: share_mono_in simp add: restrict_shared_fuse)
  apply (auto simp add: )
  done
*)
lemma share_all_until_volatile_write_Read_commute:
  shows "\<And>S i.  \<lbrakk>i < length ls; ls!i=(p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>)
    \<rbrakk>  
   \<Longrightarrow> 
    share_all_until_volatile_write 
       (ls[i := (p,is, \<theta>(t\<mapsto>v), sb @ [Read\<^sub>s\<^sub>b volatile a t v],\<D>', \<O>)]) S =
    share_all_until_volatile_write ls S"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,Read volatile a t#is,\<theta>,sb,\<D>,\<O>)"
      by simp
    thus ?thesis 
      by (simp add: 0 share_append_Read\<^sub>s\<^sub>b del: fun_upd_apply )
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l)"
      by (cases l)
    from i_bound ith
    have "share_all_until_volatile_write
      (ls[n := (p,is, \<theta>(t\<mapsto>v), sb @ [Read\<^sub>s\<^sub>b volatile a t v],\<D>', \<O>)]) 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S) =
      share_all_until_volatile_write ls (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done
    
    then
    show ?thesis
      by (simp add: Suc l del: fun_upd_apply)
  qed
qed

lemma share_all_until_volatile_write_Write_commute:
  shows "\<And>S i.  \<lbrakk>i < length ls; ls!i=(p,Write volatile a (D,f) A L R W#is,\<theta>,sb,\<D>,\<O>)
    \<rbrakk>  
   \<Longrightarrow> 
    share_all_until_volatile_write 
       (ls[i := (p,is,\<theta>, sb @ [Write\<^sub>s\<^sub>b volatile a t (f \<theta>) A L R W], \<D>', \<O>)]) S =
    share_all_until_volatile_write ls S"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,Write volatile a (D,f) A L R W#is,\<theta>,sb,\<D>,\<O>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,Write volatile a (D,f) A L R W#is,\<theta>,sb,\<D>,\<O>)"
      by simp
    thus ?thesis 
      by (simp add: 0 share_append_Write\<^sub>s\<^sub>b del: fun_upd_apply )
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l)"
      by (cases l)
    from i_bound ith
    have "share_all_until_volatile_write
      (ls[n := (p,is, \<theta>, sb @ [Write\<^sub>s\<^sub>b volatile a t (f \<theta>) A L R W],\<D>', \<O>)]) 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S) =
      share_all_until_volatile_write ls (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done
    
    then
    show ?thesis
      by (simp add: Suc l del: fun_upd_apply)
  qed
qed

lemma share_all_until_volatile_write_RMW_commute:
  shows "\<And>S i.  \<lbrakk>i < length ls; ls!i=(p,RMW a t (D,f) cond ret A L R W#is,\<theta>,[],\<D>,\<O>)
    \<rbrakk>  
   \<Longrightarrow> 
    share_all_until_volatile_write (ls[i := (p',is, \<theta>', [],\<D>', \<O>')]) S =
    share_all_until_volatile_write ls S"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,RMW a t (D,f) cond ret A L R W#is,\<theta>,[],\<D>,\<O>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,RMW a t (D,f) cond ret A L R W#is,\<theta>,[],\<D>,\<O>)"
      by simp
    thus ?thesis 
      by (simp add: 0 share_append_Write\<^sub>s\<^sub>b del: fun_upd_apply )
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l)"
      by (cases l)
    from i_bound ith
    have "share_all_until_volatile_write
      (ls[n := (p',is,\<theta>', [], \<D>', \<O>')]) 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S) =
      share_all_until_volatile_write ls (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done
    
    then
    show ?thesis
      by (simp add: Suc l del: fun_upd_apply)
  qed
qed

lemma share_all_until_volatile_write_Fence_commute:
  shows "\<And>S i.  \<lbrakk>i < length ls; ls!i=(p,Fence#is,\<theta>,[],\<D>,\<O>,\<R>)
    \<rbrakk>  
   \<Longrightarrow> 
    share_all_until_volatile_write (ls[i := (p,is,\<theta>, [], \<D>', \<O>,\<R>')]) S =
    share_all_until_volatile_write ls S"
proof (induct ls)
  case Nil thus ?case
    by simp
next
  case (Cons l ls)
  note i_bound =  \<open>i < length (l#ls)\<close>
  note ith = \<open>(l#ls)!i = (p,Fence#is,\<theta>,[],\<D>,\<O>,\<R>)\<close>
  show ?case
  proof (cases i)
    case 0
    from ith 0 have l: "l = (p,Fence#is,\<theta>,[],\<D>,\<O>,\<R>)"
      by simp
    thus ?thesis 
      by (simp add: 0 share_append_Write\<^sub>s\<^sub>b del: fun_upd_apply )
  next
    case (Suc n)
    obtain p\<^sub>l "is\<^sub>l" \<O>\<^sub>l \<R>\<^sub>l \<D>\<^sub>l \<theta>\<^sub>l sb\<^sub>l where l: "l = (p\<^sub>l,is\<^sub>l,\<theta>\<^sub>l,sb\<^sub>l,\<D>\<^sub>l,\<O>\<^sub>l,\<R>\<^sub>l)"
      by (cases l)
    from i_bound ith
    have "share_all_until_volatile_write
      (ls[n := (p,is, \<theta>, [],\<D>', \<O>,\<R>')]) 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S) =
      share_all_until_volatile_write ls (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>l) S)"
      apply -
      apply (rule Cons.hyps)
      apply (auto simp add: Suc l)
      done
    
    then
    show ?thesis
      by (simp add: Suc l del: fun_upd_apply)
  qed
qed



(*
lemma unshared_share_takeWhile:  
  assumes unshared: "non_volatile_writes_unshared \<S> xs"
  shows "non_volatile_writes_unshared (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) xs"
proof -
  from share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb \<S>]
  have "dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) \<subseteq> dom \<S>"
    by auto
  from non_volatile_writes_unshared_antimono [OF this unshared]
  show ?thesis
    by simp
qed
*)
(*
lemma non_volatile_writes_unshared_share_all_until_volatile_write: "\<And>\<S>. non_volatile_writes_unshared \<S> xs \<Longrightarrow> 
       non_volatile_writes_unshared (share_all_until_volatile_write ts \<S>) xs"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<D> \<theta> sb where t: "t=(p,is,\<theta>,sb,\<D>,\<O>)"
    by (cases t) 

  from unshared_share_takeWhile [OF Cons.prems]
  have "non_volatile_writes_unshared (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) xs".
  from Cons.hyps [OF this]
  show ?case
    by (simp add: t)
qed
*)
(*
lemma share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b_restrict:
  "dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) \<subseteq> dom S"
  apply (auto simp add: share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b)
  done
*)

(*
lemma share_all_until_volatile_write_restrict:
  "\<And>S. dom (share_all_until_volatile_write ts S) \<subseteq> dom S"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<D> \<theta> sb where t: "t=(p,is,\<theta>,sb,\<D>,\<O>)"
    by (cases t) 

  from share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b_restrict
  have "dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) \<subseteq> dom S".
  with Cons.hyps
  show ?case
    by (auto simp add: t)
qed
*)
(*
lemma share_all_until_volatile_all_unshared:
  "\<And>S. dom (share_all_until_volatile_write ts S) = 
        dom S - \<Union>(\<lambda>(_,_,_,sb,_,_,_). all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where t: "t=(p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t) 
  from Cons.hyps 
  have "dom (share_all_until_volatile_write ts (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S)) = 
          dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) 
           - \<Union>(\<lambda>(_,_,_,sb,_,_,_). all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts".
  moreover
  from dom_share_takeWhile_non_volatile_Write\<^sub>s\<^sub>b
  have "dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) = dom S - all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)".
  ultimately
  have "dom (share_all_until_volatile_write (t#ts) S) = 
       dom S - all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) - 
       \<Union>(\<lambda>(_,_,_,sb,_,_). all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts"
    by (simp add: t)
  also
  have "\<dots> = dom S - \<Union>(\<lambda>(_,_,_,sb,_,_). all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set (t#ts)"
    by (auto simp add: t)
  finally
  show ?case
    by (auto simp del: o_apply)
qed
    
lemma share_all_until_volatile_all_unshared_i:
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>)"
  assumes a_in: "a \<in> dom (share_all_until_volatile_write ts S)" 
  shows "a \<notin> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof -
  from nth_mem [OF i_bound]  ts_i have "(p,is,\<theta>,sb,\<D>,\<O>) \<in> set ts"
    by auto
  with a_in
  show ?thesis
    by (auto simp add: share_all_until_volatile_all_unshared)
qed
*)
    
lemma unshared_share_in: "\<And>S. a \<in> dom S \<Longrightarrow> a \<notin>  all_unshared sb \<Longrightarrow> a \<in> dom (share sb S)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      show ?thesis
      proof -
	from Cons.prems obtain a_S: "a \<in> dom S" and a_L: "a \<notin> L" and  a_sb: "a \<notin> all_unshared sb" 
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
	from a_S a_L have "a \<in> dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	from Cons.hyps [OF this a_sb]
	show ?thesis  
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      qed
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


lemma dom_eq_dom_share_eq: "\<And>S S'. dom S = dom S' \<Longrightarrow> dom (share sb S) = dom (share sb S')"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.prems
      have "dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L) = dom (S' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L)"
	by auto
      from Cons.hyps [OF this]
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons.hyps [of S S'] Cons.prems Write\<^sub>s\<^sub>b show ?thesis by auto
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons.hyps [of S S'] Cons.prems show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons.hyps [of S S'] Cons.prems show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A' L R W)
    from Cons.prems
    have "dom (S \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A'\<^esub> L) = dom (S' \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A'\<^esub> L)"
      by auto
    from Cons.hyps [OF this]
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed
   
lemma share_union:
  "\<And>A B. \<lbrakk>a \<in> dom (share sb (A \<oplus>\<^bsub>z\<^esub> B)); a \<notin> dom A\<rbrakk> \<Longrightarrow> a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>z\<^esub> B))"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L R W)
    show ?thesis
    proof (cases volatile)
      case True
      from Cons.prems 
      obtain a_in: "a \<in> dom (share sb ((A \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L))" and a_A: "a \<notin> dom A"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      have "dom ((A \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L) \<subseteq> dom (A \<oplus>\<^bsub>z\<^esub> (B \<union> R - L))"
	by auto
      from share_mono [OF this] a_in
      have "a \<in> dom (share sb (A \<oplus>\<^bsub>z\<^esub> (B \<union> R - L)))"
	by blast
      from Cons.hyps [OF this] a_A
      have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>z\<^esub> (B \<union> R - L)))"
	by blast
      moreover
      have "dom (Map.empty \<oplus>\<^bsub>z\<^esub> B \<union> R - L) = dom ((Map.empty \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L)"
	by auto
      note dom_eq_dom_share_eq [OF this, of sb]
      ultimately
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A' L R W)
    from Cons.prems 
    obtain a_in: "a \<in> dom (share sb ((A \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L))" and a_A: "a \<notin> dom A"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    have "dom ((A \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L) \<subseteq> dom (A \<oplus>\<^bsub>z\<^esub> (B \<union> R - L))"
      by auto
    from share_mono [OF this] a_in
    have "a \<in> dom (share sb (A \<oplus>\<^bsub>z\<^esub> (B \<union> R - L)))"
      by blast
    from Cons.hyps [OF this] a_A
    have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>z\<^esub> (B \<union> R - L)))"
      by blast
    moreover
    have "dom (Map.empty \<oplus>\<^bsub>z\<^esub> B \<union> R - L) = dom ((Map.empty \<oplus>\<^bsub>z\<^esub> B) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A'\<^esub> L)"
      by auto
    note dom_eq_dom_share_eq [OF this, of sb]
    ultimately
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

   
lemma share_unshared_in: 
  "\<And>S. a \<in> dom (share sb S) \<Longrightarrow> a \<in> dom (share sb Map.empty) \<or> (a \<in> dom S \<and> a \<notin> all_unshared sb)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      have a_in: "a \<in> dom (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> dom S")
	case True
	from Cons.hyps [OF a_in]
	have "a \<in> dom (share sb Map.empty) \<or> a \<in> dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_unshared sb".
	then show ?thesis
	proof 
	  assume "a \<in> dom (share sb Map.empty)"
	  from share_mono_in [OF this]
	  have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" by auto
	  then show ?thesis
	    by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile True)
	next
	  assume "a \<in> dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_unshared sb"
	  then obtain "a \<notin> L" "a \<notin> all_unshared sb"
	    by auto
	  then show ?thesis by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile True)
	qed
      next
	case False
	have "dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> dom (S \<oplus>\<^bsub>W\<^esub> (R - L))"
	  by auto
	from share_mono [OF this] a_in
	have "a \<in> dom (share sb (S \<oplus>\<^bsub>W\<^esub>  (R - L)))" by blast
	from share_union [OF this False]
	have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> (R - L)))".
	moreover
	have "dom (Map.empty \<oplus>\<^bsub>W\<^esub> (R - L)) = dom (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	note dom_eq_dom_share_eq [OF this, of sb]
	ultimately
	show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      qed
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    have a_in: "a \<in> dom (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    show ?thesis
    proof (cases "a \<in> dom S")
      case True
      from Cons.hyps [OF a_in]
      have "a \<in> dom (share sb Map.empty) \<or> a \<in> dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_unshared sb".
      then show ?thesis
      proof 
	assume "a \<in> dom (share sb Map.empty)"
	from share_mono_in [OF this]
	have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" by auto
        then show ?thesis
	  by (clarsimp simp add: Ghost\<^sub>s\<^sub>b True)
      next
	assume "a \<in> dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_unshared sb"
	then obtain "a \<notin> L" "a \<notin> all_unshared sb"
	  by auto
	then show ?thesis by (clarsimp simp add: Ghost\<^sub>s\<^sub>b True)
      qed
    next
      case False
      have "dom (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> dom (S \<oplus>\<^bsub>W\<^esub> (R - L))"
        by auto
      from share_mono [OF this] a_in
      have "a \<in> dom (share sb (S \<oplus>\<^bsub>W\<^esub>  (R - L)))" by blast
      from share_union [OF this False]
      have "a \<in> dom (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> (R - L)))".
      moreover
      have "dom (Map.empty \<oplus>\<^bsub>W\<^esub> (R - L)) = dom (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      note dom_eq_dom_share_eq [OF this, of sb]
      ultimately
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b False)
    qed
  qed
qed

(* FIXME: move up *)
lemma dom_augment_rels_shared_eq: "dom (augment_rels S R \<R>) = dom (augment_rels S' R \<R>)"
  by (auto simp add: augment_rels_def domIff split: option.splits if_split_asm)

lemma dom_eq_SomeD1: "dom m = dom n \<Longrightarrow> m x = Some y \<Longrightarrow> n x \<noteq> None"
  by (auto simp add: dom_def)

lemma dom_eq_SomeD2: "dom m = dom n \<Longrightarrow> n x = Some y \<Longrightarrow> m x \<noteq> None"
  by (auto simp add: dom_def)

lemma dom_augment_rels_rels_eq: "dom \<R>'  = dom \<R> \<Longrightarrow> dom (augment_rels S R \<R>') = dom (augment_rels S R \<R>)"
  by (auto simp add: augment_rels_def domIff split: option.splits if_split_asm dest: dom_eq_SomeD1 dom_eq_SomeD2)


lemma dom_release_rels_eq: "\<And>\<S> \<R> \<R>'. dom \<R>' = dom \<R> \<Longrightarrow> 
  dom (release sb \<S> \<R>') = dom (release sb \<S> \<R>)"
proof (induct sb)
  case Nil thus ?case by simp
next 
  case (Cons x sb)
  hence dr: "dom \<R>' = dom \<R>"
    by simp
  show ?case
  proof (cases x)
    case Write\<^sub>s\<^sub>b with Cons.hyps [OF dr] show ?thesis by (clarsimp)
  next 
    case Read\<^sub>s\<^sub>b with Cons.hyps [OF dr] show ?thesis by (clarsimp)
  next 
    case Prog\<^sub>s\<^sub>b with Cons.hyps [OF dr] show ?thesis by (clarsimp)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [OF dom_augment_rels_rels_eq [OF dr]]
    show ?thesis
     by (simp add: Ghost\<^sub>s\<^sub>b)
 qed
qed



lemma dom_release_shared_eq: "\<And>\<S> \<S>' \<R>. dom (release sb \<S>' \<R>) = dom (release sb \<S> \<R>)"
proof (induct sb)
  case Nil thus ?case by simp
next 
  case (Cons x sb)
  show ?case
  proof (cases x)
    case Write\<^sub>s\<^sub>b with Cons.hyps show ?thesis by (clarsimp)
  next 
    case Read\<^sub>s\<^sub>b with Cons.hyps show ?thesis by (clarsimp)
  next 
    case Prog\<^sub>s\<^sub>b with Cons.hyps show ?thesis by (clarsimp)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    have dr: "dom (augment_rels \<S>' R \<R>) = dom (augment_rels \<S> R \<R>)"
      by(rule dom_augment_rels_shared_eq)
    have "dom (release sb (\<S>' \<union> R - L) (augment_rels \<S>' R \<R>)) =
          dom (release sb (\<S> \<union> R - L) (augment_rels \<S>' R \<R>))"
      by (rule Cons.hyps)
    also have "... = dom (release sb (\<S> \<union> R - L) (augment_rels \<S> R \<R>))"
      by (rule dom_release_rels_eq [OF dr])
    finally show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


lemma share_other_untouched:
  "\<And>\<O> \<S>. sharing_consistent \<S> \<O> sb \<Longrightarrow> a \<notin> \<O> \<union> all_acquired sb\<Longrightarrow> share sb \<S> a = \<S> a"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
        a_owns: "a \<notin> \<O>" and a_A: "a \<notin> A" and a_sb: "a \<notin> all_acquired sb"
	by ( simp add: Write\<^sub>s\<^sub>b True )

      from a_owns a_A a_sb 
      have "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
        by auto
      from Cons.hyps [OF consis' this]
      have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a".
      moreover have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
      using L_A A_R R_owns a_owns a_A
        by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
      ultimately show ?thesis
        by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
        by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case Prog\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
      a_owns: "a \<notin> \<O>" and a_A: "a \<notin> A" and a_sb: "a \<notin> all_acquired sb"
      by ( simp add: Ghost\<^sub>s\<^sub>b )

    from a_owns a_A a_sb 
    have "a \<notin> \<O> \<union> A - R \<union> all_acquired sb"
      by auto
    from Cons.hyps [OF consis' this]
    have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a".
    moreover have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
    using L_A A_R R_owns a_owns a_A
      by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
    ultimately show ?thesis
      by (simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma shared_owned: "\<And>\<O> \<S>. sharing_consistent \<S> \<O> sb \<Longrightarrow> a \<notin> dom \<S> \<Longrightarrow> a \<in> dom (share sb \<S>) \<Longrightarrow> 
    a \<in> \<O> \<union> all_acquired sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
        a_notin: "a \<notin> dom \<S>" and a_in: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	by ( simp add: Write\<^sub>s\<^sub>b True )
      
      show ?thesis
      proof (cases "a \<in> \<O>")
        case True thus ?thesis by auto
      next
        case False
        with a_notin R_owns A_shared_owns L_A A_R have "a \<notin> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
          by (auto)
        from Cons.hyps [OF consis' this a_in]
        show ?thesis
          by (auto simp add: Write\<^sub>s\<^sub>b True)
      qed
    next
      case False with Cons show ?thesis
        by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case Prog\<^sub>s\<^sub>b with Cons
    show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
      a_notin: "a \<notin> dom \<S>" and a_in: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
      by (simp add: Ghost\<^sub>s\<^sub>b)
      
    show ?thesis
    proof (cases "a \<in> \<O>")
      case True thus ?thesis by auto
    next
      case False
      with a_notin R_owns A_shared_owns L_A A_R have "a \<notin> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by (auto)
      from Cons.hyps [OF consis' this a_in]
      show ?thesis
        by (auto simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed

(*
      sharing consistent:
      a \<in> dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb!i)) empty)
      \<Longrightarrow> a \<in> dom (share_all_until_volatile_write ts \<S>)
(it should even be the same boolean value )
generalization

      a \<notin> dom S \<Longrightarrow>
      a \<in> dom (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb!i)) S)
      \<Longrightarrow> a \<in> dom (share_all_until_volatile_write ts S')

also generalize freshly_shared_owned; cf. share_owns_shared

if a is owned by a thread, no other thread can mess around with sharing!


a \<notin> \<O>; sharing_consistent \<S> \<O> sb;
share sb \<S> a = share a
*)

(* FIXME: move up *)
lemma share_all_shared_in: "a \<in> dom (share sb \<S>) \<Longrightarrow> a \<in> dom \<S> \<or> a \<in> all_shared sb"
using sharing_consistent_share_all_shared [of sb \<S>]
  by auto

lemma share_all_until_volatile_write_unowned:
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes other: "\<forall>i p is \<theta> sb \<D> \<O> \<R>. i < length ts \<longrightarrow> ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow>
              a \<notin> \<O> \<union> all_acquired sb"
  shows "share_all_until_volatile_write ts \<S> a = \<S> a"
using dist consis other 
proof (induct ts arbitrary: \<S>)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  from Cons.prems t obtain
    other': "\<forall>i p is \<theta> sb \<D> \<O> \<R>. i < length ts \<longrightarrow> ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow>
              a \<notin> \<O> \<union> all_acquired sb" and
    a_notin: "a \<notin> \<O>\<^sub>t \<union> all_acquired sb\<^sub>t"
  apply -
  apply (rule that)
  apply  clarsimp
         subgoal for i p "is" \<theta> sb \<D> \<O> \<R>
         apply (drule_tac x="Suc i" in spec)
         apply clarsimp
         done
  apply (drule_tac x="0" in spec)
  apply clarsimp
  done 

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts".
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts".

  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".
  
  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts".
  
  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)"

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t".
  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)".
  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
    by simp

  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF this]
  have "sharing_consis ?\<S>' ts".

  from Cons.hyps [OF dist' this other']
  have "share_all_until_volatile_write ts ?\<S>' a =
    share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S> a" .
  moreover
  from share_other_untouched [OF consis_sb] a_notin 
    all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"]
  have "share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S> a = \<S> a"
    by auto
  ultimately
  show ?case
    by (simp add: t)
qed

lemma share_shared_eq: "\<And>\<S>' \<S>. \<S>' a = \<S> a \<Longrightarrow> share sb \<S>' a = share sb \<S> a"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  have eq: "\<S>' a = \<S> a" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      
      have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      using eq by (auto simp add: augment_shared_def restrict_shared_def)
      from Cons.hyps [of "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)", OF this]
      show ?thesis
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      with Cons.hyps [of \<S>' \<S>] Cons.prems show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons.hyps [of \<S>' \<S>] Cons.prems show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps [of \<S>' \<S>] Cons.prems show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
    using eq by (auto simp add: augment_shared_def restrict_shared_def)
    from Cons.hyps [of "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)", OF this]
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma  share_all_until_volatile_write_thread_local:
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_owned: "a \<in> \<O> \<union> all_acquired sb"
  shows "share_all_until_volatile_write ts \<S> a = share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S> a"
using dist consis i_bound ts_i
proof (induct ts arbitrary: \<S> i)
  case Nil thus ?case by simp
next
  case (Cons t ts)


  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts".
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts".
  
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts".
  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)"

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t".
  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)".
  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
    by simp

  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF this]
  have consis_shared': "sharing_consis ?\<S>' ts".


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto

  show ?case
  proof (cases "i")
    case 0
    with Cons.prems
    have t': "t = (p, is, \<theta>, sb, \<D>, \<O>, \<R>)" 
      by simp
    
    {
      fix j p\<^sub>j "is\<^sub>j" \<theta>\<^sub>j sb\<^sub>j \<D>\<^sub>j \<O>\<^sub>j \<R>\<^sub>j
      assume j_bound: "j < length ts"
      assume ts_j: "ts ! j = (p\<^sub>j, is\<^sub>j, \<theta>\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j, \<R>\<^sub>j)"
      have "a \<notin> \<O>\<^sub>j \<union> all_acquired sb\<^sub>j"
      proof -
        from ownership_distinct [of "0" "Suc j", simplified, OF j_bound t ts_j] t a_owned t' 0
        show ?thesis
          by auto
      qed
    }
    
    with share_all_until_volatile_write_unowned [OF dist' consis_shared', of a] 
    have "share_all_until_volatile_write ts ?\<S>' a = ?\<S>' a"
      by fastforce
    then show ?thesis
    using t t' 0
      by (auto simp add: Cons t aargh)
  next
    case (Suc n)
    with Cons.prems obtain n_bound: "n < length ts" and ts_n: "ts!n = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
      by auto
    from Cons.hyps [OF dist' consis_shared' n_bound ts_n]
    have "share_all_until_volatile_write ts ?\<S>' a =
            share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) ?\<S>' a" .
    moreover 
    from ownership_distinct [of "0" "Suc n"] t a_owned ts_n n_bound
    have "a \<notin> \<O>\<^sub>t \<union> all_acquired sb\<^sub>t"
      by fastforce
    with share_other_untouched [OF consis_sb, of a]  
      all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"]
    have "?\<S>' a = \<S> a"
      by auto
    from share_shared_eq [of ?\<S>' a \<S>,OF this ]
    have "share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) ?\<S>' a = 
           share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S> a" .
    ultimately show ?thesis
    using t Suc 
      by (auto simp add: aargh)
  qed
qed

lemma share_all_until_volatile_write_thread_local':
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_owned: "a \<in> \<O> \<union> all_acquired sb"
  shows "share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (share_all_until_volatile_write ts \<S>) a = 
          share sb \<S> a"
proof -
  let ?take = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  let ?drop = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  from share_all_until_volatile_write_thread_local [OF dist consis i_bound ts_i a_owned]
  have "share_all_until_volatile_write ts \<S> a = share ?take \<S> a" .
  moreover
  from share_shared_eq [of "share_all_until_volatile_write ts \<S>" a "share ?take \<S>", OF this]
  have "share ?drop (share_all_until_volatile_write ts \<S>) a = share ?drop (share ?take \<S>) a" .
  thus ?thesis
  using share_append [of ?take ?drop \<S>]
    by simp
qed

lemma (in ownership_distinct) in_shared_sb_share_all_until_volatile_write:
  assumes consis: "sharing_consis \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_owned: "a \<in> \<O> \<union> all_acquired sb"
  assumes a_share: "a \<in> dom (share sb \<S>)"
  shows "a \<in> dom (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) 
                    (share_all_until_volatile_write ts \<S>))"
proof -
  have dist: "ownership_distinct ts" 
  using assms ownership_distinct
    apply -
    apply (rule ownership_distinct.intro)
    apply auto
    done
  from share_all_until_volatile_write_thread_local' [OF dist consis i_bound ts_i a_owned]
    a_share
  show ?thesis
    by (auto simp add: domIff)
qed

lemma owns_unshared_share_acquired:
  "\<And>\<S> \<O>. \<lbrakk>sharing_consistent \<S> \<O> sb; a \<in> \<O>; a \<notin> all_unshared sb\<rbrakk>
  \<Longrightarrow> a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	a_owns: "a \<in> \<O>" and A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and
	a_L: "a \<notin> L" and a_unsh: " a \<notin> all_unshared sb" and L_A: "L \<subseteq> A" and
        A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<union> acquired True sb (\<O> \<union> A - R)"
      proof (cases "a \<in> R")
	case True
	with a_L have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	from unshared_share_in [OF this a_unsh]
	show ?thesis by blast
      next
	case False
	hence "a \<in> \<O> \<union> A - R"
	  using a_owns
	  by auto
	from Cons.hyps [OF consis' this a_unsh]
	show ?thesis .
      qed
      then
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile) 
    next
      case False
      with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_owns: "a \<in> \<O>" and A_shared_onws: "A \<subseteq> dom \<S> \<union> \<O>" and
      a_L: "a \<notin> L" and a_unsh: " a \<notin> all_unshared sb" and L_A: "L \<subseteq> A" and
      A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<union> acquired True sb (\<O> \<union> A - R)"
    proof (cases "a \<in> R")
      case True
      with a_L have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      from unshared_share_in [OF this a_unsh]
      show ?thesis by blast
    next
      case False
      hence "a \<in> \<O> \<union> A - R"
        using a_owns
	by auto
      from Cons.hyps [OF consis' this a_unsh]
      show ?thesis .
    qed
    then show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma shared_share_acquired: "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> 
  a \<in> dom \<S> \<Longrightarrow> a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>"    
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	a_shared: "a \<in> dom \<S>" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
	L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
        consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True) 
      show ?thesis
      proof (cases "a \<in> L")
	case False with a_shared
	have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	from Cons.hyps [OF consis' this]
	show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      next
	case True
	with L_A have a_A: "a \<in> A"
	  by blast
	from sharing_consistent_mono_shared [OF _ consis', where \<S>'="(\<S> \<oplus>\<^bsub>W\<^esub> R)"]
	have "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R) (\<O> \<union> A - R) sb"
	  by auto
	from Cons.hyps [OF this] a_shared
	have hyp: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R)) \<union> acquired True sb (\<O> \<union> A - R)"
	  by auto
	{
	  assume "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R))"
	  from share_unshared_in [OF this]
	  have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<union> acquired True sb (\<O> \<union> A - R)"
	  proof 
	    assume "a \<in> dom (share sb Map.empty)"
	    from share_mono_in [OF this]
	    have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	      by auto
	    thus ?thesis by blast
	  next
	    assume "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R) \<and> a \<notin> all_unshared sb"
	    hence a_unsh: "a \<notin> all_unshared sb" by blast
	    from a_A A_R have "a \<in> \<O> \<union> A - R"
	      by auto
	    from owns_unshared_share_acquired [OF consis' this a_unsh]
	    show ?thesis .
	  qed
	}
	with hyp show ?thesis
	  by (auto simp add: Write\<^sub>s\<^sub>b volatile)
      qed
    next
      case False
      with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_shared: "a \<in> dom \<S>" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
      L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b) 
    show ?thesis
    proof (cases "a \<in> L")
      case False with a_shared
      have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      from Cons.hyps [OF consis' this]
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    next
      case True
      with L_A have a_A: "a \<in> A"
        by blast
      from sharing_consistent_mono_shared [OF _ consis', where \<S>'="(\<S> \<oplus>\<^bsub>W\<^esub> R)"]
      have "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R) (\<O> \<union> A - R) sb"
        by auto
      from Cons.hyps [OF this] a_shared
      have hyp: "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R)) \<union> acquired True sb (\<O> \<union> A - R)"
        by auto
      {
	assume "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R))"
	from share_unshared_in [OF this]
	have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<union> acquired True sb (\<O> \<union> A - R)"
        proof 
	  assume "a \<in> dom (share sb Map.empty)"
	  from share_mono_in [OF this]
	  have "a \<in> dom (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
	    by auto
	  thus ?thesis by blast
        next
	  assume "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R) \<and> a \<notin> all_unshared sb"
	  hence a_unsh: "a \<notin> all_unshared sb" by blast
	  from a_A A_R have "a \<in> \<O> \<union> A - R"
	    by auto
	  from owns_unshared_share_acquired [OF consis' this a_unsh]
	  show ?thesis .
        qed
      }
      with hyp show ?thesis
        by (auto simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed

lemma dom_release_takeWhile:
  "\<And>S \<R>.
  dom (release (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S \<R>) = 
  dom \<R> \<union> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply  (clarsimp)
subgoal for a sb S \<R>
apply (case_tac a)
apply (auto simp add: augment_rels_def domIff split: if_split_asm option.splits)
done
done

lemma  share_all_until_volatile_write_share_acquired:
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes a_notin: "a \<notin> dom \<S>"
  assumes a_in: "a \<in> dom (share_all_until_volatile_write ts \<S>)" 
  shows "\<exists>i < length ts. 
           let (_,_,_,sb,_,_,_) = ts!i 
           in a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
using dist consis a_notin a_in 
proof (induct ts arbitrary: \<S> i)
  case Nil thus ?case by simp
next
  case (Cons t ts)

  have a_notin: "a \<notin> dom \<S>" by fact
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)    

  let ?take = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
  from t Cons.prems 
  have a_in: "a \<in> dom (share_all_until_volatile_write ts (share ?take \<S>))"
    by auto

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts".
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts".
  
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts".
  let ?\<S>' = "(share ?take \<S>)"

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t".
  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t ?take".
  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired ?take \<union> \<O>\<^sub>t"
    by simp

  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF this]
  have consis_shared': "sharing_consis ?\<S>' ts".


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto

  show ?case
  proof (cases "a \<in> all_shared ?take")
    case True
    thus ?thesis
    apply -
    apply (rule_tac x=0 in exI)
    apply (auto simp add: t aargh)
    done
  next
    case False

    have a_notin': "a \<notin> dom ?\<S>'"
    proof 
      assume "a \<in> dom ?\<S>'"
      from share_all_shared_in [OF this] False a_notin
      show False
        by auto
    qed
    from Cons.hyps [OF dist' consis_shared' a_notin' a_in]
    obtain i where "i < length ts" and 
      rel: "let (p,is,\<theta>,sb,\<D>,\<O>,\<R>) = ts!i 
            in a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
      by (auto simp add: Let_def aargh)
    then show ?thesis
      apply -
      apply (rule_tac x = "Suc i" in exI)
      apply (auto simp add: Let_def aargh)
      done
  qed
qed

lemma all_shared_share_acquired: "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> 
  a \<in> all_shared sb \<Longrightarrow> a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>"    
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	a_shared: "a \<in> R \<union> all_shared sb" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
	L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
        consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True) 
      show ?thesis
      proof (cases "a \<in> all_shared sb")
        case True
        from Cons.hyps [OF consis' True]
        show ?thesis
          by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      next
        case False
        with a_shared have "a \<in> R"
          by auto
        with L_A A_R R_owns have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
          by auto
        from shared_share_acquired [OF consis' this]
        show ?thesis
          by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
     qed
   next
      case False
      with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_shared: "a \<in> R \<union> all_shared sb" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
      L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b) 
    show ?thesis
    proof (cases "a \<in> all_shared sb")
      case True
      from Cons.hyps [OF consis' True]
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    next
      case False
      with a_shared have "a \<in> R"
        by auto
      with L_A A_R R_owns have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      from shared_share_acquired [OF consis' this]
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed

lemma (in ownership_distinct) share_all_until_volatile_write_share_acquired:
  assumes consis: "sharing_consis \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_in: "a \<in> dom (share_all_until_volatile_write ts \<S>)" 
  shows "a \<in> dom (share sb \<S>) \<or> a \<in> acquired True sb \<O> \<or>    
          (\<exists>j < length ts.  j \<noteq> i \<and>
           (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
            in a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)))"
proof -
  from assms ownership_distinct have dist: "ownership_distinct ts" 
    apply - 
    apply (rule ownership_distinct.intro)
    apply simp
    done
  from consis
  interpret sharing_consis \<S> ts .
  from sharing_consis [OF i_bound ts_i]
  have consis_sb: "sharing_consistent \<S> \<O> sb".

  let ?take_sb = "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"
  let ?drop_sb = "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"

  show ?thesis
  proof (cases "a \<in> dom \<S>")
    case True
    from shared_share_acquired [OF consis_sb True]
    have "a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>".
    thus ?thesis by auto
  next
    case False
    from share_all_until_volatile_write_share_acquired [OF dist consis False a_in]
    obtain j where j_bound: "j < length ts" and 
      rel: "let (_,_,_,sb\<^sub>j,_,_,_) = ts!j 
            in a \<in> all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" 
      by auto
    show ?thesis
    proof (cases "j=i")
      case False
      with j_bound rel 
      show ?thesis
        by blast
    next
      case True
      with rel ts_i have "a \<in> all_shared ?take_sb"
        by (auto simp add: Let_def)
      hence "a \<in> all_shared sb" 
      using all_shared_append [of ?take_sb ?drop_sb]
        by auto
      from all_shared_share_acquired [OF consis_sb this]
      have "a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>".
      thus ?thesis
        by auto
    qed
  qed
qed
    
(*
lemma all_unshared_acquired: 
  assumes consis: "sharing_consistent \<S> \<O> sb"
  assumes a_in: "a \<in> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
  shows "a \<in> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>" 
proof -
  from unshared_acquired_or_owned [OF sharing_consistent_takeWhile [OF consis]]
  have "all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<subseteq> 
    \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by auto
  with a_in acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b [of sb \<O>]
  show ?thesis
    apply (auto )
qed
*)

(*
lemma not_acquired_all_unshared: 
  assumes consis: "sharing_consistent \<S> \<O> sb"
  assumes a_notin: "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>" 
  shows "a \<notin> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof -
  from a_notin
  have "a \<notin> \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by (simp add: acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b) 
  moreover
  
  from unshared_acquired_or_owned [OF sharing_consistent_takeWhile [OF consis]]
  have "all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<subseteq> 
    \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    by auto
  
  ultimately show ?thesis
    by auto
qed

*)

(*
lemma (in valid_sharing) unacquired_share_all_until_volatile_write:
shows
  "- \<Union> (\<lambda>(_,_,_,sb,_,\<O>,_).  acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) ` set ts 
    \<subseteq> dom (share_all_until_volatile_write ts \<S>)" (is "- ?U \<subseteq> ?S")
proof
  fix a
  assume a_U: "a \<in> - ?U"
  show "a \<in> ?S"
  proof -
    from a_U have a_not_U: "a \<notin> ?U"
      by auto
    with acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b
    have a_notin: "a \<notin> \<Union> (\<lambda>(_,_,_,sb,_,\<O>).  \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts "
      by force
    from a_notin have a_unowned: "a \<notin> \<Union> (\<lambda>(_,_,_,_,_,\<O>).  \<O>) ` set ts"
      by blast
    from a_unowned unowned_shared
    have a_shared: "a \<in> dom \<S>"
      by auto

    moreover

    have "a \<notin> \<Union> (\<lambda>(_,_,_,sb,_,\<O>).  all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts "
          (is "a \<notin> ?UNSH")
    proof
      assume "a \<in> ?UNSH"
      from in_Union_image_nth_conv [OF this]
      obtain i p "is" \<O> \<D> \<theta> sb where
	i_bound: "i < length ts" and
	ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>)" and
	a_in: "a \<in> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
	by fastforce
      from all_unshared_acquired [OF sharing_consis [OF i_bound ts_i] a_in]
      have "a \<in> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>".
      with a_not_U nth_mem [OF i_bound] ts_i
      show False

	by (auto)
    qed

    ultimately
    show ?thesis
      apply (simp only: share_all_until_volatile_all_unshared)
      apply blast
      done
  qed
qed
*)
lemma acquired_all_shared_in: 
  "\<And>A. a \<in> acquired True sb A \<Longrightarrow> a \<in> acquired True sb {} \<or> (a \<in> A \<and> a \<notin> all_shared sb)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L R)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      have a_in: "a \<in> acquired True sb (A \<union> A' - R)"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> A")
	case True
	from Cons.hyps [OF a_in]
	have "a \<in> acquired True sb {} \<or> a \<in> A \<union> A' - R \<and> a \<notin> all_shared sb".
	then show ?thesis
	proof 
	  assume "a \<in> acquired True sb {}"
	  from acquired_mono_in [OF this]
	  have "a \<in> acquired True sb (A' - R)" by auto
	  then show ?thesis
	    by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile True)
	next
	  assume "a \<in> A \<union> A' - R \<and> a \<notin> all_shared sb"
	  then obtain "a \<notin> R" "a \<notin> all_shared sb"
	    by blast
	  then show ?thesis by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile True)
	qed
      next
	case False
	have "(A \<union> A' - R) \<subseteq> A \<union> (A' - R)"
	  by blast
	from acquired_mono [OF this] a_in
	have "a \<in> acquired True sb (A \<union> (A' - R))" by blast
	from acquired_union_notin_first [OF this False]
	have "a \<in> acquired True sb (A' - R)".
	then show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      qed
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A' L R W)
    from Cons.prems
    have a_in: "a \<in> acquired True sb (A \<union> A' - R)"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    show ?thesis
    proof (cases "a \<in> A")
      case True
      from Cons.hyps [OF a_in]
      have "a \<in> acquired True sb {} \<or> a \<in> A \<union> A' - R \<and> a \<notin> all_shared sb".
      then show ?thesis
      proof 
	assume "a \<in> acquired True sb {}"
	from acquired_mono_in [OF this]
	have "a \<in> acquired True sb (A' - R)" by auto
        then show ?thesis
	  by (clarsimp simp add: Ghost\<^sub>s\<^sub>b True)
      next
	assume "a \<in> A \<union> A' - R \<and> a \<notin> all_shared sb"
	then obtain "a \<notin> R" "a \<notin> all_shared sb"
	  by blast
	then show ?thesis by (clarsimp simp add: Ghost\<^sub>s\<^sub>b True)
      qed
    next
      case False
      have "(A \<union> A' - R) \<subseteq> A \<union> (A' - R)"
        by blast
      from acquired_mono [OF this] a_in
      have "a \<in> acquired True sb (A \<union> (A' - R))" by blast
      from acquired_union_notin_first [OF this False]
      have "a \<in> acquired True sb (A' - R)".
      then show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    qed
  qed
qed
   

lemma all_shared_acquired_in: "\<And>A. a \<in> A \<Longrightarrow> a \<notin> all_shared sb \<Longrightarrow> a \<in> acquired True sb A"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A' L R W)
    show ?thesis
    proof (cases volatile)
      case True
      show ?thesis
      proof -
	from Cons.prems obtain a_A: "a \<in> A" and a_R: "a \<notin> R" and  a_sb: "a \<notin> all_shared sb" 
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
	from a_A a_R have "a \<in> A \<union> A' - R"
	  by blast
	from Cons.hyps [OF this a_sb]
	show ?thesis  
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      qed
    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma owned_share_acquired: "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> 
  a \<in> \<O> \<Longrightarrow> a \<in> dom (share sb \<S>) \<union> acquired True sb \<O>"    
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	a_owned: "a \<in> \<O>" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
	L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
        consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True) 
      show ?thesis
      proof (cases "a \<in> R")
	case False with a_owned
	have "a \<in> \<O> \<union> A - R"
	  by auto
	from Cons.hyps [OF consis' this]
	show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      next
	case True
	from True L_A A_R have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by auto
	from shared_share_acquired [OF consis' this]
	show ?thesis 
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile True)
      qed
    next
      case False
      with Cons
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_owned: "a \<in> \<O>" and A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and
      L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b) 
    show ?thesis
    proof (cases "a \<in> R")
      case False with a_owned
      have "a \<in> \<O> \<union> A - R"
        by auto
      from Cons.hyps [OF consis' this]
      show ?thesis
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    next
      case True
      from True L_A A_R have "a \<in> dom (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
        by auto
      from shared_share_acquired [OF consis' this]
      show ?thesis 
        by (clarsimp simp add: Ghost\<^sub>s\<^sub>b True)
    qed
  qed
qed

(*
lemma (in valid_sharing) a_unowned_by_others_owned_or_shared:
  assumes dist: "ownership_distinct ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,tsmp,sb,\<D>,\<O>)"
  assumes a_unowned_others:
        "\<forall>j<length (map owns_sb ts). i \<noteq> j \<longrightarrow> 
          (let (\<O>\<^sub>j,sb\<^sub>j) = (map owns_sb ts)!j 
           in a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j)" 

  shows "a \<in> acquired True sb \<O> \<or> 
         a \<in> dom (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (share_all_until_volatile_write ts \<S>))"
proof -
  
  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

{
    fix j p\<^sub>j is\<^sub>j \<O>\<^sub>j \<D>\<^sub>j xs\<^sub>j sb\<^sub>j
    assume a_unowned: "a \<notin> acquired True ?take_sb \<O>"
    assume j_bound: "j < length ts"
    assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,xs\<^sub>j, sb\<^sub>j, \<D>\<^sub>j, \<O>\<^sub>j)"
    have "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j "
    proof (cases "i=j")
      case True
      from a_unowned ts_i jth True
      show ?thesis
	by auto
    next
      case False
      from a_unowned_others [rule_format, of j] j_bound jth False
      have "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j) \<O>\<^sub>j"
	by auto
      then
      show ?thesis
	by auto
    qed
  } note lem = this

  from prems have consis: "sharing_consis \<S> ts"
    by (simp add: valid_sharing_def)
  
  from sharing_consistent_share_all_until_volatile_write [OF dist consis i_bound ts_i]
  have consis':
    "sharing_consistent (share_all_until_volatile_write ts \<S>) (acquired True ?take_sb \<O>) ?drop_sb"
    by simp

  {
    assume a_notin: "a \<notin> acquired True sb \<O>"
    have ?thesis
    proof (cases "a \<in> acquired True ?take_sb \<O>")
      case True

      from owned_share_acquired [OF consis' True]
      have "a \<in> dom (share ?drop_sb (share_all_until_volatile_write ts \<S>)) \<union> 
	        acquired True ?drop_sb (acquired True ?take_sb \<O>)".
      with acquired_append [of True "?take_sb" "?drop_sb" \<O>]
      show ?thesis
	by auto
    next
      case False
      assume "a \<notin> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>"
      from lem [OF this]
      have "a \<in>  - \<Union> (\<lambda>(_,_,_,sb,_,\<O>). acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) ` set ts"
	by (fastforce simp add: in_set_conv_nth)

      with unacquired_share_all_until_volatile_write 
      have a_in: "a \<in> dom (share_all_until_volatile_write ts \<S>)"
	by auto

      from shared_share_acquired [OF consis' a_in] acquired_append [of True "?take_sb" "?drop_sb" \<O>]
      show ?thesis
	by auto
    qed
  } 
  then
  show ?thesis
    by auto
qed

*)
lemma outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired: 
"\<And>m \<S> \<O> pending_write. 
  \<lbrakk>reads_consistent pending_write \<O> m sb;non_volatile_owned_or_read_only pending_write \<S> \<O> sb;  
a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb\<rbrakk>
\<Longrightarrow> a \<in>  \<O> \<or> a \<in> all_acquired sb \<or>
    a \<in> read_only_reads \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	non_vo: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) 
	            (\<O> \<union> A - R) sb" and
        out_vol: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}" and
	out: "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True) 
      show ?thesis
      proof (cases "a \<in> \<O>")
	case True
	show ?thesis
	  by (clarsimp simp add: Write\<^sub>s\<^sub>b True volatile)
      next
	case False
	from outstanding_non_volatile_Read\<^sub>s\<^sub>b_acquired_or_read_only_reads [OF non_vo out]
	have a_in: "a \<in> acquired_reads True sb (\<O> \<union> A - R) \<or>
                    a \<in> read_only_reads (\<O> \<union> A - R) sb"
	  by auto
	with acquired_reads_all_acquired [of True sb "(\<O> \<union> A - R)"]
	show ?thesis 
	  by (auto simp add: Write\<^sub>s\<^sub>b volatile)
        qed
     next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      apply (clarsimp simp del: o_apply simp add: Read\<^sub>s\<^sub>b 
	acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b split: if_split_asm)
      apply auto
      done
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L)
    with Cons show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed



lemma outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired_dropWhile: 
assumes consis: "reads_consistent pending_write \<O> m sb" 
assumes nvo: "non_volatile_owned_or_read_only pending_write \<S> \<O> sb"
assumes out: "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
shows "a \<in> \<O> \<or> a \<in> all_acquired sb \<or>
       a \<in> read_only_reads \<O> sb"
using outstanding_refs_append [of is_non_volatile_Read\<^sub>s\<^sub>b "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb" 
  "dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb"] 
  outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired [OF consis nvo, of a] out
by (auto)


lemma share_commute: 
  "\<And>L R \<S> \<O>. \<lbrakk>sharing_consistent \<S> \<O> sb; 
all_shared sb \<inter> L = {}; all_shared sb \<inter> A = {}; all_acquired sb \<inter> R = {};
all_unshared sb \<inter> R = {}; all_shared sb \<inter> R = {}\<rbrakk> \<Longrightarrow> 
  (share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) =
  (share sb \<S>) \<oplus>\<^bsub>W\<^esub>  R \<ominus>\<^bsub>A\<^esub> L"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A' L' R' W')
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	L_prop: "(R' \<union> all_shared sb) \<inter> L = {}" and 
	A_prop: "(R' \<union> all_shared sb) \<inter> A = {}" and 
	R_acq_prop: "(A' \<union> all_acquired sb) \<inter> R = {}" and
	R_prop:"(L' \<union> all_unshared sb) \<inter> R = {}" and  
	R_prop_sh: "(R' \<union> all_shared sb) \<inter> R = {}" and
	A'_shared_owns: "A' \<subseteq> dom \<S> \<union> \<O>" and L'_A': " L' \<subseteq> A'" and A'_R': "A' \<inter> R' = {}" and 
	R'_owns: "R' \<subseteq> \<O>" and
        consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') (\<O> \<union> A' - R') sb" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)


      from L_prop obtain R'_L: "R' \<inter> L = {}" and acq_L: "all_shared sb \<inter> L = {}"
	by blast
      from A_prop obtain R'_A: "R' \<inter> A = {}" and acq_A: "all_shared sb \<inter> A = {}"
	by blast
      from R_acq_prop obtain A'_R: "A' \<inter> R = {}" and acq_R:"all_acquired sb \<inter> R = {}" 
	by blast
      from R_prop obtain L'_R: "L' \<inter> R = {}" and unsh_R: "all_unshared sb \<inter> R = {}"
	by blast
      from R_prop_sh obtain R'_R: "R' \<inter> R = {}" and sh_R: "all_shared sb \<inter> R = {}"
	by blast

      from Cons.hyps [OF consis' acq_L acq_A acq_R unsh_R sh_R ]
      have "share sb ((\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = share sb (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L".

      moreover

      from R'_L L'_R R'_R R'_A A'_R (*A'_R' L'_A'*)
      have "((\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') = ((\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	apply -
	apply (rule ext)
	apply (clarsimp simp add: augment_shared_def restrict_shared_def)
	apply (auto split: if_split_asm option.splits)
	done
      
      ultimately
      have "share sb ((\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') = share sb (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
	by simp
      then
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
    next
      case False with Cons show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis
      by (clarsimp simp add: Read\<^sub>s\<^sub>b)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis
      by (clarsimp simp add: Prog\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A' L' R' W') 
    from Cons.prems obtain 
      L_prop: "(R' \<union> all_shared sb) \<inter> L = {}" and 
      A_prop: "(R' \<union> all_shared sb) \<inter> A = {}" and 
      R_acq_prop: "(A' \<union> all_acquired sb) \<inter> R = {}" and
      R_prop:"(L' \<union> all_unshared sb) \<inter> R = {}" and  
      R_prop_sh: "(R' \<union> all_shared sb) \<inter> R = {}" and
      A'_shared_owns: "A' \<subseteq> dom \<S> \<union> \<O>" and L'_A': " L' \<subseteq> A'" and A'_R': "A' \<inter> R' = {}" and 
      R'_owns: "R' \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') (\<O> \<union> A' - R') sb" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)


    from L_prop obtain R'_L: "R' \<inter> L = {}" and acq_L: "all_shared sb \<inter> L = {}"
      by blast
    from A_prop obtain R'_A: "R' \<inter> A = {}" and acq_A: "all_shared sb \<inter> A = {}"
      by blast
    from R_acq_prop obtain A'_R: "A' \<inter> R = {}" and acq_R:"all_acquired sb \<inter> R = {}" 
      by blast
    from R_prop obtain L'_R: "L' \<inter> R = {}" and unsh_R: "all_unshared sb \<inter> R = {}"
      by blast
    from R_prop_sh obtain R'_R: "R' \<inter> R = {}" and sh_R: "all_shared sb \<inter> R = {}"
      by blast

    from Cons.hyps [OF consis' acq_L acq_A acq_R unsh_R sh_R ]
    have "share sb ((\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = share sb (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L".

    moreover

    from R'_L L'_R R'_R R'_A A'_R (*A'_R' L'_A'*)
    have "((\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') = ((\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
      apply -
      apply (rule ext)
      apply (clarsimp simp add: augment_shared_def restrict_shared_def)
      apply (auto split: if_split_asm option.splits)
      done
      
    ultimately
    have "share sb ((\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') = share sb (\<S> \<oplus>\<^bsub>W'\<^esub> R' \<ominus>\<^bsub>A'\<^esub> L') \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
      by simp
    then
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


lemma share_all_until_volatile_write_commute:
"\<And> \<S> R L. \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts;
        \<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {};
        \<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {};
       \<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {};
       \<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {};
       \<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}\<rbrakk> 
 \<Longrightarrow>
share_all_until_volatile_write ts \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L = share_all_until_volatile_write ts (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where
    t: "t=(p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)
  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts".
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts".

  have L_prop: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (t#ts) \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}" by fact
  hence L_prop': "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (ts) \<longrightarrow> (ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
    by force
  have A_prop: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (t#ts) \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}" by fact
  hence A_prop': "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (ts) \<longrightarrow> (ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}"
    by force
  have  R_prop_acq: "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (t#ts) \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact
  hence R_prop_acq': "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (ts) \<longrightarrow> (ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
    by force

  have  R_prop: "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (t#ts) \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact
  hence R_prop': "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (ts) \<longrightarrow> (ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
    by force

  have  R_prop_sh: "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (t#ts) \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact
  hence R_prop_sh': "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length (ts) \<longrightarrow> (ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"
    by force

  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts".

  from L_prop [rule_format, of 0 p "is" \<theta> sb \<D> \<O> ] t 
  have sh_L: "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}" 
    by simp

  from A_prop [rule_format, of 0 p "is" \<theta> sb \<D> \<O> ] t 
  have sh_A: "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}" 
    by simp

  from R_prop_acq [rule_format, of 0 p "is" \<theta> sb \<D> \<O> ] t 
  have acq_R: "all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
    by simp

  from R_prop [rule_format, of 0 p "is" \<theta> sb \<D> \<O>  ] t 
  have unsh_R: "all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
    by simp


  from R_prop_sh [rule_format, of 0 p "is"  \<theta> sb \<D> \<O>] t 
  have sh_R: "all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
    by simp

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O> sb".
  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O> (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)".

  from share_commute [OF consis_sb sh_L sh_A acq_R unsh_R sh_R]
  have share_eq: 
    "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) =
        (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L".
    
  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"

  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> \<O>"
    by simp


  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF sep]
  have sharing_consis': "sharing_consis (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) ts".

  from Cons.hyps [OF dist' sharing_consis' L_prop' A_prop' R_prop_acq' R_prop' R_prop_sh']
  have "share_all_until_volatile_write ts ?\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L =
        share_all_until_volatile_write ts (?\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".

  then
  have "share_all_until_volatile_write ts
         ?\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L =
        share_all_until_volatile_write ts
          (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))"
    by (simp add: share_eq)
  then
  show ?case
    by (simp add: t)
qed

lemma share_append_Ghost\<^sub>s\<^sub>b: 
  "\<And>\<S>. outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {} \<Longrightarrow> (share (sb @ [Ghost\<^sub>s\<^sub>b A L R W]) \<S>) = (share sb \<S>) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
apply (induct sb)
apply simp
subgoal for a sb \<S>
apply (case_tac a)
apply auto
done
done

lemma share_append_Ghost\<^sub>s\<^sub>b':
  "\<And>\<S>. outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {} \<Longrightarrow> 
     (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Ghost\<^sub>s\<^sub>b A L R W])) \<S>) = 
      (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
apply (induct sb)
apply  simp
subgoal for a sb \<S>
apply (case_tac a)
apply force+
done
done

lemma share_all_until_volatile_write_append_Ghost\<^sub>s\<^sub>b: 
assumes no_out_VWrite\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}"
shows "\<And>\<S> i. \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts;
   i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>);
   \<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {};
   \<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {};
       \<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {};
       \<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {};
       \<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}\<rbrakk>
  \<Longrightarrow>
  share_all_until_volatile_write (ts[i := (p', is',\<theta>', sb @ [Ghost\<^sub>s\<^sub>b A L R W], \<D>', \<O>')]) \<S>
                = share_all_until_volatile_write ts \<S>  \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t acq\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t) 
  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts".
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts".

  have L_prop: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (t#ts) \<longrightarrow> i\<noteq>j \<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}" by fact

  have A_prop: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (t#ts) \<longrightarrow> i\<noteq>j \<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}" by fact

  have  R_prop_acq: "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length (t#ts) \<longrightarrow> i\<noteq>j\<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact
  have  R_prop: "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length (t#ts) \<longrightarrow> i\<noteq>j\<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact

  have  R_prop_sh: "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length (t#ts) \<longrightarrow> i\<noteq>j \<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by fact

  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts".


  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t" .

  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)".

  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)"

  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
    by simp


  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i acq\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF sep]
  have sharing_consis': "sharing_consis (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>) ts".

  show ?case
  proof (cases i)
    case 0
    with t Cons.prems have eqs: "p\<^sub>t=p" "is\<^sub>t=is" "\<O>\<^sub>t=\<O>" "\<R>\<^sub>t=\<R>" "\<theta>\<^sub>t=\<theta>" "sb\<^sub>t=sb" "\<D>\<^sub>t=\<D>" 
      by auto

    from no_out_VWrite\<^sub>s\<^sub>b
    have flush_all: "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb = sb"
      by (auto simp add: outstanding_refs_conv)


    from no_out_VWrite\<^sub>s\<^sub>b
    have flush_all': "takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb@[Ghost\<^sub>s\<^sub>b A L R W]) = sb@[Ghost\<^sub>s\<^sub>b A L R W]"
      by (auto simp add: outstanding_refs_conv)

    have share_eq:
      "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Ghost\<^sub>s\<^sub>b A L R W])) \<S>) = 
            (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub>  L"
      apply (simp only: flush_all flush_all')
      apply (rule share_append_Ghost\<^sub>s\<^sub>b [OF no_out_VWrite\<^sub>s\<^sub>b])
      done

    from L_prop 0 have L_prop': 
    "\<forall>i p is \<O> \<R> \<D> \<theta> sb.
      i < length ts \<longrightarrow>
      ts ! i = (p, is,\<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
      all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}"
      apply clarsimp
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply auto
      done
      done
    from A_prop 0 have A_prop': 
    "\<forall>i p is \<O> \<R> \<D> \<theta> sb.
      i < length ts \<longrightarrow>
      ts ! i = (p, is,\<theta>, sb, \<D>, \<O>,\<R>) \<longrightarrow>
      all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}"
      apply clarsimp
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply auto
      done
      done
    from R_prop_acq 0 have R_prop_acq':
        "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
      apply clarsimp
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply auto
      done
      done
    from R_prop 0 
    have  R_prop': 
      "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
      apply clarsimp
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply auto
      done
      done
    from R_prop_sh 0 have R_prop_sh': 
      "\<forall>i p is \<O> \<R> \<D> \<theta> sb.  i < length ts \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" 
      apply clarsimp
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply auto
      done
      done


    from share_all_until_volatile_write_commute [OF dist' sharing_consis' L_prop' A_prop' R_prop_acq' R_prop' 
      R_prop_sh']

    have "share_all_until_volatile_write ts (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>  \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) =
          share_all_until_volatile_write ts (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)  \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub>  L"
      by (simp add: eqs)
    with share_eq
    show ?thesis
      by (clarsimp simp add: 0 t)
  next
    case (Suc k)
    from L_prop Suc
    have L_prop': "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (ts) \<longrightarrow> k\<noteq>j \<longrightarrow> (ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> L = {}" by force

    from A_prop Suc
    have A_prop': "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (ts) \<longrightarrow> k\<noteq>j \<longrightarrow> (ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> A = {}" by force
    from R_prop_acq Suc have R_prop_acq':
        "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> k\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}"  by force

    from R_prop Suc
    have  R_prop': 
      "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> k\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by force

    from R_prop_sh Suc have R_prop_sh': 
      "\<forall>j p is \<O> \<R> \<D> \<theta> sb.  j < length ts \<longrightarrow> k\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<inter> R = {}" by force

    from Cons.prems Suc obtain k_bound: "k < length ts" and ts_k: "ts!k =  (p, is,\<theta>, sb, \<D>, \<O>,\<R>)"
      by auto

    from Cons.hyps [OF dist' sharing_consis' k_bound ts_k L_prop' A_prop' R_prop_acq' R_prop' R_prop_sh']
    show ?thesis
      by (clarsimp simp add: t Suc)
  qed
qed




(*
I think this is what should work:
share_all_until_volatile_write (ts[i :=(p',is',\<theta>',sb',\<D>',\<O>',\<R>')]) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) =
share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (share_all_until_volatile_write ts \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)
*)

lemma share_domain_changes:
  "\<And>\<S> \<S>'. a \<in> all_shared sb \<union> all_unshared sb \<Longrightarrow> share sb \<S>' a = share sb \<S> a "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain a_in: "a \<in> R \<union> all_shared sb \<union> L \<union> all_unshared sb"
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> R")
        case True
        from True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
        from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
        have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by auto
        then show ?thesis
          by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      next
        case False
        note not_R = this
        show ?thesis
        proof (cases "a \<in> L")
          case True        
          from not_R True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
            by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
          from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
          have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
            by auto
          then show ?thesis
            by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
        next
          case False
          with not_R a_in have "a \<in> all_shared sb \<union> all_unshared sb"
            by auto
          from Cons.hyps [OF this]
          show ?thesis by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
        qed
      qed
    next
      case False with Cons show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next 
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain a_in: "a \<in> R \<union> all_shared sb \<union> L \<union> all_unshared sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    show ?thesis
    proof (cases "a \<in> R")
      case True
      from True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
      from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
      have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by auto
      then show ?thesis
       by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    next
      case False
      note not_R = this
      show ?thesis
      proof (cases "a \<in> L")
        case True        
        from not_R True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
        from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
        have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by auto
        then show ?thesis
          by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      next
        case False
        with not_R a_in have "a \<in> all_shared sb \<union> all_unshared sb"
          by auto
        from Cons.hyps [OF this]
        show ?thesis by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      qed
    qed
  qed
qed

lemma share_domain_changesX:
  "\<And>\<S> \<S>' X. \<forall>a \<in> X. \<S>' a = \<S> a 
  \<Longrightarrow> a \<in> all_shared sb \<union> all_unshared sb \<union> X \<Longrightarrow> share sb \<S>' a = share sb \<S> a "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  then have shared_eq: "\<forall>a \<in> X. \<S>' a = \<S> a"
    by auto
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain a_in: "a \<in> R \<union> all_shared sb \<union> L \<union> all_unshared sb \<union> X"
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      show ?thesis
      proof (cases "a \<in> R")
        case True
        from True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
        from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
        have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by auto
        then show ?thesis
          by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
      next
        case False
        note not_R = this
        show ?thesis
        proof (cases "a \<in> L")
          case True        
          from not_R True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
            by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
          from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
          have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
            by auto
          then show ?thesis
            by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
        next
          case False
          from shared_eq have shared_eq': "\<forall>a \<in> X. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
            by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
          from False not_R a_in have "a \<in> all_shared sb \<union> all_unshared sb \<union> X"
            by auto
          from Cons.hyps [OF shared_eq' this]
          show ?thesis by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
        qed
      qed
    next
      case False with Cons show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next 
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain a_in: "a \<in> R \<union> all_shared sb \<union> L \<union> all_unshared sb \<union> X"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    show ?thesis
    proof (cases "a \<in> R")
      case True
      from True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
      from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
      have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
        by auto
      then show ?thesis
       by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    next
      case False
      note not_R = this
      show ?thesis
      proof (cases "a \<in> L")
        case True        
        from not_R True have "(\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
        from  share_shared_eq [where \<S>'="\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L" and \<S>="\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L",  OF this]
        have "share sb (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by auto
        then show ?thesis
          by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      next
        case False
        from shared_eq have shared_eq': "\<forall>a \<in> X. (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
          by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
        from False not_R a_in have "a \<in> all_shared sb \<union> all_unshared sb \<union> X"
          by auto
        from Cons.hyps [OF shared_eq' this]
        show ?thesis by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      qed
    qed
  qed
qed

lemma share_unchanged: 
  "\<And>\<S>. a \<notin> all_shared sb \<union> all_unshared sb \<union> all_acquired sb \<Longrightarrow> share sb \<S> a = \<S> a "
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain a_R: "a \<notin> R" and a_L: "a \<notin> L"  and a_A: "a \<notin> A" 
        and a': "a \<notin> all_shared sb \<union> all_unshared sb \<union> all_acquired sb"
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
      from Cons.hyps [OF a']
      have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a" .
      moreover
      from a_R a_L a_A have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
        by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
      ultimately
      show ?thesis
       by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
   next
     case False with Cons show ?thesis by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next 
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain a_R: "a \<notin> R" and a_L: "a \<notin> L"  and a_A: "a \<notin> A" 
      and a': "a \<notin> all_shared sb \<union> all_unshared sb \<union> all_acquired sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    from Cons.hyps [OF a']
    have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a" .
    moreover
    from a_R a_L a_A have "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
      by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
    ultimately
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

(* FIXME: duplication with share_commute *)
lemma share_augment_release_commute: 
assumes dist: "(R \<union> L \<union> A) \<inter> (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) = {}"
shows "(share sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
proof -
  from dist have shared_eq: "\<forall>a \<in> all_acquired sb. (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = \<S> a"
    by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)  
  {
    fix a
    assume a_in: "a \<in> all_shared sb \<union> all_unshared sb \<union> all_acquired sb"
    from share_domain_changesX [OF shared_eq this]
    have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = share sb \<S> a".
    also
    from dist a_in have "... = (share sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)  
    finally have  "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (share sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a".
  }
  moreover
  {
    fix a
    assume a_notin: "a \<notin> all_shared sb \<union> all_unshared sb \<union> all_acquired sb"
    from share_unchanged [OF a_notin]
    have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a".
    moreover
    from share_unchanged [OF a_notin]
    have "share sb \<S> a = \<S> a".
    hence "(share sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by (auto simp add: augment_shared_def restrict_shared_def split: option.splits)
    ultimately have "share sb (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a = (share sb \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) a"
      by simp
  }
  ultimately show ?thesis
    apply -
    apply (rule ext)
    subgoal for x
    apply (case_tac "x \<in> all_shared sb \<union> all_unshared sb \<union> all_acquired sb")
    apply auto
    done
    done
qed

lemma share_append_commute: 
  "\<And>ys \<S>. (all_shared xs \<union> all_unshared xs \<union> all_acquired xs) \<inter> 
             (all_shared ys \<union> all_unshared ys \<union> all_acquired ys) = {} 
\<Longrightarrow> share xs (share ys \<S>) = share ys (share xs \<S>)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems have 
        dist': "(all_shared xs \<union> all_unshared xs \<union> all_acquired xs) \<inter> 
                (all_shared ys \<union>  all_unshared ys \<union> all_acquired ys) = {} "
        apply (clarsimp  simp add: Write\<^sub>s\<^sub>b True)
        apply blast
        done
      from Cons.prems have
        dist: "(R \<union> L \<union> A) \<inter> (all_shared ys \<union> all_unshared ys \<union> all_acquired ys) = {}"
        apply (clarsimp  simp add: Write\<^sub>s\<^sub>b True)
        apply blast
        done
      from share_augment_release_commute [OF dist]
      have "(share ys \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = share ys (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
      
      with Cons.hyps [OF dist']
      show ?thesis
        by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
        by (clarsimp simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems have 
      dist': "(all_shared xs \<union> all_unshared xs \<union> all_acquired xs) \<inter> 
                (all_shared ys \<union>  all_unshared ys \<union> all_acquired ys) = {} "
      apply (clarsimp  simp add: Ghost\<^sub>s\<^sub>b)
      apply blast
      done
    from Cons.prems have
      dist: "(R \<union> L \<union> A) \<inter> (all_shared ys \<union> all_unshared ys \<union> all_acquired ys) = {}"
      apply (clarsimp  simp add: Ghost\<^sub>s\<^sub>b)
      apply blast
      done
    from share_augment_release_commute [OF dist]
    have "(share ys \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = share ys (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
      
    with Cons.hyps [OF dist']
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed

lemma share_append_commute': 
  assumes dist: "(all_shared xs \<union> all_unshared xs \<union> all_acquired xs) \<inter> 
             (all_shared ys \<union> all_unshared ys \<union> all_acquired ys) = {} "
  shows "share (ys@xs) \<S> = share (xs@ys) \<S>"
proof -
  from share_append_commute [OF dist] share_append [of xs ys] share_append [of ys xs]
  show ?thesis
    by simp
qed

lemma share_all_until_volatile_write_share_commute:
shows "\<And> \<S> (sb'::'a memref list). \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts; 
        \<forall>i p is \<O> \<R> \<D> \<theta> (sb::'a memref list). i < length ts 
            \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared sb' \<union> all_unshared sb' \<union> all_acquired sb') = {}\<rbrakk> 
 \<Longrightarrow>
share_all_until_volatile_write ts (share sb' \<S>) =
share sb' (share_all_until_volatile_write ts \<S>)"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  let ?take = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts" .

  have dist_prop: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (t#ts) 
            \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared sb' \<union> all_unshared sb' \<union> all_acquired sb') = {}" by fact
  from dist_prop [rule_format, of 0] t
  have dist_t: "(all_shared ?take \<union> all_unshared ?take \<union> all_acquired ?take) \<inter> 
         (all_shared sb' \<union> all_unshared sb' \<union> all_acquired sb') = {}"
    apply clarsimp
    done
  from dist_prop have 
  dist_prop':"\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts 
            \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared sb' \<union> all_unshared sb' \<union> all_acquired sb') = {}"
    apply (clarsimp)
    subgoal for i p "is" \<O> \<R> \<D> \<theta> sb
    apply (drule_tac x="Suc i" in spec)
    apply clarsimp
    done
    done

  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts" .

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t" .

  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t ?take".

  let ?\<S>' = "(share ?take \<S>)"

  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
    by simp


  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i acq\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF sep]
  have sharing_consis': "sharing_consis ?\<S>' ts".

  have "share_all_until_volatile_write ts (share ?take (share sb' \<S>)) =
        share sb' (share_all_until_volatile_write ts (share ?take \<S>))"
  proof -
    from share_append_commute [OF dist_t]
    have "(share ?take (share sb' \<S>)) = (share sb' (share ?take \<S>))" .
    then
    have "share_all_until_volatile_write ts (share ?take (share sb' \<S>)) =
          share_all_until_volatile_write ts (share sb' (share ?take \<S>))"
      by (simp)
    also
    from Cons.hyps [OF dist' sharing_consis' dist_prop']
    have "... = share sb' (share_all_until_volatile_write ts (share ?take \<S>))".
    finally show ?thesis .
  qed
  then show ?case
    by (clarsimp simp add: t)
qed
  
  
(* FIXME: move up*)
lemma all_shared_takeWhile_subset: "all_shared (takeWhile P sb) \<subseteq> all_shared sb"
using all_shared_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto
lemma all_shared_dropWhile_subset: "all_shared (dropWhile P sb) \<subseteq> all_shared sb"
using all_shared_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto

lemma all_unshared_takeWhile_subset: "all_unshared (takeWhile P sb) \<subseteq> all_unshared sb"
using all_unshared_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto
lemma all_unshared_dropWhile_subset: "all_unshared (dropWhile P sb) \<subseteq> all_unshared sb"
using all_unshared_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto

lemma all_acquired_takeWhile_subset: "all_acquired (takeWhile P sb) \<subseteq> all_acquired sb"
using all_acquired_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto
lemma all_acquired_dropWhile_subset: "all_acquired (dropWhile P sb) \<subseteq> all_acquired sb"
using all_acquired_append [of "(takeWhile P sb)" "(dropWhile P sb)"]
  by auto

lemma share_all_until_volatile_write_flush_commute:
assumes takeWhile_empty: "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) = []"
shows "\<And> \<S> R L W A i. \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts; i < length ts;
        ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>); 
        \<forall>i p is \<O> \<R> \<D> \<theta> (sb::'a memref list). i < length ts 
            \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union> 
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') \<union> 
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')) = {};
        \<forall>j p is \<O> \<R> \<D> \<theta> (sb::'a memref list). j < length ts \<longrightarrow> i\<noteq>j 
            \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) \<inter> 
                    (R \<union> L \<union> A) = {}\<rbrakk> 
 \<Longrightarrow>
share_all_until_volatile_write (ts[i :=(p',is',\<theta>',sb',\<D>',\<O>',\<R>')]) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) =
share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') (share_all_until_volatile_write ts \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  let ?take = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
  let ?take_sb' = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')"
  let ?drop = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts" .
  have dist_prop: "\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length (t#ts) 
            \<longrightarrow> (t#ts)!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared ?take_sb' \<union> all_unshared ?take_sb' \<union> all_acquired ?take_sb') = {}" by fact
  from dist_prop [rule_format, of 0] t
  have dist_t: "(all_shared ?take \<union> all_unshared ?take \<union> all_acquired ?take) \<inter> 
         (all_shared ?take_sb' \<union> all_unshared ?take_sb' \<union> all_acquired ?take_sb') = {}"
    apply clarsimp
    done
  from dist_prop have 
  dist_prop':"\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts 
            \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union>
                     all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (all_shared ?take_sb' \<union> all_unshared ?take_sb' \<union> all_acquired ?take_sb') = {}"
    apply (clarsimp)
    subgoal for i p "is" \<O> \<R> \<D> \<theta> sb
    apply (drule_tac x="Suc i" in spec)
    apply clarsimp
    done
    done
  have dist_prop_R_L_A: "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (t#ts) \<longrightarrow> i \<noteq> j
            \<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) \<inter> 
                    (R \<union> L \<union> A) = {}" by fact

    
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts" .

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t" .

  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)".

  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto


  show ?case
  proof (cases i)
    case 0

    with t Cons.prems have eqs: "p\<^sub>t=p" "is\<^sub>t=is" "\<O>\<^sub>t=\<O>" "\<R>\<^sub>t=\<R>" "\<theta>\<^sub>t=\<theta>" "sb\<^sub>t=sb" "\<D>\<^sub>t=\<D>" 
      by auto

    let ?\<S>' = "\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"

    from dist_prop_R_L_A 0 have 
      dist_prop_R_L_A':"\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts 
            \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) \<inter> 
                    (R \<union> L \<union> A) = {}"
      apply (clarsimp)
      subgoal for i1 p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc i1" in spec)
      apply clarsimp
      done 
      done
    then 
    have dist_prop_R_L_A'':"\<forall>i p is \<O> \<R> \<D> \<theta> sb. i < length ts 
        \<longrightarrow> ts!i=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
      (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> 
      all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
      (R \<union> L \<union> A) = {}"
      apply (clarsimp)
      subgoal for i p "is" \<O> \<R> \<D> \<theta> sb
      apply (cut_tac sb=sb in all_shared_takeWhile_subset [where P="Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"])
      apply (cut_tac sb=sb in all_unshared_takeWhile_subset [where P="Not \<circ> is_volatile_Write\<^sub>s\<^sub>b"])
      apply (cut_tac sb=sb in all_acquired_takeWhile_subset [where P="Not \<circ> is_volatile_Write\<^sub>s\<^sub>b" ])
      apply fastforce
      done
      done

    have  sep: "\<forall>i<length ts.
      let (_, _, _, sb, _, _, _) = ts ! i
      in \<forall>a\<in>all_acquired sb. ?\<S>' a = \<S> a"
    proof -
      {
        fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i acq\<^sub>i \<theta>\<^sub>i sb\<^sub>i a
        assume i_bound: "i < length ts"
        assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
        assume a_in: "a \<in> all_acquired sb\<^sub>i"
        have "?\<S>' a = \<S> a"
        proof -
          from dist_prop_R_L_A' [rule_format, OF i_bound ts_i] a_in
          show ?thesis
            by (auto simp add: augment_shared_def restrict_shared_def split: option.splits) 
        qed
      }
      thus ?thesis by auto
    qed
    from consis'.sharing_consis_shared_exchange [OF sep]
    have sharing_consis': "sharing_consis ?\<S>' ts".
    
    from share_all_until_volatile_write_share_commute [of ts "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb')", OF dist' sharing_consis' dist_prop']

    have "share_all_until_volatile_write ts (share ?take_sb' ?\<S>') =
          share ?take_sb' (share_all_until_volatile_write ts ?\<S>')" .

    moreover 

    from dist_prop_R_L_A''
    have "(share_all_until_volatile_write ts (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) =
          (share_all_until_volatile_write ts \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"

      apply -
      apply (rule  share_all_until_volatile_write_commute [OF dist' consis', of L A R W,symmetric])
      apply (clarsimp,blast)+
      done
    ultimately
    show ?thesis
      using takeWhile_empty
      by (clarsimp simp add: t 0  aargh eqs)
  next
    case (Suc k)
    from Cons.prems Suc obtain k_bound: "k < length ts" and ts_k: "ts!k =  (p, is,\<theta>, sb, \<D>, \<O>,\<R>)"
      by auto

    let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)"
    from freshly_shared_owned [OF consis_sb]
    have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
    from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
    have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
      by simp



    from freshly_shared_owned [OF consis_sb]
    have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
    from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
    have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
      by simp


    have sep: 
      "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
    proof -
      {
        fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i acq\<^sub>i \<theta>\<^sub>i sb\<^sub>i
        assume i_bound: "i < length ts"
        assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
        have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
              all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
        proof -
	  from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	  have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	    by force


	  from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	  have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	    by blast

	  moreover
	
	  from sharing_consis [of "Suc i"] ts_i i_bound
	  have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	    by force
	  from unshared_acquired_or_owned [OF this]
	  have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	  with dist fresh_owned
	  have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	    by blast
      
	  ultimately show ?thesis by simp
        qed
      }
      thus ?thesis
        by (fastforce simp add: Let_def)
    qed
    from consis'.sharing_consis_preservation [OF sep]
    have sharing_consis': "sharing_consis ?\<S>' ts".


    from dist_prop_R_L_A [rule_format, of 0] Suc t
    have dist_t_R_L_A: "(all_shared sb\<^sub>t \<union> all_unshared sb\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> 
         (R \<union> L \<union> A) = {}"
      apply clarsimp
      done
    from dist_t_R_L_A 
    have "(R \<union> L \<union> A) \<inter> (all_shared ?take \<union> all_unshared ?take \<union> all_acquired ?take) = {}"
    using all_shared_append [of ?take ?drop] all_unshared_append [of ?take ?drop] all_acquired_append [of ?take ?drop]
      by auto

    from share_augment_release_commute [OF this]
    have "share ?take \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L = share ?take (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" .
    moreover
    
    from dist_prop_R_L_A Suc
    have "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (ts) \<longrightarrow> k \<noteq> j
      \<longrightarrow> (ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared sb \<union> all_unshared sb \<union> all_acquired sb) \<inter> 
                    (R \<union> L \<union> A) = {}" 
      apply (clarsimp)
      subgoal for j p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc j" in spec)
      apply clarsimp
      done
      done
    note Cons.hyps [OF dist' sharing_consis' k_bound ts_k dist_prop' this, of W]
    ultimately
    show ?thesis
      by (clarsimp simp add: t Suc )
  qed
qed


lemma share_all_until_volatile_write_Ghost\<^sub>s\<^sub>b_commute:
shows "\<And> \<S> i. \<lbrakk>ownership_distinct ts; sharing_consis \<S> ts; i < length ts;
        ts!i = (p,is,\<theta>,Ghost\<^sub>s\<^sub>b A L R W#sb,\<D>,\<O>,\<R>); 
        \<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts \<longrightarrow> i\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (R \<union> L \<union> A) = {}\<rbrakk> 
 \<Longrightarrow>
share_all_until_volatile_write (ts[i :=(p',is',\<theta>',sb,\<D>',\<O>',\<R>')]) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) =
share_all_until_volatile_write ts \<S>"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)
  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  have consis: "sharing_consis \<S> (t#ts)" by fact
  then interpret sharing_consis \<S> "t#ts" .
  have dist_prop:  "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length (t#ts) \<longrightarrow> i\<noteq>j \<longrightarrow> (t#ts)!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (R \<union> L \<union> A) = {}" by fact

  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".

  from sharing_consis_tl [OF consis]
  have consis': "sharing_consis \<S> ts".
  then
  interpret consis': sharing_consis \<S> "ts" .

  from sharing_consis [of 0, simplified, OF t]
  have "sharing_consistent \<S> \<O>\<^sub>t sb\<^sub>t" .

  from sharing_consistent_takeWhile [OF this]
  have consis_sb: "sharing_consistent \<S> \<O>\<^sub>t (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)".

  let ?\<S>' = "(share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)"

  from freshly_shared_owned [OF consis_sb]
  have fresh_owned: "dom ?\<S>' - dom \<S> \<subseteq> \<O>\<^sub>t".
  from unshared_all_unshared [OF consis_sb] unshared_acquired_or_owned [OF consis_sb]
  have unshared_acq_owned: "dom \<S> - dom ?\<S>'
                 \<subseteq> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> \<O>\<^sub>t"
    by simp


  have sep: 
    "\<forall>i < length ts. let (_,_,_,sb',_,_,_) = ts!i in 
          all_acquired sb' \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
          all_unshared sb' \<inter> dom ?\<S>' - dom \<S> = {}"
  proof -
    {
      fix i p\<^sub>i "is\<^sub>i" \<O>\<^sub>i \<R>\<^sub>i \<D>\<^sub>i \<theta>\<^sub>i sb\<^sub>i
      assume i_bound: "i < length ts"
      assume ts_i: "ts ! i = (p\<^sub>i,is\<^sub>i,\<theta>\<^sub>i,sb\<^sub>i,\<D>\<^sub>i,\<O>\<^sub>i,\<R>\<^sub>i)"
      have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {} \<and> 
            all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
      proof -
	from ownership_distinct [of "0" "Suc i"] ts_i t i_bound
	have dist: "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>i \<union> all_acquired sb\<^sub>i) = {}"
	  by force


	from dist unshared_acq_owned all_acquired_takeWhile [of "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)" sb\<^sub>t]
	have "all_acquired sb\<^sub>i \<inter> dom \<S> - dom ?\<S>' = {}"
	  by blast

	moreover
	
	from sharing_consis [of "Suc i"] ts_i i_bound
	have "sharing_consistent \<S> \<O>\<^sub>i sb\<^sub>i"
	  by force
	from unshared_acquired_or_owned [OF this]
	have "all_unshared sb\<^sub>i \<subseteq> all_acquired sb\<^sub>i \<union> \<O>\<^sub>i".      
	with dist fresh_owned
	have "all_unshared sb\<^sub>i \<inter> dom ?\<S>' - dom \<S> = {}"
	  by blast
      
	ultimately show ?thesis by simp
      qed
    }
    thus ?thesis
      by (fastforce simp add: Let_def)
  qed

  from consis'.sharing_consis_preservation [OF sep]
  have sharing_consis': "sharing_consis (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>) ts".

  show ?case
  proof (cases i)
    case 0

    with t Cons.prems have eqs: "p\<^sub>t=p" "is\<^sub>t=is" "\<O>\<^sub>t=\<O>" "\<R>\<^sub>t=\<R>" "\<theta>\<^sub>t=\<theta>" "sb\<^sub>t=Ghost\<^sub>s\<^sub>b A L R W#sb" "\<D>\<^sub>t=\<D>" 
      by auto

    show ?thesis
      by (clarsimp simp add: 0 t eqs)
  next
    case (Suc k)
    from Cons.prems Suc obtain k_bound: "k < length ts" and ts_k: "ts!k =  (p, is,\<theta>, Ghost\<^sub>s\<^sub>b A L R W#sb, \<D>, \<O>,\<R>)"
      by auto

    from dist_prop Suc 
    have dist_prop':  "\<forall>j p is \<O> \<R> \<D> \<theta> sb. j < length ts \<longrightarrow> k\<noteq>j \<longrightarrow> ts!j=(p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<longrightarrow> 
                    (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) \<inter> 
                    (R \<union> L \<union> A) = {}" 
      apply (clarsimp)
      subgoal for j p "is" \<O> \<R> \<D> \<theta> sb
      apply (drule_tac x="Suc j" in spec)
      apply auto
      done
      done

    from Cons.hyps [OF dist' sharing_consis' k_bound ts_k dist_prop']
    have "share_all_until_volatile_write (ts[k := (p', is', \<theta>', sb, \<D>', \<O>', \<R>')])
        (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) =
     share_all_until_volatile_write ts
       (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S>)" .
    
    moreover
    from dist_prop [rule_format, of 0 p\<^sub>t "is\<^sub>t" \<theta>\<^sub>t sb\<^sub>t \<D>\<^sub>t  \<O>\<^sub>t \<R>\<^sub>t ] t Suc
    have "(R \<union> L \<union> A) \<inter> (all_shared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> all_unshared (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)) = {}"
      apply clarsimp
      apply blast
      done
    from share_augment_release_commute [OF this]
    have "share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) \<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L =
      share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t) (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)".
    ultimately
      show ?thesis
      by (clarsimp simp add: Suc t)
  qed
qed

lemma share_all_until_volatile_write_update_sb:
assumes congr: "\<And>S. share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb') S = share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S"
shows  "\<And>\<S> i. \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk> 
  \<Longrightarrow>
  share_all_until_volatile_write ts \<S> =
    share_all_until_volatile_write (ts[i := (p', is',\<theta>', sb', \<D>', \<O>',\<R>')]) \<S>"
proof (induct ts)
  case Nil
  thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)

  show ?case
  proof (cases i)
    case 0
    with t Cons.prems have eqs: "p\<^sub>t=p" "is\<^sub>t=is" "\<O>\<^sub>t=\<O>" "\<R>\<^sub>t=\<R>" "\<theta>\<^sub>t=\<theta>" "sb\<^sub>t=sb" "\<D>\<^sub>t=\<D>" 
      by auto

    show ?thesis
      by (clarsimp simp add: 0 t eqs congr)
  next
    case (Suc k)
    from Cons.prems Suc obtain k_bound: "k < length ts" and ts_k: "ts!k =  (p, is,\<theta>, sb, \<D>, \<O>, \<R>)"
      by auto
    from Cons.hyps [OF k_bound ts_k ]
    show ?thesis
      by (clarsimp simp add: t Suc)
  qed
qed

lemma share_all_until_volatile_write_append_Ghost\<^sub>s\<^sub>b':
assumes out_VWrite\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb \<noteq> {}"
assumes i_bound: "i < length ts"
assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
shows "share_all_until_volatile_write ts \<S> =
    share_all_until_volatile_write
     (ts[i := (p', is',\<theta>', sb @ [Ghost\<^sub>s\<^sub>b A L R W], \<D>', \<O>',\<R>')]) \<S>"
proof -
  from out_VWrite\<^sub>s\<^sub>b 
  have "\<And>S. share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Ghost\<^sub>s\<^sub>b A L R W])) S = 
             share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S"
    by (simp add: outstanding_vol_write_takeWhile_append)
  from share_all_until_volatile_write_update_sb [OF this i_bound ts_i]
  show ?thesis
    by simp
qed

lemma acquired_append_Prog\<^sub>s\<^sub>b:
"\<And>S. (acquired pending_write (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (sb @ [Prog\<^sub>s\<^sub>b p\<^sub>1 p\<^sub>2 mis])) S) = 
       (acquired pending_write (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) S) "
  by (induct sb) (auto split: memref.splits)

(* FIXME: move up *)
lemma outstanding_refs_non_empty_dropWhile: 
  "outstanding_refs P xs \<noteq> {} \<Longrightarrow> outstanding_refs P (dropWhile (Not \<circ> P) xs) \<noteq> {}"
apply (induct xs)
apply simp
apply (simp split: if_split_asm)
done

lemma ex_not: "Ex Not"
  by blast



(*
lemma read_only_share_all_until_volatile_write:
  "\<And>\<S>. read_only (share_all_until_volatile_write ts \<S>) \<subseteq> read_only \<S>"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
    by (cases t)
  let ?take_sb\<^sub>t ="(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
 
  from read_only_share_takeWhile 
  have "read_only (share ?take_sb\<^sub>t \<S>) \<subseteq> read_only \<S>".
  moreover
  from Cons.hyps 
  have "read_only (share_all_until_volatile_write ts (share ?take_sb\<^sub>t \<S>)) \<subseteq> 
    read_only (share ?take_sb\<^sub>t \<S>)".
  ultimately
  show ?case
    by (simp add: t)
qed
*)

(*       
lemma read_only_takeWhile_share_all_until_volatile_write:
  "\<And>i \<S>. \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>)\<rbrakk>
   \<Longrightarrow> read_only (share_all_until_volatile_write ts \<S>)
       \<subseteq> read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t where
    t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t)"
    by (cases t)

  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?take_sb\<^sub>t ="(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"

  note i_bound = `i < length (t#ts)`
  note ts_i = `(t#ts)!i = (p,is,\<theta>,sb,\<D>,\<O>)`
  show ?case
  proof (cases i)
    case 0
    from read_only_share_all_until_volatile_write
    have "read_only (share_all_until_volatile_write ts (share ?take_sb \<S>))
           \<subseteq> read_only (share ?take_sb \<S>)".
    with ts_i
    show ?thesis
      by (simp add: t 0 del: o_apply)
  next
    case (Suc k)
    from i_bound Suc have k_bound: "k < length ts"
      by auto
    from ts_i Suc have ts_k: "ts!k = (p,is,\<theta>,sb,\<D>,\<O>)"
      by auto

    from Cons.hyps [OF k_bound ts_k]
    have "read_only (share_all_until_volatile_write ts (share ?take_sb\<^sub>t \<S>)) \<subseteq> 
      read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) 
           (share ?take_sb\<^sub>t \<S>))".
    moreover
    from read_only_share_takeWhile
    have "read_only (share ?take_sb\<^sub>t \<S>) \<subseteq> read_only \<S>".
    from share_read_only_mono [OF this, of ?take_sb]
    have "read_only (share ?take_sb (share ?take_sb\<^sub>t \<S>)) \<subseteq> 
      read_only (share ?take_sb \<S>)".
    ultimately
    show ?thesis
      by (simp add: t del: o_apply)
  qed
qed
*)

(*
lemma read_only_takeWhile_dropWhile_share_all_until_volatile_write:
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>)"
  shows "read_only (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) 
           (share_all_until_volatile_write ts \<S>))
          \<subseteq> read_only (share sb \<S>)"
proof -
  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from read_only_takeWhile_share_all_until_volatile_write [OF i_bound ts_i]
  have "read_only (share_all_until_volatile_write ts \<S>)
        \<subseteq> read_only (share ?take_sb \<S>)".
  from share_read_only_mono [OF this]
  have "read_only (share ?drop_sb (share_all_until_volatile_write ts \<S>)) \<subseteq> 
        read_only (share ?drop_sb (share ?take_sb \<S>))".
  with share_append [of ?take_sb ?drop_sb \<S>]
  show ?thesis
    by simp
qed
*)


(* FIXME: unused ? *)
lemma (in computation) concurrent_step_append:
  assumes step: "(ts,m,\<S>) \<Rightarrow> (ts',m',\<S>')"
  shows "(xs@ts,m,\<S>) \<Rightarrow> (xs@ts',m',\<S>')"
using step
proof (cases)
  case (Program i p "is" \<theta> sb \<D> \<O> \<R> p' is'   )
  then obtain
    i_bound: "i < length ts" and
    ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
    prog_step:   "\<theta>\<turnstile>p \<rightarrow>\<^sub>p (p',is')" and
    ts': "ts'=ts[i:=(p',is@is',\<theta>,record p p' is' sb,\<D>,\<O>,\<R>)]" and
    \<S>': "\<S>'=\<S>" and
    m': "m'=m"
    by auto
  
  from i_bound have i_bound': "i + length xs < length (xs@ts)"
    by auto

  from ts_i i_bound have ts_i': "(xs@ts)!(i + length xs) = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (auto simp add: nth_append)
	
  from concurrent_step.Program [OF i_bound' ts_i' prog_step, of m \<S> ] ts' i_bound
  show ?thesis    
    by (auto simp add: ts' list_update_append \<S>' m')
next
  case (Memop i p "is" \<theta> sb  \<D> \<O> \<R> is' \<theta>' sb' \<D>' \<O>' \<R>' )
  then obtain
    i_bound: "i < length ts" and
    ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
    memop_step: "(is,\<theta>,sb,m,\<D>,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>m (is',\<theta>',sb',m',\<D>',\<O>',\<R>',\<S>')" and
    ts': "ts'=ts[i:=(p,is',\<theta>',sb',\<D>',\<O>',\<R>')]"
    by auto

  from i_bound have i_bound': "i + length xs < length (xs@ts)"
    by auto

  from ts_i i_bound have ts_i': "(xs@ts)!(i + length xs) = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (auto simp add: nth_append)
  
  from concurrent_step.Memop [OF i_bound' ts_i' memop_step] ts' i_bound
  show ?thesis
    by (auto simp add: ts' list_update_append)
next
  case (StoreBuffer i p "is" \<theta> sb \<D> \<O> \<R> sb' \<O>' \<R>')
  then obtain
    i_bound: "i < length ts" and
    ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)" and
    sb_step: "(m,sb,\<O>,\<R>,\<S>) \<rightarrow>\<^sub>s\<^sub>b (m',sb',\<O>',\<R>',\<S>')" and
    ts': "ts'=ts[i:=(p,is,\<theta>,sb',\<D>,\<O>',\<R>')]"
    by auto
  from i_bound have i_bound': "i + length xs < length (xs@ts)"
    by auto

  from ts_i i_bound have ts_i': "(xs@ts)!(i + length xs) = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (auto simp add: nth_append)
  
  from concurrent_step.StoreBuffer [OF i_bound' ts_i' sb_step] ts' i_bound
  show ?thesis
    by (auto simp add: ts' list_update_append)
qed

primrec weak_sharing_consistent:: "owns \<Rightarrow> 'a memref list \<Rightarrow>  bool"
where
"weak_sharing_consistent \<O> [] = True"
| "weak_sharing_consistent \<O> (r#rs) =
   (case r of
     Write\<^sub>s\<^sub>b volatile _ _ _ A L R W \<Rightarrow> 
      (if volatile then L \<subseteq> A \<and> A \<inter> R = {} \<and> R \<subseteq> \<O> \<and> 
                       weak_sharing_consistent (\<O> \<union> A - R) rs
      else weak_sharing_consistent \<O> rs)  
   | Ghost\<^sub>s\<^sub>b A L R W \<Rightarrow> L \<subseteq> A \<and> A \<inter> R = {} \<and> R \<subseteq> \<O> \<and> weak_sharing_consistent (\<O> \<union> A - R) rs
   | _ \<Rightarrow> weak_sharing_consistent \<O> rs)"

lemma sharing_consistent_weak_sharing_consistent:
  "\<And>\<S> \<O>. sharing_consistent \<S> \<O> sb \<Longrightarrow> weak_sharing_consistent \<O> sb"
apply (induct sb)
apply (auto split: memref.splits)
done

lemma weak_sharing_consistent_append: 
"\<And>\<O>. weak_sharing_consistent \<O> (xs @ ys) =
  (weak_sharing_consistent \<O> xs \<and> weak_sharing_consistent (acquired True xs \<O>) ys)"
apply (induct xs)
apply (auto split: memref.splits)
done

lemma read_only_share_unowned: "\<And>\<O> \<S>.
  \<lbrakk>weak_sharing_consistent \<O> sb; a \<notin> \<O> \<union> all_acquired sb; a \<in> read_only (share sb \<S>)\<rbrakk> 
  \<Longrightarrow> a \<in> read_only \<S>"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True
      from Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True in_read_only_restrict_conv in_read_only_augment_conv
	split: if_split_asm)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)       
    with Cons.hyps [where \<S>="(\<S> \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A\<^esub> L)" and \<O>="(\<O> \<union> A - R)"] Cons.prems show ?thesis 
      by (auto simp add: in_read_only_restrict_conv in_read_only_augment_conv split: if_split_asm)
  qed
qed


(*
lemma read_only_share_not_acquired_takeWhile: "\<And>\<S>. 
  read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>) \<subseteq> 
  - all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
apply (induct sb)
apply simp
apply (case_tac a)
apply (auto dest: read_only_share_takeWhile_in simp add: in_read_only_restrict_conv)
done

*)
(*
lemma read_only_share_all_until_volatile_Write\<^sub>s\<^sub>b_not_acquired_takeWhile: 
"\<And>\<S>. read_only (share_all_until_volatile_write ts \<S> ) \<subseteq> 
               (- \<Union>(\<lambda>(_, _, _, sb, _, _).
                   all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  
  obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t 
    where t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t)"
    by (cases t)

  let "?take" = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"

  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto


  from read_only_share_all_until_volatile_write
  have "read_only (share_all_until_volatile_write ts (share ?take \<S>)) \<subseteq>
        read_only (share ?take \<S>)".
  also
  from read_only_share_not_acquired_takeWhile 
  have "read_only (share ?take \<S>) \<subseteq> - all_acquired ?take"
    by blast
  finally have "read_only (share_all_until_volatile_write ts (share ?take \<S>)) \<subseteq> - all_acquired ?take".

  moreover

  from Cons.hyps [of "share ?take \<S>"]
  have hyp: "read_only (share_all_until_volatile_write ts (share ?take \<S>)) \<subseteq> 
              (- \<Union>(\<lambda>(_, _, _, sb, _, _).
                   all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts)".

  ultimately
  show ?case
    by (force simp add: t aargh)
qed
*)

(*
lemma read_only_share_all_until_volatile_Write\<^sub>s\<^sub>b_not_acquired_takeWhile_in:
assumes a_in: "a \<in> read_only (share_all_until_volatile_write ts \<S> )"
assumes i_bound: "i < length ts"
assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>)"
shows "a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof -
  from nth_mem [OF i_bound] ts_i read_only_share_all_until_volatile_Write\<^sub>s\<^sub>b_not_acquired_takeWhile [of ts \<S>] a_in
  show ?thesis
    by fastforce
qed
*)

lemma share_read_only_mono_in: 
  assumes a_in: "a \<in> read_only (share sb \<S>)"
  assumes ss: "read_only \<S> \<subseteq> read_only \<S>'"
  shows "a \<in> read_only (share sb \<S>')"
using share_read_only_mono [OF ss] a_in
by auto


lemma read_only_unacquired_share:
  "\<And>S \<O>. \<lbrakk>\<O> \<inter> read_only S = {}; weak_sharing_consistent \<O> sb; a \<in> read_only S; 
  a \<notin> all_acquired sb \<rbrakk>
\<Longrightarrow> a \<in> read_only (share sb S)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      obtain a_ro: "a \<in> read_only S" and a_A: "a \<notin> A" and a_unacq: "a \<notin> all_acquired sb" and 
	owns_ro: "\<O> \<inter> read_only S = {}" and 
	L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	by (auto simp add: in_read_only_convs)

      from a_ro a_A owns_ro R_owns L_A have a_ro': "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF owns_ro' consis' a_ro' a_unacq]
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      with Cons show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by (clarsimp)
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by (clarsimp)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    obtain a_ro: "a \<in> read_only S" and a_A: "a \<notin> A" and a_unacq: "a \<notin> all_acquired sb" and 
      owns_ro: "\<O> \<inter> read_only S = {}" and 
      L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)

    from a_ro a_A owns_ro R_owns L_A have a_ro': "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
      by (auto simp add: in_read_only_convs)
    from Cons.hyps [OF owns_ro' consis' a_ro' a_unacq]
    show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed



lemma read_only_share_unacquired: "\<And> \<O> S. \<O> \<inter> read_only S = {} \<Longrightarrow> weak_sharing_consistent \<O> sb \<Longrightarrow> 
 a \<in> read_only (share sb S) \<Longrightarrow> a \<notin> acquired True sb \<O>"
proof (induct sb)
  case Nil thus ?case by auto
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    next
      case True 
      note volatile=this
      from Cons.prems
      obtain a_ro: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
	owns_ro: "\<O> \<inter> read_only S = {}" and 
	L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
        by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF owns_ro' consis' a_ro]
      show ?thesis
        by (auto simp add: Write\<^sub>s\<^sub>b volatile) 
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    obtain a_ro: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      owns_ro: "\<O> \<inter> read_only S = {}" and 
      L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)
    from Cons.hyps [OF owns_ro' consis' a_ro]
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b) 
  qed
qed


lemma read_only_share_all_acquired_in: 
  "\<And>S \<O>. \<lbrakk>\<O> \<inter> read_only S = {}; weak_sharing_consistent \<O> sb; a \<in> read_only (share sb S)\<rbrakk> 
  \<Longrightarrow> a \<in> read_only (share sb Map.empty) \<or> (a \<in> read_only S \<and> a \<notin> all_acquired sb)"
proof (induct sb)
    case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems
      obtain a_in: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
	owns_ro: "\<O> \<inter> read_only S = {}" and 
	L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
	consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	by (auto simp add: in_read_only_convs)

      from Cons.hyps [OF owns_ro' consis' a_in]
      have hyp: "a \<in> read_only (share sb Map.empty) \<or> a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_acquired sb".

      have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<or> (a \<in> read_only S \<and> a \<notin> A \<and> a \<notin> all_acquired sb)"
      proof -
	{
	  assume a_emp: "a \<in> read_only (share sb Map.empty)"
	  have "read_only Map.empty \<subseteq> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs)
	  
	  from share_read_only_mono_in [OF a_emp this]
	  have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	}
	moreover
	{
	  assume a_ro: "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unacq: "a \<notin> all_acquired sb"
	  have ?thesis
	  proof (cases "a \<in> read_only S")
	    case True
	    with a_ro obtain "a \<notin> A"
	      by (auto simp add: in_read_only_convs)
	    with True a_unacq show ?thesis
	      by auto
	  next
	    case False
	    with a_ro have a_ro_empty: "a \<in> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add: in_read_only_convs split: if_split_asm)
	    
	    have "read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	      by (auto simp add: in_read_only_convs)
	    with owns_ro'
	    have owns_ro_empty: "(\<O> \<union> A - R) \<inter> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	      by blast


	    from read_only_unacquired_share [OF owns_ro_empty consis' a_ro_empty a_unacq]
	    have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	    thus ?thesis
	      by simp
	  qed
	}
	moreover note hyp
	ultimately show ?thesis by blast
      qed

      then show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems
    obtain a_in: "a \<in> read_only (share sb (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
      owns_ro: "\<O> \<inter> read_only S = {}" and 
      L_A: "L \<subseteq> A" and A_R:  "A \<inter> R = {}" and R_owns: "R \<subseteq> \<O>" and
      consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    
    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)

    from Cons.hyps [OF owns_ro' consis' a_in]
    have hyp: "a \<in> read_only (share sb Map.empty) \<or> a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<and> a \<notin> all_acquired sb".

    have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<or> (a \<in> read_only S \<and> a \<notin> A \<and> a \<notin> all_acquired sb)"
    proof -
      {
	assume a_emp: "a \<in> read_only (share sb Map.empty)"
	have "read_only Map.empty \<subseteq> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	  by (auto simp add: in_read_only_convs)
	  
	from share_read_only_mono_in [OF a_emp this]
	have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
      }
      moreover
      {
	assume a_ro: "a \<in> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unacq: "a \<notin> all_acquired sb"
	have ?thesis
        proof (cases "a \<in> read_only S")
	  case True
	  with a_ro obtain "a \<notin> A"
	    by (auto simp add: in_read_only_convs)
	  with True a_unacq show ?thesis
	    by auto
	next
	  case False
	  with a_ro have a_ro_empty: "a \<in> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs split: if_split_asm)
	    
	  have "read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<subseteq> read_only (S \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	    by (auto simp add: in_read_only_convs)
	  with owns_ro'
	  have owns_ro_empty: "(\<O> \<union> A - R) \<inter> read_only (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	    by blast


	  from read_only_unacquired_share [OF owns_ro_empty consis' a_ro_empty a_unacq]
	  have "a \<in> read_only (share sb (Map.empty \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))".
	  thus ?thesis
	    by simp
	qed
      }
      moreover note hyp
      ultimately show ?thesis by blast
    qed 
    then show ?thesis
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed




lemma weak_sharing_consistent_preserves_distinct:
  "\<And>\<O> \<S>. weak_sharing_consistent \<O> sb \<Longrightarrow> \<O> \<inter> read_only \<S> = {} \<Longrightarrow>
           acquired True sb \<O> \<inter> read_only (share sb \<S>) = {}"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain
	owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
	by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF consis' owns_ro']
      show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b True)
    next
      case False with Cons Write\<^sub>s\<^sub>b show ?thesis by auto
    qed
  next
    case Read\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain
      owns_ro: "\<O> \<inter> read_only \<S> = {}" and L_A: " L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and consis': "weak_sharing_consistent (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from owns_ro A_R R_owns have owns_ro': "(\<O> \<union> A - R) \<inter> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) = {}"
      by (auto simp add: in_read_only_convs)
    from Cons.hyps [OF consis' owns_ro']
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed


locale weak_sharing_consis =
fixes ts::"('p,'p store_buffer,bool,owns,rels) thread_config list"
assumes weak_sharing_consis:
  "\<And>i p is \<O> \<R> \<D> \<theta> sb. 
   \<lbrakk>i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>) \<rbrakk> 
   \<Longrightarrow>
   weak_sharing_consistent \<O> sb"

sublocale sharing_consis \<subseteq> weak_sharing_consis
proof
  fix i p "is" \<O> \<R> \<D> \<theta> sb
  assume i_bound: "i < length ts" 
  assume ts_i: "ts ! i = (p, is, \<theta>, sb, \<D>, \<O>,\<R>)"
  from sharing_consistent_weak_sharing_consistent [OF sharing_consis [OF i_bound ts_i]]
  show "weak_sharing_consistent \<O> sb".
qed

    
lemma weak_sharing_consis_tl: "weak_sharing_consis (t#ts) \<Longrightarrow> weak_sharing_consis ts"
apply (unfold weak_sharing_consis_def)
apply force
done


lemma read_only_share_all_until_volatile_write_unacquired:
  "\<And>\<S>. \<lbrakk>ownership_distinct ts; read_only_unowned \<S> ts; weak_sharing_consis ts; 
  \<forall>i < length ts. (let (_,_,_,sb,_,\<O>,\<R>) = ts!i in 
     a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)); 
  a \<in> read_only \<S>\<rbrakk> 
  \<Longrightarrow> a \<in> read_only (share_all_until_volatile_write ts \<S>)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where
    t: "t = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto

  have a_ro: "a \<in> read_only \<S>" by fact
  have ro_unowned: "read_only_unowned \<S> (t#ts)" by fact
  then interpret read_only_unowned \<S> "t#ts" .
  have consis: "weak_sharing_consis (t#ts)" by fact
  then interpret weak_sharing_consis "t#ts" .

  note consis' = weak_sharing_consis_tl [OF consis]

  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from weak_sharing_consis [of 0] t
  have consis_sb: "weak_sharing_consistent \<O> sb"
    by force
  with weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
  have consis_take: "weak_sharing_consistent \<O> ?take_sb"
    by auto


  have ro_unowned': "read_only_unowned (share ?take_sb \<S>) ts"
  proof 
    fix j
    fix p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
    assume j_bound: "j < length ts"
    assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
    show "\<O>\<^sub>j \<inter> read_only (share ?take_sb \<S>) = {}"
    proof -
      {
        fix a
        assume a_owns: "a \<in> \<O>\<^sub>j" 
        assume a_ro: "a \<in> read_only (share ?take_sb \<S>)"
        have False
        proof -
          from ownership_distinct [of 0 "Suc j"] j_bound jth t
          have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
            by fastforce
    
          from read_only_unowned [of "Suc j"] j_bound jth
          have dist_ro: "\<O>\<^sub>j \<inter> read_only \<S> = {}" by force
          show ?thesis
          proof (cases "a \<in> (\<O> \<union> all_acquired sb)")
            case True
            with dist a_owns show False by auto
          next
            case False
            hence "a \<notin>  (\<O> \<union> all_acquired ?take_sb)"
            using all_acquired_append [of ?take_sb ?drop_sb]
              by auto
            from read_only_share_unowned [OF consis_take this a_ro]
            have "a \<in> read_only \<S>".
            with dist_ro a_owns show False by auto
         qed
       qed
      }
      thus ?thesis by auto
    qed
  qed

      
  from Cons.prems
  obtain unacq_ts: "\<forall>i < length ts. (let (_,_,_,sb,_,\<O>,_) = ts!i in 
           a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb))" and
    unacq_sb: "a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
    by (force simp add: t aargh)


  
  from read_only_unowned [of 0] t
  have owns_ro: "\<O> \<inter> read_only \<S> = {}"
    by force
  from read_only_unacquired_share [OF owns_ro consis_take a_ro unacq_sb]
  have "a \<in> read_only (share (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<S>)".
  from Cons.hyps [OF dist' ro_unowned' consis' unacq_ts this]
  show ?case
    by (simp add: t)
qed

lemma read_only_share_unowned_in: 
"\<lbrakk>weak_sharing_consistent \<O> sb; a \<in> read_only (share sb \<S>)\<rbrakk>
\<Longrightarrow> a \<in> read_only \<S> \<union> \<O> \<union> all_acquired sb" 
using read_only_share_unowned [of \<O> sb]
by auto


lemma read_only_shared_all_until_volatile_write_subset:
"\<And>\<S>. \<lbrakk>ownership_distinct ts;  
           weak_sharing_consis ts\<rbrakk> \<Longrightarrow>
read_only (share_all_until_volatile_write ts \<S>) \<subseteq> 
  read_only \<S> \<union> (\<Union>((\<lambda>(_, _, _, sb, _, \<O>,_). \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  obtain p "is" \<O> \<R> \<D> \<theta> sb where
    t: "t = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
    by (cases t)

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".


  have consis: "weak_sharing_consis (t#ts)" by fact
  then interpret weak_sharing_consis "t#ts" .

  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto

  note consis' = weak_sharing_consis_tl [OF consis]

  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from weak_sharing_consis [of 0] t
  have consis_sb: "weak_sharing_consistent \<O> sb"
    by force
  with weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
  have consis_take: "weak_sharing_consistent \<O> ?take_sb"
    by auto

  {
    fix a
    assume a_in: "a \<in> read_only
              (share_all_until_volatile_write ts
                 (share ?take_sb \<S>))" and
    a_notin_shared: "a \<notin> read_only \<S>" and
    a_notin_rest: "a \<notin> (\<Union>((\<lambda>(_, _, _, sb, _, \<O>,_). \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
    have "a \<in> \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
    proof -
      from Cons.hyps [OF dist' consis', of "(share ?take_sb \<S>)"] a_in a_notin_rest
      have "a \<in> read_only (share ?take_sb \<S>)"
        by (auto simp add: aargh)
      from read_only_share_unowned_in [OF consis_take this] a_notin_shared
      show ?thesis by auto
    qed
  }
      
  then show ?case
    by (auto simp add: t aargh)
qed
(*
lemma weak_sharing_consistent_preserves_distinct_share_all_until_volatile_write:
  assumes dist: "ownership_distinct ts" 
  assumes ro: "read_only_unowned \<S> ts"  
  assumes consis: "weak_sharing_consis ts" 
  assumes i_bound: "i < length ts" 
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  shows "acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<inter> 
     read_only (share_all_until_volatile_write ts \<S>) = {}"
proof -
  {
    fix a
    assume a_in: "a \<in> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>"
    assume a_in_share: "a \<in>  read_only (share_all_until_volatile_write ts \<S>)"
    have False
    proof -
      from read_only_shared_all_until_volatile_write_subset [OF dist consis, of \<S>] a_in_share
      have "a \<in> read_only \<S> \<union> 
                  (\<Union>(\<lambda>(_, _, _, sb, _, \<O>,_). \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts)"
        by fastforce
      moreover
      from acquired_all_acquired [of True "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" \<O>] a_in
      have "a \<in> \<O> \<union> 
      find_theorems acquired all_acquired
      from a_in 
*)
lemma weak_sharing_consistent_preserves_distinct_share_all_until_volatile_write:
  "\<And>\<S> i. \<lbrakk>ownership_distinct ts; read_only_unowned \<S> ts;weak_sharing_consis ts; 
 i < length ts; ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)\<rbrakk>
 \<Longrightarrow> acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<inter> 
  read_only (share_all_until_volatile_write ts \<S>) = {}"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts)
  note \<open>read_only_unowned \<S> (t#ts)\<close>
  then interpret read_only_unowned \<S> "t#ts" .
  note i_bound = \<open>i < length (t # ts)\<close>
  note ith = \<open>(t # ts) ! i = (p,is,\<theta>, sb, \<D>, \<O>,\<R>)\<close>

  have dist: "ownership_distinct (t#ts)" by fact
  then interpret ownership_distinct "t#ts" .
  from ownership_distinct_tl [OF dist]
  have dist': "ownership_distinct ts".


  have consis: "weak_sharing_consis (t#ts)" by fact
  then interpret weak_sharing_consis "t#ts" .

  note consis' = weak_sharing_consis_tl [OF consis]

  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"


  have aargh: "(Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) = (\<lambda>a. \<not> is_volatile_Write\<^sub>s\<^sub>b a)"
    by (rule ext) auto
  show ?case
  proof (cases i)
    case 0
    from read_only_unowned [of 0] ith 0
    have owns_ro: "\<O> \<inter> read_only \<S> = {}"
      by force
    from weak_sharing_consis [of 0] ith 0
    have "weak_sharing_consistent \<O> sb"
      by force
    with weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
    have consis_take: "weak_sharing_consistent \<O> ?take_sb"
      by auto
    from weak_sharing_consistent_preserves_distinct [OF this owns_ro]
    have dist_t: "acquired True ?take_sb \<O> \<inter> read_only (share ?take_sb \<S>) = {}".
    from read_only_shared_all_until_volatile_write_subset [OF dist' consis', of "(share ?take_sb \<S>)"]
    have ro_rest: "read_only (share_all_until_volatile_write ts (share ?take_sb \<S>)) \<subseteq> 
            read_only (share ?take_sb \<S>) \<union> 
            (\<Union>((\<lambda>(_, _, _, sb, _, \<O>,_). \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
      by auto
    {
      fix a
      assume a_in_sb: "a \<in> acquired True ?take_sb \<O>"
      assume a_in_ro: "a \<in> read_only (share_all_until_volatile_write ts (share ?take_sb \<S>))"
      have False
      proof -
        
        from Set.in_mono [rule_format, OF ro_rest a_in_ro] dist_t a_in_sb
        
        have "a \<in> (\<Union>((\<lambda>(_, _, _, sb, _, \<O>,_). \<O> \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)) ` set ts))"
          by auto
        then obtain j p\<^sub>j "is\<^sub>j" \<theta>\<^sub>j sb\<^sub>j \<D>\<^sub>j \<O>\<^sub>j \<R>\<^sub>j
            where j_bound: "j < length ts" and ts_j: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
            and a_in_j: "a \<in> \<O>\<^sub>j \<union> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"
          by (fastforce simp add: in_set_conv_nth)
        from ownership_distinct [of 0 "Suc j"] ith ts_j j_bound 0
        have dist: "(\<O> \<union> all_acquired sb) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
          by fastforce
        moreover
        from acquired_all_acquired [of True ?take_sb \<O>] a_in_sb all_acquired_append [of ?take_sb ?drop_sb]
        have "a \<in> \<O> \<union> all_acquired sb"
          by auto
        with a_in_j all_acquired_append [of "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)" "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j)"] 
          dist
        have False by fastforce
        thus ?thesis ..
     qed
   }
   then show ?thesis
   using 0 ith
     by (auto simp add: aargh)
  next
    case (Suc k)
    from i_bound Suc have k_bound: "k < length ts"
      by auto
    from ith Suc have kth: "ts!k = (p, is, \<theta>, sb, \<D>, \<O>, \<R>)"
      by auto

    obtain p\<^sub>t "is\<^sub>t" \<O>\<^sub>t \<R>\<^sub>t \<D>\<^sub>t \<theta>\<^sub>t sb\<^sub>t 
      where t: "t=(p\<^sub>t,is\<^sub>t,\<theta>\<^sub>t,sb\<^sub>t,\<D>\<^sub>t,\<O>\<^sub>t,\<R>\<^sub>t)"
      by (cases t)

    let ?take_sb\<^sub>t = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"
    let ?drop_sb\<^sub>t = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>t)"

    have ro_unowned': "read_only_unowned (share ?take_sb\<^sub>t \<S>) ts"
    proof 
      fix j
      fix p\<^sub>j is\<^sub>j \<O>\<^sub>j \<R>\<^sub>j \<D>\<^sub>j \<theta>\<^sub>j sb\<^sub>j
      assume j_bound: "j < length ts"
      assume jth: "ts!j = (p\<^sub>j,is\<^sub>j,\<theta>\<^sub>j,sb\<^sub>j,\<D>\<^sub>j,\<O>\<^sub>j,\<R>\<^sub>j)"
      show "\<O>\<^sub>j \<inter> read_only (share ?take_sb\<^sub>t \<S>) = {}"
      proof -
	from read_only_unowned [of "Suc j"] j_bound jth
	have dist: "\<O>\<^sub>j \<inter> read_only \<S> = {}" by force
        
        from weak_sharing_consis [of 0] t
        have "weak_sharing_consistent \<O>\<^sub>t sb\<^sub>t" 
          by fastforce
        with weak_sharing_consistent_append [of \<O>\<^sub>t ?take_sb\<^sub>t ?drop_sb\<^sub>t]
        have consis_t: "weak_sharing_consistent \<O>\<^sub>t ?take_sb\<^sub>t" 
          by auto
        {
          fix a
          assume a_in_j: "a \<in> \<O>\<^sub>j"
          assume a_ro: "a \<in> read_only (share ?take_sb\<^sub>t \<S>)"
          have False
          proof -
            from a_in_j ownership_distinct [of 0 "Suc j"] j_bound t jth
            have "(\<O>\<^sub>t \<union> all_acquired sb\<^sub>t) \<inter> (\<O>\<^sub>j \<union> all_acquired sb\<^sub>j) = {}"
              by fastforce
            with a_in_j all_acquired_append [of ?take_sb\<^sub>t ?drop_sb\<^sub>t]
            have "a \<notin> (\<O>\<^sub>t \<union> all_acquired ?take_sb\<^sub>t)"
              by fastforce
            from  read_only_share_unowned [OF consis_t this a_ro]
            have "a \<in> read_only \<S>" .
            with a_in_j dist 
            show False by auto
          qed
        }
        then
	show ?thesis
	  by auto
      qed
    qed

    from Cons.hyps [OF dist' ro_unowned' consis' k_bound kth]
    show ?thesis
      by (simp add: t)
  qed
qed


lemma in_read_only_share_all_until_volatile_write:
  assumes dist: "ownership_distinct ts"
  assumes consis: "sharing_consis \<S> ts"
  assumes ro_unowned: "read_only_unowned \<S> ts"
  assumes i_bound: "i < length ts"
  assumes ts_i: "ts!i = (p,is,\<theta>,sb,\<D>,\<O>,\<R>)"
  assumes a_unacquired_others: "\<forall>j < length ts. i\<noteq>j \<longrightarrow> 
            (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j in
            a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
  assumes a_ro_share: "a \<in> read_only (share sb \<S>)"
  shows "a \<in> read_only (share (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) 
                    (share_all_until_volatile_write ts \<S>))"
proof -
  from consis
  interpret sharing_consis \<S> ts .
  interpret read_only_unowned \<S> ts by fact

  from sharing_consis [OF i_bound ts_i]
  have consis_sb: "sharing_consistent \<S> \<O> sb".
  from sharing_consistent_weak_sharing_consistent [OF this] 
  have weak_consis: "weak_sharing_consistent \<O> sb".
  from read_only_unowned [OF i_bound ts_i]
  have owns_ro: "\<O> \<inter> read_only \<S> = {}".
  from read_only_share_all_acquired_in [OF owns_ro weak_consis a_ro_share]
  have "a \<in> read_only (share sb Map.empty) \<or> a \<in> read_only \<S> \<and> a \<notin> all_acquired sb".
  moreover
  
  let ?take_sb = "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
  let ?drop_sb = "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"

  from weak_consis weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
  obtain weak_consis': "weak_sharing_consistent (acquired True ?take_sb \<O>) ?drop_sb" and
    weak_consis_take: "weak_sharing_consistent \<O> ?take_sb" 
    by auto
  
  {
    assume "a \<in> read_only (share sb Map.empty)"
    with share_append [of ?take_sb ?drop_sb]
    have a_in': "a \<in> read_only (share ?drop_sb (share ?take_sb Map.empty))"
      by auto

    have owns_empty: "\<O> \<inter> read_only Map.empty = {}"
      by auto

    from weak_sharing_consistent_preserves_distinct [OF weak_consis_take owns_empty]
    have "acquired True ?take_sb \<O> \<inter> read_only (share ?take_sb Map.empty) = {}".

    from read_only_share_all_acquired_in [OF this weak_consis' a_in']
    have "a \<in> read_only (share ?drop_sb Map.empty) \<or> a \<in> read_only (share ?take_sb Map.empty) \<and> a \<notin> all_acquired ?drop_sb".
    moreover
    {
      assume a_ro_drop: "a \<in> read_only (share ?drop_sb Map.empty)"
      have "read_only Map.empty \<subseteq> read_only (share_all_until_volatile_write ts \<S>)"
	by auto
      from share_read_only_mono_in [OF a_ro_drop this]
      have ?thesis .
    }
    moreover
    {
      assume a_ro_take: "a \<in> read_only (share ?take_sb Map.empty)" 
      assume a_unacq_drop: "a \<notin> all_acquired ?drop_sb"
      from read_only_share_unowned_in [OF weak_consis_take a_ro_take] 
      have "a \<in> \<O> \<union> all_acquired ?take_sb" by auto
      hence "a \<in> \<O> \<union> all_acquired sb" using all_acquired_append [of ?take_sb ?drop_sb]
        by auto
      from  share_all_until_volatile_write_thread_local' [OF dist consis i_bound ts_i this] a_ro_share
      have ?thesis by (auto simp add: read_only_def)
    }
    ultimately have ?thesis by blast
  }

  moreover

  {
    assume a_ro: "a \<in> read_only \<S>" 
    assume a_unacq: "a \<notin> all_acquired sb"
    with all_acquired_append [of ?take_sb ?drop_sb]
    obtain "a \<notin> all_acquired ?take_sb" and a_notin_drop: "a \<notin> all_acquired ?drop_sb"
      by auto
    with a_unacquired_others i_bound ts_i
    have a_unacq: "\<forall>j < length ts. 
            (let (_,_,_,sb\<^sub>j,_,_,_) = ts!j in
            a \<notin> all_acquired (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb\<^sub>j))"
      by (auto simp add: Let_def)
    
    from local.weak_sharing_consis_axioms have "weak_sharing_consis ts" .
    from read_only_share_all_until_volatile_write_unacquired [OF dist ro_unowned 
      \<open>weak_sharing_consis ts\<close> a_unacq a_ro]
    have a_ro_all: "a \<in> read_only (share_all_until_volatile_write ts \<S>)" .

    from weak_consis weak_sharing_consistent_append [of \<O> ?take_sb ?drop_sb]
    have weak_consis_drop: "weak_sharing_consistent (acquired True ?take_sb \<O>) ?drop_sb"
      by auto

    from weak_sharing_consistent_preserves_distinct_share_all_until_volatile_write [OF dist 
      ro_unowned \<open>weak_sharing_consis ts\<close> i_bound ts_i]
    have "acquired True ?take_sb \<O> \<inter>
       read_only (share_all_until_volatile_write ts \<S>) = {}".

    from read_only_unacquired_share [OF this weak_consis_drop a_ro_all a_notin_drop]
    have ?thesis .
  }
  ultimately show ?thesis by blast
qed

lemma all_acquired_dropWhile_in: "x \<in> all_acquired (dropWhile P sb) \<Longrightarrow> x \<in> all_acquired sb"	
  using all_acquired_append [of "takeWhile P sb" "dropWhile P sb"]
  by auto


lemma all_acquired_takeWhile_in: "x \<in> all_acquired (takeWhile P sb) \<Longrightarrow> x \<in> all_acquired sb"	
  using all_acquired_append [of "takeWhile P sb" "dropWhile P sb"]
  by auto

lemmas all_acquired_takeWhile_dropWhile_in = all_acquired_takeWhile_in all_acquired_dropWhile_in



lemma split_in_read_only_reads: 
  "\<And>\<O>. a \<in> read_only_reads \<O> xs \<Longrightarrow> 
  (\<exists>t v ys zs. xs=ys @ Read\<^sub>s\<^sub>b False a t v # zs \<and> a \<notin> acquired True ys \<O>)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have a_in: "a \<in> read_only_reads \<O> (x#xs)" by fact
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case False
      from a_in have "a \<in> read_only_reads \<O> xs"
	by (auto simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF this] obtain t v ys zs where
	xs: "xs=ys@Read\<^sub>s\<^sub>b False a t v # zs" and a_notin: "a \<notin> acquired True ys \<O>"
	by auto
      with xs a_notin obtain "x#xs=(x#ys)@Read\<^sub>s\<^sub>b False a t v # zs" "a \<notin> acquired True (x#ys) \<O>"
	by (simp add: Write\<^sub>s\<^sub>b False)
      then show ?thesis
	by blast
    next
      case True
      from a_in have "a \<in> read_only_reads (\<O> \<union> A - R) xs"
	by (auto simp add: Write\<^sub>s\<^sub>b True)
      from Cons.hyps [OF this] obtain t v ys zs where
	xs: "xs=ys@Read\<^sub>s\<^sub>b False a t v # zs" and a_notin: "a \<notin> acquired True ys (\<O> \<union> A - R)"
	by auto
      with xs a_notin obtain "x#xs=(x#ys)@Read\<^sub>s\<^sub>b False a t v # zs" "a \<notin> acquired True (x#ys) \<O>"
	by (simp add: Write\<^sub>s\<^sub>b True)
      then show ?thesis
	by blast
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t' v')
    show ?thesis
    proof (cases "\<not> volatile \<and> a \<notin> \<O> \<and> a'=a")
      case True
      with Read\<^sub>s\<^sub>b show ?thesis
	by fastforce
    next
      case False
      with a_in have "a \<in> read_only_reads \<O> xs"	
	by (auto simp add: Read\<^sub>s\<^sub>b  split: if_split_asm)
      from Cons.hyps [OF this] obtain t v ys zs where
	xs: "xs=ys@Read\<^sub>s\<^sub>b False a t v # zs" and a_notin: "a \<notin> acquired True ys \<O>"
	by auto
      with xs a_notin obtain "x#xs=(x#ys)@Read\<^sub>s\<^sub>b False a t v # zs" "a \<notin> acquired True (x#ys) \<O>"
	by (simp add: Read\<^sub>s\<^sub>b)
      then show ?thesis
	by blast
    qed
  next
    case Prog\<^sub>s\<^sub>b
    with a_in have "a \<in> read_only_reads \<O> xs"	
      by (auto)
    from Cons.hyps [OF this] obtain t v ys zs where
      xs: "xs=ys@Read\<^sub>s\<^sub>b False a t v # zs" and a_notin: "a \<notin> acquired True ys \<O>"
      by auto
    with xs a_notin obtain "x#xs=(x#ys)@Read\<^sub>s\<^sub>b False a t v # zs" "a \<notin> acquired True (x#ys) \<O>"
      by (simp add: Prog\<^sub>s\<^sub>b)
    then show ?thesis
      by blast
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    with a_in have "a \<in> read_only_reads (\<O> \<union> A - R) xs"	
      by (auto)
    from Cons.hyps [OF this] obtain t v ys zs where
      xs: "xs=ys@Read\<^sub>s\<^sub>b False a t v # zs" and a_notin: "a \<notin> acquired True ys (\<O> \<union> A -R)"
      by auto
    with xs a_notin obtain "x#xs=(x#ys)@Read\<^sub>s\<^sub>b False a t v # zs" "a \<notin> acquired True (x#ys) \<O>"
      by (simp add: Ghost\<^sub>s\<^sub>b)
    then show ?thesis
      by blast
  qed
qed


lemma insert_monoD: "W \<subseteq> W' \<Longrightarrow> insert a W \<subseteq> insert a W'"
  by blast


primrec unforwarded_non_volatile_reads:: "'a memref list \<Rightarrow> addr set \<Rightarrow> addr set"
where
"unforwarded_non_volatile_reads [] W = {}"
| "unforwarded_non_volatile_reads (x#xs) W =
  (case x of
     Read\<^sub>s\<^sub>b volatile a _ _ \<Rightarrow> (if a \<notin> W \<and> \<not> volatile 
                             then insert a (unforwarded_non_volatile_reads xs W) 
                             else  (unforwarded_non_volatile_reads xs W))
  | Write\<^sub>s\<^sub>b _ a _ _ _ _ _ _ \<Rightarrow> unforwarded_non_volatile_reads xs (insert a W)
  | _ \<Rightarrow> unforwarded_non_volatile_reads xs W)"


lemma unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b:
  "\<And>W. unforwarded_non_volatile_reads sb W \<subseteq> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
apply (induct sb)
apply (auto split: memref.splits if_split_asm)
done

lemma in_unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b:
  "a \<in> unforwarded_non_volatile_reads sb W \<Longrightarrow> a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
using unforwarded_non_volatile_reads_non_volatile_Read\<^sub>s\<^sub>b
by blast


lemma unforwarded_non_volatile_reads_antimono:
 "\<And>W W'. W \<subseteq> W' \<Longrightarrow> unforwarded_non_volatile_reads xs W' \<subseteq> unforwarded_non_volatile_reads xs W"
apply (induct xs)
apply (auto split: memref.splits dest: insert_monoD)
done

lemma unforwarded_non_volatile_reads_antimono_in:
 "x \<in> unforwarded_non_volatile_reads xs W' \<Longrightarrow> W \<subseteq> W'
  \<Longrightarrow> x \<in> unforwarded_non_volatile_reads xs W"
  using unforwarded_non_volatile_reads_antimono
  by blast

lemma unforwarded_non_volatile_reads_append: "\<And>W. unforwarded_non_volatile_reads (xs@ys) W =
 (unforwarded_non_volatile_reads xs W \<union> 
  unforwarded_non_volatile_reads ys (W \<union> outstanding_refs is_Write\<^sub>s\<^sub>b xs))"
apply (induct xs)
apply  clarsimp
apply (auto split: memref.splits)
done

lemma reads_consistent_mem_eq_on_unforwarded_non_volatile_reads:
  assumes mem_eq: "\<forall>a \<in> A \<union> W. m' a = m a"
  assumes subset: "unforwarded_non_volatile_reads sb W \<subseteq> A"
  assumes consis_m: "reads_consistent pending_write \<O> m sb"
  shows "reads_consistent pending_write \<O> m' sb"
using mem_eq subset consis_m 
proof (induct sb arbitrary: A W m' m pending_write \<O>)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  note mem_eq = \<open>\<forall>a \<in> A \<union> W. m' a = m a\<close>
  note subset = \<open>unforwarded_non_volatile_reads (r#sb) W \<subseteq> A\<close>
  note consis_m = \<open>reads_consistent pending_write \<O> m (r#sb)\<close>

  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a sop v A' L R W')
    from subset obtain
      subset': "unforwarded_non_volatile_reads sb (insert a W) \<subseteq> A"
      by (auto simp add: Write\<^sub>s\<^sub>b)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> (A \<union> (insert a W)). (m'(a:=v)) a' = (m(a:=v)) a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case True
      from consis_m obtain
	consis': "reads_consistent True (\<O> \<union> A' - R) (m(a := v)) sb" and
        no_volatile_Read\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}" 
	by (simp add: Write\<^sub>s\<^sub>b True)

      from Cons.hyps [OF mem_eq' subset' consis']
      have "reads_consistent True (\<O> \<union> A' - R) (m'(a := v)) sb".
      with no_volatile_Read\<^sub>s\<^sub>b 
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      from consis_m obtain consis': "reads_consistent pending_write \<O> (m(a := v)) sb" 
	by (simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF mem_eq' subset' consis']
      have "reads_consistent pending_write \<O> (m'(a := v)) sb".
      then
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A \<union> W. m' a' = m a'"
      by (auto)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from consis_m obtain	
	consis': "reads_consistent pending_write \<O> m sb"  
	by (simp add: Read\<^sub>s\<^sub>b True)

      show ?thesis
      proof (cases "a \<in> W")
	case False
	from subset obtain
	  subset': "unforwarded_non_volatile_reads sb W \<subseteq> A"
	  using False
	  by (auto simp add: Read\<^sub>s\<^sub>b True split: if_split_asm)
	from Cons.hyps [OF mem_eq' subset' consis']
	show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b True)
      next
	case True
	from subset have
	  subset': "unforwarded_non_volatile_reads sb W \<subseteq> 
	             insert a A "
	  using True
	  apply (auto simp add: Read\<^sub>s\<^sub>b volatile split: if_split_asm)
	  done
	from mem_eq True have mem_eq': "\<forall>a' \<in> (insert a A) \<union> W. m' a' = m a'"
	  by auto
	from Cons.hyps [OF mem_eq' subset' consis']
	show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b volatile)
      qed
    next
      case False
      note non_vol = this
      from consis_m obtain	
	consis': "reads_consistent pending_write \<O> m sb"  and 
	v: "(pending_write \<or> a \<in> \<O>) \<longrightarrow> v=m a" 
	by (simp add: Read\<^sub>s\<^sub>b False)
      show ?thesis
      proof (cases "a \<in> W")
	case True
	from mem_eq subset Read\<^sub>s\<^sub>b True non_vol have "m' a = m a"
	  by (auto simp add: False)
	from subset obtain
	  subset': "unforwarded_non_volatile_reads sb W \<subseteq> insert a A"
	  using False
	  by (auto simp add: Read\<^sub>s\<^sub>b non_vol split: if_split_asm)
	from mem_eq True have mem_eq': "\<forall>a' \<in> (insert a A) \<union> W. m' a' = m a'"
	  by auto

	with Cons.hyps [OF mem_eq' subset' consis'] v
	show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b non_vol)
      next
	case False
	from mem_eq subset Read\<^sub>s\<^sub>b False non_vol have meq: "m' a = m a"
	  by (clarsimp )
	from subset obtain
	  subset': "unforwarded_non_volatile_reads sb W \<subseteq> A"
	  using non_vol False
	  by (auto simp add: Read\<^sub>s\<^sub>b non_vol split: if_split_asm)
	from mem_eq non_vol have mem_eq': "\<forall>a' \<in> A \<union> W. m' a' = m a'"
	  by auto
	with Cons.hyps [OF mem_eq' subset' consis'] v meq
	show ?thesis
	  by (simp add: Read\<^sub>s\<^sub>b non_vol False)
      qed
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed


lemma reads_consistent_mem_eq_on_unforwarded_non_volatile_reads_drop:
  assumes mem_eq: "\<forall>a \<in> A \<union> W. m' a = m a"
  assumes subset: "unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) W \<subseteq> A"
  assumes subset_acq: "acquired_reads True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<subseteq> A"
  assumes consis_m: "reads_consistent False \<O> m sb"
  shows "reads_consistent False \<O> m' sb"
using mem_eq subset subset_acq consis_m 
proof (induct sb arbitrary: A W m' m \<O>)
  case Nil thus ?case by simp
next
  case (Cons r sb)
  note mem_eq = \<open>\<forall>a \<in> A \<union> W. m' a = m a\<close>
  note subset = \<open>unforwarded_non_volatile_reads 
    (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) (r#sb)) W \<subseteq> A\<close>
  note subset_acq = \<open>acquired_reads True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b)(r#sb)) \<O> \<subseteq> A\<close>
  note consis_m = \<open>reads_consistent False \<O> m (r#sb)\<close>

  show ?case
  proof (cases r)
    case (Write\<^sub>s\<^sub>b volatile a sop v A' L R W')
    show ?thesis
    proof (cases volatile)
      case True
      from mem_eq
      have mem_eq': 
	"\<forall>a' \<in> (A \<union> (insert a W)). (m'(a:=v)) a' = (m(a:=v)) a'"
	by (auto)

      from consis_m obtain
	consis': "reads_consistent True (\<O> \<union> A' - R) (m(a := v)) sb" and
        no_volatile_Read\<^sub>s\<^sub>b: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}" 
	by (simp add: Write\<^sub>s\<^sub>b True)

      from subset obtain "unforwarded_non_volatile_reads sb (insert a W) \<subseteq> A" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from reads_consistent_mem_eq_on_unforwarded_non_volatile_reads [OF mem_eq' this consis']
      have "reads_consistent True (\<O> \<union> A' - R) (m'(a := v)) sb".
      with no_volatile_Read\<^sub>s\<^sub>b 
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b True)
    next
      case False
      from mem_eq
      have mem_eq': 
	"\<forall>a' \<in> (A \<union> W). (m'(a:=v)) a' = (m(a:=v)) a'"
	by (auto)
      from subset obtain
	subset': "unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) W \<subseteq> A"
	by (auto simp add: Write\<^sub>s\<^sub>b False)
      from subset_acq have 
	subset_acq': "acquired_reads True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<subseteq> A"
	by (auto simp add: Write\<^sub>s\<^sub>b False)
	
      from consis_m obtain consis': "reads_consistent False \<O> (m(a := v)) sb" 
	by (simp add: Write\<^sub>s\<^sub>b False)
      from Cons.hyps [OF mem_eq' subset' subset_acq' consis']
      have "reads_consistent False \<O> (m'(a := v)) sb".
      then
      show ?thesis
	by (simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    from mem_eq
    have mem_eq': 
      "\<forall>a' \<in> A \<union> W. m' a' = m a'"
      by (auto)
    from subset obtain
      subset': "unforwarded_non_volatile_reads (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) W \<subseteq> A"
      by (clarsimp simp add: Read\<^sub>s\<^sub>b)
    from subset_acq obtain
      a_A: "\<not> volatile \<longrightarrow> a \<in> \<O> \<longrightarrow> a \<in> A" and
      subset_acq': "acquired_reads True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O> \<subseteq> A"
      by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from consis_m obtain	
	consis': "reads_consistent False \<O> m sb"  
	by (simp add: Read\<^sub>s\<^sub>b True)
      
      from Cons.hyps [OF mem_eq' subset' subset_acq'  consis']
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b True)
    next
      case False
      note non_vol = this
      from consis_m obtain	
	consis': "reads_consistent False \<O> m sb"  and 
	v: "a \<in> \<O> \<longrightarrow> v=m a" 
	by (simp add: Read\<^sub>s\<^sub>b False)

      from mem_eq a_A v have v': "a \<in> \<O> \<longrightarrow> v=m' a"
	by (auto simp add: non_vol)
      from Cons.hyps [OF mem_eq' subset' subset_acq'  consis'] v'
      show ?thesis
	by (simp add: Read\<^sub>s\<^sub>b False)
    qed
  next
    case Prog\<^sub>s\<^sub>b with Cons show ?thesis by auto
  next
    case Ghost\<^sub>s\<^sub>b with Cons show ?thesis by auto
  qed
qed





(* FIXME: unused?*)
lemma read_only_read_witness:"\<And>\<S> \<O>.
  \<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb;
   a \<in> read_only_reads \<O> sb\<rbrakk>
  \<Longrightarrow> 
  \<exists>xs ys t v. sb=xs@ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True

      from Cons.prems obtain 
	a_ro: "a \<in> read_only_reads (\<O> \<union> A - R) sb" and
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from Cons.hyps [OF nvo' a_ro]
      obtain xs ys t v where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<and> 
	a \<notin> read_only_reads (\<O> \<union> A - R) xs"
	by blast
      
      thus ?thesis
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b True)
	done
    next
      case False
      from Cons.prems obtain 
	a_ro: "a \<in> read_only_reads \<O> sb" and
	nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)

      from Cons.hyps [OF nvo' a_ro]
      obtain xs ys t v where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
	by blast
      
      thus ?thesis
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b False)
	done
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    show ?thesis
    proof (cases "a'=a \<and> a \<notin> \<O> \<and> \<not> volatile")
      case True
      with Cons.prems have "a \<in> read_only \<S>"
	by (simp add: Read\<^sub>s\<^sub>b)
      
      with True show ?thesis
	apply -
	apply (rule_tac x="[]" in exI)
	apply (rule_tac x="sb" in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Read\<^sub>s\<^sub>b)
	done
    next
      case False
      with Cons.prems obtain 	
	a_ro: "a \<in> read_only_reads \<O> sb" and
	nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" 
	by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)
      from Cons.hyps [OF nvo' a_ro]
      obtain xs ys t' v' where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t' v' # ys \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
	by blast
      
      with False show ?thesis
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t' in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Read\<^sub>s\<^sub>b )
	done
    qed
  next
    case Prog\<^sub>s\<^sub>b
    from Cons.prems obtain 
      a_ro: "a \<in> read_only_reads \<O> sb" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" 
      by (clarsimp simp add: Prog\<^sub>s\<^sub>b)
    
    from Cons.hyps [OF nvo' a_ro]
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
      by blast
    
    thus ?thesis
      apply -
      apply (rule_tac x="(x#xs)" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Prog\<^sub>s\<^sub>b)
      done
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      a_ro: "a \<in> read_only_reads (\<O> \<union> A - R) sb" and
      nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
    
    from Cons.hyps [OF nvo' a_ro]
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<and> a \<notin> read_only_reads (\<O> \<union> A - R) xs"
      by blast
    
    thus ?thesis
      apply -
      apply (rule_tac x="(x#xs)" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      done
  qed
qed

(* FIXME: unused?*)
lemma read_only_read_acquired_witness: "\<And>\<S> \<O>.
  \<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb; sharing_consistent \<S> \<O> sb;
  a \<notin> read_only \<S>; a \<notin> \<O>; a \<in> read_only_reads \<O> sb\<rbrakk>
  \<Longrightarrow> 
  \<exists>xs ys t v. sb=xs@ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> all_acquired xs \<and> a \<in> read_only (share xs \<S>) \<and>
              a \<notin> read_only_reads \<O> xs"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	a_nro: "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	a_ro': "a \<in> read_only_reads (\<O> \<union> A - R) sb" and 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from R_owns a_unowned
      have a_R: "a \<notin> R"
	by auto
      show ?thesis
      proof (cases "a \<in> A")
	case True
	from read_only_read_witness [OF nvo' a_ro']
	obtain xs ys t v' where
	  sb: "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys" and
	  ro: "a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
	  a_ro_xs: "a \<notin> read_only_reads (\<O> \<union> A - R) xs"
	  by blast

	with True show ?thesis
	  apply -
	  apply (rule_tac x="x#xs" in exI)
	  apply (rule_tac x=ys in exI)
	  apply (rule_tac x=t in exI)
	  apply (rule_tac x=v' in exI)
	  apply (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
	  done
      next
	case False
	with a_unowned R_owns a_nro L_A A_R
	obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
	  by (force simp add: in_read_only_convs)

	from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_ro']
	obtain xs ys t v' where "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
	  a \<in> all_acquired xs \<and> a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<and> 
	  a \<notin> read_only_reads (\<O> \<union> A - R) xs"
	  by blast

	then show ?thesis
	  apply -
	  apply (rule_tac x="x#xs" in exI)
	  apply (rule_tac x=ys in exI)
	  apply (rule_tac x=t in exI)
	  apply (rule_tac x=v' in exI)
	  apply (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
	  done
      qed
    next
      case False
      from Cons.prems obtain 
	consis': "sharing_consistent \<S> \<O> sb" and
	a_nro': "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	a_ro': "a \<in> read_only_reads \<O> sb" and
	"a' \<in> \<O>" and
	nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)
      
      from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro']
      obtain xs ys t v' where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
         a \<in> all_acquired xs \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
	by blast

      then show ?thesis
	apply -
	apply (rule_tac x="x#xs" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b False)
	done
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads \<O> sb" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb"
      by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)

    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro']
    obtain xs ys t v' where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
      a \<in> all_acquired xs \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
      by blast

    with Cons.prems show ?thesis
      apply -
      apply (rule_tac x="x#xs" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v' in exI)
      apply (clarsimp simp add: Read\<^sub>s\<^sub>b)
      done
  next
    case Prog\<^sub>s\<^sub>b
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads \<O> sb" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb"
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro']
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
      a \<in> all_acquired xs \<and> a \<in> read_only (share xs \<S>) \<and> a \<notin> read_only_reads \<O> xs"
      by blast

    then show ?thesis
      apply -
      apply (rule_tac x="x#xs" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Prog\<^sub>s\<^sub>b)
      done
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
      a_nro: "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads (\<O> \<union> A - R) sb" and 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb"
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from R_owns a_unowned
    have a_R: "a \<notin> R"
      by auto
    show ?thesis
    proof (cases "a \<in> A")
      case True
      from read_only_read_witness [OF nvo' a_ro']
      obtain xs ys t v' where
	sb: "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys" and
	ro: "a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L))" and
	a_ro_xs: "a \<notin> read_only_reads (\<O> \<union> A - R) xs"
        by blast

      with True show ?thesis
        apply -
        apply (rule_tac x="x#xs" in exI)
        apply (rule_tac x=ys in exI)
        apply (rule_tac x=t in exI)
        apply (rule_tac x=v' in exI)
        apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
        done
    next
      case False
      with a_unowned R_owns a_nro L_A A_R
      obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
        by (force simp add: in_read_only_convs)

      from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_ro']
      obtain xs ys t v' where "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
	a \<in> all_acquired xs \<and> a \<in> read_only (share xs (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)) \<and> 
	a \<notin> read_only_reads (\<O> \<union> A - R) xs"
        by blast

      then show ?thesis
        apply -
	apply (rule_tac x="x#xs" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
	done
    qed
  qed
qed
    


lemma unforwarded_not_written: "\<And>W. a \<in> unforwarded_non_volatile_reads sb W \<Longrightarrow> a \<notin> W"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W')
    from Cons.prems
    have "a \<in> unforwarded_non_volatile_reads sb (insert a' W)"
      by (clarsimp simp add: Write\<^sub>s\<^sub>b )
    from Cons.hyps [OF this]
    have "a \<notin> insert a' W".
    then show ?thesis
      by blast
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    with Cons.hyps [of W] Cons.prems show ?thesis
      by (auto split: if_split_asm)
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps [of W] Cons.prems show ?thesis
      by (auto split: if_split_asm)
  next
    case Ghost\<^sub>s\<^sub>b
    with Cons.hyps [of W] Cons.prems show ?thesis
      by (auto split: if_split_asm)
  qed
qed

   
lemma unforwarded_witness:"\<And>X.
  \<lbrakk>a \<in> unforwarded_non_volatile_reads sb X\<rbrakk>
  \<Longrightarrow> 
  \<exists>xs ys t v. sb=xs@ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      
      from Cons.prems obtain 
	a_unforw: "a \<in> unforwarded_non_volatile_reads sb (insert a' X)" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from unforwarded_not_written  [OF a_unforw]
      have a'_a: "a'\<noteq>a"
	by auto

      from Cons.hyps [OF a_unforw]
      obtain xs ys t v where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
	a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	by blast
      
      thus ?thesis
	using a'_a
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b True)
	done
    next
      case False
      from Cons.prems obtain 
	a_unforw: "a \<in> unforwarded_non_volatile_reads sb (insert a' X)" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b False)

      from unforwarded_not_written  [OF a_unforw]
      have a'_a: "a'\<noteq>a"
	by auto

      from Cons.hyps [OF a_unforw] 
      obtain xs ys t v where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
	a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	by blast
      
      thus ?thesis
	using a'_a
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b False)
	done
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    show ?thesis
    proof (cases "a'=a \<and> a \<notin> X \<and> \<not> volatile")
      case True
      
      with True show ?thesis
	apply -
	apply (rule_tac x="[]" in exI)
	apply (rule_tac x="sb" in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Read\<^sub>s\<^sub>b)
	done
    next
      case False
      note not_ror = this
      with Cons.prems obtain a_unforw: "a \<in> unforwarded_non_volatile_reads sb X" 
	by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)

      from Cons.hyps [OF a_unforw]
      obtain xs ys t v where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
	a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	by blast
      
      thus ?thesis
	apply -
	apply (rule_tac x="(x#xs)" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v in exI)
	apply (clarsimp simp add: Read\<^sub>s\<^sub>b)
	done
    qed
  next
    case Prog\<^sub>s\<^sub>b
    from Cons.prems obtain a_unforw: "a \<in> unforwarded_non_volatile_reads sb X" 
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    from Cons.hyps [OF a_unforw]
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
      a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by blast
    
    thus ?thesis
      apply -
      apply (rule_tac x="(x#xs)" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Prog\<^sub>s\<^sub>b)
      done
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain a_unforw: "a \<in> unforwarded_non_volatile_reads sb X" 
      by (auto simp add: Ghost\<^sub>s\<^sub>b)

    from Cons.hyps [OF a_unforw]
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
      a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by blast
    
    thus ?thesis
      apply -
      apply (rule_tac x="(x#xs)" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
      done
  qed
qed


lemma read_only_read_acquired_unforwarded_witness: "\<And>\<S> \<O> X.
  \<lbrakk>non_volatile_owned_or_read_only True \<S> \<O> sb; sharing_consistent \<S> \<O> sb;
  a \<notin> read_only \<S>; a \<notin> \<O>; a \<in> read_only_reads \<O> sb;
  a \<in> unforwarded_non_volatile_reads sb X \<rbrakk>
  \<Longrightarrow> 
  \<exists>xs ys t v. sb=xs@ Read\<^sub>s\<^sub>b False a t v # ys \<and> a \<in> all_acquired xs \<and>
              a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	a_nro: "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	a_ro': "a \<in> read_only_reads (\<O> \<union> A - R) sb" and 
	A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
	R_owns: "R \<subseteq> \<O>" and
	consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
	a_unforw: "a \<in> unforwarded_non_volatile_reads sb (insert a' X)" 
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True)

      from unforwarded_not_written [OF a_unforw]
      have a_notin: "a \<notin> insert a' X".
      from R_owns a_unowned
      have a_R: "a \<notin> R"
	by auto
      show ?thesis
      proof (cases "a \<in> A")
	case True

	from unforwarded_witness [OF a_unforw]
	obtain xs ys t v' where
	  sb: "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys" and
	  a_xs: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	  by blast

	with True a_notin show ?thesis
	  apply -
	  apply (rule_tac x="x#xs" in exI)
	  apply (rule_tac x=ys in exI)
	  apply (rule_tac x=t in exI)
	  apply (rule_tac x=v' in exI)
	  apply (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
	  done
      next
	case False
	with a_unowned R_owns a_nro L_A A_R
	obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
	  by (force simp add: in_read_only_convs)

	from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_ro' a_unforw]
	obtain xs ys t v' where "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
	  a \<in> all_acquired xs \<and> 
	  a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	  by blast

	with a_notin show ?thesis
	  apply -
	  apply (rule_tac x="x#xs" in exI)
	  apply (rule_tac x=ys in exI)
	  apply (rule_tac x=t in exI)
	  apply (rule_tac x=v' in exI)
	  apply (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
	  done
      qed
    next
      case False
      from Cons.prems obtain 
	consis': "sharing_consistent \<S> \<O> sb" and
	a_nro': "a \<notin> read_only \<S>" and
	a_unowned: "a \<notin> \<O>" and
	a_ro': "a \<in> read_only_reads \<O> sb" and
	"a' \<in> \<O>" and
	nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and
	a_unforw': "a \<in> unforwarded_non_volatile_reads sb (insert a' X)"
	by (auto simp add: Write\<^sub>s\<^sub>b False split: if_split_asm)
      
      from unforwarded_not_written [OF a_unforw']
      have a_notin: "a \<notin> insert a' X".

      from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro' a_unforw']
      obtain xs ys t v' where
	"sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
         a \<in> all_acquired xs \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
	by blast

      with a_notin show ?thesis
	apply -
	apply (rule_tac x="x#xs" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Write\<^sub>s\<^sub>b False)
	done
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a' t v)
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads \<O> sb" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb X"
      by (auto simp add: Read\<^sub>s\<^sub>b split: if_split_asm)

    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro' a_unforw]
    obtain xs ys t v' where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
      a \<in> all_acquired xs \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by blast

    with Cons.prems show ?thesis
      apply -
      apply (rule_tac x="x#xs" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v' in exI)
      apply (clarsimp simp add: Read\<^sub>s\<^sub>b)
      done
  next
    case Prog\<^sub>s\<^sub>b
    from Cons.prems
    obtain 	
      consis': "sharing_consistent \<S> \<O> sb" and
      a_nro': "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads \<O> sb" and
      nvo': "non_volatile_owned_or_read_only True \<S> \<O> sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb X"
      by (auto simp add: Prog\<^sub>s\<^sub>b)

    from Cons.hyps [OF nvo' consis' a_nro' a_unowned a_ro' a_unforw]
    obtain xs ys t v where
      "sb = xs @ Read\<^sub>s\<^sub>b False a t v # ys \<and>
      a \<in> all_acquired xs \<and> a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
      by blast

    then show ?thesis
      apply -
      apply (rule_tac x="x#xs" in exI)
      apply (rule_tac x=ys in exI)
      apply (rule_tac x=t in exI)
      apply (rule_tac x=v in exI)
      apply (clarsimp simp add: Prog\<^sub>s\<^sub>b)
      done
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.prems obtain 
      nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
      a_nro: "a \<notin> read_only \<S>" and
      a_unowned: "a \<notin> \<O>" and
      a_ro': "a \<in> read_only_reads (\<O> \<union> A - R) sb" and 
      A_shared_owns: "A \<subseteq> dom \<S> \<union> \<O>" and L_A: "L \<subseteq> A" and A_R: "A \<inter> R = {}" and
      R_owns: "R \<subseteq> \<O>" and
      consis': "sharing_consistent (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and 
      a_unforw: "a \<in> unforwarded_non_volatile_reads sb (X)" 
      by (clarsimp simp add: Ghost\<^sub>s\<^sub>b)

    from unforwarded_not_written [OF a_unforw]
    have a_notin: "a \<notin> X".
    from R_owns a_unowned
    have a_R: "a \<notin> R"
      by auto
    show ?thesis
    proof (cases "a \<in> A")
      case True

      from unforwarded_witness [OF a_unforw]
      obtain xs ys t v' where
	sb: "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys" and
	a_xs: "a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
        by blast

      with True a_notin show ?thesis
        apply -
        apply (rule_tac x="x#xs" in exI)
        apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
	done
    next
      case False
      with a_unowned R_owns a_nro L_A A_R
      obtain a_nro': "a \<notin> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" and a_unowned': "a \<notin> \<O> \<union> A - R"
        by (force simp add: in_read_only_convs)

      from Cons.hyps [OF nvo' consis' a_nro' a_unowned' a_ro' a_unforw]
      obtain xs ys t v' where "sb = xs @ Read\<^sub>s\<^sub>b False a t v' # ys \<and>
	a \<in> all_acquired xs \<and> 
	a \<notin> outstanding_refs is_Write\<^sub>s\<^sub>b xs"
        by blast

      with a_notin show ?thesis
        apply -
	apply (rule_tac x="x#xs" in exI)
	apply (rule_tac x=ys in exI)
	apply (rule_tac x=t in exI)
	apply (rule_tac x=v' in exI)
	apply (clarsimp simp add: Ghost\<^sub>s\<^sub>b)
	done
    qed
  qed
qed


lemma takeWhile_prefix: "\<exists>ys. takeWhile P xs @ ys = xs"
apply (induct xs)
apply auto
done

lemma unforwarded_empty_extend: 
  "\<And>W. x \<in> unforwarded_non_volatile_reads sb {}  \<Longrightarrow> x \<notin> W \<Longrightarrow> x \<in> unforwarded_non_volatile_reads sb W"
apply (induct sb)
apply  clarsimp
subgoal for a sb W
apply (case_tac a) 
apply    clarsimp
apply    (frule unforwarded_not_written)
apply    (drule_tac W="{}" in unforwarded_non_volatile_reads_antimono_in)
apply    blast
apply   (auto split: if_split_asm)
done
done

lemma notin_unforwarded_empty: 
  "\<And>W. a \<notin> unforwarded_non_volatile_reads sb W \<Longrightarrow> a \<notin> W \<Longrightarrow> a \<notin> unforwarded_non_volatile_reads sb {}"
using unforwarded_empty_extend
by blast

lemma 
  assumes ro: "a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>'"
  assumes a_in: "a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R) "
  shows "a \<in> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R) "
  using ro a_in
  by (auto simp add: in_read_only_convs)

lemma 
  assumes ro: "a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>'"
  assumes a_in: "a \<in> read_only (\<S> \<ominus>\<^bsub>A\<^esub> L) "
  shows "a \<in> read_only (\<S>' \<ominus>\<^bsub>A\<^esub> L) "
  using ro a_in
  by (auto simp add: in_read_only_convs)

lemma non_volatile_owned_or_read_only_read_only_reads_eq:
  "\<And>\<S> \<S>' \<O> pending_write.
  \<lbrakk>non_volatile_owned_or_read_only pending_write \<S> \<O> sb;
   \<forall>a \<in> read_only_reads \<O> sb. a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>' 
  \<rbrakk>
  \<Longrightarrow> non_volatile_owned_or_read_only pending_write \<S>' \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	ro': "\<forall>a\<in>read_only_reads (\<O> \<union> A - R) sb. a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>'"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)

      from ro'
      have ro'':"\<forall>a\<in>read_only_reads (\<O> \<union> A - R) sb.
        a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF nvo' ro'']
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
    next
      case False
      with Cons.hyps [of pending_write \<S> \<O> \<S>'] Cons.prems show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    show ?thesis
    proof (cases volatile)
      case True
      with Cons.hyps [of pending_write \<S> \<O> \<S>'] Cons.prems show ?thesis
	by (auto simp add: Read\<^sub>s\<^sub>b)
    next
      case False
      note non_vol = this
      show ?thesis
      proof (cases "a \<in> \<O>")
	case True
	with Cons.hyps [of pending_write \<S> \<O> \<S>'] Cons.prems show ?thesis
	  by (auto simp add: Read\<^sub>s\<^sub>b non_vol)
      next
	case False
	from Cons.prems Cons.hyps [of pending_write \<S> \<O> \<S>'] show ?thesis 
	  by (clarsimp simp add: Read\<^sub>s\<^sub>b non_vol False)
      qed
    qed
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps [of pending_write \<S> \<O> \<S>'] Cons.prems show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [of pending_write "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "\<O> \<union> A - R" "\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b in_read_only_convs)
  qed
qed


lemma non_volatile_owned_or_read_only_read_only_reads_eq':
  "\<And>\<S> \<S>' \<O>.
  \<lbrakk>non_volatile_owned_or_read_only False \<S> \<O> sb;
   \<forall>a \<in> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
         (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb). a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>' 
  \<rbrakk>
  \<Longrightarrow> non_volatile_owned_or_read_only False \<S>' \<O> sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) (\<O> \<union> A - R) sb" and
	ro': "\<forall>a\<in>read_only_reads (\<O> \<union> A - R) sb. a \<in> read_only \<S> \<longrightarrow> a \<in> read_only \<S>'"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)

      from ro'
      have ro'':"\<forall>a\<in>read_only_reads (\<O> \<union> A - R) sb.
        a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs)
      from non_volatile_owned_or_read_only_read_only_reads_eq [OF nvo' ro'']
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
    next
      case False
      with Cons.hyps [of \<S> \<O> \<S>'] Cons.prems show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    show ?thesis
    proof (cases volatile)
      case True
      with Cons.hyps [of \<S> \<O> \<S>'] Cons.prems show ?thesis
	by (auto simp add: Read\<^sub>s\<^sub>b)
    next
      case False
      note non_vol = this
      show ?thesis
      proof (cases "a \<in> \<O>")
	case True
	with Cons.hyps [of \<S> \<O> \<S>'] Cons.prems show ?thesis
	  by (auto simp add: Read\<^sub>s\<^sub>b non_vol)
      next
	case False
	from Cons.prems Cons.hyps [of \<S> \<O> \<S>'] show ?thesis 
	  by (clarsimp simp add: Read\<^sub>s\<^sub>b non_vol False)
      qed
    qed
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps [of \<S> \<O> \<S>'] Cons.prems show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "\<O> \<union> A - R" "\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b in_read_only_convs)
  qed
qed


lemma no_write_to_read_only_memory_read_only_reads_eq:
  "\<And>\<S> \<S>'.
  \<lbrakk>no_write_to_read_only_memory \<S> sb;
   \<forall>a \<in> outstanding_refs is_Write\<^sub>s\<^sub>b sb. a \<in> read_only \<S>' \<longrightarrow> a \<in> read_only \<S> 
  \<rbrakk>
  \<Longrightarrow> no_write_to_read_only_memory \<S>' sb"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	nvo': "no_write_to_read_only_memory (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) sb" and
	ro': "\<forall>a\<in>outstanding_refs is_Write\<^sub>s\<^sub>b sb. a \<in> read_only \<S>' \<longrightarrow> a \<in> read_only \<S>" and
	not_ro: "a \<notin> read_only \<S>'"
	by (auto simp add: Write\<^sub>s\<^sub>b volatile)

      from ro'
      have ro'':"\<forall>a\<in>outstanding_refs is_Write\<^sub>s\<^sub>b sb.
        a \<in> read_only (\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) \<longrightarrow> a \<in> read_only (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)"
	by (auto simp add: in_read_only_convs)
      from Cons.hyps [OF nvo' ro''] not_ro
      show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b volatile)
    next
      case False
      with Cons.hyps [of \<S> \<S>'] Cons.prems show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b)
    qed
  next
    case (Read\<^sub>s\<^sub>b volatile a t v)
    with Cons.hyps [of \<S> \<S>'] Cons.prems show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)  
  next
    case Prog\<^sub>s\<^sub>b
    with Cons.hyps [of \<S> \<S>'] Cons.prems show ?thesis
      by (auto)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    from Cons.hyps [of "(\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L)" "\<S>' \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L"] Cons.prems
    show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b in_read_only_convs)
  qed
qed


lemma reads_consistent_drop:
  "reads_consistent False \<O> m sb
  \<Longrightarrow> reads_consistent True  
      (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
      (flush (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) m)
      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
using reads_consistent_append [of False \<O> m "(takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)" 
  "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"]
apply (cases "outstanding_refs is_volatile_Write\<^sub>s\<^sub>b sb = {}")
apply  (clarsimp simp add: outstanding_vol_write_take_drop_appends 
  takeWhile_not_vol_write_outstanding_refs dropWhile_not_vol_write_empty)
apply(clarsimp simp add: outstanding_vol_write_take_drop_appends 
  takeWhile_not_vol_write_outstanding_refs dropWhile_not_vol_write_empty )
apply (case_tac "(dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)")
apply  (fastforce simp add: outstanding_refs_conv)
apply (frule dropWhile_ConsD)
apply (clarsimp split: memref.splits)
done

(* FIXME: subsumes outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired_drop *)
lemma outstanding_refs_non_volatile_Read\<^sub>s\<^sub>b_all_acquired_dropWhile': 
"\<And>m \<S> \<O> pending_write. 
  \<lbrakk>reads_consistent pending_write \<O> m sb;non_volatile_owned_or_read_only pending_write \<S> \<O> sb;  
a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)\<rbrakk>
\<Longrightarrow> a \<in> \<O> \<or> a \<in> all_acquired sb \<or>
    a \<in> read_only_reads (acquired True (takeWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb) \<O>) 
      (dropWhile (Not \<circ> is_volatile_Write\<^sub>s\<^sub>b) sb)"
proof (induct sb)
  case Nil thus ?case by simp
next
  case (Cons x sb)
  show ?case
  proof (cases x)
    case (Write\<^sub>s\<^sub>b volatile a' sop v A L R W)
    show ?thesis
    proof (cases volatile)
      case True
      note volatile=this
      from Cons.prems obtain 
	non_vo: "non_volatile_owned_or_read_only True (\<S> \<oplus>\<^bsub>W\<^esub> R \<ominus>\<^bsub>A\<^esub> L) 
	            (\<O> \<union> A - R) sb" and
        out_vol: "outstanding_refs is_volatile_Read\<^sub>s\<^sub>b sb = {}" and
	out: "a \<in> outstanding_refs is_non_volatile_Read\<^sub>s\<^sub>b sb"
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True) 
      show ?thesis
      proof (cases "a \<in> \<O>")
	case True
	show ?thesis
	by (clarsimp simp add: Write\<^sub>s\<^sub>b True volatile)
      next
	case False
	from outstanding_non_volatile_Read\<^sub>s\<^sub>b_acquired_or_read_only_reads [OF non_vo out]
	have a_in: "a \<in> acquired_reads True sb (\<O> \<union> A - R) \<or>
                    a \<in> read_only_reads (\<O> \<union> A - R) sb"
	  by auto
	with acquired_reads_all_acquired [of True sb "(\<O> \<union> A - R)"]
	show ?thesis 
	  by (auto simp add: Write\<^sub>s\<^sub>b volatile)
      qed

    next
      case False
      with Cons show ?thesis
	by (auto simp add: Write\<^sub>s\<^sub>b False)
    qed
  next
    case Read\<^sub>s\<^sub>b
    with Cons show ?thesis
      apply (clarsimp simp del: o_apply simp add: Read\<^sub>s\<^sub>b 
	acquired_takeWhile_non_volatile_Write\<^sub>s\<^sub>b split: if_split_asm)
      apply auto
      done
  next
    case Prog\<^sub>s\<^sub>b
    with Cons show ?thesis
      by (auto simp add: Read\<^sub>s\<^sub>b)
  next
    case (Ghost\<^sub>s\<^sub>b A L R W)
    with Cons.hyps [of pending_write "\<O> \<union> A - R" "m" "\<S> \<oplus>\<^bsub>W\<^esub> R  \<ominus>\<^bsub>A\<^esub> L"]  read_only_reads_antimono [of \<O> "\<O> \<union> A - R"]
      Cons.prems show ?thesis
      by (auto simp add: Ghost\<^sub>s\<^sub>b)
  qed
qed



end
